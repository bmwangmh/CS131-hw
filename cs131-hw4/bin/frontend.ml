open Ll
open Llutil
open Ast

(* This file is where much of the work of the project will be carried out. 
   Follow the instructions on the project web site, but first skim through
   this file to see what it contains.   
*)


(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements that will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

(* The type of streams of LLVMLite instructions. Note that to improve performance,
 * we will emit the instructions in reverse order. That is, the LLVMLite code:
 *     %1 = mul i64 2, 2
 *     %2 = add i64 1, %1
 *     br label %l1
 * would be constructed as a stream as follows:
 *     I ("1", Binop (Mul, I64, Const 2L, Const 2L))
 *     >:: I ("2", Binop (Add, I64, Const 1L, Id "1"))
 *     >:: T (Br "l1")
 *)
type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearerhw, I may do that for next time around.]]

 
   Consider globals7.oat (in hw4programs)

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: to compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]


(* aux functions *)
let cmp_bop (b:Ast.binop) (ty:Ll.ty) (op1:Ll.operand) (op2:Ll.operand) (ret:Ll.uid) : stream =
  let trans_bop (b:Ast.binop) : Ll.bop = match b with Add -> Add|Sub -> Sub|Mul -> Mul|IAnd -> And|IOr -> Or|Shl -> Shl|Shr -> Lshr
  |Sar -> Ashr|And -> And|Or -> Or|_ -> failwith "transbop: invalid binop" in
  let trans_cnd (b:Ast.binop) : Ll.cnd = match b with Eq -> Eq|Neq -> Ne|Gt -> Sgt|Gte -> Sge|Lt -> Slt|Lte -> Sle
  |_ -> failwith "trans_cnd: invalid binop" in
  match b with 
  |Eq|Neq|Lt|Lte|Gt|Gte -> [I (ret, Icmp ((trans_cnd b),ty , op1, op2))]
  |_ -> [I (ret, Binop ((trans_bop b),ty , op1, op2))]

let cmp_uop (u:Ast.unop) (ty:Ll.ty) (op:Ll.operand) (ret:Ll.uid) : stream =
  match u with 
  |Neg -> [I (ret, Binop (Sub ,ty , Const 0L, op))]
  |Lognot -> [I (ret, Binop (Xor ,ty , Const 1L, op))]
  |Bitnot -> [I (ret, Binop (Xor ,ty , Const (-1L), op))]

let cmp_deref (ty:Ll.ty) : Ll.ty =
  match ty with
  |Ptr dty -> dty
  |_ -> failwith "cmp_deref: not a pointer"
(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)
let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream = match exp.elt with
  |CNull rty -> Ptr (cmp_rty rty), Null, []
  |CBool v -> I1, Const (if v then 1L else 0L), []
  |CInt v -> I64, Const v, []
  |CStr st -> let gstrsym = gensym "str" in 
    let arr_of_str = Array (String.length st + 1, I8) in
    let strsym = gensym "str" in 
    Ptr I8, Id strsym, [G (gstrsym, (arr_of_str, GString st))] 
    >:: I (strsym, (Gep (Ptr arr_of_str, Gid gstrsym, [Const 0L; Const 0L])))
  |CArr (ty, el) -> let aty, aop, acode = oat_alloc_array ty (Const (Int64.of_int (List.length el))) in
    let tsym = gensym "tmp" in
    let nc = Ctxt.add c tsym (Ptr aty, Id tsym) in
    let cmp_arr_idx (idx:int64) (exp:Ast.exp node) : stream = 
      let ety, eop, ecode = cmp_exp c exp in
      let _, lop, lcode = cmp_lhs nc (no_loc (Index (no_loc (Id tsym), no_loc (CInt idx)))) in
      ecode >@ lcode >:: I (gensym "store", Store (ety, eop, lop))
    in
    let _, stm = List.fold_left (fun (acc, s) e -> 
      (Int64.succ acc, 
      s >@ cmp_arr_idx acc e)) 
      (0L, []) el
    in
  aty, aop, acode >:: I (tsym, Alloca aty) >:: I (gensym "store", Store (aty, aop, Id tsym)) >@ stm
  |NewArr (ty, e) -> let _, lop, lcode = cmp_exp c e in
    let aty, aop, acode = oat_alloc_array ty lop in
    let tsym = gensym "tmp" in
    let szsym = gensym "size" in
    let nc = Ctxt.add (Ctxt.add c tsym (Ptr aty, Id tsym)) 
      szsym (Ptr I64, Id szsym) in
    let i = gensym "i" in
    let _, stm = cmp_stmt nc Void (no_loc (
      For (
        [i, no_loc (CInt 0L)],
        Some (no_loc (Bop (Lt, no_loc(Id i), no_loc(Id szsym)))),
        Some (no_loc (Assn (no_loc(Id i),
          no_loc(Bop (Add, no_loc(Id i), no_loc(CInt 1L)))))),
        [no_loc(Assn (no_loc(Index (no_loc(Id tsym), no_loc(Id i))),
          match ty with TInt -> no_loc(CInt 0L)|TBool -> no_loc(CBool false)
          |_ -> failwith "cmp_exp:unsupplied newarr type"))]
      )
    ))
    in
    aty, aop, lcode >@ acode
    >:: I (tsym, Alloca aty) >:: I (szsym, Alloca I64)
    >:: I (gensym "store", Store (aty, aop, Id tsym))
    >:: I (gensym "store", Store (I64, lop, Id szsym))
    >@ stm
  |Bop (bp, e1, e2) -> let ret = gensym "bop" in
    let _, _, rt = typ_of_binop bp in
    let oty, op1, code1 = cmp_exp c e1 in 
    let _, op2, code2 = cmp_exp c e2 in
    cmp_ty rt, Ll.Id ret, code1 >@ code2 >@ cmp_bop bp oty op1 op2 ret 
  |Uop (up, e) -> let ret = gensym "uop" in
    let _, rt = typ_of_unop up in
    let oty, op, code = cmp_exp c e in
    cmp_ty rt, Ll.Id ret, code >@ cmp_uop up oty op ret
  |Call (e, args) -> let fty, fop = match e.elt with
    |Id id -> Ctxt.lookup_function id c
    |_ -> failwith "cmp_exp: invalid call expression" in
    let tyl, rty = match fty with
    |Ptr (Fun (tyl, rty)) -> tyl, rty
    |_ -> failwith "cmp_exp: invalid call type" in
    let ops, ss = List.fold_left 
    (fun (acc_ops, acc_ss) e -> let ty, op, s = cmp_exp c e in
        (ty, op) :: acc_ops, s >@ acc_ss)
      ([], []) args in
    let ops = List.rev ops in
    let res = gensym "call" in
      rty, Id res, ss >:: I (res, Call (rty, fop, ops))
  |Id id -> let idsym = gensym id in
    let ty, op = Ctxt.lookup id c in
    (cmp_deref ty), Id idsym , [I (idsym, Load (ty, op))]
  |Index (arr, idx) -> let pty, op, pcode = cmp_lhs c exp in
      let res = gensym "result" in
      (cmp_deref pty), Id res, pcode >:: I (res, Load (pty, op))

and cmp_lhs (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream = match exp.elt with
  |Id id -> let idsym = gensym id in
    let ty, op = Ctxt.lookup id c in
    ty, op, []
  |Index (arr, idx) -> 
    let aty, aop, acode = cmp_exp c arr in
    let ety = match aty with |Ptr Struct [I64; Array (0, ety)] -> ety 
    |_ -> failwith "cmp_lhs: not an array" in
    let _, iop, icode = cmp_exp c idx in
    let idsym = gensym "index" in
    Ptr ety, Id idsym, 
    acode >@ icode >:: I (idsym, Gep (aty, aop, [Const 0L; Const 1L; iop]))
  |_ -> failwith "cmp_lhs: unimplemented"

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)
and cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream = match stmt.elt with
  |Ret None -> c, [T (Ret (rt, None))]
  |Ret Some rval -> let (_, op, stm) = cmp_exp c rval in
    c, stm >@ [T (Ret (rt, Some op))]
  |Assn (lhs, e) -> let _, lop, lcode = cmp_lhs c lhs in
    let rty, rop, rcode = cmp_exp c e in
    c, lcode >@ rcode >:: I (gensym "store", Store (rty, rop, lop))
  |Decl (id, v) -> let (ty, op, stm) = cmp_exp c v in
    let vid = gensym id in
    (Ctxt.add c id (Ptr ty, Id vid)), stm >:: E (vid, Alloca ty) >:: I (gensym "store", Store (ty, op, Id vid))
  |If (cnd, s1, s2) -> let _, op, ifcode = cmp_exp c cnd in
    let _, thcode = cmp_block c rt s1 in
    let _, elcode = cmp_block c rt s2 in
    let thlbl = gensym "then" in
    let ellbl = gensym "else" in
    let endlbl = gensym "end" in
    c, ifcode >:: T (Cbr (op, thlbl, ellbl))  
      >:: L thlbl >@ thcode >:: T (Br endlbl) 
      >:: L ellbl >@ elcode >:: T (Br endlbl) 
      >:: L endlbl
  |While (cnd, s) -> let _, op, ifcode = cmp_exp c cnd in
    let _, code = cmp_block c rt s in
    let stlbl = gensym "while" in
    let blbl = gensym "body" in
    let endlbl = gensym "end" in
    c, [T (Br stlbl)] 
      >:: L stlbl >@ ifcode >:: T (Cbr (op, blbl, endlbl))
      >:: L blbl >@ code >:: T (Br stlbl)
      >:: L endlbl
  |For (vdecls, cnd, tail, blk) -> let vals = List.map (fun vd -> no_loc (Decl vd)) vdecls in
    let nblk = blk @ (match tail with None -> [] |Some ntail -> [ntail]) in
    let ncnd = match cnd with None -> no_loc (CBool true)| Some cond -> cond in
    c, snd (cmp_block c rt (vals @ [no_loc (While (ncnd, nblk))]))
  |SCall (e, el) -> let _, _, s = cmp_exp c (no_loc (Call (e, el))) in
    c, s


(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.fold_left (fun c -> function
  | Ast.Gvdecl { elt={ name; init } } ->
     let gt = match init.elt with
      |CNull rty -> TRef rty
      |CBool _ -> TBool
      |CInt _ -> TInt
      |CStr _ -> TRef RString
      |CArr (ty, _) -> TRef (RArray ty)
      |NewArr (ty, _) -> TRef (RArray ty)
      |_ -> failwith "cmp_global_ctxt: invalid initializer" 
    in
     Ctxt.add c name (Ptr(cmp_ty gt), Gid name)
  | _ -> c
) c p 

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)
let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let rt = cmp_ret_ty f.elt.frtyp in
  let f_ty = (List.map (fun (arg, _) -> cmp_ty arg) f.elt.args), rt in
  let f_param = List.map snd f.elt.args in
  let pass_arg (c:Ctxt.t) ((ty, id):(Ast.ty * Ast.id)) : Ctxt.t * (uid * insn) list =
    let ty_arg = cmp_ty ty in
    let para = gensym id in
    let nc = Ctxt.add c id (Ptr ty_arg, Id para) in
    nc, [para, Alloca ty_arg; gensym "store", Store (ty_arg, Id id, Id para)]
  in
  let nc, pcode = List.fold_left 
    (fun (c, code) (ty, id) -> let nc, ncode = pass_arg c (ty, id) in nc, code @ ncode)
    (c, []) f.elt.args in
  let plbl = gensym "prework" in
  let pblk = {insns = pcode; term = "", Br plbl} in
  let (f_entry, f_body_cfg), gdecls = cfg_of_stream (snd (cmp_block nc rt f.elt.body)) in
  let f_cfg = pblk , ((plbl, f_entry)::f_body_cfg) in
    {f_ty; f_param; f_cfg}, gdecls


(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)
let rec cmp_gexp (c:Ctxt.t) (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  |CNull rty -> (Ptr (cmp_rty rty), GNull), []
  |CBool v -> (I1, GInt (if v then 1L else 0L)), []
  |CInt v -> (I64, GInt v), []
  |CStr st -> let strsym = gensym "gstr" in 
    let arr_of_str = Array (String.length st + 1, I8) in
    let cast = GBitcast (Ptr arr_of_str, GGid strsym, Ptr I8) in
    ((Ptr I8, cast), [strsym, (arr_of_str, GString st)])
  |CArr (ty, es) -> let l = List.length es in
    let ety = cmp_ty ty in
    let arr_ty = Struct [I64; Array (l, ety)] in
    let arrsym = gensym "garr" in
    let gexps = List.map (cmp_gexp c) es in
    let narr_ty = Struct [I64; Array (0, ety)] in
    let cast = GBitcast (Ptr arr_ty, GGid arrsym, Ptr narr_ty) in
    (Ptr narr_ty, cast)
    ,(arrsym, (arr_ty, GStruct [(I64, GInt (Int64.of_int l));
    (Array (l, ety), GArray (List.map fst gexps))]))
    ::List.flatten (List.map snd gexps)
  |_ -> failwith "cmp_gexp: invalid global type"


(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
