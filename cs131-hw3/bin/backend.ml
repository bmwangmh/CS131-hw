(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

module Platform = Util.Platform

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip) %rax.

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins = function
  |Ll.Const i -> (Movq, [(Imm (Lit i)); dest])
  |Ll.Null -> (Movq, [(Imm (Lit 0L)); dest])
  |Ll.Gid gid -> (Leaq, [Ind3 (Lbl (Platform.mangle gid), Rip); dest])
  |Ll.Id id -> (Movq, [lookup ctxt.layout id; dest])



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: Don't forget to preserve caller-save registers (only if needed). ]

   [ NOTE: Remember, call can use labels as immediates! You shouldn't need to 
     perform any RIP-relative addressing for this one. ]

   [ NOTE: It is the caller's responsibility to clean up arguments pushed onto
     the stack, so you must free the stack space after the call returns. (But 
     see below about alignment.) ]

   [ NOTE: One important detail about the ABI besides the conventions is that, 
  at the time the [callq] instruction is invoked, %rsp *must* be 16-byte aligned.  
  However, because LLVM IR provides the Alloca instruction, which can dynamically
  allocate space on the stack, it is hard to know statically whether %rsp meets
  this alignment requirement.  Moroever: since, according to the calling 
  conventions, stack arguments numbered > 6 are pushed to the stack, we must take
  that into account when enforcing the alignment property.  

  We suggest that, for a first pass, you *ignore* %rsp alignment -- only a few of 
  the test cases rely on this behavior.  Once you have everything else working,
  you can enforce proper stack alignment at the call instructions by doing 
  these steps: 
    1. *before* pushing any arguments of the call to the stack, ensure that the
    %rsp is 16-byte aligned.  You can achieve that with the x86 instruction:
    `andq $-16, %rsp`  (which zeros out the lower 4 bits of %rsp, possibly 
    "allocating" unused padding space on the stack)

    2. if there are an *odd* number of arguments that will be pushed to the stack
    (which would break the 16-byte alignment because stack slots are 8 bytes),
    allocate an extra 8 bytes of padding on the stack. 
    
    3. follow the usual calling conventions - any stack arguments will still leave
    %rsp 16-byte aligned

    4. after the call returns, in addition to freeing up the stack slots used by
    arguments, if there were an odd number of slots, also free the extra padding. 
    
  ]
*)




(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
  match t with 
  |Void|I8|Fun _ -> 0
  |I1|I64|Ptr _ -> 8
  |Array (n, tp) -> n * size_ty tdecls tp
  |Struct tl -> List.fold_left (fun acc tp -> acc + size_ty tdecls tp) 0 tl
  |Namedt lb -> size_ty tdecls (lookup tdecls lb)



(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let rec compile_ptr (ctxt:ctxt) (tp:Ll.ty) (path: Ll.operand list) : ins list =
  let open Asm in
  match tp with
  |Namedt tp -> compile_ptr ctxt (lookup ctxt.tdecls tp) path
  |Struct tl -> (match path with
    |(Const n) :: rest -> (match List.nth_opt tl (Int64.to_int n) with None -> failwith "compile_ptr: index out of range"
      |Some ntp -> let ofs = List.fold_left (fun acc i -> acc + i) 0 (List.filteri (fun i _ -> i < Int64.to_int n) (List.map (size_ty ctxt.tdecls) tl)) in
      [Addq, [~$ofs; ~%Rax]]
      @ compile_ptr ctxt ntp rest)
    |_ -> failwith "compile_ptr: unconst struct index")
  |Array (_, ntp) -> (match path with |(Const _ as idx) :: rest|(Id _ as idx) :: rest -> (compile_operand ctxt ~%Rcx idx)
      ::[Imulq, [~$(size_ty ctxt.tdecls ntp); ~%Rcx]; Addq, [~%Rcx; ~%Rax]]
      @ compile_ptr ctxt ntp rest
    |_ -> failwith "compile_ptr: invalid array index")
  |_ -> match path with [] -> []
    |_ -> failwith "compile_ptr: invalid type"


let rec compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  let open Asm in
  match op with
  |Namedt tp, op -> compile_gep ctxt (lookup ctxt.tdecls tp, op) path
  |Ptr tp, op -> (match op with 
    |Id _|Gid _ -> compile_operand ctxt ~%Rax op
    |_ -> failwith "compile_gep: invalid operand")
    :: (match path with |(Const _ as idx) :: rest|(Id _ as idx) :: rest -> [compile_operand ctxt ~%Rcx idx;
      Imulq, [~$(size_ty ctxt.tdecls tp); ~%Rcx]; Addq, [~%Rcx; ~%Rax]]
      @ compile_ptr ctxt tp rest
    |_ -> failwith "compile_gep: invalid index operand")
  |_ -> failwith "compile_gep: invalid type"



(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let rec is_loadable (ctxt:ctxt) (tp:ty): bool = match tp with
  |Ptr _ -> true
  |Namedt lb -> is_loadable ctxt (lookup ctxt.tdecls lb)
  |_ -> false

let is_callable (op:Ll.operand): bool = match op with
  |Id _ -> true
  |Gid _ -> true
  |_ -> false

(* Complete this helper function, which computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions. We will test this function as part of
   the hidden test cases.

   You might find it useful for compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  match n with
  |0 -> Reg Rdi
  |1 -> Reg Rsi
  |2 -> Reg Rcx
  |3 -> Reg Rdx
  |4 -> Reg R08
  |5 -> Reg R09
  |_ -> Ind3 (Lit (Int64.of_int(8 *(n - 4))), Rbp)

let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  let open Asm in
  let dest = lookup ctxt.layout uid in
    match i with
    |Binop (bop, _, op1 ,op2) -> [compile_operand ctxt ~%Rax op1; compile_operand ctxt ~%Rcx op2;
    ((match bop with Add -> Addq|Sub -> Subq|Mul -> Imulq|Shl -> Shlq|Lshr -> Shrq|Ashr -> Sarq|And -> Andq|Or -> Orq|Xor -> Xorq), [~%Rcx; ~%Rax]);
    Movq, [~%Rax; dest]]
    |Icmp (cnd, _, op1, op2) -> [compile_operand ctxt ~%Rax op1; compile_operand ctxt ~%Rcx op2;
    Movq, [~$0; ~%Rdx]; Cmpq, [~%Rcx; ~%Rax];
    Set (compile_cnd cnd), [~%Rdx]; Movq, [~%Rdx; dest]]
    |Alloca _ -> [Subq, [~$8; ~%Rsp]; Movq, [~%Rsp; dest]]
    |Load (tp, op) when is_loadable ctxt tp -> (match op with
      |Id id -> [Movq, [(lookup ctxt.layout id); ~%Rax]; Movq, [Ind2 Rax; ~%Rax]]
      |Gid id -> [Movq, [Ind3 (Lbl (Platform.mangle id), Rip); ~%Rax]]
      |_ -> failwith "compile_insn: invalid load")
      @ [Movq, [~%Rax; dest]]
    |Store (_, op1, op2) -> (compile_operand ctxt ~%Rax op1)
      ::(match op2 with
      |Id id -> [Movq, [(lookup ctxt.layout id); ~%Rcx]; Movq, [~%Rax; Ind2 Rcx]]
      |Gid id -> [Movq, [~%Rax; Ind3 (Lbl (Platform.mangle id), Rip)]]
      |_ -> failwith "compile_insn: invalid store")
    |Call (tp, op, args) when is_callable op-> 
      let cnt_stk = max 0 (List.length args) - 6 in
      [Subq,[~$16; ~%Rsp]]
      @ snd (List.fold_left (fun ((acc:int),(inss:ins list)) arg -> (acc + 1, inss
        @ (match acc with
        |n when n < 6 -> [compile_operand ctxt (arg_loc n) arg]
        |_ -> [compile_operand ctxt ~%Rax arg; Pushq, [~%Rax]])
        )) (0,[]) (List.map snd args))
      @ (match op with |Gid id -> [Callq, [Imm (Lbl (Platform.mangle id))]]
        |Id id -> [Movq, [(lookup ctxt.layout id); ~%Rax]; Callq, [~%Rax]]
        |_ -> failwith "compile_insn: invalid call")
      @ (if cnt_stk > 0 then [Addq, [~$(8 * cnt_stk); ~%Rsp]] else [])
      @ (if tp <> Void then [Movq, [~%Rax; lookup ctxt.layout uid]] else [])
    |Bitcast (_, op, _) -> [compile_operand ctxt ~%Rax op; Movq, [~%Rax; dest]]
    |Gep (tp, op, opl) -> compile_gep ctxt (tp, op) opl @ [Movq, [~%Rax; dest]]
    |_ -> failwith "compile_insn: this part unimplemented"


(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are 
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let open Asm in
  match t with
  |Ret (_, None) -> [Movq, [~%Rbp; ~%Rsp]; Popq, [~%Rbp]; Retq, []]
  |Ret (_, Some op) -> [compile_operand ctxt ~%Rax op; Movq, [~%Rbp; ~%Rsp]; Popq, [~%Rbp]; Retq, []]
  |Br lb -> [Jmp, [~$$(mk_lbl fn lb)]]
  |Cbr (op,lb1,lb2) -> [compile_operand ctxt ~%Rax op; Cmpq, [~$1; ~%Rax];J Eq, [~$$(mk_lbl fn lb1)];Jmp, [~$$(mk_lbl fn lb2)]]


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  List.flatten (List.map (compile_insn ctxt) blk.insns) @
  compile_terminator fn ctxt (snd blk.term)

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)

(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  let blocks = [block] @ (List.map (fun (_, blk) -> blk) lbled_blocks) in
  let uidlist = args @ List.flatten (List.map (fun blk -> (fst blk.term) :: List.map fst blk.insns) blocks) in
  let uids = List.sort_uniq (String.compare) uidlist in
  let ret = List.fold_left_map (fun acc arg -> (acc + 1, (arg, Ind3 (Lit (Int64.of_int (-8 * acc)), Rbp)))) 1 uids in
  snd ret

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_param; f_cfg; _ }:fdecl) : prog =
  let open Asm in
  let stk = stack_layout f_param f_cfg in
  let stk_sz = 8 * List.length stk in
  let funcname = Platform.mangle name in
  let ctxt = {tdecls; layout = stk} in
  gtext funcname ([ Pushq, [ ~%Rbp ]; Movq, [ ~%Rsp; ~%Rbp ]; Subq, [ ~$stk_sz; ~%Rsp ]]
  @ snd (List.fold_left (fun (acc, inss) param -> (acc + 1, inss @ [Movq, [ arg_loc acc; ~%Rax ]; Movq, [ ~%Rax; lookup stk param ]])) (0, []) f_param)
  @ compile_block funcname ctxt (fst f_cfg))
  :: List.map (fun (lbl, lblk) -> compile_lbl_block funcname lbl ctxt lblk) (snd f_cfg)


(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (_t1,g,_t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls; _} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
