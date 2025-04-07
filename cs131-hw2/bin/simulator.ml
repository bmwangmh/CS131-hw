(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next sevent bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref false


(* override some useful operators  *)
let ( +. ) = Int64.add
let ( -. ) = Int64.sub
let ( *. ) = Int64.mul
let ( <. ) a b = (Int64.compare a b) < 0
let ( >. ) a b = (Int64.compare a b) > 0
let ( <=. ) a b = (Int64.compare a b) <= 0
let ( >=. ) a b = (Int64.compare a b) >= 0

(* Interpret a condition code with respect to the given flags. *)
(* !!! Check the Specification for Help *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x -> match x with
 |Eq -> fz
 |Neq -> not fz
 |Lt -> fo <> fs
 |Le -> fo <> fs || fz
 |Gt -> fo = fs && not fz
 |Ge -> fo = fs


(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  let res = Int64.to_int (Int64.sub addr mem_bot) in 
  if res < 0 || res >= mem_size then None else Some res

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* Raise X86lite_segfault when addr is invalid. *)
let map_addr_segfault (addr:quad) : int =
  match (map_addr addr) with
  |None -> raise X86lite_segfault
  |Some res -> res

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags

  We provide the basic structure of step function and helper functions.
  Implement the subroutine below to complete the step function.
  See step function to understand each subroutine and how they 
  are glued together.
*)

let readquad (m:mach) (addr:quad) : quad =
  let lst =
    let res = map_addr_segfault addr in
      List.init 8 (fun i -> m.mem.(res + i))
  in
    int64_of_sbytes (lst)


let writequad (m:mach) (addr:quad) (w:quad) : unit =
  let res = map_addr_segfault addr in
    List.iteri (fun i byte -> m.mem.(res + i) <- byte) (sbytes_of_int64 w)

exception Impossible
let fetchins (m:mach) (addr:quad) : ins =
  let res = map_addr_segfault addr in
    match m.mem.(res) with
    |InsB0 (ret) -> ret
    |_ -> raise Impossible


(* Compute the instruction result.
 * NOTE: See int64_overflow.ml for the definition of the return type
*  Int64_overflow.t. *)
let interp_opcode (m: mach) (o:opcode) (args:int64 list) : Int64_overflow.t = 
    let open Int64 in
    let open Int64_overflow in
    match o, args with
      | Movq, [src; dest] -> {value = src; overflow = false}
      | Pushq, [src] -> failwith "interp_opcode: Pushq"
      | Popq, [dest] -> failwith "interp_opcode: Popq"
      | Leaq, [ind; dest] -> {value = ind; overflow = false}
      | Incq, [dest] -> add dest 1L
      | Decq, [dest] -> sub dest 1L
      | Negq, [dest] -> neg dest
      | Notq, [dest] -> {value = lognot dest; overflow = false}
      | Addq, [src; dest] -> add dest src
      | Subq, [src; dest] -> sub dest src
      | Imulq, [src; dest] -> mul dest src
      | Xorq, [src; dest] -> {value = logxor dest src; overflow = false}
      | Orq, [src; dest] -> {value = logor dest src; overflow = false}
      | Andq, [src; dest] -> {value = logand dest src; overflow = false}
      | Sarq, [amt; dest] -> {value = (shift_right dest (to_int amt)); overflow = false}
      | Shlq, [amt; dest] -> {value = (shift_left dest (to_int amt)); overflow = false}
      | Shrq, [amt; dest] -> {value = (shift_right_logical dest (to_int amt)); overflow = false}
      | Jmp, [src] -> {value = src; overflow = false}
      | J cnd, [src] -> if (interp_cnd m.flags cnd) then {value = src; overflow = false} else {value = m.regs.(rind Rip); overflow = false}
      | Cmpq, [src1; src2] -> sub src2 src1
      | Set cnd, [dest] -> if (interp_cnd m.flags cnd) then {value = logor dest 1L; overflow = false} else {value = logand dest 0L; overflow = false}
      | Callq, [src] -> failwith "interp_opcode: Callq"
      | Retq, [] -> failwith "interp_opcode: Retq"
      | _ -> failwith "interp_opcode: Unsupported instruction"

let rec interp_operand (m: mach) : operand -> int64 = function 
  | Imm i -> (match i with |Lit x -> x |Lbl x -> failwith "interp_operand: interp a label")
  | Reg r -> m.regs.(rind r)
  | Ind1 i -> let idx = interp_operand m (Imm i) in
    readquad m idx
  | Ind2 r -> let idx = interp_operand m (Reg r) in
    readquad m idx
  | Ind3 (i, r) -> let idx = interp_operand m (Imm i) in
  let ofs = interp_operand m (Reg r) in
    readquad m (Int64.add idx ofs)

let operand_writeback (m: mach) (v: int64): operand -> unit = function
  | Imm i -> failwith "operand_writeback: writeback an imm"
  | Reg r -> m.regs.(rind r) <- v
  | Ind1 i -> let idx = interp_operand m (Imm i) in
    writequad m idx v
  | Ind2 r -> let idx = interp_operand m (Reg r) in
    writequad m idx v
  | Ind3 (i, r) -> let idx = interp_operand m (Imm i) in
  let ofs = interp_operand m (Reg r) in
    writequad m (Int64.add idx ofs) v
(** Update machine state with instruction results. *)
let ins_writeback (m: mach) : ins -> int64 -> unit  = fun (ins: ins) (v: int64) ->
  let (op, operands) = ins in
  match op, operands with
  | (Movq|Leaq|Addq|Subq|Imulq|Xorq|Orq|Andq|Sarq|Shlq|Shrq), [src; dest] -> operand_writeback m v dest
  | (Pushq|Jmp|Callq|Retq), [src] -> m.regs.(rind Rip) <- v
  | (Popq|Decq|Negq|Notq), [dest] -> operand_writeback m v dest
  | J cnd, [src] -> m.regs.(rind Rip) <- v
  | Cmpq, [src1; src2] -> ()
  | Set cnd, [dest] -> operand_writeback m v dest
  | _ -> failwith "ins_writeback: Unsupported instruction"


(* mem addr ---> mem array index *)

let interp_operands (m:mach) : ins -> int64 list = fun ins ->
  let (op, operands) = ins in
    List.map (interp_operand m) operands

let validate_operands : ins -> unit = function
  | ( (Movq|Addq|Subq|Imulq|Xorq|Orq|Andq|Sarq|Shlq|Shrq), [src; dest]) -> (match src with |(Imm (Lbl lb)) -> failwith "validate_operands: invalid arguments" | _ -> 
    (match dest with (Imm _) -> failwith "validate_operands: invalid arguments"|_ -> ()))
  | ( (Pushq|Jmp|Callq), [src]) -> (match src with |(Imm (Lbl lb)) -> failwith "validate_operands: invalid arguments" | _ -> ())
  | ( (Popq|Incq|Decq|Negq|Notq), [dest]) -> (match dest with (Imm _) -> failwith "validate_operands: invalid arguments"|_ -> ())
  | ( Leaq, [ind; dest]) -> (match ind with |(Imm _|Reg _) -> failwith "validate_operands: invalid arguments" | _ -> 
    (match dest with (Imm _) -> failwith "validate_operands: invalid arguments"|_ -> ()))
  | (J cnd, [src]) -> (match src with |(Imm (Lbl lb)) -> failwith "validate_operands: invalid arguments" | _ -> ())
  | ( Cmpq, [src1; src2]) -> (match src1 with |(Imm (Lbl lb)) -> failwith "validate_operands: invalid arguments" | _ -> 
    (match src2 with |(Imm (Lbl lb)) -> failwith "validate_operands: invalid arguments" | _ -> ()))
  | (Set cnd, [dest]) -> (match dest with (Imm _) -> failwith "validate_operands: invalid arguments"|_ -> ())
  | (Retq, []) -> ()
  | _ -> failwith "validate_operands: invalid arguments"

let rec crack : ins -> ins list = function
  | ( Pushq, [src]) -> [(Subq, [(Imm (Lit 8L)); Reg Rsp]); (Movq, [src; Ind2 Rsp])]
  | ( Popq, [dest]) -> [(Movq, [Ind2 Rsp; dest]); (Addq, [(Imm (Lit 8L)); Reg Rsp])]
  | ( Callq, [src]) -> List.append (crack (Pushq, [Reg Rip])) [(Movq, [src; Reg Rip])]
  | ( Retq, []) -> crack (Popq, [Reg Rip])
  | ins -> [ins]
 
(* TODO: double check against spec *)
let set_flags (m:mach) (op:opcode) (ws: quad list) (w : Int64_overflow.t) : unit =
  match op with
  |(Incq|Decq|Addq|Subq|Imulq|Xorq|Orq|Andq|Negq|Cmpq) -> 
    m.flags.fo <- w.overflow;
    m.flags.fz <- w.value = 0L;
    m.flags.fs <- w.value <. 0L
  |(Sarq|Shlq|Shrq) ->
    m.flags.fz <- w.value = 0L;
    m.flags.fs <- w.value <. 0L;
    (match ws with |[1L;ori]->
    (match op with 
    |Shlq -> m.flags.fo <- (Int64.shift_right ori 63) <> (Int64.logand (Int64.shift_right ori 62) 1L)
    |Shrq -> m.flags.fo <- (Int64.shift_right ori 63) = 1L
    |Sarq -> m.flags.fo <- false
    |_ -> ())
    |_ -> ())
  |_ -> ()


let step (m:mach) : unit =
  (* execute an instruction *)
  let (op, args) as ins = fetchins m m.regs.(rind Rip) in
  validate_operands ins;
  
  (* Some instructions involve running two or more basic instructions. 
   * For other instructions, just return a list of one instruction.
   * See the X86lite specification for details. *)
  let uops: ins list = crack (op,args) in

  m.regs.(rind Rip) <- m.regs.(rind Rip) +. ins_size;

  List.iter
    (fun (uop,_ as u) ->
     if !debug_simulator then print_endline @@ string_of_ins u;
     let ws = interp_operands m u in
     let res = interp_opcode m uop ws in
     ins_writeback m u @@ res.Int64_overflow.value;
     set_flags m op ws res
    ) uops

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.
     HINT: consider building a mapping from symboli Lbl to memory address

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let is_size (is: ins list): quad = 
  failwith "is_size not implemented"

let ds_size (ds: data list): quad = 
  failwith "ds_size not implemented"

let assemble (p:prog) : exec =
  failwith "assemble unimplemented"

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
   failwith "load not implemented"