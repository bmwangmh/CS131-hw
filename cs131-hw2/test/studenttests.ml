open Util.Assert
open X86
open Sim.Simulator
open Gradedtests
open Asm 
(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)


let test_my =
  let bin = [
    InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    ] 
  
  in 

  let asm =  [gtext "main"
  [ 
    Movq,  [~$42; ~%Rax]];
  ] in 

  (assert_eqf (fun() ->  (assemble asm).text_seg) bin )

 
let mov_ri =
 test_machine
 [
 InsB0 (Movq, Asm.[ ~$42; ~%Rax ]);
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 InsFrag;
 ]

let provided_tests : suite = [
  
  Test ("My Tests", [
    ("assert", test_my)
  ]);

  Test ("Student-Provided Big Test for Part III: Score recorded as PartIIITestCase", [
    
  ]);

] 
