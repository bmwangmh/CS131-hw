open Util.Assert
open Hellocaml

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let student_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);
  Test ("Student-Provided Tests For Problem 4-4", [
    ("optimize1", assert_eqf (fun () -> optimize (Mult(Const 3L, Const 4L))) (Const 12L));
    ("optimize2", assert_eqf (fun () -> optimize (Mult(Const 1L, Var "x"))) (Var "x"));
    ("optimize3", assert_eqf (fun () -> optimize (Add(Neg(Const 3L), Mult(Const 0L, Var "x")))) (Const (-3L)));
  ]);
  
] 
