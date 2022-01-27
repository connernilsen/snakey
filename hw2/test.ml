open Compile
open Runner
open Printf
open OUnit2
open ExtLib
open Sexp

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name >:: fun _ -> assert_equal expected value ~printer:dump

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) : OUnit2.test =
  name >:: test_run program name expected

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) : OUnit2.test =
  name >:: test_err program name expected_err

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to

   expected *)

let ti (filename : string) (expected : string) = filename >:: test_run_input filename expected

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to

   expected *)

let tie (filename : string) (expected_err : string) =
  filename >:: test_err_input filename expected_err

let expr_of_sexp_tests =
  [ t_any "expr_of_sexp0" (expr_of_sexp (parse "1")) (Number (1L, (0, 0, 0, 1)))
  ; t_any "expr_of_sexp1"
      (expr_of_sexp (parse "(let ((x 1)) x)"))
      (Let ([("x", Number (1L, (0, 9, 0, 10)))], Id ("x", (0, 13, 0, 14)), (0, 0, 0, 15)))
  ; t_any "expr_of_sexp2"
      (expr_of_sexp (parse "(let ((x (add1 5)) (y (sub1 x))) (add1 y))"))
      (Let
         ( [ ("x", Prim1 (Add1, Number (5L, (0, 15, 0, 16)), (0, 9, 0, 17)))
           ; ("y", Prim1 (Sub1, Id ("x", (0, 28, 0, 29)), (0, 22, 0, 30))) ]
         , Prim1 (Add1, Id ("y", (0, 39, 0, 40)), (0, 33, 0, 41))
         , (0, 0, 0, 42) ) ) ]

let all_tests = expr_of_sexp_tests

let suite : OUnit2.test = "suite" >::: all_tests

let () = run_test_tt_main suite
