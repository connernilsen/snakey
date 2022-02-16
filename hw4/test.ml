open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs


(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) = name>::test_run program name expected;;

(* Runs a program, given as an ANFed expr, and compares its output to expected *)
let ta (name : string) (program : tag expr) (expected : string) = name>::test_run_anf program name expected;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) = name>::test_err program name expected_err;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_expr;;

(* Checks if two strings are equal *)
let teq (name : string) (actual : string) (expected : string) = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename>::test_run_input filename expected;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename>::test_err_input filename expected;;

let forty = "let x = 40 in x"
let fals = "let x = false in x"
let tru = "let x = true in x"

let suite =
"unit_tests">:::
 [
  t "forty" forty "40";
  t "fals" fals "false";
  t "tru" tru "true";
  t "add1" "add1(0)" "1";
  t "add1_let" "let x = add1(0) in x" "1";
  t "true" "true" "true";
  t "not_true" "!(true)" "false";
  t "not_false" "!(false)" "true";
  t "print" "print(40)" "40\n40";
  t "print2" "let _ = print(40) in 40" "40\n40";
  t "isbool" "isbool(40)" "false";
  t "isboolT" "isbool(true)" "true";
  t "isnumT" "isnum(40)" "true";
  t "isnum" "isnum(false)" "false";

  (* te "bool_instead_of_num" "add1(true)" "Error 2: Expected number type for arithmetic op, got bool(true)";
  te "bool_instead_of_num2" "sub1(false)" "Error 2: Expected number type for arithmetic op, got bool(false)";
  te "bool_instead_of_num3" "1 < true" "Error 2: Expected number type for arithmetic op, got bool(true)";
  te "num_instead_of_bool" "!(1)" "Error 2: Expected bool type for arithmetic op, got num(1)";
  te "num_instead_of_bool2" "if (1): 1 else: 0" "Error 2: Expected bool type for arithmetic op, got num(1)"; *)
  

  tprog "do_pass/test1.cobra" "6"; 
  teprog "do_err/test1.cobra" "Error 2: Expected number type for arithmetic op, got bool(false)";
 ]
;;


(* input_file_test_suite () will run all the tests in the subdirectories of input/ *)
let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;
