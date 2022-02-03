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

(* Runs check scope. Asserts no errors *)
let t_check_scope name (program : string) = name>::
                                            (fun _ -> (check_scope (parse_string name program)));;

(* Checks scope of a function, given as a source string, and compares its error to expected *)
let te_check_scope name (program : string) e = name>::
                                               (fun _ -> (assert_raises e (fun _ -> (check_scope (parse_string name program)))));;

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

let forty_one = "41";;

let forty_one_a = (ENumber(41L, ()))

let check_scope_tests = [
  t_check_scope "good_scope_1" "let x = 1 in x"
; t_check_scope "good_scope_2" "let x = 1 in let y = 2 in 5"
; t_check_scope "good_scope_3" "let x = 1 in let x = 2 in 5"
; te_check_scope "bad_scope_1" "x" (BindingError "invalid")
; te_check_scope "bad_scope_2" "let x = 1 in y" (BindingError "invalid")
; te_check_scope "bad_scope_3" "let x = 1, x = 2 in x" (BindingError "invalid")
; te_check_scope "bad_scope_nested" "let y = 2 in let x = 1, x = 2 in x" (BindingError "invalid")
; te_check_scope "bad_scope_in_binding_duples" "let y = (let x = 10, x = 20 in x) in y" (BindingError "invalid")
; te_check_scope "bad_scope_in_binding_unbound" "let y = (let x = y in x) in y" (BindingError "invalid")
]

let anf_tests = [
  tanf "forty_one_anf"
    (ENumber(41L, ()))
    forty_one_a;

  (* For CS4410 students, with unnecessary let-bindings *)
  tanf "prim1_anf_4410"
    (EPrim1(Sub1, ENumber(55L, ()), ()))
    (ELet(["unary_1", EPrim1(Sub1, ENumber(55L, ()), ()), ()],
          EId("unary_1", ()),
          ()));

  (* For CS6410 students, with optimized let-bindings *)
  (* tanf "prim1_anf_6410"
       (EPrim1(Sub1, ENumber(55L, ()), ()))
       (EPrim1(Sub1, ENumber(55L, ()), ())); *)
]

let integration_tests = [
  (* ta "forty_one_run_anf" (tag forty_one_a) "41";

     t "forty_one" forty_one "41";

     t "if1" "if 5: 4 else: 2" "4";
     t "if2" "if 0: 4 else: 2" "2";

     tprog "test1.boa" "3"; *)
]

let suite =
  "suite">:::
  check_scope_tests
  (* @ anf_tests @ integration_tests *)
;;


let () =
  run_test_tt_main suite
;;
