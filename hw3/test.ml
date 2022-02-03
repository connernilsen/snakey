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

let t_check_tags name (program : string) (expected : tag expr) = name>::
                                                                 (fun _ -> assert_equal expected (tag (parse_string name program)) ~printer:ast_of_tag_expr);;

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
; t_check_scope "good_scope_4" "let x = 1, y = (x * x) in y - x"
; t_check_scope "good_scope_deep_let"
    ("let x = (if 1: (5 * 5) else: 10), y = (let z = sub1(x) in z - x) in\n\t" ^
     "(let z = x + y in z)")
; t_check_scope "good_scope_deep_if"
    ("if (if 0: sub1(1) else: 10): (if (5 * -1): let x = 10 in sub1(x) else: add1(10))\n" ^
     "else: 4321")
; t_check_scope "good_scope_shadow_var"
    "let x = 10 in let x = 11 in x"
; t_check_scope "good_scope_available_deep"
    "let x = 10, y = (let z = 11, a = x + z in a + x) in y + x"
; t_check_scope "good_scope_let_available_in_if_1_condition"
    "let x = 10 in if x: 1 else: 2"
; t_check_scope "good_scope_let_available_in_if_2_thn"
    "let x = 10 in if 0: x else: 2"
; t_check_scope "good_scope_let_available_in_if_3_els"
    "let x = 10 in if 1: 0 else: x"
; t_check_scope "good_scope_use_before_shadow"
    "let x = 10 in x + (let x = 10 in x)"
; te_check_scope "bad_scope_1" "x" 
    (BindingError "Unbound variable x at bad_scope_1, 1:0-1:1")
; te_check_scope "bad_scope_2" "let x = 1 in y" 
    (BindingError "Unbound variable y at bad_scope_2, 1:13-1:14")
; te_check_scope "bad_scope_3" "let x = 1, x = 2 in x"  
    (BindingError "Duplicate bindings in let at bad_scope_3, 1:4-1:9")
; te_check_scope "bad_scope_nested" "let y = 2 in let x = 1, x = 2 in x" 
    (BindingError "Duplicate bindings in let at bad_scope_nested, 1:17-1:22")
; te_check_scope "bad_scope_in_binding_duples" "let y = (let x = 10, x = 20 in x) in y" 
    (BindingError "Duplicate bindings in let at bad_scope_in_binding_duples, 1:13-1:19")
; te_check_scope "bad_scope_in_binding_unbound" "let y = (let x = y in x) in y" 
    (BindingError "Unbound variable y at bad_scope_in_binding_unbound, 1:17-1:18")
; te_check_scope "bad_scope_if_cond_bind_1"
    "if (let x = 10 in x): x else: 11"
    (BindingError "Unbound variable x at bad_scope_if_cond_bind_1, 1:22-1:23")
; te_check_scope "bad_scope_if_cond_bind_2"
    "if (let x = 10 in x): 1 else: x"
    (BindingError "Unbound variable x at bad_scope_if_cond_bind_2, 1:30-1:31")
; te_check_scope "bad_scope_if_thn_bind_1"
    "if x: (let x = 10 in x) else: 0"
    (BindingError "Unbound variable x at bad_scope_if_thn_bind_1, 1:3-1:4")
; te_check_scope "bad_scope_if_thn_bind_2"
    "if 1: (let x = 10 in x) else: x"
    (BindingError "Unbound variable x at bad_scope_if_thn_bind_2, 1:30-1:31")
; te_check_scope "bad_scope_if_els_bind_1"
    "if 1: x else: (let x = 10 in x)"
    (BindingError "Unbound variable x at bad_scope_if_els_bind_1, 1:6-1:7")
; te_check_scope "bad_scope_if_els_bind_2"
    "if x: 1 else: (let x = 10 in x)"
    (BindingError "Unbound variable x at bad_scope_if_els_bind_2, 1:3-1:4")
]

let check_tag_tests = [
  t_check_tags "tag_atom_num" "1" (ENumber(1L, 1));
  t_check_tags "tag_atom_id" "x" (EId("x", 1));
  t_check_tags "tag_simple_let" "let x = 1 in x"
    (ELet ([("x", ENumber(1L, 1), 2)], EId("x", 3), 4));
  t_check_tags "tag_prim1_simple" "add1(123)"
    (EPrim1 (Add1, ENumber(123L, 1), 2));
  t_check_tags "tag_prim1_in_let" "let x = add1(123) in sub1(x)"
    (ELet ([("x", EPrim1 (Add1, ENumber (123L, 1), 2), 3)], 
           EPrim1 (Sub1, EId ("x", 4), 5), 6));
  t_check_tags "tag_prim2_simple" "5 * 6"
    (EPrim2 (Times, ENumber (5L, 1), ENumber (6L, 2), 3));
  t_check_tags "tag_prim2_nested" "(5 - 6) * (1 + 3)"
    (EPrim2 (Times,
             EPrim2 (Minus, ENumber (5L, 1), ENumber (6L, 2), 3),
             EPrim2 (Plus, ENumber (1L, 4), ENumber (3L, 5), 6),
             7));
  t_check_tags "tag_if_simple" "if 0: add1(5) else: 7"
    (EIf (ENumber (0L, 1),
          EPrim1 (Add1, ENumber (5L, 2), 3),
          ENumber (7L, 4),
          5));
  t_check_tags "tag_let_deep" 
    ("let x = (if 1: (5 * 5) else: 10), y = (let z = sub1(x) in z - x) in\n\t" ^
     "(let z = x + y in z)")
    (ELet ([
         ("x", EIf (
             ENumber (1L, 1),
             EPrim2 (Times, ENumber (5L, 2), ENumber (5L, 3), 4),
             ENumber (10L, 5), 6),
          7);
         ("y", ELet (
             [("z", EPrim1 (Sub1, EId ("x", 8), 9), 10)],
             EPrim2 (Minus, EId ("z", 11), EId ("x", 12), 13),
             14), 15)],
         ELet (
           [("z", EPrim2 (Plus, EId ("x", 16), EId ("y", 17), 18), 19)],
           EId ("z", 20),
           21),
         22));
  t_check_tags "tag_if_deep"
    ("if (if 0: sub1(1) else: 10): (if (5 * -1): let x = 10 in sub1(x) else: add1(10))\n" ^
     "else: 4321")
    (EIf (
        EIf (ENumber (0L, 1), EPrim1 (Sub1, ENumber (1L, 2), 3), ENumber(10L, 4), 5),
        EIf (
          EPrim2 (Times, ENumber (5L, 6), ENumber (Int64.neg 1L, 7), 8),
          ELet (
            [("x", ENumber (10L, 9), 10)],
            EPrim1 (Sub1, EId ("x", 11), 12),
            13),
          EPrim1 (Add1, ENumber (10L, 14), 15),
          16),
        ENumber (4321L, 17),
        18));
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
  @ check_tag_tests
  (* @ anf_tests @ integration_tests *)
;;


let () =
  run_test_tt_main suite
;;
