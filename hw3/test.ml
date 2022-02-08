open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) = name>:: test_run program name expected;;

(* Runs a program, given as an ANFed expr, and compares its output to expected *)
let ta (name : string) (program : tag expr) (expected : string) = name>:: test_run_anf program name expected;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) = name>:: test_err program name expected_err;;

(* Runs check scope. Asserts no errors *)
let t_check_scope name (program : string) = name>:: fun _ -> 
    (check_scope (parse_string name program));;

(* Checks scope of a function, given as a source string, and compares its error to expected *)
let te_check_scope name (program : string) e = name>:: fun _ -> 
    (assert_raises e (fun _ -> (check_scope (parse_string name program))));;

let t_check_tags name (program : string) (expected : tag expr) = name>:: fun _ -> 
    assert_equal expected (tag (parse_string name program)) ~printer:ast_of_tag_expr;;

let t_rename name (program : string) (expected : unit expr) = name>:: fun _ -> 
    assert_equal expected (untag (rename (tag (parse_string name program)))) ~printer:ast_of_expr;;

let tisanf (name : string) (program : 'a expr) = name>:: fun _ ->
    assert_equal true (is_anf (anf (rename (tag program))));;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) = name>:: fun _ ->
    assert_equal expected (anf (rename (tag program))) ~printer:string_of_expr;
    check_scope_helper (fun _-> "ignored") program [];
    assert_equal true (is_anf (anf (rename (tag program))));;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf_improved (name : string) (program : string) (expected : string) = name>:: fun _ ->
    assert_equal expected (string_of_expr (anf (rename (tag (parse_string name program))))) ~printer:(fun s->s);
    check_scope_helper (fun _-> "ignored") (parse_string name program) [];
    assert_equal true (is_anf (anf (rename (tag (parse_string name program)))));;

let tcompile (name : string) (program : string) (expected : string) = name>:: fun _ ->
    assert_equal expected (compile_to_string (parse_string name program)) ~printer:(fun s->s);;

(* Checks if two strings are equal *)
let teq (name : string) (actual : string) (expected : string) = name>:: fun _ ->
    assert_equal expected actual ~printer:(fun s -> s);;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename>:: test_run_input filename expected;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename>:: test_err_input filename expected;;

let forty_one_a = (ENumber(41L, ()))

let is_anf_tests = [
  tisanf "isanf_let_in_prim" 
    (EPrim1(Sub1, ELet(["x", ENumber(1L, ()), ()], EId("x", ()), ()),
            ()));
  tisanf "isanf_let_in_let_in_if"
    (parse_string "isanf_let_in_let_in_if" 
       ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
        "(let abcd = 10 in add1(abcd)) " ^
        "else: (let x = 0, y = sub1(if x: x else: 1) in y)"))
]

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

let rename_tests = [
  t_rename "rename_atom_num" "1" (ENumber (1L, ()))
;t_rename "rename_let" "let x = 5 in x" (ELet (
      [("x#2", ENumber (5L, ()), ())],
      EId ("x#2", ()),
      ()))
;t_rename "rename_let*" "let x = 5, y = x in y" (ELet (
    [("x#2", ENumber (5L, ()), ());("y#4", EId ("x#2", ()), ())],
    EId ("y#4", ()),
    ()))

;t_rename "rename_let_prim" "let x = 5 in add1(x)" (ELet (
    [("x#2", ENumber (5L, ()), ())],
    EPrim1 (Add1, EId ("x#2", ()), ()),
    ()))
;t_rename "rename_let_shadow" "let x = 5 in (let x = x in x)" (ELet (
    [("x#2", ENumber (5L, ()), ())],
    ELet (
      [("x#4", EId ("x#2", ()), ())],
      EId ("x#4", ()),
      ()),
    ()))
;t_rename "rename_let_multiple" "let x = 5, y = 6 in (let x = x in x)" (ELet (
    [("x#2", ENumber (5L, ()), ());("y#4", ENumber (6L, ()), ())],
    ELet (
      [("x#6", EId ("x#2", ()), ())],
      EId ("x#6", ()),
      ()),
    ()))
;t_rename "rename_let_multiple_with_if_and_prim_2" "let x = 5, y = 6 in (let x = x in (if (x - 1): x + 5 else: x * 5))" (ELet (
    [("x#2", ENumber (5L, ()), ());("y#4", ENumber (6L, ()), ())],
    ELet (
      [("x#6", EId ("x#2", ()), ())],
      EIf (EPrim2 (Minus, EId ("x#6", ()), ENumber (1L, ()), ()), 
           EPrim2 (Plus, (EId ("x#6", ())), ENumber (5L, ()), ()), 
           EPrim2 (Times, (EId ("x#6", ())), ENumber (5L, ()), ()), ()), ()), ()))
]

let anf_tests = [
  tanf "forty_one_anf"
    (ENumber(41L, ()))
    forty_one_a;

  tanf "prim1" (* sub1(55) *)
    (EPrim1(Sub1, ENumber(55L, ()), ()))
    (EPrim1(Sub1, ENumber(55L, ()), ()));

  tanf "prim2" (* 55 + 56 *)
    (EPrim2(Plus, ENumber(55L, ()), ENumber(56L, ()), ()))
    (EPrim2(Plus, ENumber(55L, ()), ENumber(56L, ()), ()));

  tanf "prim2_in_prim2" (* (55 + 56) + 57 *)
    (EPrim2(Plus, EPrim2(Plus, ENumber(55L, ()), ENumber(56L, ()), ()), ENumber(57L, ()), ()))
    (ELet(["plus_3", EPrim2(Plus, ENumber(55L, ()), ENumber(56L, ()), ()), ()],
          EPrim2(Plus, EId("plus_3", ()), ENumber(57L, ()), ()),
          ()));

  tanf "prim1_in_let" (* let x = 55 in x *)
    (ELet(["x", EPrim1(Sub1, ENumber(55L, ()), ()), ()], EId("x", ()), ()))
    (ELet(["x#3", EPrim1(Sub1, ENumber(55L, ()), ()), ()], EId("x#3", ()), ()));

  tanf_improved "let_in_prim"
    "add1(let x = 5 in x)"
    "(let let_4 = (let x#2 = 5 in x#2) in add1(let_4))";

  tanf_improved "let_in_prim_with_eval"
    "add1(let x = 5 in add1(x))"
    "(let let_5 = (let x#2 = 5 in add1(x#2)) in add1(let_5))";

  tanf_improved "let_in_prim2_with_eval"
    "add1(let x = 5 in (x + (let x = 2 in x)))"
    "(let let_9 = (let x#2 = 5, let_7 = (let x#5 = 2 in x#5) in (x#2 + let_7)) in add1(let_9))";

  tanf_improved "let_in_let_in_if"
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    ("(let let_17 = (let x#2 = 5, y#13 = " ^
     "(let x#5 = sub1(x#2), add1_7 = add1(x#5), y#10 = (add1_7 - 10) in y#10) in " ^
     "(y#13 + x#2)) in " ^
     "(if let_17: (let abcd#19 = 10 in add1(abcd#19)) else: " ^
     "(let x#24 = 0, if_28 = (if x#24: x#24 else: 1), y#30 = sub1(if_28) in y#30)))"
    );

  tanf_improved "lets_in_prim"
    "(let x = 1 in x) + (let x = 2 in x)"
    "(let let_4 = (let x#2 = 1 in x#2), let_8 = (let x#6 = 2 in x#6) in (let_4 + let_8))";

  tanf "if_basic" (* if 0: 0 else: 1 *)
    (EIf(ENumber(0L, ()), ENumber(0L, ()), ENumber(1L, ()), ()))
    (EIf(ENumber(0L, ()), ENumber(0L, ()), ENumber(1L, ()), ()));

  tanf "if_in_if" (* if (if 0: 0 else: 1) else: 1 *)
    (EIf((EIf(ENumber(0L, ()), ENumber(0L, ()), ENumber(1L, ()), ())), ENumber(0L, ()), ENumber(1L, ()), ()))
    (ELet(["if_4", (EIf(ENumber(0L, ()), ENumber(0L, ()), ENumber(1L, ()), ())), ()],
          (EIf(EId("if_4", ()), ENumber(0L, ()), ENumber(1L, ()), ())), ()));

  tanf_improved "if_in_if_in_let_in_add1"
    "add1(let x = (if (if 0: 0 else: 1): 2 else: 3) in (if x: 4 else: 5))"
    "(let let_13 = (let if_4 = (if 0: 0 else: 1), x#8 = (if if_4: 2 else: 3) in (if x#8: 4 else: 5)) in add1(let_13))";

  tanf_improved "simple_conditional"
    "(let x = (if 1: 5 + 5 else: 6 * 2) in (let y = (if 0: x * 3 else: x + 5) in x + y))"
    ("(let x#9 = (if 1: (5 + 5) else: (6 * 2)) in " ^
     "(let y#18 = (if 0: (x#9 * 3) else: (x#9 + 5)) in (x#9 + y#18)))"
    );

  tanf_improved "complex_conditional"
    ("(let x = (if (5 - 10): add1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))"
    )
    ("(let minus_3 = (5 - 10), x#13 = (if minus_3: " ^
     "(let plus_6 = (5 + 5) in add1(plus_6)) else: " ^
     "(let times_10 = (6 * 2) in sub1(times_10))) in " ^
     "(let times_16 = (x#13 * 0), if_25 = " ^
     "(if times_16: (let sub1_19 = sub1(3) in (x#13 * sub1_19)) else: " ^
     "(let add1_22 = add1(x#13) in (add1_22 + 5))), y#27 = sub1(if_25), " ^
     "plus_30 = (x#13 + y#27) in sub1(plus_30)))"
    );

  tanf_improved "test1.boa" "let x = if sub1(55): (if 1: add1(2) else: add1(3)) else: (if 0: sub1(4) else: sub1(5)) in x" 
    "(let sub1_2 = sub1(55), x#16 = (if sub1_2: (if 1: add1(2) else: add1(3)) else: (if 0: sub1(4) else: sub1(5))) in x#16)";

  tanf "prim1_anf_6410"
    (EPrim1(Sub1, ENumber(55L, ()), ()))
    (EPrim1(Sub1, ENumber(55L, ()), ()));
]

let compile_tests = [
  tcompile "forty_one" "41" "section .text
global our_code_starts_here
our_code_starts_here:
  mov rax, QWORD 41
  ret
";
  tcompile "if" "if 5: 4 else: 2" "section .text
global our_code_starts_here
our_code_starts_here:
  mov rax, QWORD 5
  cmp rax, QWORD 0
  je if_false_4
if_true_4:
  mov rax, QWORD 4
  jmp done_4
if_false_4:
  mov rax, QWORD 2
done_4:
  ret
";
]

let integration_tests = [
  t "forty_one" "41" "41";
  t "basic_let" "let a = 1 in a" "1";

  t "if1" "if 5: 4 else: 2" "4";
  t "if2" "if 0: 4 else: 2" "2";

  t "multi_let" "let a = 1, b = a in b" "1";

  t "let_in_let_in_if_it_1"
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    "0";

  t "let_in_let_in_if_it_2"
    ("if (let x = 4, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    "11";

  t "let_in_let_in_if_it_3"
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 1, y = sub1(if x: x else: 2) in y)")
    "0";

  t "let_in_let_in_if_it_4"
    ("if (let x = 4, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    "11";


  t "complex_conditional_it_1" 
    ("(let x = (if (5 - 10): sub1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "22";

  t "complex_conditional_it_2" 
    ("(let x = (if (5 - 5): sub1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "26";

  t "complex_conditional_it_3" 
    ("(let x = (if (5 - 10): sub1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 1): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "25";

  t "complex_conditional_it_4" 
    ("(let x = (if (5 - 5): sub1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 1): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "31";

  tprog "test1.boa" "3";
]

let suite =
  "suite">:::
  is_anf_tests
  @ check_scope_tests
  @ check_tag_tests
  @ rename_tests
  @ anf_tests 
  @ compile_tests
  @ integration_tests
;;


let () =
  run_test_tt_main suite
;;
