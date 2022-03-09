open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Libtest

let check_name (name : string) : string =
  if String.contains name ' '
  then failwith (sprintf "Test name cannot contain ' ': %s" name)
  else name

let t name program input expected = (check_name name)>::test_run ~args:[] ~std_input:input program name expected;;
let ta name program input expected = (check_name name)>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = (check_name name)>::test_run ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tvg name program input expected = (check_name name)>::test_run_valgrind ~args:[] ~std_input:input program name expected;;
let tvgc name heap_size program input expected = (check_name name)>::test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let terr name program input expected = (check_name name)>::test_err ~args:[] ~std_input:input program name expected;;
let tgcerr name heap_size program input expected = (check_name name)>::test_err ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tanf name program input expected = (check_name name)>::fun _ ->
    assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf_improved (name : string) (program : string) (expected : string) = (check_name name)>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_aprogram (anf (tag (desugar (rename_and_tag (tag (parse_string name program))))))) ~printer:(fun s->s)
;;

let teq name actual expected = (check_name name)>::fun _ ->
    assert_equal expected actual ~printer:(fun s -> s);;

let tdesugar (name : string) (program : string) (expected : string) = (check_name name)>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_program (desugar (tag (parse_string name program)))) ~printer:(fun s->s);;

let wf_tests = [
  terr "wf_tuple" "(a, 1, 2, 3)" "" "The identifier a, used at <wf_tuple, 1:1-1:2>, is not in scope";
  terr "wf_tuple_in_tuple" "((a,), 1, 2, 3)" "" "The identifier a, used at <wf_tuple_in_tuple, 1:2-1:3>, is not in scope";
  terr "wf_tuple_get" "(a, 1, 2, 3)[0]" "" "The identifier a, used at <wf_tuple_get, 1:1-1:2>, is not in scope";
  terr "wf_tuple_get_arg" "(1, 2, 3)[a]" "" "The identifier a, used at <wf_tuple_get_arg, 1:10-1:11>, is not in scope";
  terr "wf_tuple_set" "(a, 1, 2, 3)[0] := 0" "" "The identifier a, used at <wf_tuple_set, 1:1-1:2>, is not in scope";
  terr "wf_tuple_set_arg" "(1, 2, 3)[a] := 0" "" "The identifier a, used at <wf_tuple_set_arg, 1:10-1:11>, is not in scope";
  terr "wf_tuple_set_set" "(1, 2, 3)[0] := a" "" "The identifier a, used at <wf_tuple_set_set, 1:16-1:17>, is not in scope";
  terr "wf_rebind_fun" "def input(): true\n1" "" "do we want to make sure input can't be rebound?";
  terr "wf_sequence_1" "a; a" "" "The identifier a, used at <wf_sequence_1, 1:0-1:1>, is not in scope\nThe identifier a, used at <wf_sequence_1, 1:3-1:4>, is not in scope";
]
let desugar_tests = [
  tdesugar "desugar_and"
    "true && false"
    "\n(if true: (if false: true else: false) else: false)";
  tdesugar "desugar_or"
    "true || false"
    "\n(if true: true else: (if false: true else: false))";
  tdesugar "desugar_nested_or"
    "true || true || false"
    "\n(if (if true: true else: (if true: true else: false)): true else: (if false: true else: false))";
  tdesugar "desugar_nested_and"
    "true && true && false"
    "\n(if (if true: (if true: true else: false) else: false): (if false: true else: false) else: false)";
  tdesugar "desugar_print"
    "true || print(1)"
    "\n(if true: true else: (if print(1): true else: false))";
  tdesugar "desugar_seq_basic"
    "true; false"
    "\n(let _ = true in false)";
  tdesugar "desugar_seq_nested"
    "true; false; true"
    "\n(let _ = true in (let _ = false in true))";
  tdesugar "desugar_seq_complex"
    "true; true && true; true"
    "\n(let _ = true in (let _ = (if true: (if true: true else: false) else: false) in true))";
  tdesugar "desugar_destructure_basic"
    "let (a, b, c) = (1, 2, 3) in (a, b, c)"
    "\n(let bind_temp4 = (1, 2, 3), a = bind_temp4[0], b = bind_temp4[1], c = bind_temp4[2] in (a, b, c))";
  tdesugar "desugar_destructure_nested"
    "let (a, (b, c), d) = (1, (2, 3), 4) in (a, (b, c), d)"
    "\n(let bind_temp4 = (1, (2, 3), 4), a = bind_temp4[0], bind_temp6 = bind_temp4[1], b = bind_temp6[0], c = bind_temp6[1], d = bind_temp4[2] in (a, (b, c), d))";
  tdesugar "desugar_destructure_nested_w_blanks"
    "let (a, (b, _), _) = (1, (2, 3), 4) in (a, (b, c), d)"
    "\n(let bind_temp4 = (1, (2, 3), 4), a = bind_temp4[0], bind_temp6 = bind_temp4[1], b = bind_temp6[0], _ = bind_temp6[1], _ = bind_temp4[2] in (a, (b, c), d))";
  tdesugar "desugar_decl_with_destructure"
    "def f((a, b), c): ((a, b), c)\nf((1, 2), 3)"
    "(def f(fun_arg#3, c):\n  (let bind_temp3 = fun_arg#3, a = bind_temp3[0], b = bind_temp3[1] in ((a, b), c)))\n(?f((1, 2), 3))";
  tdesugar "desugar_decl_with_destructure_and_blank"
    "def f((a, _), c): ((a,), c)\nf((1, 2), 3)"
    "(def f(fun_arg#3, c):\n  (let bind_temp3 = fun_arg#3, a = bind_temp3[0], _ = bind_temp3[1] in ((a,), c)))\n(?f((1, 2), 3))";
  tdesugar "desugar_destructure_not_nested"
    "let (a, b, c) = (1, (2, 3), ()) in (a, b, c)"
    "\n(let bind_temp4 = (1, (2, 3), ()), a = bind_temp4[0], b = bind_temp4[1], c = bind_temp4[2] in (a, b, c))";
]

let anf_tests = [
  tanf_improved "let_in_prim"
    "add1(let x = 5 in x)"
    "\n(alet x#5 = 5 in add1(x#5))";

  tanf_improved "let_in_prim_with_eval"
    "add1(let x = 5 in add1(x))"
    "\n(alet x#5 = 5 in (alet unary_7 = add1(x#5) in add1(unary_7)))";

  tanf_improved "let_in_prim2_with_eval"
    "add1(let x = 5 in (x + (let x = 2 in x)))"
    "\n(alet x#5 = 5 in (alet x#11 = 2 in (alet binop_7 = (x#5 + x#11) in add1(binop_7))))";

  tanf_improved "let_in_let_in_if" 
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    ("\n(alet x#5 = 5 in (alet x#11 = sub1(x#5) in (alet unary_17 = add1(x#11) in (alet y#15 = (unary_17 - 10) in (alet y#8 = y#15 in (alet binop_21 = (y#8 + x#5) in (if binop_21: (alet abcd#26 = 10 in add1(abcd#26)) else: (alet x#32 = 0 in (alet if_37 = (if x#32: x#32 else: 1) in (alet y#35 = sub1(if_37) in y#35))))))))))");

  tanf_improved "lets_in_prim"
    "(let x = 1 in x) + (let x = 2 in x)"
    "\n(alet x#5 = 1 in (alet x#10 = 2 in (x#5 + x#10)))";

  tanf_improved "if_in_if_in_let_in_add1"
    "add1(let x = (if (if 0: 0 else: 1): 2 else: 3) in (if x: 4 else: 5))"
    "\n(alet if_7 = (if 0: 0 else: 1) in (alet x#5 = (if if_7: 2 else: 3) in (alet if_13 = (if x#5: 4 else: 5) in add1(if_13))))";

  tanf_improved "simple_conditional"
    "(let x = (if 1: 5 + 5 else: 6 * 2) in (let y = (if 0: x * 3 else: x + 5) in x + y))"
    ("\n(alet x#4 = (if 1: (5 + 5) else: (6 * 2)) in (alet y#15 = (if 0: (x#4 * 3) else: (x#4 + 5)) in (x#4 + y#15)))");

  tanf_improved "complex_conditional"
    ("(let x = (if (5 - 10): add1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))"
    )
    ("\n(alet binop_6 = (5 - 10) in (alet x#4 = (if binop_6: (alet binop_10 = (5 + 5) in add1(binop_10)) else: (alet binop_14 = (6 * 2) in sub1(binop_14))) in (alet binop_22 = (x#4 * 0) in (alet if_21 = (if binop_22: (alet unary_27 = sub1(3) in (x#4 * unary_27)) else: (alet unary_30 = add1(x#4) in (unary_30 + 5))) in (alet y#19 = sub1(if_21) in (alet binop_34 = (x#4 + y#19) in sub1(binop_34)))))))");
  tanf_improved "expr_basic"
    ("def f() : 1\n1")
    ("(fun f$2(): 1)\n1");
  tanf_improved "expr_call"
    ("def f() : 1\nf()")
    ("(fun f$2(): 1)\n(f$2())\n");
  tanf_improved "expr_call_w_imm_args"
    ("def f(a, b) : 1\n(f(1, 2))")
    ("(fun f$2(a#3, b#4): 1)\n(f$2(1, 2))");
  tanf_improved "expr_call_w_compound_args"
    ("def f(a, b) : 1\nf(add1(1), 2)")
    ("(fun f$2(a#3, b#4): 1)
(alet unary_7 = add1(1) in (f$2(unary_7, 2)))");
  tanf_improved "expr_call_w_multiple_compound_args"
    ("def f(a, b) : 1\nf(add1(1), add1(1))")
    ("(fun f$2(a#3, b#4): 1)
(alet unary_7 = add1(1) in (alet unary_9 = add1(1) in (f$2(unary_7, unary_9))))");
  tanf_improved "multiple_expr_call_w_multiple_compound_args"
    ("def f(a, b) : 1\ndef g(a, b, c) : a == b\nlet c = f(add1(1), add1(1)), d = g(add1(2), add1(3), 4 + 3) in d")
    ("(fun f$2(a#3, b#4): 1)
(fun g$6(a#7, b#8, c#9): (a#7 == b#8))
(alet unary_17 = add1(1) in (alet unary_19 = add1(1) in (alet c#15 = (f$2(unary_17, unary_19)) in (alet unary_24 = add1(2) in (alet unary_26 = add1(3) in (alet binop_28 = (4 + 3) in (alet d#22 = (g$6(unary_24, unary_26, binop_28)) in d#22)))))))");
  tanf_improved "expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\nf(g(1))")
    ("(fun f$2(a#3): a#3)
(fun g$5(b#6): add1(b#6))
(alet app_10 = (g$5(1)) in (f$2(app_10)))");
  tanf_improved "expr_within_expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\ndef h(b) : b\nh(f(g(1)))")
    ("(fun f$2(a#3): a#3)
(fun g$5(b#6): add1(b#6))
(fun h$9(b#10): b#10)
(alet app_14 = (g$5(1)) in (alet app_13 = (f$2(app_14)) in (h$9(app_13))))");
  tanf_improved "infinite_loop"
    ("def f(a) : g(a)\ndef g(a) : f(a)\ng(1)")
    ("(fun f$2(a#3): (g$6(a#3)))\n(fun g$6(a#7): (f$2(a#7)))\n(g$6(1))");
  tanf_improved "tuple"
    ("(1, 2, 3)")
    ("\n(1, 2, 3)");
  tanf_improved "get_tuple"
    ("(1, 2, 3)[0]")
    ("\n(alet tuple_4 = (1, 2, 3) in tuple_4[0])");
  tanf_improved "set_tuple"
    ("(1, 2, 3)[0] := 2")
    ("\n(alet tuple_5 = (1, 2, 3) in (tuple_5[0]:= 2))");
    (* todo: more tuple tests *)
]

(* Pair tests with no potential side effects (like lets, functions, etc) *)
let basic_pair_tests = [
  t "empty_pair" "()" "" "()";
  t "single_pair" "(5,)" "" "(5,)";
  t "double_pair" "(5, 6)" "" "(5, 6)";
  t "long_pair" "(5, 6, 7, 8, 9, 10, 100)" "" "(5, 6, 7, 8, 9, 10, 100)";
  t "tuple_within_tuple" "((5, 6), (7, 8))" "" "((5, 6), (7, 8))";
  t "tuple_within_tuple_2" "((5, 6), (7, 8, 9))" "" "((5, 6), (7, 8, 9))";
  t "tuple_within_tuple_3" "((5, 6, 9), (7, 8))" "" "((5, 6, 9), (7, 8))";
  t "tuple_within_tuple_complex" "((5, 6, (7, 8, (9, 10, (11, (12, 13)))), 14), (15, 16))" ""
    "((5, 6, (7, 8, (9, 10, (11, (12, 13)))), 14), (15, 16))";
  t "expr_within_tuple" "(1 + 1, 2)" ""
    "(2, 2)";
  t "expr_within_tuple_2" "(1 + 1, add1(2))" ""
    "(2, 3)";
  t "print_within_tuple" "(print(2), add1(2))" ""
    "2\n(2, 3)";
  t "print_of_tuple_within_tuple" "(print((2, 3)), add1(2))" ""
    "(2, 3)\n((2, 3), 3)";
  t "get_value_from_tuple_0" "(1, 2, 3, 4, 5)[0]" "" "1";
  t "get_value_from_tuple_1" "(1, 2, 3, 4, 5)[1]" "" "2";
  t "get_value_from_tuple_2" "(1, 2, 3, 4, 5)[2]" "" "3";
  t "get_value_from_tuple_3" "(1, 2, 3, 4, 5)[3]" "" "4";
  t "get_value_from_tuple_4" "(1, 2, 3, 4, 5)[4]" "" "5";
  t "get_value_from_tuple_5_tuple" "(1, (1, 2, 3), 3, 4, 5)[1]" "" "(1, 2, 3)";
  t "get_value_from_tuple_expr" "(1, 2, 3, 4, 5)[add1(3)]" "" "5";
  t "get_value_from_tuple_expr2" "(1, 2, 3, 4, 5)[sub1(1)]" "" "1";
  terr "get_value_from_tuple_low_idx" "(1, 2, 3, 4, 5)[-1]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too small";
  terr "get_value_from_tuple_low_idx_expr" "(1, 2, 3, 4, 5)[sub1(0)]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too small";
  terr "get_value_from_tuple_high_idx" "(1, 2, 3, 4, 5)[5]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too large";
  terr "get_value_from_tuple_high_idx_expr" "(1, 2, 3, 4, 5)[add1(4)]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too large";
  terr "tuple_access_wrong_type" "1[5]" "" "tuple access expected tuple num(1)";
  terr "tuple_access_idx_wrong_type" "(1, 2)[true]" "" "unable to access tuple position bool(true)";
  t "nil_list_1" "(1, nil)" "" "(1, nil)";
  t "nil_list_2" "(1, (2, nil))" "" "(1, (2, nil))";
  terr "tuple_access_idx_wrong_type_nil_access" "nil[true]" "" "unable to dereference value, got nil";
  terr "tuple_access_idx_wrong_type_nil_idx" "(1, 2)[nil]" "" "unable to access tuple position nil";
  t "get_value_from_tuple_0_set" "(1, 2, 3, 4, 5)[0] := 3" "" "3";
  t "get_value_from_tuple_4_set" "(1, 2, 3, 4, 5)[4] := 3" "" "3";
  t "get_value_from_tuple_expr_set" "(1, 2, 3, 4, 5)[add1(3)] := 3" "" "3";
  t "get_value_from_tuple_expr2_set" "(1, 2, 3, 4, 5)[sub1(1)] := 3" "" "3";
  t "get_value_from_tuple_expr2_set_tuple" "(1, 2, 3, 4, 5)[sub1(1)] := (1, 2, 3)" "" "(1, 2, 3)";
  t "unchanged_modify_new_tuples" "print((1, 2, 3, 4, 5)); (1, 2, 3, 4, 5)[sub1(1)] := (1, 2, 3); (1, 2, 3, 4, 5)" "" "(1, 2, 3, 4, 5)\n(1, 2, 3, 4, 5)";
  terr "get_value_from_tuple_low_idx_set" "(1, 2, 3, 4, 5)[-1] := 3" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too small";
  terr "get_value_from_tuple_low_idx_expr_set" "(1, 2, 3, 4, 5)[sub1(0)] := 3" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too small";
  terr "get_value_from_tuple_high_idx_set" "(1, 2, 3, 4, 5)[5] := 3" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too large";
  terr "get_value_from_tuple_high_idx_expr_set" "(1, 2, 3, 4, 5)[add1(4)] := 3" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. index too large";
  terr "tuple_access_wrong_type_set" "1[5] := 3" "" "tuple access expected tuple num(1)";
  terr "tuple_access_idx_wrong_type_set" "(1, 2)[true] := 3" "" "unable to access tuple position bool(true)";
  terr "tuple_unary_type" "add1((1, 2))" "" "arithmetic expected a number, got tuple((num(1), num(2)))";
  terr "tuple_binary_type_l" "(1, 2) + 1" "" "arithmetic expected a number, got tuple((num(1), num(2)))";
  terr "tuple_binary_type_r" "1 + (1, 2)" "" "arithmetic expected a number, got tuple((num(1), num(2)))";
  t "equality_ref" "(1, 2, 3) == (1, 2, 3)" "" "false";
  t "equality_ref_true" "let x = (1, 2, 3) in x == x" "" "true";
  t "equality_equal_ref" "let x = (1, 2, 3) in equal(x, x)" "" "true";
  t "equality_equal_structural" "equal((1, 2, 3), (1, 2, 3))" "" "true";
  t "equality_equal_structural_nest" "equal(((1, 2, 3), 2, 3), ((1, 2, 3), 2, 3))" "" "true";
  t "equality_equal_structural_prims" "equal(((add1(1), 2, 3), 2, 3), ((2, 2, 3), 2, 3))" "" "true";
  t "equality_notequal_structural_prims" "equal(((add1(1), 2, 3), 2, 3), ((2, 2, 4), 2, 3))" "" "false";
]

let stdin_tests = [
  t "stdin_print_int" "print(input())" "5" "5\n5";
  t "stdin_print_bool" "print(input())" "true" "true\ntrue";
  t "stdin_print_bool_false" "print(input())" "false" "false\nfalse";
  t "wf_input" "input()" "" "0";
]

(* todo: is_tuple tests *)
(* todo: is_well_formed tuple tests *)
let pair_tests = [
  t "tup1" "let t = (4, (5, 6)) in
            begin
              t[0] := 7;
              t
            end" "" "(7, (5, 6))";
  t "tup2" "let t = (4, (5, nil)) in
            begin
              t[1] := nil;
              t
            end" "" "(4, nil)";
  (* No need for cyclic tuples *)
  (* t "tup3" "let t = (4, (5, nil)) in
            begin
              t[1] := t;
              t
            end" "" "(4, <cyclic tuple 1>)"; *)
  t "tup4" "let t = (4, 6) in
            (t, t)"
    ""
    "((4, 6), (4, 6))"
]

(* let oom = [
 *   tgcerr "oomgc1" (7) "(1, (3, 4))" "" "Out of memory";
 *   tgc "oomgc2" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tvgc "oomgc3" (8) "(1, (3, 4))" "" "(1, (3, 4))";
 *   tgc "oomgc4" (4) "(3, 4)" "" "(3, 4)";
 * ] *)

let input = [
  t "input1" "let x = input() in x + 2" "123" "125"
]

let let_tests = [
  t "let_blank" "let _ = print(5 * 5) in print(3)" "" "25\n3\n3";
  t "tuple_modification"
    "let t = (1, 2, 3, 4),
         a = t[1],
         b = t[1] := t[a],
         _ = t[0] := a in
         print(t); print(a); print(b)" ""
         "(2, 3, 3, 4)\n2\n3\n3";
  t "tuple_double_modify"
    "let t = (1, 2, 3, 4) in
         t[0] := t[1];
         t[1] := t[0]; 
         t" ""
         "(2, 2, 3, 4)";
  t "destructure_basic"
    "let (a, b, c) = (1, 2, 3) in (a, c, b)"
    ""
    "(1, 3, 2)";
  t "destructure_complex"
    "let (a, b, (c, d), e) = (1, 2, (3, 4), 5) in (a, b, (d, c), e)"
    ""
    "(1, 2, (4, 3), 5)";
  t "destructure_expr"
    "let (a, b, (c, d), e) = (1, 2, (add1(3), add1(4)), 5) in (a, b, (d, c), e)"
    ""
    "(1, 2, (5, 4), 5)";
  t "destructure_print"
    "let (a, _, c) = (1, print(2), 5) in (a, c)"
    ""
    "2\n(1, 5)";
  t "destructure_print_nested"
    "let (a, (b, _), c) = (1, (2, print(2)), 5) in (a, c)"
    ""
    "2\n(1, 5)";
  t "destructure_not_nested" 
    "let (a, b, c, d) = (1, (2, 3), (4, 5, 6), ()) in 
      print(a); print(b); print(c); d"
    ""
    "1\n(2, 3)\n(4, 5, 6)\n()";
  t "let_empty_pair"
    "let a = () in a"
    ""
    "()";
  t "let_empty_pair_pair"
    "let a = ((), ()) in a[0]"
    ""
    "()";
]

let sequencing_tests = [
  t "print_add" "print(5 * 5) ; 5 - 2" "" "25\n3";
  t "add_twice" "5 * 5 ; 5 - 2" "" "3";
  t "sequencing" "print(5 * 5); print(3)" "" "25\n3\n3";
]

let suite =
  "suite">:::
  wf_tests @
  input @
  desugar_tests @
  anf_tests @
  pair_tests @
  basic_pair_tests @
  stdin_tests @
  sequencing_tests @
  let_tests


let () =
  run_test_tt_main ("all_tests">:::[suite; old_tests; input_file_test_suite ()])
;;

