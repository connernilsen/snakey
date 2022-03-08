open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors

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
    assert_equal ("\n" ^ expected ^ "\n") (string_of_aprogram (anf (tag (desugar (rename_and_tag (tag (parse_string name program))))))) ~printer:(fun s->s)
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
  tdesugar "desugar_complex"
    "def f1(b, n):
      let x = print(b),
          y = print(n) in 
        isnum(n) && isbool(b) 
  def f2(n, b):
    let x = print(f1(b, n)),
        y = print(n),
        z = print(b) in 
      x && isnum(y) && isbool(z)
  f2(5, false)"
    "(def f1(b, n):
  (let x = print(b), y = print(n) in (if isnum(n): (if isbool(b): true else: false) else: false)))
(def f2(n, b):
  (let x = print((f1(b, n))), y = print(n), z = print(b) in (if (if x: (if isnum(y): true else: false) else: false): (if isbool(z): true else: false) else: false)))
(f2(5, false))";
]

let anf_tests = [
  tanf_improved "let_in_prim"
    "add1(let x = 5 in x)"
    "\n(alet x#4 = 5 in add1(x#4))";

  tanf_improved "let_in_prim_with_eval"
    "add1(let x = 5 in add1(x))"
    "\n(alet x#5 = 5 in (alet unary_3 = add1(x#5) in add1(unary_3)))";

  tanf_improved "let_in_prim2_with_eval"
    "add1(let x = 5 in (x + (let x = 2 in x)))"
    "\n(alet x#9 = 5 in (alet x#6 = 2 in (alet binop_3 = (x#9 + x#6) in add1(binop_3))))";

  tanf_improved "let_in_let_in_if" 
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
    ("\n(alet x#21 = 5 in " ^
     "(alet x#26 = sub1(x#21) in " ^
     "(alet unary_32 = add1(x#26) in " ^
     "(alet y#29 = (unary_32 - 10) in " ^
     "(alet y#23 = y#29 in " ^
     "(alet binop_18 = (y#23 + x#21) in " ^
     "(if binop_18: (alet abcd#15 = 10 in " ^
     "add1(abcd#15)) " ^ 
     "else: (alet x#4 = 0 in " ^
     "(alet if_8 = (if x#4: x#4 else: 1) in " ^
     "(alet y#6 = sub1(if_8) in " ^
     "y#6))))))))))");

  tanf_improved "lets_in_prim"
    "(let x = 1 in x) + (let x = 2 in x)"
    "\n(alet x#8 = 1 in (alet x#4 = 2 in (x#8 + x#4)))";

  tanf_improved "if_in_if_in_let_in_add1"
    "add1(let x = (if (if 0: 0 else: 1): 2 else: 3) in (if x: 4 else: 5))"
    "\n(alet if_11 = (if 0: 0 else: 1) in (alet x#7 = (if if_11: 2 else: 3) in (alet if_3 = (if x#7: 4 else: 5) in add1(if_3))))";

  tanf_improved "simple_conditional"
    "(let x = (if 1: 5 + 5 else: 6 * 2) in (let y = (if 0: x * 3 else: x + 5) in x + y))"
    ("\n(alet x#15 = (if 1: (5 + 5) else: (6 * 2)) in (alet y#6 = (if 0: (x#15 * 3) else: (x#15 + 5)) in (x#15 + y#6)))");

  tanf_improved "complex_conditional"
    ("(let x = (if (5 - 10): add1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))"
    )
    ("\n(alet binop_31 = (5 - 10) in " ^
     "(alet x#21 = (if binop_31: " ^
     "(alet binop_28 = (5 + 5) in " ^ 
     "add1(binop_28)) " ^
     "else: " ^ 
     "(alet binop_24 = (6 * 2) in " ^ 
     "sub1(binop_24))) in " ^ 
     "(alet binop_18 = (x#21 * 0) in " ^ 
     "(alet if_9 = (if binop_18: " ^ 
     "(alet unary_15 = sub1(3) in (x#21 * unary_15)) " ^
     "else: " ^ 
     "(alet unary_12 = add1(x#21) in (unary_12 + 5))) in " ^ 
     "(alet y#7 = sub1(if_9) in " ^ 
     "(alet binop_4 = (x#21 + y#7) in sub1(binop_4)))))))");
  tanf_improved "expr_basic"
    ("def f() : 1\n1")
    ("(fun f$2(): 1)\n1");
  tanf_improved "expr_call"
    ("def f() : 1\nf()")
    ("(fun f$2(): 1)\n(f$2())");
  tanf_improved "expr_call_w_imm_args"
    ("def f(a, b) : 1\n(f(1, 2))")
    ("(fun f$4(a#6, b#7): 1)\n(f$4(1, 2))");
  tanf_improved "expr_call_w_compound_args"
    ("def f(a, b) : 1\nf(add1(1), 2)")
    ("(fun f$5(a#7, b#8): 1)\n(alet unary_2 = add1(1) in (f$5(unary_2, 2)))");
  tanf_improved "expr_call_w_multiple_compound_args"
    ("def f(a, b) : 1\nf(add1(1), add1(1))")
    ("(fun f$6(a#8, b#9): 1)\n(alet unary_2 = add1(1) in (alet unary_4 = add1(1) in (f$6(unary_2, unary_4))))");
  tanf_improved "multiple_expr_call_w_multiple_compound_args"
    ("def f(a, b) : 1\ndef g(a, b, c) : a == b\nlet c = f(add1(1), add1(1)), d = g(add1(2), add1(3), 4 + 3) in d")
    ("(fun f$18(a#20, b#21): 1)\n" ^
     "(fun g$22(a#26, b#27, c#28): (a#26 == b#27))\n" ^
     "(alet unary_5 = add1(1) in (alet unary_7 = add1(1) in (alet c#3 = (f$18(unary_5, unary_7)) in (alet unary_11 = add1(2) in (alet unary_13 = add1(3) in (alet binop_15 = (4 + 3) in (alet d#9 = (g$22(unary_11, unary_13, binop_15)) in d#9)))))))");
  tanf_improved "expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\nf(g(1))")
    ("(fun f$4(a#6): a#6)\n(fun g$7(b#10): add1(b#10))\n(alet app_2 = (g$7(1)) in (f$4(app_2)))");
  tanf_improved "expr_within_expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\ndef h(b) : b\nh(f(g(1)))")
    ("(fun f$5(a#7): a#7)\n(fun g$8(b#11): add1(b#11))\n(fun h$12(b#14): b#14)\n(alet app_3 = (g$8(1)) in (alet app_2 = (f$5(app_3)) in (h$12(app_2))))");
  tanf_improved "infinite_loop"
    ("def f(a) : g(a)\ndef g(a) : f(a)\ng(1)")
    ("(fun f$3(a#6): (g$7(a#6)))\n(fun g$7(a#10): (f$3(a#10)))\n(g$7(1))");
  tanf_improved "tuple"
    ("(1, 2, 3)")
    ("(1, 2, 3)");
  tanf_improved "get_tuple"
    ("(1, 2, 3)[0]")
    ("(alet tuple_4 = (1, 2, 3) in tuple_4[0])");
  tanf_improved "set_tuple"
    ("(1, 2, 3)[0] := 2")
    ("(alet tuple_5 = (1, 2, 3) in (tuple_5[0]:= 2))");
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
  t "get_value_from_tuple_expr" "(1, 2, 3, 4, 5)[add1(3)]" "" "5";
  t "get_value_from_tuple_expr2" "(1, 2, 3, 4, 5)[sub1(1)]" "" "1";
  terr "get_value_from_tuple_low_idx" "(1, 2, 3, 4, 5)[-1]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. too low";
  terr "get_value_from_tuple_low_idx_expr" "(1, 2, 3, 4, 5)[sub1(0)]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. too low";
  terr "get_value_from_tuple_high_idx" "(1, 2, 3, 4, 5)[5]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. too high";
  terr "get_value_from_tuple_high_idx_expr" "(1, 2, 3, 4, 5)[add1(4)]" "" "unable to access index of tuple tuple((num(1), num(2), num(3), num(4), num(5))), length 5. too high";
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
  t "tup3" "let t = (4, (5, nil)) in
            begin
              t[1] := t;
              t
            end" "" "(4, <cyclic tuple 1>)";
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


let suite =
  "suite">:::
  wf_tests @
  (* input @ *)
  (* desugar_tests @ *)
  (* anf_tests @ *)
  (* pair_tests @ *)
  basic_pair_tests



let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;

