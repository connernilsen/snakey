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
let teq_notstring name actual expected = (check_name name)>::fun _ ->
    assert_equal expected actual;;
let teq_num name actual expected = (check_name name)>::fun _ ->
    assert_equal expected actual ~printer:(fun d -> sprintf "%d" d);;

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
  te "wf_rebind_builtin" "def input(): true\ninput()" (print_te 
        [DuplicateFun("input",
                    (create_ss "wf_rebind_builtin" 1 8 1 9),
                    (create_ss "wf_rebind_builtin" 1 5 1 6))]);
  te "wf_rebind_builtin_2" "def print(a): true\ninput()" (print_te 
        [DuplicateFun("print",
                    (create_ss "wf_rebind_builtin_2" 1 8 1 9),
                    (create_ss "wf_rebind_builtin_2" 1 5 1 6))]);
  te "wf_rebind_fun" "def a(): true\ndef a(): true\n1" (print_te 
        [DuplicateFun("a",
                    (create_ss "wf_rebind_fun" 2 0 2 13),
                    (create_ss "wf_rebind_fun" 1 0 1 13))]);
  terr "wf_sequence_1" "a; a" "" "The identifier a, used at <wf_sequence_1, 1:0-1:1>, is not in scope\nThe identifier a, used at <wf_sequence_1, 1:3-1:4>, is not in scope";
  te "wf_let_tuple_repeats" "let (a, a) = (1, 2) in true"
      (print_te 
        [DuplicateId("a",
                    (create_ss "wf_let_tuple_repeats" 1 8 1 9),
                    (create_ss "wf_let_tuple_repeats" 1 5 1 6))]);
  te "wf_let_tuple_repeats_non_tuple" "let (a, b) = (1, 2), a = true in true"
      (print_te 
        [DuplicateId("a",
                    (create_ss "wf_let_tuple_repeats_non_tuple" 1 21 1 22),
                    (create_ss "wf_let_tuple_repeats_non_tuple" 1 5 1 6))]);
  te "wf_let_tuple_repeats_nested" "let (a, (b, a)) = (1, (2, 3)) in true"
      (print_te 
        [DuplicateId("a",
                    (create_ss "wf_let_tuple_repeats_nested" 1 12 1 13),
                    (create_ss "wf_let_tuple_repeats_nested" 1 5 1 6))]);
  te "wf_let_nested_tuple_repeats_non_tuple" "let (c, (b, a)) = (1, (2, 3)), b = true in true"
      (print_te 
        [DuplicateId("b",
                    (create_ss "wf_let_nested_tuple_repeats_non_tuple" 1 31 1 32),
                    (create_ss "wf_let_nested_tuple_repeats_non_tuple" 1 9 1 10))]);
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
    "\n(if true: true else: (if ?print(1): true else: false))";
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
    "\n(let bind_temp4 = ((1, 2, 3) should be len 3), a = bind_temp4[0], b = bind_temp4[1], c = bind_temp4[2] in (a, b, c))";
  tdesugar "desugar_destructure_nested"
    "let (a, (b, c), d) = (1, (2, 3), 4) in (a, (b, c), d)"
    "\n(let bind_temp4 = ((1, (2, 3), 4) should be len 3), a = bind_temp4[0], bind_temp6 = (bind_temp4[1] should be len 2), b = bind_temp6[0], c = bind_temp6[1], d = bind_temp4[2] in (a, (b, c), d))";
  tdesugar "desugar_destructure_nested_w_blanks"
    "let (a, (b, _), _) = (1, (2, 3), 4) in (a, (b, c), d)"
    "\n(let bind_temp4 = ((1, (2, 3), 4) should be len 3), a = bind_temp4[0], bind_temp6 = (bind_temp4[1] should be len 2), b = bind_temp6[0], _ = bind_temp6[1], _ = bind_temp4[2] in (a, (b, c), d))";
  tdesugar "desugar_decl_with_destructure"
    "def f((a, b), c): ((a, b), c)\nf((1, 2), 3)"
    "(def f(fun_arg#3, c):\n  (let bind_temp3 = (fun_arg#3 should be len 2), a = bind_temp3[0], b = bind_temp3[1] in ((a, b), c)))\n(?f((1, 2), 3))";
  tdesugar "desugar_decl_with_destructure_and_blank"
    "def f((a, _), c): ((a,), c)\nf((1, 2), 3)"
    "(def f(fun_arg#3, c):\n  (let bind_temp3 = (fun_arg#3 should be len 2), a = bind_temp3[0], _ = bind_temp3[1] in ((a,), c)))\n(?f((1, 2), 3))";
  tdesugar "desugar_destructure_not_nested"
    "let (a, b, c) = (1, (2, 3), ()) in (a, b, c)"
    "\n(let bind_temp4 = ((1, (2, 3), ()) should be len 3), a = bind_temp4[0], b = bind_temp4[1], c = bind_temp4[2] in (a, b, c))";
]

let anf_tests = [
  tanf_improved "tuple"
    ("(1, 2, 3)")
    ("\n(1, 2, 3)");
  tanf_improved "get_tuple"
    ("(1, 2, 3)[0]")
    ("\n(alet tuple_4 = (1, 2, 3) in tuple_4[0])");
  tanf_improved "set_tuple"
    ("(1, 2, 3)[0] := 2")
    ("\n(alet tuple_5 = (1, 2, 3) in (tuple_5[0]:= 2))");
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
  t "istuple_tuple" "istuple((1, 2, 3))" "" "true";
  t "istuple_nil" "istuple(())" "" "true";
  t "istuple_num" "istuple(5)" "" "false";
  t "istuple_bool" "istuple(false)" "" "false";
  t "isbool_tuple" "isbool((1, 2))" "" "false";
  t "isbool_nil" "isbool(())" "" "false";
  t "isnum_tuple" "isnum((1, 2))" "" "false";
  t "isnum_nil" "isnum(())" "" "false";
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
  t "tup3" "let t = (4, (5, nil)) in
            begin
              t[1] := t;
              t
            end" "" "(4, <cyclic tuple 1>)";
  t "tup4" "let t = (4, 6) in
            (t, t)"
    ""
    "((4, 6), (4, 6))";
  t "tuple_empty_access" "((),)[0]" "" "()";
  terr "tuple_destructure_invalid" "let temp = (1, 2), (a, b, c) = temp in true" "" "unable to destructure tuple with incorrect length tuple((num(1), num(2)))";
  terr "tuple_destructure_invalid_2" "let (a, b) = (1, 2, 3) in (a, b)" "" "";
  terr "tuple_destructure_invalid_3" "let temp = (1, 2, 3), (a, b) = temp in (a, b)" "" "";
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

let dup_exn_tests = [
  teq_notstring "dup_exn_basic" (find_dup_exns_by_env [("a", create_ss "dup_exn" 0 0 0 0);]) [];
  teq_notstring "dup_exn_basic_2" (find_dup_exns_by_env [("a", create_ss "dup_exn" 0 0 0 0);("b", create_ss "dup_exn" 0 0 0 0);]) [];
  teq_num "dup_exn_exn" (List.length (find_dup_exns_by_env [("a", create_ss "dup_exn" 0 0 0 0);("a", create_ss "dup_exn" 0 0 0 0);])) 1;
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
  let_tests @
  dup_exn_tests


let () =
  run_test_tt_main ("all_tests">:::[
    suite; 
    (* old_tests; 
    input_file_test_suite () *)
    ])
;;

