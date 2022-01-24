open Sexp
open OUnit2
open Expr
open ExtLib
open Printf

(* a helper for testing integers *)
let t_int name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_int);;

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:dump);;

(* Feel free to add any new testing functions you may need *)

(* Return a stringified list from the given ls arg
  printer: a function to stringify the given sub-list types

  Example: string_of_list (string_of_int) [1; 2; 3] => "[ 1; 2; 3; ]"
*)
let string_of_list (printer : 'a -> string) ls =
  (List.fold_left 
    (fun str item -> 
      (str ^ (sprintf "%a" (fun _ -> printer) item) ^ "; ")) 
    "[ " ls) 
  ^ "]";;

(* Test helper for lists 
  value_print_str: see string_of_list
*)
let t_list (value_printer : 'a -> string) (name : string) (value_l : 'a list) (expected_l : 'a list) = name>::
  (fun _ -> assert_equal expected_l value_l ~printer:(string_of_list value_printer));;

(* A list test function for envs *)
let t_envls = t_list (fun (name, value) -> sprintf "(%s: %d)" name value);;

(* Test function for functions that raise an exception *)
let t_expect_ex name func fail_msg = name>::
      (fun _ -> (assert_raises (Failure(fail_msg)) func));;

(* It can be useful to aggregate tests into lists if they test separate
functions, and put them together at the end *)

let env1 = [("a", 5); ("b", 15)];;
  
let get_tests = [
  t_any "get1_simple" (get env1 "a") (Some(5));
  t_any "get2_simple" (get env1 "b") (Some(15));
  t_any "get3_key_not_exist" (get env1 "c") None;
  t_any "get4_duplicate_keys" (get (("a", 0) :: env1) "a") (Some(0));
  t_any "get5_empty_env" (get [] "hello") None;
];;

let contains_tests = [
  t_any "contains1_simple" (contains env1 "c") false;
  t_any "contains2_simple" (contains env1 "a") true;
  t_any "contains3_duplicate_keys" (contains (("a", 0) :: env1) "a") true;
  t_any "contains4_empty_env" (contains [] "hello") false;
];;

let add_tests = [
  t_envls "add1_empty_env" (add [] "hello" 5) [("hello", 5)];
  t_envls "add2_key_not_exist" (add env1 "hello" 5) (env1 @ [("hello", 5)]);
  t_envls "add3_overwrite_key" (add env1 "a" 0) [("a", 0); ("b", 15)];
];;

let t_eval_ex = 
  (fun name func value -> 
    t_expect_ex name (func) (sprintf "Could not find name %s in env" value));;
let evaluate_tests = [
  t_int "evaluate1_simple" (evaluate (Times(Num(0), Num(5))) []) 0;
  t_int "evaluate2_simple" (evaluate (Times(Num(1), Num(5))) []) 5;
  t_int "evaluate3_with_vars" (evaluate (Times(Plus(Variable("x"), Variable("y")), Num(5))) 
    [("x", 5); ("y", 7)]) 60;
  t_int "evaluate4_simple" (evaluate (Plus(Num(4), Num(5))) []) 9;
  t_int "evaluate5_simple_unused_vars" (evaluate (Plus(Num(4), Num(5))) [("x", 5); ("y", 7)]) 9;
  t_eval_ex "evaluate6_unknown_var" (fun _ -> evaluate (Plus(Variable("x"), Num(5))) [("y", 2)]) "x";
  t_eval_ex "evaluate7_known_and_unknown_vars" 
    (fun _ -> evaluate (Plus(Variable("x"), Variable("y"))) [("x", 2)]) "y";
];;

let pretty_tests = [
  t_any "pretty1_simple" (pretty (Variable("x"))) "x";
  t_any "pretty2_simple" (pretty (Num(5))) "5";
  t_any "pretty3_unwrapped_plus" (pretty (Plus(Variable("x"), Num(5)))) "x + 5";
  t_any "pretty4_unwrapped_plus_with_var_mult" 
    (pretty (Plus(Num(5), Times(Num(3), Variable("x"))))) "5 + 3x";
  t_any "pretty5_wrapped_plus_with_mult" (pretty 
    (Times(Plus(Variable("x"), Variable("y")), Times(Num(3), Variable("x"))))) "(x + y)3x";
  t_any "pretty6_expanded_num_mult" (pretty 
    (Times(Times(Num(3), Num(5)), Times(Num(1234), Variable("z"))))) "3 * 5 * 1234z";
  t_any "pretty7_nested_var_mult" (pretty 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Variable("z"))))) "wxyz";
  t_any "pretty8_nested_mult_with_num" (pretty 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Num(3))))) "wxy3";
  t_any "pretty9_nested_mult_with_nums_adjacent" (pretty 
    (Times(Times(Variable("w"), Num(3)), Times(Num(3), Variable("x"))))) "w3 * 3x";
  t_any "pretty10_nested_add" (pretty 
    (Plus(Plus(Num(1), Num(2)), Plus(Num(3), Num(4))))) "1 + 2 + 3 + 4";
  t_any "pretty11_wrapped_plus_with_mult" (pretty 
    (Times(Times(Num(3), Variable("x")), Plus(Variable("x"), Variable("y"))))) "3x(x + y)";
  t_any "pretty12_nested_complex_adjacent_nums" (pretty
    (Times(Times(Num(1), Times(Num(2), Variable("x"))), 
      Times(Times(Variable("y"), Times(Variable("z"), Num(5))), Num(4))))) "1 * 2xyz5 * 4";
];;

let is_mult_edge_num_tests = [
  t_any "is_mult_edge_num1_no_times" (is_mult_edge_num (Num(5)) true) true;
  t_any "is_mult_edge_num2_no_times" (is_mult_edge_num (Num(5)) false) true;
  t_any "is_mult_edge_num3_no_times" (is_mult_edge_num (Variable("a")) true) false;
  t_any "is_mult_edge_num4_no_times" (is_mult_edge_num (Variable("a")) false) false;
  t_any "is_mult_edge_num5_no_times" (is_mult_edge_num (Plus(Num(5), Num(4))) true) false;
  t_any "is_mult_edge_num6_no_times" (is_mult_edge_num (Plus(Num(5), Num(4))) false) false;
  t_any "is_mult_edge_num7_var_edge" (is_mult_edge_num (Times(Num(5), Variable("a"))) true) true;
  t_any "is_mult_edge_num8_var_not_edge" (is_mult_edge_num (Times(Num(5), Variable("a"))) false) false;
  t_any "is_mult_edge_num9_var_not_edge" (is_mult_edge_num (Times(Variable("a"), Num(5))) true) false;
  t_any "is_mult_edge_num10_var_edge" (is_mult_edge_num (Times(Variable("a"), Num(5))) false) true;
  t_any "is_mult_edge_num11_nested_var_edge" (is_mult_edge_num 
    (Times(Times(Num(5), Variable("a")), Times(Num(5), Variable("a")))) true) true;
  t_any "is_mult_edge_num12_nested_var_not_edge" (is_mult_edge_num 
    (Times(Times(Num(5), Variable("a")), Times(Num(5), Variable("a")))) false) false;
  t_any "is_mult_edge_num13_nested_var_edge" (is_mult_edge_num 
    (Times(Times(Variable("a"), Num(5)), Times(Variable("a"), Num(5)))) false) true;
  t_any "is_mult_edge_num14_nested_var_not_edge" (is_mult_edge_num 
    (Times(Times(Variable("a"), Num(5)), Times(Variable("a"), Num(5)))) true) false;
];;

(* These tests are the same as the pretty_tests, but check different values of mult_expr *)
let pretty_helper_tests = [
  t_any "pretty_helper1_in_times" (pretty_helper (Num(5)) true) "5";
  t_any "pretty_helper2_not_in_times" (pretty_helper (Num(5)) false) "5";
  t_any "pretty_helper3_in_times" (pretty_helper (Variable("x")) true) "x";
  t_any "pretty_helper4_not_in_times" (pretty_helper (Variable("x")) false) "x";
  t_any "pretty_helper5_in_times" (pretty_helper (Plus(Variable("x"), Num(5))) true) "(x + 5)";
  t_any "pretty_helper20_in_times" (pretty_helper 
    (Plus(Num(5), Times(Num(3), Variable("x")))) true) "(5 + 3x)";
  t_any "pretty_helper6_in_times" (pretty_helper 
    (Times(Plus(Variable("x"), Variable("y")), Times(Num(3), Variable("x")))) true) "(x + y)3x";
  t_any "pretty_helper7_in_times" (pretty_helper 
    (Times(Times(Num(3), Num(5)), Times(Num(1234), Variable("z")))) true) "3 * 5 * 1234z";
  t_any "pretty_helper8_in_times" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Variable("z")))) true) "wxyz";
  t_any "pretty_helper9_in_times" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Num(3)))) true) "wxy3";
  t_any "pretty_helper10_in_times" (pretty_helper 
    (Times(Times(Variable("w"), Num(3)), Times(Num(3), Variable("x")))) true) "w3 * 3x";
  t_any "pretty_helper11_in_times" (pretty_helper 
    (Plus(Plus(Num(1), Num(2)), Plus(Num(3), Num(4)))) true) "(1 + 2 + 3 + 4)";
  t_any "pretty_helper12_not_in_times" (pretty_helper (Plus(Variable("x"), Num(5))) false) "x + 5";
  t_any "pretty_helper13_not_in_times" (pretty_helper (Plus(Num(5), Times(Num(3), Variable("x")))) false) "5 + 3x";
  t_any "pretty_helper14_not_in_times" (pretty_helper 
    (Times(Plus(Variable("x"), Variable("y")), Times(Num(3), Variable("x")))) false) "(x + y)3x";
  t_any "pretty_helper15_not_in_times" (pretty_helper 
    (Times(Times(Num(3), Num(5)), Times(Num(1234), Variable("z")))) false) "3 * 5 * 1234z";
  t_any "pretty_helper16_not_in_times" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Variable("z")))) false) "wxyz";
  t_any "pretty_helper17_not_in_times" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Num(3)))) false) "wxy3";
  t_any "pretty_helper18_not_in_times" (pretty_helper 
    (Times(Times(Variable("w"), Num(3)), Times(Num(3), Variable("x")))) false) "w3 * 3x";
  t_any "pretty_helper19_not_in_times" (pretty_helper 
    (Plus(Plus(Num(1), Num(2)), Plus(Num(3), Num(4)))) false) "1 + 2 + 3 + 4";
];;

let all_arith_tests =
  get_tests @
  contains_tests @
  add_tests @
  evaluate_tests @
  pretty_tests @
  is_mult_edge_num_tests
;;

let arith_suite = "arithmetic_evaluation">:::all_arith_tests
;;

run_test_tt_main arith_suite
;;

let parse_toks_tests = [
  t_any "parse_toks_test1_simple_nest" (parse_toks (tokenize "(a b)"))
    (Ok([Nest([Sym("a", (0, 1, 0, 2)); Sym("b", (0, 3, 0, 4))], (0, 0, 0, 5))]));
  t_any "parse_toks_test2_multiple_nest" (parse_toks (tokenize "(a (b true) 3)")) 
    (Ok([
      Nest([Sym("a", (0, 1, 0, 2)); 
        Nest([Sym("b", (0, 4, 0, 5)); Bool(true, (0, 6, 0, 10))], (0, 3, 0, 11)); 
      Int(3, (0, 12, 0, 13))],
    (0, 0, 0, 14))]));
  t_any "parse_toks_test3_error_lp" (parse_toks (tokenize "(a")) (Error("Unmatched left paren at line 0, col 0"));
  t_any "parse_toks_test4_error_multi_lp" (parse_toks (tokenize "(a (b c")) (Error("Unmatched left paren at line 0, col 3"));
  t_any "parse_toks_test5_error_rp" (parse_toks (tokenize "(a (b c)))")) (Error("Unmatched right paren at line 0, col 9"));
  t_any "parse_toks_test6_deep_nest" (parse_toks (tokenize "(a (b (c) d) e)"))
    (Ok([
      Nest([
        Sym("a", (0, 1, 0, 2)); Nest([
          Sym("b", (0, 4, 0, 5)); Nest([
            Sym("c", (0, 7, 0, 8))
          ], (0, 6, 0, 9)); 
          Sym("d", (0, 10, 0, 11))
        ], (0, 3, 0, 12)); 
        Sym("e", (0, 13, 0, 14))
      ], (0, 0, 0, 15))
    ]));
  t_any "parse_toks_nest7_multi_top_level" (parse_toks (tokenize "() a b")) 
    (Ok([Nest([], (0, 0, 0, 2)); Sym("a", (0, 3, 0, 4)); Sym("b", (0, 5, 0, 6))]));
  t_any "parse_toks_nest8_heavy_empty_nests" (parse_toks (tokenize "(((())()))()"))
    (Ok([Nest([Nest([
      Nest([Nest([], (0, 3, 0, 5))], (0, 2, 0, 6)); 
      Nest([], (0, 6, 0, 8))], (0, 1, 0, 9))], (0, 0, 0, 10));
      Nest([], (0, 10, 0, 12))]));
  t_any "parse_toks_nest9_heavy_empty_nests_error_rp" (parse_toks (tokenize "(((()))))())()"))
    (Error("Unmatched right paren at line 0, col 8"));
  t_any "parse_toks_nest10_heavy_val_nests_error_rp" 
    (parse_toks (tokenize "(a (b (c (3) d) e) f) g) h)())()"))
    (Error("Unmatched right paren at line 0, col 23"));
  t_any "parse_toks_nest11_heavy_empty_nests_error_lp" (parse_toks (tokenize "(((()(()((()))((((((()))())()"))
    (Error("Unmatched left paren at line 0, col 16"));
  t_any "parse_toks_nest12_simple_error_lp" (parse_toks (tokenize "("))
    (Error("Unmatched left paren at line 0, col 0"));
  t_any "parse_toks_nest13_simple_error_rp" (parse_toks (tokenize ")"))
    (Error("Unmatched right paren at line 0, col 0"));
  t_any "parse_toks_nest14_simple_nest" (parse_toks (tokenize "a (b) c"))
    (Ok([Sym("a", (0, 0, 0, 1)); 
      Nest([Sym("b", (0, 3, 0, 4))], (0, 2, 0, 5)); 
      Sym("c", (0, 6, 0, 7))]));
  t_any "parse_toks_nest15_whitespace_heavy_empty_nests_error_lp" 
    (parse_toks (tokenize "(((\n()\n(()(((\n)))\n((((\n((())\n)())()"))
    (Error("Unmatched left paren at line 4, col 2"));
  t_any "parse_toks_test16_nest_vals_with_whitespace" 
    (parse_toks (tokenize "\n(\nabcd\n\tbcd\t)"))
    (Ok([Nest([Sym("abcd", (2, 0, 2, 4)); Sym("bcd", (3, 1, 3, 4))], (1, 0, 3, 6))]));
  t_any "parse_toks_test17_heavy_nest_vals" 
    (parse_toks (tokenize "(a (b (c) true d) e)"))
    (Ok([
      Nest([
        Sym("a", (0, 1, 0, 2)); Nest([
          Sym("b", (0, 4, 0, 5)); Nest([
            Sym("c", (0, 7, 0, 8))
          ], (0, 6, 0, 9)); 
          Bool(true, (0, 10, 0, 14));
          Sym("d", (0, 15, 0, 16))
        ], (0, 3, 0, 17)); 
        Sym("e", (0, 18, 0, 19))
      ], (0, 0, 0, 20))
    ]));
  t_any "parse_toks_test18_heavy_nest_vals_with_whitespace" 
    (parse_toks (tokenize "(a \n\t(b \n\t\t(c) \n\t\ttrue d\n\t\t) \n\te\n)"))
    (Ok([
      Nest([
        Sym("a", (0, 1, 0, 2)); Nest([
          Sym("b", (1, 2, 1, 3)); Nest([
            Sym("c", (2, 3, 2, 4))
          ], (2, 2, 2, 5)); 
          Bool(true, (3, 2, 3, 6));
          Sym("d", (3, 7, 3, 8))
        ], (1, 1, 4, 3)); 
        Sym("e", (5, 1, 5, 2))
      ], (0, 0, 6, 1))
    ]))
];;

(* These tests are the same as the parse_toks_tests, but don't tokenize values from 
  the input string 
*)
let parse_tests = [
  t_any "parse_test1" (parse "(a b)")
    (Ok([Nest([Sym("a", (0, 1, 0, 2)); Sym("b", (0, 3, 0, 4))], (0, 0, 0, 5))]));
  t_any "parse_test2" (parse "(a (b true) 3)")
    (Ok([
      Nest([Sym("a", (0, 1, 0, 2)); 
        Nest([Sym("b", (0, 4, 0, 5)); Bool(true, (0, 6, 0, 10))], (0, 3, 0, 11)); 
      Int(3, (0, 12, 0, 13))],
    (0, 0, 0, 14))]));
  t_any "parse_test3" (parse "(a") (Error("Unmatched left paren at line 0, col 0"));
  t_any "parse_test4" (parse "(a (b c") (Error("Unmatched left paren at line 0, col 3"));
  t_any "parse_test5" (parse "(a (b c)))") (Error("Unmatched right paren at line 0, col 9"));
  t_any "parse_test6" (parse "(a (b (c) d) e)")
    (Ok([
      Nest([
        Sym("a", (0, 1, 0, 2)); Nest([
          Sym("b", (0, 4, 0, 5)); Nest([
            Sym("c", (0, 7, 0, 8))
          ], (0, 6, 0, 9)); 
          Sym("d", (0, 10, 0, 11))
        ], (0, 3, 0, 12)); 
        Sym("e", (0, 13, 0, 14))
      ], (0, 0, 0, 15))
    ]));
    t_any "parse_nest7" (parse "() a b")
      (Ok([Nest([], (0, 0, 0, 2)); Sym("a", (0, 3, 0, 4)); Sym("b", (0, 5, 0, 6))]));
    t_any "parse_nest8" (parse "(((())()))()")
      (Ok([Nest([Nest([
        Nest([Nest([], (0, 3, 0, 5))], (0, 2, 0, 6)); 
        Nest([], (0, 6, 0, 8))], (0, 1, 0, 9))], (0, 0, 0, 10));
        Nest([], (0, 10, 0, 12))]));
    t_any "parse_nest9" (parse "(((()))))())()")
      (Error("Unmatched right paren at line 0, col 8"));
    t_any "parse_nest10" (parse "(a (b (c (3) d) e) f) g) h)())()")
      (Error("Unmatched right paren at line 0, col 23"));
    t_any "parse_nest11" (parse "(((()(()((()))((((((()))())()")
      (Error("Unmatched left paren at line 0, col 16"));
    t_any "parse_nest12" (parse "(")
      (Error("Unmatched left paren at line 0, col 0"));
    t_any "parse_nest13" (parse ")")
      (Error("Unmatched right paren at line 0, col 0"));
    t_any "parse_nest14" (parse "a (b) c")
      (Ok([Sym("a", (0, 0, 0, 1)); 
        Nest([Sym("b", (0, 3, 0, 4))], (0, 2, 0, 5)); 
        Sym("c", (0, 6, 0, 7))]));
    t_any "parse_nest15" (parse "(((\n()\n(()(((\n)))\n((((\n((())\n)())()")
      (Error("Unmatched left paren at line 4, col 2"));
    t_any "parse_test16" (parse "\n(\nabcd\n\tbcd\t)")
      (Ok([Nest([Sym("abcd", (2, 0, 2, 4)); Sym("bcd", (3, 1, 3, 4))], (1, 0, 3, 6))]));
];;

(* Tests for parse_toks_helper that add different accumulator values;
  NOTE: "|" (a pipe character) represents where the tokenized string input starts from --
    all values preceeding the | are added in the accumulators
*)
let parse_toks_helper_tests = [
  (* mock input: "|()" *)
  t_any "parse_toks_helper_test1_no_acc" (parse_toks_helper (tokenize "()") [] [])
    [Nest([], (0, 0, 0, 2))];
  (* mock input: 
    a |
    () 
  *)
  t_any "parse_toks_helper_test2_top_level_sym_in_ret_acc" 
    (parse_toks_helper (tokenize "\n()") [] [Sym("a", (0, 1, 0, 2))])
    [Sym("a", (0, 1, 0, 2)); Nest([], (1, 0, 1, 2))];
  (* mock input: 
    ( |
    ) 
  *)
  t_any "parse_toks_helper_test3_nest_acc" 
    (parse_toks_helper (tokenize "\n)") [([], (0, 0, 0, 0))] [])
    [Nest([], (0, 0, 1, 1))];
  (* mock input: 
    (a |
    )
  *)
  t_any "parse_toks_helper_test4_single_sym_in_nest_acc" 
    (parse_toks_helper (tokenize "\n)") [([Sym("a", (0, 1, 0, 2))], (0, 0, 0, 0))] [])
    [Nest([Sym("a", (0, 1, 0, 2))], (0, 0, 1, 1))];
  (* mock input:
    (() |
    )
  *)
  t_any "parse_toks_helper_test5_single_nest_in_nest_acc" 
  (parse_toks_helper (tokenize "\n)") [([Nest([], (0, 1, 0, 3))], (0, 0, 0, 0))] [])
    [Nest([Nest([], (0, 1, 0, 3))], (0, 0, 1, 1))];
  (* mock input: 
    ((a) |
    )
  *)
  t_any "parse_toks_helper_test6_single_nest_with_sym_in_nest_acc" 
  (parse_toks_helper (tokenize "\n)") [([Nest([Sym("a", (0, 2, 0, 3))], (0, 1, 0, 5))], (0, 0, 0, 0))] [])
    [Nest([Nest([Sym("a", (0, 2, 0, 3))], (0, 1, 0, 5))], (0, 0, 1, 1))];
  (* mock input:
    ( 5
    ( a b |
    ))
  *)
  t_any "parse_toks_helper_test7_multiple_nests_in_nest_acc_with_values" 
    (parse_toks_helper (tokenize "\n\n))") 
      [([Sym("b", (1, 4, 1, 5)); Sym("a", (1, 2, 1, 3))], (1, 0, 1, 1)); ([Int(5, (0, 2, 0, 3))], (0, 0, 0, 1))] [])
    [Nest([Int(5, (0, 2, 0, 3)); Nest([Sym("a", (1, 2, 1, 3)); Sym("b", (1, 4, 1, 5))], (1, 0, 2, 1))], (0, 0, 2, 2))];
  t_any "parse_toks_helper_test8"
  (* mock input:
    0 
    (1 
      (2 
        (3 4) 
        5) 
      6) 
    7
  *)
    (parse_toks_helper (tokenize "\n\n\n\t\t   4)\n\t\t5)\n\t6)\n7")
      [([Int(3, (3, 3, 3, 4))], (3, 2, 3, 3)); 
        ([Int(2, (2, 2, 2, 3))], (2, 1, 2, 2));
        ([Int(1, (1, 1, 1, 2))], (1, 0, 1, 1))]
      [Int(0, (0, 0, 0, 1))])
    [Int(0, (0, 0, 0, 1)); Nest([
      Int(1, (1, 1, 1, 2)); Nest([
        Int(2, (2, 2, 2, 3)); Nest([
          Int(3, (3, 3, 3, 4)); Int(4, (3, 5, 3, 6))], (3, 2, 3, 7));
        Int(5, (4, 2, 4, 3))], (2, 1, 4, 4));
      Int(6, (5, 1, 5, 2))], (1, 0, 5, 3));
    Int(7, (6, 0, 6, 1))];
];;

let all_sexp_tests = 
  parse_toks_tests @
  parse_tests @
  parse_toks_helper_tests
;;

let sexp_suite = "sexp_parsing">:::all_sexp_tests
;;

run_test_tt_main sexp_suite
;;

