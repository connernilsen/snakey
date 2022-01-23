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
  t_any "get1" (get env1 "a") (Some(5));
  t_any "get2" (get env1 "b") (Some(15));
  t_any "get3" (get env1 "c") None;
  t_any "get4" (get (("a", 0) :: env1) "a") (Some(0));
  t_any "get5" (get [] "hello") None;
];;

let contains_tests = [
  t_any "contains1" (contains env1 "c") false;
  t_any "contains2" (contains env1 "a") true;
  t_any "contains3" (contains (("a", 0) :: env1) "a") true;
  t_any "contains4" (contains [] "hello") false;
];;

let add_tests = [
  t_envls "add1" (add [] "hello" 5) [("hello", 5)];
  t_envls "add2" (add env1 "hello" 5) (env1 @ [("hello", 5)]);
  t_envls "add3" (add env1 "a" 0) [("a", 0); ("b", 15)];
];;

let t_eval_ex = 
  (fun name func value -> 
    t_expect_ex name (func) (sprintf "Could not find name %s in env" value));;
let evaluate_tests = [
  t_int "evaluate1" (evaluate (Times(Num(0), Num(5))) []) 0;
  t_int "evaluate2" (evaluate (Times(Num(1), Num(5))) []) 5;
  t_int "evaluate3" (evaluate (Times(Plus(Variable("x"), Variable("y")), Num(5))) 
    [("x", 5); ("y", 7)]) 60;
  t_int "evaluate4" (evaluate (Plus(Num(4), Num(5))) []) 9;
  t_int "evaluate5" (evaluate (Plus(Num(4), Num(5))) [("x", 5); ("y", 7)]) 9;
  t_eval_ex "evaluate6" (fun _ -> evaluate (Plus(Variable("x"), Num(5))) [("y", 2)]) "x";
  t_eval_ex "evaluate7" (fun _ -> evaluate (Plus(Variable("x"), Variable("y"))) [("x", 2)]) "y";
];;

let pretty_tests = [
  t_any "pretty1" (pretty (Variable("x"))) "x";
  t_any "pretty2" (pretty (Num(5))) "5";
  t_any "pretty3" (pretty (Plus(Variable("x"), Num(5)))) "x + 5";
  t_any "pretty4" (pretty (Plus(Num(5), Times(Num(3), Variable("x"))))) "5 + 3x";
  t_any "pretty5" (pretty 
    (Times(Plus(Variable("x"), Variable("y")), Times(Num(3), Variable("x"))))) "(x + y)3x";
  t_any "pretty6" (pretty 
    (Times(Times(Num(3), Num(5)), Times(Num(1234), Variable("z"))))) "3 * 5 * 1234z";
  t_any "pretty7" (pretty 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Variable("z"))))) "wxyz";
  t_any "pretty8" (pretty 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Num(3))))) "wxy3";
  t_any "pretty9" (pretty 
    (Times(Times(Variable("w"), Num(3)), Times(Num(3), Variable("x"))))) "w3 * 3x";
  t_any "pretty10" (pretty 
    (Plus(Plus(Num(1), Num(2)), Plus(Num(3), Num(4))))) "1 + 2 + 3 + 4";
  t_any "pretty11" (pretty 
    (Times(Times(Num(3), Variable("x")), Plus(Variable("x"), Variable("y"))))) "3x(x + y)";
  t_any "pretty12" (pretty
    (Times(Times(Num(1), Times(Num(2), Variable("x"))), 
      Times(Times(Variable("y"), Times(Variable("z"), Num(5))), Num(4))))) "1 * 2xyz5 * 4";
];;

let is_mult_edge_num_tests = [
  t_any "is_mult_edge_num1" (is_mult_edge_num (Num(5)) true) true;
  t_any "is_mult_edge_num2" (is_mult_edge_num (Num(5)) false) true;
  t_any "is_mult_edge_num3" (is_mult_edge_num (Variable("a")) true) false;
  t_any "is_mult_edge_num4" (is_mult_edge_num (Variable("a")) false) false;
  t_any "is_mult_edge_num5" (is_mult_edge_num (Plus(Num(5), Num(4))) true) false;
  t_any "is_mult_edge_num6" (is_mult_edge_num (Plus(Num(5), Num(4))) false) false;
  t_any "is_mult_edge_num7" (is_mult_edge_num (Times(Num(5), Variable("a"))) true) true;
  t_any "is_mult_edge_num8" (is_mult_edge_num (Times(Num(5), Variable("a"))) false) false;
  t_any "is_mult_edge_num9" (is_mult_edge_num (Times(Variable("a"), Num(5))) true) false;
  t_any "is_mult_edge_num10" (is_mult_edge_num (Times(Variable("a"), Num(5))) false) true;
  t_any "is_mult_edge_num11" (is_mult_edge_num 
    (Times(Times(Num(5), Variable("a")), Times(Num(5), Variable("a")))) true) true;
  t_any "is_mult_edge_num12" (is_mult_edge_num 
    (Times(Times(Num(5), Variable("a")), Times(Num(5), Variable("a")))) false) false;
  t_any "is_mult_edge_num13" (is_mult_edge_num 
    (Times(Times(Variable("a"), Num(5)), Times(Variable("a"), Num(5)))) false) true;
  t_any "is_mult_edge_num14" (is_mult_edge_num 
    (Times(Times(Variable("a"), Num(5)), Times(Variable("a"), Num(5)))) true) false;
];;

let pretty_helper_tests = [
  t_any "pretty_helper1" (pretty_helper (Num(5)) true) "5";
  t_any "pretty_helper2" (pretty_helper (Num(5)) false) "5";
  t_any "pretty_helper3" (pretty_helper (Variable("x")) true) "x";
  t_any "pretty_helper4" (pretty_helper (Variable("x")) false) "x";
  t_any "pretty_helper5" (pretty_helper (Plus(Variable("x"), Num(5))) true) "(x + 5)";
  t_any "pretty_helper4" (pretty_helper 
    (Plus(Num(5), Times(Num(3), Variable("x")))) true) "(5 + 3x)";
  t_any "pretty_helper6" (pretty_helper 
    (Times(Plus(Variable("x"), Variable("y")), Times(Num(3), Variable("x")))) true) "(x + y)3x";
  t_any "pretty_helper7" (pretty_helper 
    (Times(Times(Num(3), Num(5)), Times(Num(1234), Variable("z")))) true) "3 * 5 * 1234z";
  t_any "pretty_helper8" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Variable("z")))) true) "wxyz";
  t_any "pretty_helper9" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Num(3)))) true) "wxy3";
  t_any "pretty_helper10" (pretty_helper 
    (Times(Times(Variable("w"), Num(3)), Times(Num(3), Variable("x")))) true) "w3 * 3x";
  t_any "pretty_helper11" (pretty_helper 
    (Plus(Plus(Num(1), Num(2)), Plus(Num(3), Num(4)))) true) "(1 + 2 + 3 + 4)";
  t_any "pretty_helper12" (pretty_helper (Plus(Variable("x"), Num(5))) false) "x + 5";
  t_any "pretty_helper13" (pretty_helper (Plus(Num(5), Times(Num(3), Variable("x")))) false) "5 + 3x";
  t_any "pretty_helper14" (pretty_helper 
    (Times(Plus(Variable("x"), Variable("y")), Times(Num(3), Variable("x")))) false) "(x + y)3x";
  t_any "pretty_helper15" (pretty_helper 
    (Times(Times(Num(3), Num(5)), Times(Num(1234), Variable("z")))) false) "3 * 5 * 1234z";
  t_any "pretty_helper16" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Variable("z")))) false) "wxyz";
  t_any "pretty_helper17" (pretty_helper 
    (Times(Times(Variable("w"), Variable("x")), Times(Variable("y"), Num(3)))) false) "wxy3";
  t_any "pretty_helper18" (pretty_helper 
    (Times(Times(Variable("w"), Num(3)), Times(Num(3), Variable("x")))) false) "w3 * 3x";
  t_any "pretty_helper19" (pretty_helper 
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
  t_any "parse_toks_test1" (parse_toks (tokenize "(a b)"))
    (Ok([Nest([Sym("a", (0, 1, 0, 2)); Sym("b", (0, 3, 0, 4))], (0, 0, 0, 5))]));
  t_any "parse_toks_test2" (parse_toks (tokenize "(a (b true) 3)")) 
    (Ok([
      Nest([Sym("a", (0, 1, 0, 2)); 
        Nest([Sym("b", (0, 4, 0, 5)); Bool(true, (0, 6, 0, 10))], (0, 3, 0, 11)); 
      Int(3, (0, 12, 0, 13))],
    (0, 0, 0, 14))]));
  t_any "parse_toks_test3" (parse_toks (tokenize "(a")) (Error("Unmatched left paren at line 0, col 0"));
  t_any "parse_toks_test4" (parse_toks (tokenize "(a (b c")) (Error("Unmatched left paren at line 0, col 3"));
  t_any "parse_toks_test5" (parse_toks (tokenize "(a (b c)))")) (Error("Unmatched right paren at line 0, col 9"));
  t_any "parse_toks_test6" (parse_toks (tokenize "(a (b (c) d) e)"))
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
    t_any "parse_toks_nest7" (parse_toks (tokenize "() a b")) 
      (Ok([Nest([], (0, 0, 0, 2)); Sym("a", (0, 3, 0, 4)); Sym("b", (0, 5, 0, 6))]));
];;

let all_sexp_tests = 
  parse_toks_tests
;;

let sexp_suite = "sexp_parsing">:::all_sexp_tests
;;

run_test_tt_main sexp_suite
;;

