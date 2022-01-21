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
let t_list ~(value_printer : 'a -> string) (name : string) (value_l : 'a list) (expected_l : 'a list) = name>::
  (fun _ -> assert_equal expected_l value_l ~printer:(string_of_list value_printer));;

(* a list test function for envs *)
let t_envls = t_list ~value_printer:(fun (name, value) -> sprintf "%s: %d" name value);;

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
  t_envls "add1" (add [] "hello" 5) [];
]

let evaluate_tests = [
  t_int "evaluate1" (evaluate (Times(Num(0), Num(5))) []) 0;
  t_int "evaluate2" (evaluate (Times(Num(1), Num(5))) []) 5;
  (* More tests here *)
]

let all_arith_tests =
  get_tests @
  contains_tests @
  add_tests @
  evaluate_tests
  (* More tests here *)
;;

let arith_suite = "arithmetic_evaluation">:::all_arith_tests
;;

run_test_tt_main arith_suite
;;

let all_sexp_tests = [
    (* More tests here *)
  ]
;;

let sexp_suite = "sexp_parsing">:::all_sexp_tests
;;

run_test_tt_main sexp_suite
;;

