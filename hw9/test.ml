open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Libtest

let t name program input expected = name>::test_run ~args:[] ~std_input:input program name expected;;
let ta name program input expected = name>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = name>::test_run ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tvg name program input expected = name>::test_run_valgrind ~args:[] ~std_input:input program name expected;;
let tvgc name heap_size program input expected = name>::test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let terr name program input expected = name>::test_err ~args:[] ~std_input:input program name expected;;
let tgcerr name heap_size program input expected = name>::test_err ~args:[string_of_int heap_size] ~std_input:input program name expected;;
let tanf name program input expected = name>::fun _ ->
    assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let tparse name program expected = name>::fun _ ->
    assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program;;

let teq name actual expected = name>::fun _ ->
    assert_equal expected actual ~printer:(fun s -> s);;

(* let tfvs name program expected = name>:: *)
(*   (fun _ -> *)
(*     let ast = parse_string name program in *)
(*     let anfed = anf (tag ast) in *)
(*     let vars = free_vars_P anfed [] in *)
(*     let c = Stdlib.compare in *)
(*     let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in *)
(*     assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print) *)
(* ;; *)

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * 1 (* TODO FIXME (List.length Compile.native_fun_bindings) *)

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
  terr "bad_destruct_func" "def new_func((a, v, bong, (e, w)), tree):
   if a: true else: bong + tree 
new_func((1, 2, 1, true), 1)" "" "unable to destructure tuple with incorrect length, got true";
  terr "bad_destruct" "let ((a, b), _) = (true, 0) in 0" "" "unable to destructure tuple with incorrect length, got true";
  terr "bad_tuple" "(true, 0)[0][0]" "" "get expected tuple, got true";
  terr "bad_destruct_2" "let (a, _) = true in 0" "" "unable to destructure tuple with incorrect length, got true";
  terr "nil_destruct" "let (a, b) = nil in a" "" "tried to access component of nil";
  terr "nil_tuple" "nil[0]" "" "tried to access component of nil";
]

let oom = [
  tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
  tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
  tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation";
]

let gc = [
  tgc "gc_lam1" (10 + builtins_size)
    "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
    ""
    "(1, 2)";
]

let native = [
  t "input0" "input() + 2" "123" "125";
  t "print0" "print(125) + 2" "" "125\n127";
  t "input1" "let x = input() in x + 2" "123" "125";
  t "input2" "let x = input() in print(x + 2)" "123" "125\n125";
]

let prim = [
  t "prim1_in_lambda" "(lambda: 1 + 1)()" "" "2";
]

let nested = [
  t "lambda" "(lambda: 1)()" "" "1";
  t "nested_lambda" "(lambda: (lambda: 1)())()" "" "1";
  t "free_in_nested_fun" "let x = 5 in (lambda: (lambda: x)())()" "" "5";
]


let suite =
  "unit_tests">:::
  pair_tests @ oom @ gc @ native @ prim @ nested



let () =
  run_test_tt_main ("all_tests">:::[
      suite;
      old_tests;
      input_file_test_suite ()])
;;
