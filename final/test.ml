open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Libtest
open Assembly
open Pretty
open Graph

let t name program input expected = name>::test_run ~args:[] ~std_input:input ~skip_newline:true Naive program name expected;;
let tr name program input expected = name>::test_run ~args:[] ~std_input:input ~skip_newline:true Register program name expected;;
let ta name program input expected = name>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = name>::test_run ~args:[string_of_int heap_size] ~std_input:input ~skip_newline:true Naive program name expected;;
let tvg name program input expected = name>::test_run_valgrind ~args:[] ~std_input:input Naive program name expected;;
let tvgc name heap_size program input expected = name>::test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let terr name program input expected = name>::test_err ~args:[] ~std_input:input Naive program name expected;;
let tgcerr name heap_size program input expected = name>::test_err ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
let tanf name program input expected = name>::fun _ ->
    assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let tparse name program expected = name>::fun _ ->
    assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program;;

let teq name actual expected = name>::fun _ ->
    assert_equal expected actual ~printer:(fun s -> s);;

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * (List.length Compile.native_fun_bindings)

let lexing_and_parsing = [
  terr "unmatched_parens" "\"hello" "" "Unterminated string";
  terr "unmatched_parens_second" "\"hello\"; \"" "" "Unterminated string";
]
let tstring = [
  t "tstring_simple" "\"test\"" "" "test";
  t "tstring_complex" "\"\"\"test
  test\"\"\"" "" "test\n  test";
  t "tstring_quotes" "\"test\\\"\"" ""
    "test\"";
  t "tstring_newline" "\"test\ntest\"" ""
    "test\ntest";
  t "tstring_seq" "\"t1\"; print(\"hey\"); \"t2\"" ""
    "heyt2";
  t "input_test" "input()" "hello" "hello";
]
let tstring_complex = [
  (let long = "hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello
  hellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohellohello"
   in t "very_long" ("\"" ^ long ^ "\"") "" long);
  t "tstring_in_let" "let s = \"test\" in s" "" "test";
]
let tstring_gc = [
  tgc "tstring_gc_simple" (builtins_size + 6) "\"test\"" "" "test";
  tgc "tstring_gc_repeat" (builtins_size + 6) "\"test\"; \"test\"; \"test\"; \"test\"" "" "test";

]
let tis = [
  t "isstr_str" "isstr(\"hello\")" "" "true";
  t "isstr_num" "isstr(5)" "" "false";
  t "isstr_bool_t" "isstr(true)" "" "false";
  t "isstr_bool_f" "isstr(false)" "" "false";
  t "isstr_tuple" "isstr((1, 2, 3))" "" "false";
  t "isnum_str" "isnum(\"1\")" "" "false";
  t "isbool_str" "isnum(\"true\")" "" "false";
  t "istuple_str" "istuple(\"1\")" "" "false";
]

(* testing todos: ensure register allocation still works *)

let suite =
  "unit_tests">:::
  lexing_and_parsing
  @ tstring
  @ tis
  @ tstring_complex
  @ tstring_gc

let () =
  run_test_tt_main ("all_tests">:::[
      suite; 
      (* old_tests; *)
      input_file_test_suite ()])
;;
