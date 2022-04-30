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

let te name program expected_err = name>::test_err ~vg:false Naive program name expected_err;;
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
  t "tstring_newline" "\"test\ntest\"" ""
    "test\ntest";
  t "tstring_carriage_return" "\"test\rtest\"" ""
    "test\rtest";
  t "tstring_tag" "\"test\ttest\"" ""
    "test\ttest";
  t "tstring_question" "\"test?\"" ""
    "test?";
  t "input_test" "input()" "hello" "hello";
]
let tstring_wf = [
  terr "tstring_illegal" "\"é\"" "" "String é at tstring_illegal, 1:3-1:4 contains at least one illegal character.";
  terr "tstring_illegal_2" "\"€\"" "" "String € at tstring_illegal_2, 1:4-1:5 contains at least one illegal character.";
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
  (* todo: string overflow? concat overflow? *)
  t "empty" "let s = \"\" in s" "" "";
  t "big" "let s = \"~\" in s" "" "~";
  t "tstring_in_let" "let s = \"test\" in s" "" "test";
  t "string_in_tuple" "let s = \"test\" in (s, s, s)" "" "(test, test, test)";
  t "string_in_lambda_in_tuple" "let s = (lambda: \"test\") in (s(), s(), s())" "" "(test, test, test)";
]
let tstring_gc = [
  tgc "tstring_gc_simple" (builtins_size + 6) "\"test\"" "" "test";
  tgc "tstring_gc_repeat" (builtins_size + 6) "\"test\"; \"test\"; \"tesc\"; \"tesh\"" "" "tesh";
  tgc "tstring_gc_odd" (builtins_size + 6) "let a = \"a\" in let b = \"b\";\"c\" in let c = \"c\" in a" "" "a";
  tgc "tstring_gc_lambda" (builtins_size + 12) "let a = \"a\" in let b = (lambda: \"ccccc\") in print(b()); print(\"aaaaa\"); a" "" "cccccaaaaaa";
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
  t "tonum_int" "tonum(1) + 0" "" "1";
  t "tonum_str" "tonum(\"1\") + 0" "" "1";
  t "tonum_bool_f" "tonum(false) + 0" "" "0";
  t "tonum_bool_t" "tonum(true) + 0" "" "1";
  te "tonum_invalid_str" "tonum(\"a\")" "Error 18: Error: conversion function received invalid value";
  t "tonum_empty_str" "tonum(\"\") + 0" "" "0";
  t "tobool_bool_f" "tobool(false) && false" "" "false";
  t "tobool_bool_t" "tobool(true) || false" "" "true";
  t "tobool_num_0" "tobool(0) || false" "" "false";
  t "tobool_num_1" "tobool(1) || false" "" "true";
  t "tobool_num_5" "tobool(5) || false" "" "true";
  t "tobool_str_t" "tobool(\"true\") || false" "" "true";
  t "tobool_str_f" "tobool(\"false\") || false" "" "false";
  te "tobool_invalid_str" "tobool(\"truee\")" "Error: conversion function received invalid value, got \"truee\"";
  t "tostr_str" "tostr(\"hello\")" "" "hello";
  t "tostr_bool_f" "tostr(false)" "" "false";
  t "tostr_bool_t" "tostr(true)" "" "true";
  t "tostr_num" "tostr(5)" "" "5";
  te "tostr_bool_f_err" "tostr(false) || false" "Error 3: Error: expected a boolean, got \"false\"";
  te "tostr_bool_t_err" "tostr(true) || false" "Error 3: Error: expected a boolean, got \"true\"";
  te "tostr_num_err" "tostr(5) + 0" "Error 2: Error: arithmetic expected a number, got \"5\"";
  t "tonum_str_neg" "tonum(\"-5\") * 1" "" "-5";
  t "tonum_str_neg_only" "tonum(\"-\")" "" "0";
  t "tostr_neg" "tostr(-5)" "" "-5";
  te "tostr_neg_err" "tostr(-5) * 1" "Error 2: Error: arithmetic expected a number, got \"-5\"";
  t "streq_1" "equal(\"asdf\", \"asdf\")" "" "true";
  t "streq_2" "equal(\"asdf\", \"asdh\")" "" "false";
  t "streq_3" "equal(5, \"a\")" "" "false";
  t "streq_4" "equal(\"a\", 5)" "" "false";
  t "streq_5" "equal(\"false\", false)" "" "false";
  t "streq_6" "equal(true, \"true\")" "" "false";
  t "streq_7" "equal((0, 1), \"a\")" "" "false";
  t "streq_8" "equal(\"a\", (0, 1))" "" "false";
  t "streq_9" "equal(\"a\", \"b\")" "" "false";
]

let tconcat = [
  terr "incorrect_type_1"  "5 ^ \"\"" "" "Value not a string, got 5";
  terr "incorrect_type_2"  "\"\" ^ 15" "" "Value not a string, got 15";
  terr "incorrect_type_both"  "12 ^ 12" "" "Value not a string, got 12";
  t "concat_empty" "\"\" ^ \"\"" "" "";
  t "concat_first" "\"a\" ^ \"\"" "" "a";
  t "concat_second" "\"\" ^ \"b\"" "" "b";
  t "concat_both" "\"a\" ^ \"b\"" "" "ab";
  t "concat_complex" "\"abc\" ^ \"def\" ^ \"ghijkl\"" "" "abcdefghijkl";
  tgc "concat_gc" (builtins_size + 12) "let a = (lambda: \"123456\") in (print(a()); \"abc\" ^ \"def\")" "" "123456abcdef";
]

let tsubstr = [
  terr "substr_of_nonstring" "5[1:3]" "" "Value not a string, got 5";
  terr "substr_of_backwards" "\"hi\"[1:0]" "" "substring index out of bounds of string \"hi\"";
  terr "substr_oob_lower_low" "\"hi\"[-1:1]" "" "substring index out of bounds of string \"hi\"";
  terr "substr_oob_lower_high" "\"hi\"[3:3]" "" "substring index out of bounds of string \"hi\"";
  terr "substr_oob_higher_high" "\"hi\"[0:3]" "" "substring index out of bounds of string \"hi\"";
  t "substr_same" "\"hi\"[0:2]" "" "hi";
  t "substr_first" "\"hi\"[0:1]" "" "h";
  t "substr_middle" "\"hello friends\"[1:5]" "" "ello";
  t "substr_empty" "\"hello friends\"[1:1]" "" "";
  t "substr_exprs" "\"hello friends\"[1 - 1:1 + 2]" "" "hel";
  t "substr_let" "let a = \"hello friends\" in a[1 - 1: 1 + 2]" "" "hel";
  te "substr_tuple_access" "\"hello\"[3]" "get expected tuple";
  te "tuple_substr_access" "(1, 2, 3)[0:1]" "Value not a string"
]

let format = [
  t "format_empty" "format()" "" "";
  t "format_no_subst" "format(\"hello world\")" "" "hello world";
  t "format_one_subst" "format(\"my name is {}\", \"conner nilsen\")" "" "my name is conner nilsen";
  t "format_two_subst" "format(\"my name is {} {}\", \"kyle\", \"into\")" "" "my name is kyle into";
  t "format_other_types" "format(\"{} {} {} {}\", true, false, 5, -3)" "" "true false 5 -3";
  te "format_error_low" "format(\"{}\")" "conversion function received invalid value";
  te "format_error_low_2" "format(\"{}{}\", 5)" "conversion function received invalid value";
  te "format_error_high" "format(\"abcd\", 1)" "conversion function received invalid value";
]

(* testing todos: ensure register allocation still works *)

let suite =
  "unit_tests">:::
  lexing_and_parsing
  @ tstring
  @ tis
  @ tstring_wf
  @ tstring_complex
  @ tstring_gc
  @ tconcat
  @ tsubstr
  @ format

let () =
  run_test_tt_main ("all_tests">:::[
      suite; 
      (* old_tests; *)
      input_file_test_suite ()])
;;
