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

let te ?input:(input="") name program expected_err = name>::test_err ~std_input:input ~vg:false Naive program name expected_err;;
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
  t "tstring_simple" "\"aa\"" "" "aa";
  t "tstring_complex" "\"\"\"aaaa
  aaaa\"\"\"" "" "aaaa\n  aaaa";
  t "tstring_quotes" "\"aaaa\\\"\"" ""
    "aaaa\"";
  t "tstring_encoded_newline" "\"aaaa\\naaaa\"" ""
    "aaaa\naaaa";
  t "tstring_carriage_return" "\"aaaa\raaaa\"" ""
    "aaaa\raaaa";
  t "tstring_encoded_carriage_return" "\"aaaa\\raaaa\"" ""
    "aaaa\raaaa";
  t "tstring_tag" "\"aaaa\taaaa\"" ""
    "aaaa\taaaa";
  t "tstring_question" "\"aaaa?\"" ""
    "aaaa?";
  t "input_test" "input()" "hello" "hello";
  t "herestring" "let multiline = \"\"\"
\\t\"   \"
  this is a string
abcd
      \"\"\" in multiline" ""
    "\n\t\"   \"\n  this is a string\nabcd\n      ";
  te "herestring_in_string" "\" hello \"\"\" \"" "Herestring terminated in non-herestring literal";
  t "escaped_herestring_in_string" "\" hello \\\"\\\"\\\" \"" "" " hello \"\"\" ";
  te "broken_string" "\" \n \"" "Unterminated string literal";
  te "unterminated_string" "\"" "Unterminated string";
  te "unterminated_herestring" "\"\"\"" "Unterminated string";
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
   in t "very_long" ("\"\"\"" ^ long ^ "\"\"\"") "" long);
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
let conversions_and_istype = [
  t "isstr_str" "isstr(\"hello\")" "" "true";
  t "isstr_num" "isstr(5)" "" "false";
  t "isstr_bool_t" "isstr(true)" "" "false";
  t "isstr_bool_f" "isstr(false)" "" "false";
  t "isstr_tuple" "isstr((1, 2, 3))" "" "false";
  t "isnum_str" "isnum(\"1\")" "" "false";
  t "isbool_str" "isnum(\"true\")" "" "false";
  t "istuple_str" "istuple(\"1\")" "" "false";
  t "istuple_nil" "istuple(nil)" "" "true";
  t "isstr_nil" "isstr(nil)" "" "false";
  t "isnum_nil" "isnum(nil)" "" "false";
  t "isbool_nil" "isbool(nil)" "" "false";
  t "tonum_int" "tonum(1) + 0" "" "1";
  t "tonum_str" "tonum(\"1\") + 0" "" "1";
  t "tonum_bool_f" "tonum(false) + 0" "" "0";
  t "tonum_bool_t" "tonum(true) + 0" "" "1";
  te "tonum_nil" "tonum(nil)" "conversion function received invalid value";
  te "tonum_invalid_str" "tonum(\"a\")" "Error 18: Error: conversion function received invalid value";
  t "tonum_empty_str" "tonum(\"\") + 0" "" "0";
  t "tobool_bool_f" "tobool(false) && false" "" "false";
  t "tobool_nil" "tobool(nil)" "" "false";
  t "tobool_bool_t" "tobool(true) || false" "" "true";
  t "tobool_num_0" "tobool(0) || false" "" "false";
  t "tobool_num_1" "tobool(1) || false" "" "true";
  t "tobool_num_5" "tobool(5) || false" "" "true";
  t "tobool_str_t" "tobool(\"true\") || false" "" "true";
  t "tobool_str_f" "tobool(\"false\") || false" "" "false";
  t "tobool_other_str" "tobool(\"a\")" "" "true";
  t "tobool_empty_str" "tobool(\"\")" "" "false";
  t "tobool_tuple_empty" "tobool(nil)" "" "false";
  t "tobool_tuple_not_empty" "tobool((1,))" "" "true";
  t "tostr_str" "tostr(\"hello\")" "" "hello";
  t "tostr_nil" "tostr(nil)" "" "nil";
  t "tostr_bool_f" "tostr(false)" "" "false";
  t "tostr_bool_t" "tostr(true)" "" "true";
  t "tostr_num" "tostr(5)" "" "5";
  te "tostr_bool_f_err" "tostr(false) || false" "Error 3: Error: expected a boolean, got \"false\"";
  te "tostr_bool_t_err" "tostr(true) || false" "Error 3: Error: expected a boolean, got \"true\"";
  te "tostr_num_err" "tostr(5) + 0" "Error 2: Error: arithmetic expected a number, got \"5\"";
  t "tostr_tuple" "tostr((1, 2, 3))" "" "<tuple>";
  t "tonum_str_neg" "tonum(\"-5\") * 1" "" "-5";
  te "tonum_tuple" "tonum((1, 2))" "conversion function received invalid value";
  t "tonum_str_neg_only" "tonum(\"-\")" "" "0";
  t "tostr_neg" "tostr(-5)" "" "-5";
  te "tostr_neg_err" "tostr(-5) * 1" "Error 2: Error: arithmetic expected a number, got \"-5\"";
  t "totuple_num_1" "tuple(1)" "" "(0, )";
  t "len_nil" "len(nil)" "" "0";
  t "len_one" "len(tuple(1))" "" "1";
  t "totuple_num_5" "tuple(5)" "" "(0, 0, 0, 0, 0)";
  t "len_totuple_5" "len(tuple(5))" "" "5";
  te "totuple_bool" "tuple(false)" "Tuple creation expected num";
  te "totuple_str_empty" "tuple(\"\")" "Tuple creation expected num";
  te "ascii_tuple_to_str_invalid_tuple" "ascii_tuple_to_str((128, ))" "Given char ascii value is invalid";
  te "ascii_tuple_to_str_invalid_tuple_neg" "ascii_tuple_to_str((-1, ))" "Given char ascii value is invalid";
  te "ascii_tuple_to_str_invalid_tuple_bool" "ascii_tuple_to_str((97, false))" "Given char ascii value is invalid";
  te "ascii_tuple_to_str_invalid_tuple_nested_str" "ascii_tuple_to_str((97, \"hello\"))" "Given char ascii value is invalid";
  te "ascii_tuple_to_str_invalid_tuple_nested_tuple" "ascii_tuple_to_str((97, (1, 2, 3)))" "Given char ascii value is invalid";
  t "input_invalid_char" "input()" "é" "C)";
  t "streqeqf" "\"asdf\" == \"asdf\"" "" "false";
  t "streqeqt" "let a = \"asdf\" in a == a" "" "true";
  t "streqeqt_2" "let a = \"asdf\" in 5 == a" "" "false";
  t "streq_1" "equal(\"asdf\", \"asdf\")" "" "true";
  t "streq_2" "equal(\"asdf\", \"asdh\")" "" "false";
  t "streq_3" "equal(5, \"a\")" "" "false";
  t "streq_4" "equal(\"a\", 5)" "" "false";
  t "streq_5" "equal(\"false\", false)" "" "false";
  t "streq_6" "equal(true, \"true\")" "" "false";
  t "streq_7" "equal((0, 1), \"a\")" "" "false";
  t "streq_8" "equal(\"a\", (0, 1))" "" "false";
  t "streq_9" "equal(\"a\", \"b\")" "" "false";
  t "string_edit" "let str = print(\"hello!\"), tup = print(str_to_ascii_tuple(str)), _ = tup[0] := 97, res = ascii_tuple_to_str(print(tup)) in res" "" 
    "hello!(104, 101, 108, 108, 111, 33)(97, 101, 108, 108, 111, 33)aello!";
  t "many_conversions" "ascii_tuple_to_str(str_to_ascii_tuple(tostr(tobool(tonum(len(str_to_ascii_tuple(\"hello\" ^ \"world\")))))))" "" "true";
  t "get_char" "get_ascii_char(\"a\", 0)" "" "97";
  te "get_char_high" "get_ascii_char(\"a\", 1)" "index too large to get";
  te "get_char_low" "get_ascii_char(\"a\", -1)" "index too small to get";
  t "get_char_long" "get_ascii_char(\"abcd\", 3)" "" "100";
  te "get_char_not_str" "get_ascii_char(false, 3)" "Value not a string";
  te "get_char_not_num" "get_ascii_char(\"false\", \"a\")" "substring expected num";
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
  t "concat_let" "let a = \"abc\", b = \"def\", c = \"ghijkl\" in a ^ b ^ c" "" "abcdefghijkl";
  t "concat_let_2" "let a = \"abc\", b = \"def\", c = \"ghijkl\" in let d = a ^ b ^ c in d ^ a" "" "abcdefghijklabc";
  t "concat_equality" "let a = \"abc\" in equal(a ^ a, a ^ a)" "" "true";
  t "concat_equality_2" "let a = \"abc\", b = \"abc\" in equal(a ^ b, b ^ a)" "" "true";
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
  t "substr_equality" "let a = \"hello friends\" in equal(a[0:2], a[0:2])" "" "true";
  t "substr_eqeq" "let a = \"hello friends\" in a[0: 2] == a[0: 2]" "" "false";
  te "substr_tuple_access" "\"hello\"[3]" "get expected tuple";
  te "tuple_substr_access" "(1, 2, 3)[0:1]" "Value not a string"
]

let format = [
  t "format_empty" "format()" "" "";
  t "format_no_subst" "format(\"hello world\")" "" "hello world";
  t "format_one_subst" "format(\"my name is {}\", \"conner nilsen\")" "" "my name is conner nilsen";
  t "format_two_subst" "format(\"my name is {} {}\", \"kyle\", \"into\")" "" "my name is kyle into";
  t "format_other_types" "format(\"{} {} {} {}\", true, false, 5, -3)" "" "true false 5 -3";
  te "format_error_low" "format(\"{}\")" "incorrect arity for format replacement values";
  te "format_error_low_2" "format(\"{}{}\", 5)" "incorrect arity for format replacement values";
  te "format_error_high" "format(\"abcd\", 1)" "incorrect arity for format replacement values";
]

let len = [
  t "str_len_empty" "len(\"\")" "" "0";
  t "tuple_len_1" "len((5, ))" "" "1";
  t "str_len_1" "len(\"a\")" "" "1";
  t "tuple_len_2" "len((5, 4))" "" "2";
  t "str_len_2" "len(\"ab\")" "" "2";
  te "len_bool" "len(true)" "len expected tuple or num, got true";
  te "len_num" "len(5)" "len expected tuple or num, got 5";
]

let split_tests = [
  t "split_empty_empty"  "\"\".split(\"\")" "" "()";
  t "split_empty_not_there"  "\"\".split(\"f\")" "" "()";
  t "split_miss"  "\"hi\".split(\"f\")" "" "(hi, )";
  t "split_empty"  "\"hi\".split(\"\")" "" "(hi, )";
  t "split_space"  "\"hi friends i'm kyle\".split(\" \")" "" "(hi, friends, i'm, kyle)";
  t "split_multiple"  "\"hi friends.i'mzkyle\".split(\" .z\")" "" "(hi, friends, i'm, kyle)";
  t "split_lets"  "let s1 = \"hi friends.i'mzkyle\", s2 = \" .z\" in s1.split(s2)" "" "(hi, friends, i'm, kyle)";
  t "split_empty_char"  "\"no\".split(\"n\")" "" "(o, )";
  terr "split_nonstring" "5.split(\" .z\")" "" "unable to split non-string 5";
  terr "split_nonstring_2" "\"\".split(5)" "" "unable to split non-string 5";
]
let join_tests = [
  t "join_empty_empty"  "\"\".join(())" "" "";
  t "join_delim_empty"  "\"f\".join(())" "" "";
  t "join_empty_delim"  "\"\".join((\"hello\", \"hi\"))" "" "hellohi";
  t "join_single"  "\" \".join((\"hello\", ))" "" "hello";
  t "join_space"  "\" \".join((\"hello\", \"hi\"))" "" "hello hi";
  t "join_long"  "\" \".join((\"hello\", \"hi\",\"hello\", \"hi\",\"hello\", \"hi\",\"hello\", \"hi\"))" "" "hello hi hello hi hello hi hello hi";
  t "join_newline"  "\"\\n\".join((\"hello\", \"hi\"))" "" "hello\nhi";
  t "join_lets"  "let delim = \" \", t = (\"hello\", \"hi\") in delim.join(t)" "" "hello hi";
  terr "join_nonstring"  "5.join((\"hello\", \"hi\"))" "" "unable to join non-string 5";
  terr "join_nonstring_2"  "5.join((5, ))" "" "unable to join non-string 5";
  terr "join_nontuple"  "\"\".join(5)" "" "unable to join non-tuple 5";
]

let integration_tests = [
  terr "plus_string"  "\"hello\" + 6" "" "arithmetic expected a number";
  terr "plus_strings"  "\"hello\" + \"hi\"" "" "arithmetic expected a number";
  terr "g_strings"  "\"hello\" > \"hi\"" "" "comparison expected a number";
  terr "le_strings"  "\"hello\" <= \"hi\"" "" "comparison expected a number";
  terr "ge_strings"  "\"hello\" >= \"hi\"" "" "comparison expected a number";
  terr "l_strings"  "\"hello\" < \"hi\"" "" "comparison expected a number";
  terr "minus_strings"  "\"hello\" - \"hi\"" "" "arithmetic expected a number";
  terr "times_strings"  "\"hello\" * \"hi\"" "" "arithmetic expected a number";
  terr "add1_strings" "add1(\"hello\")" "" "arithmetic expected a number";
  terr "sub1_strings" "sub1(\"hello\")" "" "arithmetic expected a number";
]
(* testing todos: ensure register allocation still works *)

let suite =
  "unit_tests">:::
  lexing_and_parsing
  @ tstring
  @ conversions_and_istype
  @ tstring_wf
  @ tstring_complex
  @ tstring_gc
  @ tconcat
  @ tsubstr
  @ format
  @ len
  @ split_tests
  @ join_tests
  @ integration_tests

let () =
  run_test_tt_main ("all_tests">:::[
      suite; 
      (* old_tests; *)
      input_file_test_suite ()])
;;
