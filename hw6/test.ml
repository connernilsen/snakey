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

let teq name actual expected = (check_name name)>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tdesugar (name : string) (program : string) (expected : string) = (check_name name)>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_program (desugar (tag (parse_string name program)))) ~printer:(fun s->s);;

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
 (* pair_tests @ 
 input @ *)
 desugar_tests



let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;

