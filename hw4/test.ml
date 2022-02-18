open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs


(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) = name>::test_run program name expected;;

(* Runs a program, given as an ANFed expr, and compares its output to expected *)
let ta (name : string) (program : tag expr) (expected : string) = name>::test_run_anf program name expected;;

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) = name>::test_err program name expected_err;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf (name : string) (program : 'a expr) (expected : unit expr) = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_expr;;

(* Checks if two strings are equal *)
let teq (name : string) (actual : string) (expected : string) = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename>::test_run_input filename expected;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename>::test_err_input filename expected;;

let forty = "let x = 40 in x"
let fals = "let x = false in x"
let tru = "let x = true in x"

let suite =
"unit_tests">:::
 [
  t "forty" forty "40";
  t "fals" fals "false";
  t "tru" tru "true";
  t "add1" "add1(0)" "1";
  t "add1_let" "let x = add1(0) in x" "1";
  t "true" "true" "true";
  t "false" "false" "false";
  t "not_true" "!(true)" "false";
  t "not_false" "!(false)" "true";
  t "print" "print(40)" "40\n40";
  t "print2" "let _ = print(40) in 40" "40\n40";
  t "print3" "let x = print(40) in x" "40\n40";
  t "print4" "let x = print(40) in print(x)" "40\n40\n40";
  t "isbool" "isbool(40)" "false";
  t "isboolT" "isbool(true)" "true";
  t "isnumT" "isnum(40)" "true";
  t "isnum" "isnum(false)" "false";
  t "isnum_highest" "isnum(4611686018427387903)" "true";
  t "isnum_lowest" "isnum(-4611686018427387904)" "true";
  t "plus1" "1 + 1" "2";
  t "plus2" "-1 + 5" "4";
  t "plus3" "1 + -5" "-4";
  t "plus4" "-1 + -5" "-6";
  t "minus1" "1 - 1" "0";
  t "minus2" "-1 - 5" "-6";
  t "minus3" "1 - -5" "6";
  t "minus4" "-1 - -5" "4";
  t "times1" "2 * 5" "10";
  t "times2" "2 * -5" "-10";
  t "times3" "-2 * 5" "-10";
  t "times4" "-2 * -5" "10";
  t "and0" "false && false" "false";
  t "and1" "true && false" "false";
  t "and2" "false && true" "false";
  t "and3" "true && true" "true";
  t "or0" "false || false" "false";
  t "or1" "true || false" "true";
  t "or2" "false || true" "true";
  t "or3" "true || true" "true";
  t "andSS" "false && 1" "false";
  t "orSS" "true || 1" "true";
  te "andE1" "1 && true" "Error 3: logic expected a boolean, got num(1)";
  te "andE2" "true && 1" "Error 3: logic expected a boolean, got num(1)";
  te "orE1" "1 || true" "Error 3: logic expected a boolean, got num(1)";
  te "orE2" "false || 1" "Error 3: logic expected a boolean, got num(1)";
  t "notIsbool" "!(isbool(40))" "true";
  t "notIsboolT" "!(isbool(true))" "false";
  t "notIsnumT" "!(isnum(40))" "false";
  t "notIsnum" "!(isnum(false))" "true";
  te "bool_instead_of_num" "add1(true)" "Error 2: arithmetic expected a number, got bool(true)";
  te "bool_instead_of_num_in_if" "add1(if true: false else: 5)" "Error 2: arithmetic expected a number, got bool(false)";
  te "bool_instead_of_num2" "sub1(false)" "Error 2: arithmetic expected a number, got bool(false)";
  te "num_instead_of_bool" "!(1)" "Error 3: logic expected a boolean, got num(1)";
  te "num_instead_of_bool_in_if" "!(if false: false else: 5)" "Error 3: logic expected a boolean, got num(5)";
  te "bool_instead_of_num3" "1 < true" "Error 1: comparison expected a number, got bool(true)";
  te "num_instead_of_bool2" "if (1): 1 else: 0" "Error 4: if expected a boolean, got num(1)";
  t "if_short_circuits1" "add1(if true: 1 else: add1(false))" "2";
  t "if_short_circuits2" "add1(if false: add1(false) else: 1)" "2";
  t "greater1" "1 > 1" "false";
  t "greater2" "2 > 1" "true";
  t "greater3" "1 > 2" "false";
  t "greaterEqual1" "1 >= 1" "true";
  t "greaterEqual2" "2 >= 1" "true";
  t "greaterEqual3" "1 >= 2" "false";
  t "less1" "1 < 1" "false";
  t "less2" "2 < 1" "false";
  t "less3" "1 < 2" "true";
  t "lessEqual1" "1 <= 1" "true";
  t "lessEqual2" "2 <= 1" "false";
  t "lessEqual3" "1 <= 2" "true";
  t "equal1" "1 == 1" "true";
  t "equal2" "2 == 1" "false";
  t "equal3" "2 == 1" "false";
  t "equal4" "true == true" "true";
  t "equal5" "false == false" "true";
  t "equal6" "false == true" "false";
  t "equal7" "true == false" "false";
  t "equal8" "8 == true" "false";
  t "equal9" "false == 100" "false";
  te "greaterE1" "1 > true" "Error 1: comparison expected a number, got bool(true)";
  te "greaterE2" "false > 1" "Error 1: comparison expected a number, got bool(false)";
  te "greaterEqE1" "1 >= false" "Error 1: comparison expected a number, got bool(false)";
  te "greaterEqE2" "true >= 1" "Error 1: comparison expected a number, got bool(true)";
  te "lessE1" "1 < true" "Error 1: comparison expected a number, got bool(true)";
  te "lessE2" "false < 1" "Error 1: comparison expected a number, got bool(false)";
  te "lessEqE1" "1 <= false" "Error 1: comparison expected a number, got bool(false)";
  te "lessEqE2" "true <= 1" "Error 1: comparison expected a number, got bool(true)";
  te "lessEqE2_in_if" "1 <= (if true: false else: 5)" "Error 1: comparison expected a number, got bool(false)";

  t "let_typing"
    "let x = isnum(5 * add1(7)), y = (if x: isnum(x) else: 10) in if (x && y): 27 else: !(x && y)" 
    "true";
  t "let_typing_not"
    "!(let x = isnum(5 * add1(7)), y = (if x: isnum(x) else: 10) in if (x && y): 27 else: !(x && y))" 
    "false";

  t "bangbang1" "!(!(true))" "true";
  t "bangbang2" "!(!(false))" "false";

  te "overflow_2^62_base"
    "4611686018427387904" "Failure(\"Compile error: Integer overflow: 4611686018427387904\")";
  te "overflow_-2^62_base"
    "-4611686018427387905" "Failure(\"Compile error: Integer overflow: -4611686018427387905\")";

  te "overflow_2^62_plus"
    "4611686018427387903 + 1" "Error 5: overflow occurred for arithmetic operation, got num(-4611686018427387904)";

  te "overflow_2^62_add1"
    "add1(4611686018427387903)" "Error 5: overflow occurred for arithmetic operation, got num(-4611686018427387904)";

  te "overflow_-2^62"
    "-4611686018427387904 - 1" "Error 5: overflow occurred for arithmetic operation, got num(4611686018427387903)";

  te "overflow_-2^62_sub1"
    "sub1(-4611686018427387904)" "Error 5: overflow occurred for arithmetic operation, got num(4611686018427387903)";

  te "overflow_2^61_times"
    "4611686018427387903 * 4" "Error 5: overflow occurred for arithmetic operation, got num(-4)";

  te "overflow_2^61_times_neg"
    "4611686018427387903 * -4" "Error 5: overflow occurred for arithmetic operation, got num(4)";

  tprog "do_pass/test1.cobra" "6"; 
  teprog "do_err/test1.cobra" "Error 2: arithmetic expected a number, got bool(false)";

  t "forty_one" "41" "41";
  t "basic_let" "let a = 1 in a" "1";

  t "if1" "if true: 4 else: 2" "4";
  t "if2" "if false: 4 else: 2" "2";

  t "multi_let" "let a = 1, b = a in b" "1";

  t "let_in_let_in_if_it_1"
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in ((y + x) == 0)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 0, y = sub1(if isbool(x): x else: 1) in y)")
    "11";

  t "let_in_let_in_if_it_2"
    ("if (let x = 4, y = (let x = sub1(x), y = (add1(x) - 10) in y) in ((y + x) >= 0)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 0, y = sub1(if (x == 1): x else: 1) in y)")
    "0";

  t "let_in_let_in_if_it_3"
    ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in ((y + x) < -5)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 1, y = sub1(if isnum(x): x else: 2) in y)")
    "0";

  t "let_in_let_in_if_it_4"
    ("if (let x = 4, y = (let x = sub1(x), y = (add1(x) - 10) in y) in ((y + x) < -5)): " ^
      "(let abcd = 10 in add1(abcd)) " ^
      "else: (let x = 0, y = sub1(if (x == 0): x else: 1) in y)")
    "-1";

  t "negative"
    "-1" "-1";

  t "if_basic"
    "if (0 == 0): 0 else: 1" "0";

  t "complex_conditional_it_ft" 
    ("(let x = (if ((5 - 10) > -4): sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if true: x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "31";

  t "complex_conditional_it_tt" 
    ("(let x = (if true: sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if true: x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "25";

  t "complex_conditional_it_tf" 
    ("(let x = (if true: sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if false: x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "22";

  t "complex_conditional_it_ff" 
    ("(let x = (if false: sub1(5 + 5) else: sub1(6 * 2)) in " ^
      "(let y = sub1(if isbool(x * 1): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))")
    "26";

  t "wrapped_let_and_if"
    ("((let x = 10, z = (let x = (x + 1), y = (x * 2) in x - y), " ^
      "y = (if isnum(z): 1 else: z) in (if (sub1(sub1(y)) == sub1(y)): z else: (z - y))) - " ^
      "(if (let abcd = true in abcd): 11 else: -11))") "-23";
]


(* input_file_test_suite () will run all the tests in the subdirectories of input/ *)
let () =
  run_test_tt_main ("all_tests">:::[
    suite; 
    input_file_test_suite ()
  ])
;;
