open Assembly
open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Errors
open Phases

let t name program expected = name>::test_run program name expected;;

let ta name program_and_env expected = name>::test_run_anf program_and_env name expected;;

let te name program expected_err = name>::test_err ~vg:false program name expected_err;;

(* let t name program expected = name>::test_run_valgrind program name expected;; *)
  
let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag (desugar (tag program)))) ~printer:string_of_aprogram;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf_improved (name : string) (program : string) (expected : string) = name>:: fun _ ->
    assert_equal (expected) (string_of_aprogram (anf (tag (desugar (rename_and_tag (tag (parse_string name program))))))) ~printer:(fun s->s);
    (* check_scope_helper (fun _-> "ignored") (parse_string name program) []; *)
;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename>::test_run_input filename expected;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename>::test_err_input filename expected;;

let tdesugar (name : string) (program : string) (expected : string) = name>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_program (desugar (tag (parse_string name program)))) ~printer:(fun s->s);;

let tvg name program expected = name>::test_run_valgrind program name expected;;

let forty = "let x = 40 in x"
let fals = "let x = false in x"
let tru = "let x = true in x"

let create_ss (file : string) (start_l : int) (start_c : int) (end_l : int) (end_c : int) : sourcespan =
  ({pos_fname=file; pos_lnum=start_l; pos_bol=0; pos_cnum=start_c},
   {pos_fname=file; pos_lnum=end_l; pos_bol=0; pos_cnum=end_c})
;;

let print_te (exns : exn list) : string =
  String.concat "\n" (print_errors exns)
;;

let arg_envt_printer args =
  ("[" ^
   (String.concat "; " 
      (List.map (fun (name, v) -> "(" ^ name ^ ", " ^ (arg_to_asm v) ^ ")")
         args)) ^
   "]")
;;

let old_tests =
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
  te "andE1" "1 && true" "Error 3: expected a boolean, got num(1)";
  te "andE2" "true && 1" "Error 3: expected a boolean, got num(1)";
  te "orE1" "1 || true" "Error 3: expected a boolean, got num(1)";
  te "orE2" "false || 1" "Error 3: expected a boolean, got num(1)";
  t "notIsbool" "!(isbool(40))" "true";
  t "notIsboolT" "!(isbool(true))" "false";
  t "notIsnumT" "!(isnum(40))" "false";
  t "notIsnum" "!(isnum(false))" "true";
  te "bool_instead_of_num" "add1(true)" "Error 2: arithmetic expected a number, got bool(true)";
  te "bool_instead_of_num_in_if" "add1(if true: false else: 5)" "Error 2: arithmetic expected a number, got bool(false)";
  te "bool_instead_of_num2" "sub1(false)" "Error 2: arithmetic expected a number, got bool(false)";
  te "num_instead_of_bool" "!(1)" "Error 3: expected a boolean, got num(1)";
  te "num_instead_of_bool_in_if" "!(if false: false else: 5)" "Error 3: expected a boolean, got num(5)";
  te "bool_instead_of_num3" "1 < true" "Error 1: comparison expected a number, got bool(true)";
  te "num_instead_of_bool2" "if (1): 1 else: 0" "Error 3: expected a boolean, got num(1)";
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
  t "conditional_in_let" "let x = 1 == 1 in x == true" "true";
  te "greaterE1" "1 > true" "Error 1: comparison expected a number, got bool(true)";
  te "greaterE2" "false > 1" "Error 1: comparison expected a number, got bool(false)";
  te "greaterEqE1" "1 >= false" "Error 1: comparison expected a number, got bool(false)";
  te "greaterEqE2" "true >= 1" "Error 1: comparison expected a number, got bool(true)";
  te "lessE1" "1 < true" "Error 1: comparison expected a number, got bool(true)";
  te "lessE2" "false < 1" "Error 1: comparison expected a number, got bool(false)";
  te "lessEqE1" "1 <= false" "Error 1: comparison expected a number, got bool(false)";
  te "lessEqE2" "true <= 1" "Error 1: comparison expected a number, got bool(true)";
  te "lessEqE2_in_if" "1 <= (if true: false else: 5)" "Error 1: comparison expected a number, got bool(false)";
  te "lessEqE2_in_if_in_let" "let x = 1 <= (if true: false else: 5) in x" "Error 1: comparison expected a number, got bool(false)";

  t "let_typing"
    "let x = isnum(5 * add1(7)), y = (if x: isnum(x) else: 10) in if (x && y): 27 else: !(x && y)" 
    "true";
  t "let_typing_not"
    "!(let x = isnum(5 * add1(7)), y = (if x: isnum(x) else: 10) in if (x && y): 27 else: !(x && y))" 
    "false";

  t "bangbang1" "!(!(true))" "true";
  t "bangbang2" "!(!(false))" "false";

  te "overflow_2^62_base"
    "4611686018427387904" 
    "The number literal 4611686018427387904, used at <overflow_2^62_base, 1:0-1:19>, is not supported in this language";
  te "overflow_-2^62_base"
    "-4611686018427387905" 
    "The number literal -4611686018427387905, used at <overflow_-2^62_base, 1:0-1:20>, is not supported in this language";
  te "overflow_2^62_plus_positive"
    "4611686018427387903 + 1" "Error 4: overflow occurred for arithmetic operation, got num(-4611686018427387904)";
  te "overflow_2^62_plus_negative"
    "-4611686018427387904 + -1" "Error 4: overflow occurred for arithmetic operation, got num(4611686018427387903)";
  te "overflow_2^62_add1"
    "add1(4611686018427387903)" "Error 4: overflow occurred for arithmetic operation, got num(-4611686018427387904)";
  te "overflow_-2^62_minus_positive"
    "4611686018427387903 - -1" "Error 4: overflow occurred for arithmetic operation, got num(-4611686018427387904)";
  te "overflow_-2^62_minus_negative"
    "-4611686018427387904 - 1" "Error 4: overflow occurred for arithmetic operation, got num(4611686018427387903)";
  te "overflow_-2^62_sub1"
    "sub1(-4611686018427387904)" "Error 4: overflow occurred for arithmetic operation, got num(4611686018427387903)";
  te "overflow_2^61_times_positive_1"
    "4611686018427387903 * 4" "Error 4: overflow occurred for arithmetic operation, got num(-4)";
  te "overflow_2^61_times_positive_2"
    "-4611686018427387903 * -4" "Error 4: overflow occurred for arithmetic operation, got num(-4)";
  te "overflow_2^61_times_negative_1"
    "4611686018427387903 * -4" "Error 4: overflow occurred for arithmetic operation, got num(4)";
  te "overflow_2^61_times_negative_2"
    "-4611686018427387903 * 4" "Error 4: overflow occurred for arithmetic operation, got num(4)";

  t "add_large_numbers_1"
    "4611686018427387903 + -4511686018427387903" "100000000000000000";
  t "add_large_numbers_2"
    "-4511686018427387903 + 4611686018427387903" "100000000000000000";
  t "sub_large_numbers_1"
    "4611686018427387903 - 4511686018427387903" "100000000000000000";
  t "sub_large_numbers_2"
    "4511686018427387903 - 4611686018427387903" "-100000000000000000";
  t "mult_large_numbers_1"
    "4294967296 * 1073741823" "4611686014132420608";
  t "mult_large_numbers_2"
    "1073741823 * 4294967296" "4611686014132420608";
  t "mult_large_numbers_3"
    "-4294967296 * 1073741823" "-4611686014132420608";
  t "mult_large_numbers_4"
    "1073741823 * -4294967296" "-4611686014132420608";
  t "add1_large_number" "add1(4611686018427387902)" "4611686018427387903";
  t "sub1_large_number" "sub1(-4611686018427387902)" "-4611686018427387903";
  t "greater1_large_numbers" "4611686018427387903 > 4611686018427387903" "false";
  t "greater2_large_numbers" "4611686018427387903 > 4511686018427387903" "true";
  t "greater3_large_numbers" "4511686018427387903 > 4611686018427387903" "false";
  t "greaterEqual1_large_numbers" "4611686018427387903 >= 4611686018427387903" "true";
  t "greaterEqual2_large_numbers" "4611686018427387903 >= 4511686018427387903" "true";
  t "greaterEqual3_large_numbers" "4511686018427387903 >= 4611686018427387903" "false";
  t "less1_large_numbers" "4611686018427387903 < 4611686018427387903" "false";
  t "less2_large_numbers" "4611686018427387903 < 4511686018427387903" "false";
  t "less3_large_numbers" "4511686018427387903 < 4611686018427387903" "true";
  t "lessEqual1_large_numbers" "4611686018427387903 <= 4611686018427387903" "true";
  t "lessEqual2_large_numbers" "4611686018427387903 <= 4511686018427387903" "false";
  t "lessEqual3_large_numbers" "4511686018427387903 <= 4611686018427387903" "true";
  t "equal1_large_numbers" "4611686018427387903 == 4611686018427387903" "true";
  t "equal2_large_numbers" "4611686018427387903 == 4511686018427387903" "false";
  t "equal3_large_numbers" "4511686018427387903 == 4611686018427387903" "false";
  t "equal4_large_numbers" "4611686018427387903 == true" "false";
  t "equal5_large_numbers" "false == 4611686018427387903" "false";
  t "equal6_large_numbers" "4611686018427387903 == -4611686018427387903" "false";

  t "greater1_negatives" "-1 > -1" "false";
  t "greater2_negatives" "-2 > -1" "false";
  t "greater3_negatives" "-1 > -2" "true";
  t "greaterEqual1_negatives" "-1 >= -1" "true";
  t "greaterEqual2_negatives" "-2 >= -1" "false";
  t "greaterEqual3_negatives" "-1 >= -2" "true";
  t "less1_negatives" "-1 < -1" "false";
  t "less2_negatives" "-2 < -1" "true";
  t "less3_negatives" "-1 < -2" "false";
  t "lessEqual1_negatives" "-1 <= -1" "true";
  t "lessEqual2_negatives" "-2 <= -1" "true";
  t "lessEqual3_negatives" "-1 <= -2" "false";
  t "equal1_negatives" "-1 == -1" "true";
  t "equal2_negatives" "-2 == -1" "false";
  t "equal3_negatives" "-2 == -1" "false";

  t "greater1_neg_pos" "-1 > 1" "false";
  t "greater2_neg_pos" "1 > -1" "true";
  t "greater3_neg_pos" "5 > -1" "true";
  t "greater4_neg_pos" "-5 > 1" "false";
  t "greater5_neg_pos" "1 > -5" "true";
  t "greater6_neg_pos" "-1 > 5" "false";
  t "greaterEqual1_neg_pos" "-1 >= 1" "false";
  t "greaterEqual2_neg_pos" "1 >= -1" "true";
  t "greaterEqual3_neg_pos" "5 >= -1" "true";
  t "greaterEqual4_neg_pos" "-5 >= 1" "false";
  t "greaterEqual5_neg_pos" "1 >= -5" "true";
  t "greaterEqual6_neg_pos" "-1 >= 5" "false";
  t "less1_neg_pos" "-1 < 1" "true";
  t "less2_neg_pos" "1 < -1" "false";
  t "less3_neg_pos" "5 < -1" "false";
  t "less4_neg_pos" "-5 < 1" "true";
  t "less5_neg_pos" "1 < -5" "false";
  t "less6_neg_pos" "-1 < 5" "true";
  t "lessEqual1_neg_pos" "-1 <= 1" "true";
  t "lessEqual2_neg_pos" "1 <= -1" "false";
  t "lessEqual3_neg_pos" "5 <= -1" "false";
  t "lessEqual4_neg_pos" "-5 <= 1" "true";
  t "lessEqual5_neg_pos" "1 <= -5" "false";
  t "lessEqual6_neg_pos" "-1 <= 5" "true";

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

  "setup_call_to_func_1">::(fun _ -> 
    assert_equal [ICall("label")] (setup_call_to_func 0 [] "label") ~printer:to_asm);
  "setup_call_to_func_2">::(fun _ ->
    assert_equal [IMov(Reg(RDI), Const(1L)); ICall("label")]
      (setup_call_to_func 0 [Const(1L)] "label") ~printer:to_asm);
  "setup_call_to_func_3">::(fun _ -> 
    assert_equal [
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      ICall("label")]
      (setup_call_to_func 0
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_4">::(fun _ -> 
    assert_equal [
      IPush(Const(0L));
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      IPush(Const(7L));
      ICall("label");
      IAdd(Reg(RSP), Const(16L))]
      (setup_call_to_func 0
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_5">::(fun _ -> 
    assert_equal [
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      IPush(Const(8L));
      IPush(Const(7L));
      ICall("label");
      IAdd(Reg(RSP), Const(16L))]
      (setup_call_to_func 0
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L); Const(8L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_6">::(fun _ -> 
    assert_equal [
      IPush(Const(0L));
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      IPush(Const(9L));
      IPush(Const(8L));
      IPush(Const(7L));
      ICall("label");
      IAdd(Reg(RSP), Const(32L))]
      (setup_call_to_func 0
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L); Const(8L); Const(9L)] 
         "label") ~printer:to_asm);
  tanf_improved "let_in_prim"
    "add1(let x = 5 in x)"
    "\n(alet x#4 = 5 in add1(x#4))";
  tanf_improved "let_in_prim_with_eval"
    "add1(let x = 5 in add1(x))"
    "\n(alet x#5 = 5 in (alet unary_3 = add1(x#5) in add1(unary_3)))";
  tanf_improved "let_in_prim2_with_eval"
    "add1(let x = 5 in (x + (let x = 2 in x)))"
    "\n(alet x#9 = 5 in (alet x#6 = 2 in (alet binop_3 = (x#9 + x#6) in add1(binop_3))))";
  tanf_improved "let_in_let_in_if" 
  ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
  ("\n(alet x#21 = 5 in " ^
      "(alet x#26 = sub1(x#21) in " ^
        "(alet unary_32 = add1(x#26) in " ^
          "(alet y#29 = (unary_32 - 10) in " ^
            "(alet y#23 = y#29 in " ^
              "(alet binop_18 = (y#23 + x#21) in " ^
                "(if binop_18: (alet abcd#15 = 10 in " ^
                                  "add1(abcd#15)) " ^ 
                "else: (alet x#4 = 0 in " ^
                  "(alet if_8 = (if x#4: x#4 else: 1) in " ^
                    "(alet y#6 = sub1(if_8) in " ^
                      "y#6))))))))))");
  tanf_improved "lets_in_prim"
    "(let x = 1 in x) + (let x = 2 in x)"
    "\n(alet x#8 = 1 in (alet x#4 = 2 in (x#8 + x#4)))";
  tanf_improved "if_in_if_in_let_in_add1"
    "add1(let x = (if (if 0: 0 else: 1): 2 else: 3) in (if x: 4 else: 5))"
    "\n(alet if_11 = (if 0: 0 else: 1) in (alet x#7 = (if if_11: 2 else: 3) in (alet if_3 = (if x#7: 4 else: 5) in add1(if_3))))";
  tanf_improved "simple_conditional"
    "(let x = (if 1: 5 + 5 else: 6 * 2) in (let y = (if 0: x * 3 else: x + 5) in x + y))"
    ("\n(alet x#15 = (if 1: (5 + 5) else: (6 * 2)) in (alet y#6 = (if 0: (x#15 * 3) else: (x#15 + 5)) in (x#15 + y#6)))");
  tanf_improved "complex_conditional"
    ("(let x = (if (5 - 10): add1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))"
    )
    ("\n(alet binop_31 = (5 - 10) in " ^
     "(alet x#21 = (if binop_31: " ^
        "(alet binop_28 = (5 + 5) in " ^ 
          "add1(binop_28)) " ^
        "else: " ^ 
        "(alet binop_24 = (6 * 2) in " ^ 
          "sub1(binop_24))) in " ^ 
            "(alet binop_18 = (x#21 * 0) in " ^ 
              "(alet if_9 = (if binop_18: " ^ 
                "(alet unary_15 = sub1(3) in (x#21 * unary_15)) " ^
              "else: " ^ 
                "(alet unary_12 = add1(x#21) in (unary_12 + 5))) in " ^ 
                  "(alet y#7 = sub1(if_9) in " ^ 
                    "(alet binop_4 = (x#21 + y#7) in sub1(binop_4)))))))");
  tanf_improved "expr_basic"
    ("def f() : 1\n1")
    ("(fun f$2(): 1)\n1");
  tanf_improved "expr_call"
    ("def f() : 1\nf()")
    ("(fun f$2(): 1)\n(f$2())");
  tanf_improved "expr_call_w_imm_args"
    ("def f(a, b) : 1\n(f(1, 2))")
    ("(fun f$4(a#6, b#7): 1)\n(f$4(1, 2))");
  tanf_improved "expr_call_w_compound_args"
    ("def f(a, b) : 1\nf(add1(1), 2)")
    ("(fun f$5(a#7, b#8): 1)\n(alet unary_2 = add1(1) in (f$5(unary_2, 2)))");
  tanf_improved "expr_call_w_multiple_compound_args"
    ("def f(a, b) : 1\nf(add1(1), add1(1))")
    ("(fun f$6(a#8, b#9): 1)\n(alet unary_2 = add1(1) in (alet unary_4 = add1(1) in (f$6(unary_2, unary_4))))");
  tanf_improved "multiple_expr_call_w_multiple_compound_args"
    ("def f(a, b) : 1\ndef g(a, b, c) : a == b\nlet c = f(add1(1), add1(1)), d = g(add1(2), add1(3), 4 + 3) in d")
    ("(fun f$18(a#20, b#21): 1)\n" ^
    "(fun g$22(a#26, b#27, c#28): (a#26 == b#27))\n" ^
    "(alet unary_5 = add1(1) in (alet unary_7 = add1(1) in (alet c#3 = (f$18(unary_5, unary_7)) in (alet unary_11 = add1(2) in (alet unary_13 = add1(3) in (alet binop_15 = (4 + 3) in (alet d#9 = (g$22(unary_11, unary_13, binop_15)) in d#9)))))))");
  tanf_improved "expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\nf(g(1))")
    ("(fun f$4(a#6): a#6)\n(fun g$7(b#10): add1(b#10))\n(alet app_2 = (g$7(1)) in (f$4(app_2)))");
  tanf_improved "expr_within_expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\ndef h(b) : b\nh(f(g(1)))")
    ("(fun f$5(a#7): a#7)\n(fun g$8(b#11): add1(b#11))\n(fun h$12(b#14): b#14)\n(alet app_3 = (g$8(1)) in (alet app_2 = (f$5(app_3)) in (h$12(app_2))))");
  tanf_improved "infinite_loop"
    ("def f(a) : g(a)\ndef g(a) : f(a)\ng(1)")
    ("(fun f$3(a#6): (g$7(a#6)))\n(fun g$7(a#10): (f$3(a#10)))\n(g$7(1))");
  te "basic" "f()" "The function name f, used at <basic, 1:0-1:3>, is not in scope";
  te "dup_fun" 
    "def test(): 1
def test(): 2
test()"
    (print_te 
       [DuplicateFun("test", 
                     (create_ss "dup_fun" 2 0 2 13), 
                     (create_ss "dup_fun" 1 0 1 13))]);
  te "dup_binds_fun"
    "def test(x, x): x
test(1, 2)"
    (print_te 
      [DuplicateId("x",
                   create_ss "dup_binds_fun" 1 12 1 13,
                   create_ss "dup_binds_fun" 1 9 1 10)]);
  te "unbound_id"
    "def test(): x test()"
    (print_te [UnboundId("x", create_ss "unbound_id" 1 12 1 13)]);
  te "dup_binds_let"
    "let x = 5, x = 6 in x"
    (print_te 
      [DuplicateId("x",
                   (create_ss "dup_binds_let" 1 11 1 12),
                   (create_ss "dup_binds_let" 1 4 1 5))]);
  te "unbound_fun"
    "test()"
    (print_te 
       [UnboundFun("test",
                   (create_ss "unbound_fun" 1 0 1 6))]);
  te "function_as_arg"
    "def a(b):
      b
     def b(a):
      a
    b(a)"
    (print_te [
        UnboundId("a", create_ss "function_as_arg" 5 6 5 7);
      ]);
  te "let_call"
    "let a = 1 in a(1)"
    (print_te [
        UnboundFun("a", create_ss "let_call" 1 13 1 17);
      ]);
  te "arity_less"
    "def test(x): x test()"
    (print_te 
       [Arity(1, 0, (create_ss "arity_less" 1 15 1 21))]);
  te "arity_more"
    "def test(x, y): x + y test(1)"
    (print_te 
       [Arity(2, 1, (create_ss "arity_more" 1 22 1 29))]);
  te "arity_and_dup_correct"
    "def test(x): x def test(x, y): x + y test(1)"
    (print_te 
       [DuplicateFun("test", 
                     (create_ss "arity_and_dup_correct" 1 15 1 36), 
                     (create_ss "arity_and_dup_correct" 1 0 1 14))]);
  te "arity_and_dup_incorrect"
    "def test(x, y): x + y def test(x): x test(1)"
    (print_te 
       [DuplicateFun("test", 
                     (create_ss "arity_and_dup_incorrect" 1 22 1 36), 
                     (create_ss "arity_and_dup_incorrect" 1 0 1 21));
        Arity(2, 1, (create_ss "arity_and_dup_incorrect" 1 37 1 44))]);
  te "overflow"
    "4611686018427387904" 
    (print_te [Overflow(4611686018427387904L,
                        (create_ss "overflow" 1 0 1 19))]);
  te "underflow"
    "-4611686018427387905" 
    (print_te [Overflow(-4611686018427387905L,
                        (create_ss "underflow" 1 0 1 20))]);
  t "ocsh_dup"
    "def our_code_starts_here():
      5
    our_code_starts_here()"
    "5";
  te "print_dup"
    "def print():
      5
    print()"
    (print_te [ParseError("Parse error at line 1, col 9: token `print`")]);
  te "func_invalid_bind"
    "def test(1):
      1
    test(2)"
    (print_te [ParseError("Parse error at line 1, col 10: token `1`")]);
  te "nested_errors"
    "def test(abc):
      if add1(a * b):
        a
      else:
        b
    let a = test(1, a) in hello(b)"
    (print_te [
        UnboundId("a", create_ss "nested_errors" 2 14 2 15);
        UnboundId("b", create_ss "nested_errors" 2 18 2 19);
        UnboundId("a", create_ss "nested_errors" 3 8 3 9);
        UnboundId("b", create_ss "nested_errors" 5 8 5 9);
        Arity(1, 2, create_ss "nested_errors" 6 12 6 22);
        UnboundId("a", create_ss "nested_errors" 6 20 6 21);
        UnboundFun("hello", create_ss "nested_errors" 6 26 6 34);
        UnboundId("b", create_ss "nested_errors" 6 32 6 33);
      ]);
  t "call_func"
    "def double_print(val):
      print(print(val))
    double_print(123)"
    "123\n123\n123";
  t "recursion"
    "def print_dec(x):
      if x <= 0:
        print(0)
      else:
        print_dec(sub1(print(x)))
    print_dec(7)"
    "7\n6\n5\n4\n3\n2\n1\n0\n0";
  t "if_print_stmts"
    "if print(true): print(true) else: print(false)"
    "true\ntrue\ntrue";
  t "mutually_recursive"
    "def abs_dec(num):
      if num == 0:
        0
      else:
        if num < 0:
          num + 1
        else:
          num - 1
    def t1(print_neg, num):
      if print_neg:
        t2(print(num * -1))
      else:
        t2(print(num))
    def t2(val):
      let dec_num = abs_dec(val) in
      if dec_num == 0:
        val > 0 
      else:
        let neg = t1(true, dec_num),
            pos = t1(false, dec_num) in 
            neg || pos
    t1(false, 4)"
    "4\n-3\n2\n-1\n1\n-2\n1\n-1\n3\n-2\n1\n-1\n2\n-1\n1\ntrue";
  te "eventual_error"
    "def abs_dec(num):
      if num == 0:
        0
      else:
        if num < 0:
          num + 1
        else:
          num - 1
    def t1(print_neg, num):
      if print_neg:
        t2(print(num * -1))
      else:
        t2(print(num))
    def t2(val):
      let dec_num = abs_dec(val) in
      if dec_num == 0:
        0 
      else:
        let neg = t1(true, dec_num),
            pos = t1(false, dec_num)
          in neg && pos
      t1(false, 4)"
    "expected a boolean, got num(0)";
  t "reuse_reg_args_not_tail_recursive"
    "def f1(b, n):
      let x = print(b),
          y = print(n) in 
        isnum(n) && isbool(b) 
        && isnum(y) && isbool(x)
    def f2(n, b):
      let x = print(f1(b, n)),
          y = print(n),
          z = print(b) in 
        x && isnum(y) && isbool(z)
        && isnum(n) && isbool(b)
    f2(5, false)"
    "false\n5\ntrue\n5\nfalse\ntrue";
  t "mutual_recursion_swap_args_and_counter"
    "def f1(b, n, i):
      if i == 10:
        isbool(b) && isnum(n)
      else:
        let a = print(i) in 
          f2(n, b, i + 1)
    def f2(n, b, i):
        f1(b, n, i)
    f2(5, false, 0)"
    "0\n1\n2\n3\n4\n5\n6\n7\n8\n9\ntrue";
  tvg "valgrind_mutual"
    "def f1(b, n, i):
      if i == 10:
        isbool(b) && isnum(n)
      else:
        let a = print(i) in 
          f2(n, b, i + 1)
    def f2(n, b, i):
        f1(b, n, i)
    f2(5, false, 0)"
    "0\n1\n2\n3\n4\n5\n6\n7\n8\n9\ntrue";
  tvg "valgrind_swap_tail_recursive"
    "def f1(a, b, c, i):
      if (a == 10) && (b == a) && (c == a):
        i
      else:
        if (a > 10) || (b > 10) || (c > 10):
          let x = print(a),
              y = print(b),
              z = print(c) in 
            print(print(i) || 2)
        else:
          f1(b, c, a + 1, i + 1)
    f1(0, 0, 0, 0)"
    "30";
  t "function_def_in_let"
    "def run(val):
      let run = val in print(run)
    let run = 5 in run(run)"
    "5\n5";
  t "function_def_in_let_2"
    "def run(run): print(run)
    let run = 5 in run(run)"
    "5\n5";
  t "short_circuit_def_1"
    "def run(run): print(run)
    false && run(6)"
    "false";
  t "short_circuit_def_2"
    "def run(run): print(run)
    true || run(6)"
    "true";
  t "short_circuit_and"
    "false && print(6)"
    "false";
  t "short_circuit_or"
    "true || print(6)"
    "true";
  t "short_circuit_let_and"
    "let x = print(6) in false && x"
    "6\nfalse";
  t "short_circuit_let_or"
    "let x = print(6) in true || x"
    "6\ntrue";
  t "short_circuit_def_and"
    "def run(run): print(run)
    false && run(6)"
    "false";
  t "short_circuit_def_or"
    "def run(run): print(run)
    true || run(6)"
    "true";
  "get_func_call_params_1">::(fun _ -> 
      assert_equal [] (get_func_call_params []) 
        ~printer:arg_envt_printer);
  "get_func_call_params_2">::(fun _ -> 
      assert_equal [("first", Reg(RDI))] (get_func_call_params ["first"])
        ~printer:arg_envt_printer);
  "get_func_call_params_3">::(fun _ -> 
      assert_equal [
        ("1", Reg(RDI));
        ("2", Reg(RSI));
        ("3", Reg(RDX));
        ("4", Reg(RCX));
        ("5", Reg(R8));
        ("6", Reg(R9));
      ] (get_func_call_params 
           ["1"; "2"; "3"; "4"; "5"; "6"])
        ~printer:arg_envt_printer);
  "get_func_call_params_4">::(fun _ -> 
      assert_equal [
        ("1", Reg(RDI));
        ("2", Reg(RSI));
        ("3", Reg(RDX));
        ("4", Reg(RCX));
        ("5", Reg(R8));
        ("6", Reg(R9));
        ("7", RegOffset(16, RBP));
      ] (get_func_call_params 
           ["1"; "2"; "3"; "4"; "5"; "6"; "7"])
        ~printer:arg_envt_printer);
  "get_func_call_params_5">::(fun _ -> 
      assert_equal [
        ("1", Reg(RDI));
        ("2", Reg(RSI));
        ("3", Reg(RDX));
        ("4", Reg(RCX));
        ("5", Reg(R8));
        ("6", Reg(R9));
        ("7", RegOffset(16, RBP));
        ("8", RegOffset(24, RBP));
        ("9", RegOffset(32, RBP));
      ] (get_func_call_params 
           ["1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"])
        ~printer:arg_envt_printer);
  "setup_call_to_func_save_regs_one_1">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Const(0L));
        IMov(Reg(RDI), Const(1L));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 1 [Const(1L)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_one_2">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Const(0L));
        IMov(Reg(RDI), RegOffset(word_size, RSP));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 1 [Reg(RDI)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_one_3">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Const(0L));
        IMov(Reg(RDI), Const(0L));
        IMov(Reg(RSI), Const(1L));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 1 [Const(0L); Const(1L)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_one_4">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Const(0L));
        IMov(Reg(RDI), Const(0L));
        IMov(Reg(RSI), RegOffset(word_size, RSP));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 1 [Const(0L); Reg(RDI)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_two_1">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IMov(Reg(RDI), Const(1L));
        ICall("label");
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 2 [Const(1L)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_two_2">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IMov(Reg(RDI), RegOffset(word_size, RSP));
        ICall("label");
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 2 [Reg(RDI)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_two_3">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IMov(Reg(RDI), Const(0L));
        IMov(Reg(RSI), Const(1L));
        ICall("label");
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 2 [Const(0L); Const(1L)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_two_4">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IMov(Reg(RDI), RegOffset(0, RSP));
        IMov(Reg(RSI), RegOffset(word_size, RSP));
        ICall("label");
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 2 [Reg(RSI); Reg(RDI)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_three_1">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IPush(Reg(RDX));
        IPush(Const(0L));
        IMov(Reg(RDI), Const(1L));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDX));
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 3 [Const(1L)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_three_2">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IPush(Reg(RDX));
        IPush(Const(0L));
        IMov(Reg(RDI), RegOffset(word_size * 3, RSP));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDX));
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 3 [Reg(RDI)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_three_3">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IPush(Reg(RDX));
        IPush(Const(0L));
        IMov(Reg(RDI), Const(0L));
        IMov(Reg(RSI), Const(1L));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDX));
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 3 [Const(0L); Const(1L)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_three_4">::(fun _ ->
      assert_equal [
        IPush(Reg(RDI));
        IPush(Reg(RSI));
        IPush(Reg(RDX));
        IPush(Const(0L));
        IMov(Reg(RDI), RegOffset(word_size * 2, RSP));
        IMov(Reg(RSI), RegOffset(word_size * 3, RSP));
        ICall("label");
        IAdd(Reg(RSP), Const(Int64.of_int word_size));
        IPop(Reg(RDX));
        IPop(Reg(RSI));
        IPop(Reg(RDI));
      ]
        (setup_call_to_func 3 [Reg(RSI); Reg(RDI)] "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_five_equal">::(fun _ -> 
    assert_equal [
      IPush(Reg(RDI));
      IPush(Reg(RSI));
      IPush(Reg(RDX));
      IPush(Reg(RCX));
      IPush(Reg(R8));
      IPush(Const(0L));
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      ICall("label");
      IAdd(Reg(RSP), Const(8L));
      IPop(Reg(R8));
      IPop(Reg(RCX));
      IPop(Reg(RDX));
      IPop(Reg(RSI));
      IPop(Reg(RDI));
    ]
      (setup_call_to_func 5
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_five_odd">::(fun _ -> 
    assert_equal [
      IPush(Reg(RDI));
      IPush(Reg(RSI));
      IPush(Reg(RDX));
      IPush(Reg(RCX));
      IPush(Reg(R8));
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      IPush(Const(7L));
      ICall("label");
      IAdd(Reg(RSP), Const(8L));
      IPop(Reg(R8));
      IPop(Reg(RCX));
      IPop(Reg(RDX));
      IPop(Reg(RSI));
      IPop(Reg(RDI));
    ]
      (setup_call_to_func 5
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_six_equal">::(fun _ -> 
    assert_equal [
      IPush(Reg(RDI));
      IPush(Reg(RSI));
      IPush(Reg(RDX));
      IPush(Reg(RCX));
      IPush(Reg(R8));
      IPush(Reg(R9));
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      ICall("label");
      IPop(Reg(R9));
      IPop(Reg(R8));
      IPop(Reg(RCX));
      IPop(Reg(RDX));
      IPop(Reg(RSI));
      IPop(Reg(RDI));
    ]
      (setup_call_to_func 6
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_six_odd">::(fun _ -> 
    assert_equal [
      IPush(Reg(RDI));
      IPush(Reg(RSI));
      IPush(Reg(RDX));
      IPush(Reg(RCX));
      IPush(Reg(R8));
      IPush(Reg(R9));
      IPush(Const(0L));
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      IPush(Const(7L));
      ICall("label");
      IAdd(Reg(RSP), Const(16L));
      IPop(Reg(R9));
      IPop(Reg(R8));
      IPop(Reg(RCX));
      IPop(Reg(RDX));
      IPop(Reg(RSI));
      IPop(Reg(RDI));
    ]
      (setup_call_to_func 6
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_six_even">::(fun _ -> 
    assert_equal [
      IPush(Reg(RDI));
      IPush(Reg(RSI));
      IPush(Reg(RDX));
      IPush(Reg(RCX));
      IPush(Reg(R8));
      IPush(Reg(R9));
      IMov(Reg(RDI), Const(1L));
      IMov(Reg(RSI), Const(2L));
      IMov(Reg(RDX), Const(3L));
      IMov(Reg(RCX), Const(4L));
      IMov(Reg(R8), Const(5L));
      IMov(Reg(R9), Const(6L));
      IPush(Const(8L));
      IPush(Const(7L));
      ICall("label");
      IAdd(Reg(RSP), Const(16L));
      IPop(Reg(R9));
      IPop(Reg(R8));
      IPop(Reg(RCX));
      IPop(Reg(RDX));
      IPop(Reg(RSI));
      IPop(Reg(RDI));
    ]
      (setup_call_to_func 6
         [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L); Const(8L)] 
         "label") ~printer:to_asm);
  "setup_call_to_func_save_regs_six_even">::(fun _ -> 
    assert_equal [
      IPush(Reg(RDI));
      IPush(Reg(RSI));
      IPush(Reg(RDX));
      IPush(Reg(RCX));
      IPush(Reg(R8));
      IPush(Reg(R9));
      IMov(Reg(RDI), RegOffset(word_size * 4, RSP));
      IMov(Reg(RSI), RegOffset(word_size * 3, RSP));
      IMov(Reg(RDX), RegOffset(word_size * 2, RSP));
      IMov(Reg(RCX), RegOffset(word_size * 1, RSP));
      IMov(Reg(R8), RegOffset(word_size * 0, RSP));
      IMov(Reg(R9), RegOffset(word_size * 5, RSP));
      ICall("label");
      IPop(Reg(R9));
      IPop(Reg(R8));
      IPop(Reg(RCX));
      IPop(Reg(RDX));
      IPop(Reg(RSI));
      IPop(Reg(RDI));
    ]
      (setup_call_to_func 6
         [Reg(RSI); Reg(RDX); Reg(RCX); Reg(R8); Reg(R9); Reg(RDI)]
         "label") ~printer:to_asm);
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

  "(def f1(new_args_2_1, new_args_2_2):
  (let b = new_args_2_1, n = new_args_2_2 in (let x = print(b), y = print(n) in (if isnum(n): (if isbool(b): true else: false) else: false))))

(def f2(new_args_19_3, new_args_19_4):
  (let n = new_args_19_3, b = new_args_19_4 in (let x = print((?f1(b, n))), y = print(n), z = print(b) in (if (if x: (if isnum(y): true else: false) else: false): (if isbool(z): true else: false) else: false))))
(?f2(5, false))";
]
