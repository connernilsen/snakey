open Assembly
open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Errors
open Phases
open Exprs
open ExtLib

let check_name (name : string) : string =
  if String.contains name ' '
  then failwith (sprintf "Test name cannot contain ' ': %s" name)
  else name
;;

let t name program expected = name>::test_run program name expected;;

let tcontains name program expected = name>::test_run ~args:[] program name expected ~cmp: (fun check result ->
    match check, result with
    | Ok(a), Ok(b) -> (String.exists b a)
    | _ -> false
  );;

let ti name program input expected = (check_name name)>::test_run ~args:[] ~std_input:input program name expected;;

let ta name program_and_env expected = name>::test_run_anf program_and_env name expected;;

let te name program expected_err = name>::test_err ~vg:false program name expected_err;;

(* let t name program expected = name>::test_run_valgrind program name expected;; *)

let tanf name program expected = name>::fun _ ->
    assert_equal expected (anf (tag (desugar program))) ~printer:string_of_aprogram;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf_improved (name : string) (program : string) (expected : string) = name>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_aprogram (anf (tag (desugar (parse_string name program))))) ~printer:(fun s->s);
    (* check_scope_helper (fun _-> "ignored") (parse_string name program) []; *)
;;

let teq name actual expected = name>::fun _ ->
    assert_equal expected actual ~printer:(fun s -> s);;

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to expected *)
let tprog (filename : string) (expected : string) = filename>::test_run_input filename expected;;

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to expected *)
let teprog (filename : string) (expected : string) = filename>::test_err_input filename expected;;

let tdesugar (name : string) (program : string) (expected : string) = name>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_program (desugar (parse_string name program))) ~printer:(fun s->s);;

let tvg name program expected = name>::test_run_valgrind program name expected;;
let teq_notstring name actual expected = (check_name name)>::fun _ ->
    assert_equal expected actual;;
let teq_num name actual expected = (check_name name)>::fun _ ->
    assert_equal expected actual ~printer:(fun d -> sprintf "%d" d);;

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

let terr name program input expected = (check_name name)>::test_err ~args:[] ~std_input:input program name expected
;;

let arg_envt_printer args =
  ("[" ^
   (String.concat "; " 
      (List.map (fun (tag, name, v) -> sprintf "(%d, %s, %s)" tag name (arg_to_asm v))
         args)) ^
   "]")
;;
let list_library = "def link(first, rest):
  (first, rest)
def generate_helper(n):
  if n == 0: nil
  else:
    link(n, generate_helper(n - 1))
def append(l, l2):
  if l == nil: l2
  else:
    link(l[0], append(l[1], l2))
def reverse(l):
  if l == nil: nil
  else:
    append(reverse(l[1]), link(l[0], nil))
def generate(n):
  reverse(generate_helper(n))
def map(f, l):
  if l == nil: l
  else: link(f(l[0]), map(f, l[1]))"

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
    te "andE1" "1 && true" "Error 3: expected a boolean, got 1";
    te "andE2" "true && 1" "Error 3: expected a boolean, got 1";
    te "orE1" "1 || true" "Error 3: expected a boolean, got 1";
    te "orE2" "false || 1" "Error 3: expected a boolean, got 1";
    t "notIsbool" "!(isbool(40))" "true";
    t "notIsboolT" "!(isbool(true))" "false";
    t "notIsnumT" "!(isnum(40))" "false";
    t "notIsnum" "!(isnum(false))" "true";
    te "bool_instead_of_num" "add1(true)" "Error 2: arithmetic expected a number, got true";
    te "bool_instead_of_num_in_if" "add1(if true: false else: 5)" "Error 2: arithmetic expected a number, got false";
    te "bool_instead_of_num2" "sub1(false)" "Error 2: arithmetic expected a number, got false";
    te "num_instead_of_bool" "!(1)" "Error 3: expected a boolean, got 1";
    te "num_instead_of_bool_in_if" "!(if false: false else: 5)" "Error 3: expected a boolean, got 5";
    te "bool_instead_of_num3" "1 < true" "Error 1: comparison expected a number, got true";
    te "num_instead_of_bool2" "if (1): 1 else: 0" "Error 3: expected a boolean, got 1";
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
    te "greaterE1" "1 > true" "Error 1: comparison expected a number, got true";
    te "greaterE2" "false > 1" "Error 1: comparison expected a number, got false";
    te "greaterEqE1" "1 >= false" "Error 1: comparison expected a number, got false";
    te "greaterEqE2" "true >= 1" "Error 1: comparison expected a number, got true";
    te "lessE1" "1 < true" "Error 1: comparison expected a number, got true";
    te "lessE2" "false < 1" "Error 1: comparison expected a number, got false";
    te "lessEqE1" "1 <= false" "Error 1: comparison expected a number, got false";
    te "lessEqE2" "true <= 1" "Error 1: comparison expected a number, got true";
    te "lessEqE2_in_if" "1 <= (if true: false else: 5)" "Error 1: comparison expected a number, got false";
    te "lessEqE2_in_if_in_let" "let x = 1 <= (if true: false else: 5) in x" "Error 1: comparison expected a number, got false";

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
      "4611686018427387903 + 1" "Error 5: overflow occurred for arithmetic operation, got -4611686018427387904";
    te "overflow_2^62_plus_negative"
      "-4611686018427387904 + -1" "Error 5: overflow occurred for arithmetic operation, got 4611686018427387903";
    te "overflow_2^62_add1"
      "add1(4611686018427387903)" "Error 5: overflow occurred for arithmetic operation, got -4611686018427387904";
    te "overflow_-2^62_minus_positive"
      "4611686018427387903 - -1" "Error 5: overflow occurred for arithmetic operation, got -4611686018427387904";
    te "overflow_-2^62_minus_negative"
      "-4611686018427387904 - 1" "Error 5: overflow occurred for arithmetic operation, got 4611686018427387903";
    te "overflow_-2^62_sub1"
      "sub1(-4611686018427387904)" "Error 5: overflow occurred for arithmetic operation, got 4611686018427387903";
    te "overflow_2^61_times_positive_1"
      "4611686018427387903 * 4" "Error 5: overflow occurred for arithmetic operation, got -4";
    te "overflow_2^61_times_positive_2"
      "-4611686018427387903 * -4" "Error 5: overflow occurred for arithmetic operation, got -4";
    te "overflow_2^61_times_negative_1"
      "4611686018427387903 * -4" "Error 5: overflow occurred for arithmetic operation, got 4";
    te "overflow_2^61_times_negative_2"
      "-4611686018427387903 * 4" "Error 5: overflow occurred for arithmetic operation, got 4";

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
        assert_equal [ICall(Label("label"))] 
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 0 [] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_2">::(fun _ ->
        assert_equal [IMov(Reg(RDI), Const(1L)); ICall(Label("label"))]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 0 [Const(1L)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_3">::(fun _ -> 
        assert_equal [
          IMov(Reg(RDI), Const(1L));
          IMov(Reg(RSI), Const(2L));
          IMov(Reg(RDX), Const(3L));
          IMov(Reg(RCX), Const(4L));
          IMov(Reg(R8), Const(5L));
          IMov(Reg(R9), Const(6L));
          ICall(Label("label"))]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 0
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(16L))]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 0
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(16L))]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 0
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L); Const(8L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(32L))]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 0
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L); Const(8L); Const(9L)] 
                  (Label("label")) false)) ~printer:to_asm);
    tanf_improved "let_in_prim"
      "add1(let x = 5 in x)"
      "(alet x_5 = 5 in add1(x_5))";
    tanf_improved "let_in_prim_with_eval"
      "add1(let x = 5 in add1(x))"
      "(alet x_5 = 5 in (alet unary_7 = add1(x_5) in add1(unary_7)))";
    tanf_improved "let_in_prim2_with_eval"
      "add1(let x = 5 in (x + (let x = 2 in x)))"
      "(alet x_5 = 5 in (alet x_11 = 2 in (alet binop_7 = (x_5 + x_11) in add1(binop_7))))";
    tanf_improved "let_in_let_in_if" 
      ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
       "(let abcd = 10 in add1(abcd)) " ^
       "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
      ("(alet x_5 = 5 in (alet x_11 = sub1(x_5) in (alet unary_17 = add1(x_11) in " ^
       "(alet y_15 = (unary_17 - 10) in (alet y_8 = y_15 in (alet binop_21 = (y_8 + x_5) in " ^
       "(if binop_21: (alet abcd_26 = 10 in add1(abcd_26)) else: (alet x_32 = 0 in " ^
       "(alet if_37 = (if x_32: x_32 else: 1) in (alet y_35 = sub1(if_37) in y_35))))))))))");
    tanf_improved "lets_in_prim"
      "(let x = 1 in x) + (let x = 2 in x)"
      "(alet x_5 = 1 in (alet x_10 = 2 in (x_5 + x_10)))";
    tanf_improved "if_in_if_in_let_in_add1"
      "add1(let x = (if (if 0: 0 else: 1): 2 else: 3) in (if x: 4 else: 5))"
      "(alet if_7 = (if 0: 0 else: 1) in (alet x_5 = (if if_7: 2 else: 3) in (alet if_13 = (if x_5: 4 else: 5) in add1(if_13))))";
    tanf_improved "simple_conditional"
      "(let x = (if 1: 5 + 5 else: 6 * 2) in (let y = (if 0: x * 3 else: x + 5) in x + y))"
      ("(alet x_4 = (if 1: (5 + 5) else: (6 * 2)) in (alet y_15 = (if 0: (x_4 * 3) else: (x_4 + 5)) in (x_4 + y_15)))");
    tanf_improved "complex_conditional"
      ("(let x = (if (5 - 10): add1(5 + 5) else: sub1(6 * 2)) in " ^
       "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))"
      )
      ("(alet binop_6 = (5 - 10) in " ^
       "(alet x_4 = (if binop_6: (alet binop_10 = (5 + 5) in " ^
       "add1(binop_10)) else: (alet binop_14 = (6 * 2) in sub1(binop_14))) in " ^
       "(alet binop_22 = (x_4 * 0) in " ^
       "(alet if_21 = (if binop_22: (alet unary_27 = sub1(3) in (x_4 * unary_27)) else: (alet unary_30 = add1(x_4) in (unary_30 + 5))) in " ^
       "(alet y_19 = sub1(if_21) in (alet binop_34 = (x_4 + y_19) in sub1(binop_34)))))))");
    tanf_improved "expr_basic"
      ("def f() : 1\n1")
      ("(aletrec f = (lam() 1) in 1)");
    tanf_improved "expr_call"
      ("def f() : 1\nf()")
      ("(aletrec f = (lam() 1) in (f()))");
    tanf_improved "expr_call_w_imm_args"
      ("def f(a, b) : 1\n(f(1, 2))")
      ("(aletrec f = (lam(a_3, b_4) 1) in (f(1, 2)))");
    tanf_improved "multiple_expr_call_w_multiple_compound_args"
      ("def f(a, b) : 1\ndef g(a, b, c) : a == b\nlet c = f(add1(1), add1(1)), d = g(add1(2), add1(3), 4 + 3) in d")
      ("(aletrec f = (lam(a_3, b_4) 1) in (aletrec g = (lam(a_7, b_8, c_9) (a_7 == b_8)) in " ^
       "(alet unary_23 = add1(1) in (alet unary_25 = add1(1) in (alet c_15 = (f(unary_23, unary_25)) in " ^
       "(alet unary_31 = add1(2) in (alet unary_33 = add1(3) in (alet binop_35 = (4 + 3) in " ^
       "(alet d_23 = (g(unary_31, unary_33, binop_35)) in d_23)))))))))");
    tanf_improved "expr_within_expr"
      ("def f(a) : a\ndef g(b) : add1(b)\nf(g(1))")
      ("(aletrec f = (lam(a_3) a_3) in (aletrec g = (lam(b_6) add1(b_6)) in (alet app_16 = (g(1)) in (f(app_16)))))");
    tanf_improved "expr_within_expr_within_expr"
      ("def f(a) : a\ndef g(b) : add1(b)\ndef h(b) : b\nh(f(g(1)))")
      ("(aletrec f = (lam(a_3) a_3) in (aletrec g = (lam(b_6) add1(b_6)) in (aletrec h = (lam(b_10) b_10) in (alet app_23 = (g(1)) in (alet app_22 = (f(app_23)) in (h(app_22)))))))");
    tanf_improved "infinite_loop_anf"
      ("def f(a) : g(a)\ndef g(a) : f(a)\ng(1)")
      ("(aletrec f = (lam(a_3) (g(a_3))) in (aletrec g = (lam(a_8) (f(a_8))) in (g(1))))");
    te "basic" "f()" "The identifier f, used at <basic, 1:0-1:1>, is not in scope";
    te "dup_fun" 
      "def test(): 1
def test(): 2
test()"
      (print_te 
         [DuplicateId("test", 
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
      "The identifier test, used at <unbound_fun, 1:0-1:4>, is not in scope";
    t "function_as_arg"
      "def a(b):
      b
     def b(a):
      a
    b(a)"
      "<function";
    te "let_call"
      "let a = 1 in a(1)"
      "Error 16: tried to call a non-function value: 1";
    te "arity_less"
      "def test(x): x test()"
      "Error 17: arity mismatch in call";
    te "arity_more"
      "def test(x, y): x + y test(1)"
      "Error 17: arity mismatch in call";
    te "arity_and_dup_correct"
      "def test(x): x def test(x, y): x + y test(1)"
      (print_te 
         [DuplicateId("test", 
                      (create_ss "arity_and_dup_correct" 1 15 1 36), 
                      (create_ss "arity_and_dup_correct" 1 0 1 14))]);
    te "arity_and_dup_incorrect"
      "def test(x, y): x + y def test(x): x test(1)"
      (print_te 
         [DuplicateId("test", 
                      (create_ss "arity_and_dup_incorrect" 1 22 1 36), 
                      (create_ss "arity_and_dup_incorrect" 1 0 1 21))]);
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
          UnboundId("a", create_ss "nested_errors" 6 20 6 21);
          UnboundId("hello", create_ss "nested_errors" 6 26 6 31);
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
    and def t2(val):
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
    and def t2(val):
      let dec_num = abs_dec(val) in
      if dec_num == 0:
        0 
      else:
        let neg = t1(true, dec_num),
            pos = t1(false, dec_num)
          in neg && pos
      t1(false, 4)"
      "expected a boolean, got 0";
    t "reuse_reg_args_not_tail_recursive"
      "def f1(b, n):
      let x = print(b),
          y = print(n) in 
        isnum(n) && isbool(b) 
        && isnum(y) && isbool(x)
    and def f2(n, b):
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
    and def f2(n, b, i):
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
    and def f2(n, b, i):
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
    te "function_def_in_let"
      "def run(val):
      let run = val in print(run)
    let run = 5 in run(run)"
      "Error 16: tried to call a non-function value: 5";
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
        assert_equal [] (get_func_call_params [] [] 0) 
          ~printer:arg_envt_printer);
    "get_func_call_params_2">::(fun _ -> 
        assert_equal [(0, "first", Reg(RDI))] (get_func_call_params ["first"] [] 0)
          ~printer:arg_envt_printer);
    "get_func_call_params_3">::(fun _ -> 
        assert_equal [
          (0, "1", Reg(RDI));
          (0, "2", Reg(RSI));
          (0, "3", Reg(RDX));
          (0, "4", Reg(RCX));
          (0, "5", Reg(R8));
          (0, "6", Reg(R9));
        ] (get_func_call_params 
             ["1"; "2"; "3"; "4"; "5"; "6"] [] 0)
          ~printer:arg_envt_printer);
    "get_func_call_params_4">::(fun _ -> 
        assert_equal [
          (0, "1", Reg(RDI));
          (0, "2", Reg(RSI));
          (0, "3", Reg(RDX));
          (0, "4", Reg(RCX));
          (0, "5", Reg(R8));
          (0, "6", Reg(R9));
          (0, "7", RegOffset(16, RBP));
        ] (get_func_call_params 
             ["1"; "2"; "3"; "4"; "5"; "6"; "7"] [] 0)
          ~printer:arg_envt_printer);
    "get_func_call_params_5">::(fun _ -> 
        assert_equal [
          (0, "1", Reg(RDI));
          (0, "2", Reg(RSI));
          (0, "3", Reg(RDX));
          (0, "4", Reg(RCX));
          (0, "5", Reg(R8));
          (0, "6", Reg(R9));
          (0, "7", RegOffset(16, RBP));
          (0, "8", RegOffset(24, RBP));
          (0, "9", RegOffset(32, RBP));
        ] 
          (get_func_call_params 
             ["1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] [] 0)
          ~printer:arg_envt_printer);
    "setup_call_to_func_save_regs_one_1">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Const(0L));
          IMov(Reg(RDI), Const(1L));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 1 [Const(1L)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_one_2">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Const(0L));
          IMov(Reg(RDI), RegOffset(word_size, RSP));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 1 [Reg(RDI)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_one_3">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Const(0L));
          IMov(Reg(RDI), Const(0L));
          IMov(Reg(RSI), Const(1L));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 1 [Const(0L); Const(1L)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_one_4">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Const(0L));
          IMov(Reg(RDI), Const(0L));
          IMov(Reg(RSI), RegOffset(word_size, RSP));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 1 [Const(0L); Reg(RDI)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_two_1">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IMov(Reg(RDI), Const(1L));
          ICall(Label("label"));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 2 [Const(1L)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_two_2">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IMov(Reg(RDI), RegOffset(word_size, RSP));
          ICall(Label("label"));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 2 [Reg(RDI)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_two_3">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IMov(Reg(RDI), Const(0L));
          IMov(Reg(RSI), Const(1L));
          ICall(Label("label"));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 2 [Const(0L); Const(1L)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_two_4">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IMov(Reg(RDI), RegOffset(0, RSP));
          IMov(Reg(RSI), RegOffset(word_size, RSP));
          ICall(Label("label"));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 2 [Reg(RSI); Reg(RDI)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_three_1">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IPush(Reg(RDX));
          IPush(Const(0L));
          IMov(Reg(RDI), Const(1L));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 3 [Const(1L)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_three_2">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IPush(Reg(RDX));
          IPush(Const(0L));
          IMov(Reg(RDI), RegOffset(word_size * 3, RSP));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 3 [Reg(RDI)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_three_3">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IPush(Reg(RDX));
          IPush(Const(0L));
          IMov(Reg(RDI), Const(0L));
          IMov(Reg(RSI), Const(1L));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 3 [Const(0L); Const(1L)] (Label("label")) false)) ~printer:to_asm);
    "setup_call_to_func_save_regs_three_4">::(fun _ ->
        assert_equal [
          IPush(Reg(RDI));
          IPush(Reg(RSI));
          IPush(Reg(RDX));
          IPush(Const(0L));
          IMov(Reg(RDI), RegOffset(word_size * 2, RSP));
          IMov(Reg(RSI), RegOffset(word_size * 3, RSP));
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(Int64.of_int word_size));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 3 [Reg(RSI); Reg(RDI)] (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(8L));
          IPop(Reg(R8));
          IPop(Reg(RCX));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 5
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(8L));
          IPop(Reg(R8));
          IPop(Reg(RCX));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 5
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IPop(Reg(R9));
          IPop(Reg(R8));
          IPop(Reg(RCX));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 6
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(16L));
          IPop(Reg(R9));
          IPop(Reg(R8));
          IPop(Reg(RCX));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 6
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IAdd(Reg(RSP), Const(16L));
          IPop(Reg(R9));
          IPop(Reg(R8));
          IPop(Reg(RCX));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 6
                  [Const(1L); Const(2L); Const(3L); Const(4L); Const(5L); Const(6L); Const(7L); Const(8L)] 
                  (Label("label")) false)) ~printer:to_asm);
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
          ICall(Label("label"));
          IPop(Reg(R9));
          IPop(Reg(R8));
          IPop(Reg(RCX));
          IPop(Reg(RDX));
          IPop(Reg(RSI));
          IPop(Reg(RDI));
        ]
          (List.filter (fun arg -> match arg with | ILineComment(_) -> false | _ -> true)
               (setup_call_to_func 6
                  [Reg(RSI); Reg(RDX); Reg(RCX); Reg(R8); Reg(R9); Reg(RDI)]
                  (Label("label")) false)) ~printer:to_asm);
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
    terr "wf_tuple" "(a, 1, 2, 3)" "" "The identifier a, used at <wf_tuple, 1:1-1:2>, is not in scope";
    terr "wf_tuple_in_tuple" "((a,), 1, 2, 3)" "" "The identifier a, used at <wf_tuple_in_tuple, 1:2-1:3>, is not in scope";
    terr "wf_tuple_get" "(a, 1, 2, 3)[0]" "" "The identifier a, used at <wf_tuple_get, 1:1-1:2>, is not in scope";
    terr "wf_tuple_get_arg" "(1, 2, 3)[a]" "" "The identifier a, used at <wf_tuple_get_arg, 1:10-1:11>, is not in scope";
    terr "wf_tuple_set" "(a, 1, 2, 3)[0] := 0" "" "The identifier a, used at <wf_tuple_set, 1:1-1:2>, is not in scope";
    terr "wf_tuple_set_arg" "(1, 2, 3)[a] := 0" "" "The identifier a, used at <wf_tuple_set_arg, 1:10-1:11>, is not in scope";
    terr "wf_tuple_set_set" "(1, 2, 3)[0] := a" "" "The identifier a, used at <wf_tuple_set_set, 1:16-1:17>, is not in scope";
    te "wf_rebind_fun" "def a(): true\nand def a(): true\n1" (print_te 
                                                                [DuplicateId("a",
                                                                             (create_ss "wf_rebind_fun" 1 0 1 13),
                                                                             (create_ss "wf_rebind_fun" 2 4 2 17))]);
    terr "wf_sequence_1" "a; a" "" "The identifier a, used at <wf_sequence_1, 1:0-1:1>, is not in scope\nThe identifier a, used at <wf_sequence_1, 1:3-1:4>, is not in scope";
    te "wf_let_tuple_repeats" "let (a, a) = (1, 2) in true"
      (print_te 
         [DuplicateId("a",
                      (create_ss "wf_let_tuple_repeats" 1 8 1 9),
                      (create_ss "wf_let_tuple_repeats" 1 5 1 6))]);
    te "wf_let_tuple_repeats_non_tuple" "let (a, b) = (1, 2), a = true in true"
      (print_te 
         [DuplicateId("a",
                      (create_ss "wf_let_tuple_repeats_non_tuple" 1 21 1 22),
                      (create_ss "wf_let_tuple_repeats_non_tuple" 1 5 1 6))]);
    te "wf_let_tuple_repeats_nested" "let (a, (b, a)) = (1, (2, 3)) in true"
      (print_te 
         [DuplicateId("a",
                      (create_ss "wf_let_tuple_repeats_nested" 1 12 1 13),
                      (create_ss "wf_let_tuple_repeats_nested" 1 5 1 6))]);
    te "wf_let_nested_tuple_repeats_non_tuple" "let (c, (b, a)) = (1, (2, 3)), b = true in true"
      (print_te 
         [DuplicateId("b",
                      (create_ss "wf_let_nested_tuple_repeats_non_tuple" 1 31 1 32),
                      (create_ss "wf_let_nested_tuple_repeats_non_tuple" 1 9 1 10))]);
    tdesugar "desugar_seq_basic"
      "true; false"
      "\n(let _ = true in false)";
    tdesugar "desugar_seq_nested"
      "true; false; true"
      "\n(let _ = true in (let _ = false in true))";
    tdesugar "desugar_seq_complex"
      "true; true && true; true"
      "\n(let _ = true in (let _ = (if true: (if true: true else: false) else: false) in true))";
    tdesugar "desugar_destructure_basic"
      "let (a, b, c) = (1, 2, 3) in (a, b, c)"
      "\n(let bind_temp4 = ((1, 2, 3) check_size 3), a = bind_temp4[0], b = bind_temp4[1], c = bind_temp4[2] in (a, b, c))";
    tdesugar "desugar_destructure_nested"
      "let (a, (b, c), d) = (1, (2, 3), 4) in (a, (b, c), d)"
      "\n(let bind_temp4 = ((1, (2, 3), 4) check_size 3), a = bind_temp4[0], bind_temp6 = (bind_temp4[1] check_size 2), b = bind_temp6[0], c = bind_temp6[1], d = bind_temp4[2] in (a, (b, c), d))";
    tdesugar "desugar_destructure_nested_w_blanks"
      "let (a, (b, _), _) = (1, (2, 3), 4) in (a, (b, c), d)"
      "\n(let bind_temp4 = ((1, (2, 3), 4) check_size 3), a = bind_temp4[0], bind_temp6 = (bind_temp4[1] check_size 2), b = bind_temp6[0], _ = bind_temp6[1], _ = bind_temp4[2] in (a, (b, c), d))";
    tdesugar "desugar_decl_with_destructure"
      "def f((a, b), c): ((a, b), c)\nf((1, 2), 3)"
      "\n(let-rec f = (lam(fun_arg#3, c) (let bind_temp3 = (fun_arg#3 check_size 2), a = bind_temp3[0], b = bind_temp3[1] in ((a, b), c))) in (f((1, 2), 3)))";
    tdesugar "desugar_decl_with_destructure_and_blank"
      "def f((a, _), c): ((a,), c)\nf((1, 2), 3)"
      "\n(let-rec f = (lam(fun_arg#3, c) (let bind_temp3 = (fun_arg#3 check_size 2), a = bind_temp3[0], _ = bind_temp3[1] in ((a,), c))) in (f((1, 2), 3)))";
    tdesugar "desugar_destructure_not_nested"
      "let (a, b, c) = (1, (2, 3), ()) in (a, b, c)"
      "\n(let bind_temp4 = ((1, (2, 3), ()) check_size 3), a = bind_temp4[0], b = bind_temp4[1], c = bind_temp4[2] in (a, b, c))";
    tanf_improved "tuple"
      ("(1, 2, 3)")
      ("(1, 2, 3)");
    tanf_improved "get_tuple"
      ("(1, 2, 3)[0]")
      ("(alet tuple_4 = (1, 2, 3) in tuple_4[0])");
    tanf_improved "set_tuple"
      ("(1, 2, 3)[0] := 2")
      ("(alet tuple_5 = (1, 2, 3) in tuple_5[0] := 2 )");
    ti "empty_pair" "()" "" "()";
    ti "single_pair" "(5,)" "" "(5, )";
    ti "double_pair" "(5, 6)" "" "(5, 6)";
    ti "long_pair" "(5, 6, 7, 8, 9, 10, 100)" "" "(5, 6, 7, 8, 9, 10, 100)";
    ti "tuple_within_tuple" "((5, 6), (7, 8))" "" "((5, 6), (7, 8))";
    ti "tuple_within_tuple_2" "((5, 6), (7, 8, 9))" "" "((5, 6), (7, 8, 9))";
    ti "tuple_within_tuple_3" "((5, 6, 9), (7, 8))" "" "((5, 6, 9), (7, 8))";
    ti "tuple_within_tuple_complex" "((5, 6, (7, 8, (9, 10, (11, (12, 13)))), 14), (15, 16))" ""
      "((5, 6, (7, 8, (9, 10, (11, (12, 13)))), 14), (15, 16))";
    ti "expr_within_tuple" "(1 + 1, 2)" ""
      "(2, 2)";
    ti "expr_within_tuple_2" "(1 + 1, add1(2))" ""
      "(2, 3)";
    ti "print_within_tuple" "(print(2), add1(2))" ""
      "2\n(2, 3)";
    ti "print_of_tuple_within_tuple" "(print((2, 3)), add1(2))" ""
      "(2, 3)\n((2, 3), 3)";
    ti "get_value_from_tuple_0" "(1, 2, 3, 4, 5)[0]" "" "1";
    ti "get_value_from_tuple_1" "(1, 2, 3, 4, 5)[1]" "" "2";
    ti "get_value_from_tuple_2" "(1, 2, 3, 4, 5)[2]" "" "3";
    ti "get_value_from_tuple_3" "(1, 2, 3, 4, 5)[3]" "" "4";
    ti "get_value_from_tuple_4" "(1, 2, 3, 4, 5)[4]" "" "5";
    ti "get_value_from_tuple_5_tuple" "(1, (1, 2, 3), 3, 4, 5)[1]" "" "(1, 2, 3)";
    ti "get_value_from_tuple_expr" "(1, 2, 3, 4, 5)[add1(3)]" "" "5";
    ti "get_value_from_tuple_expr2" "(1, 2, 3, 4, 5)[sub1(1)]" "" "1";
    terr "get_value_from_tuple_low_idx" "(1, 2, 3, 4, 5)[-1]" "" "index too small to get, got -1";
    terr "get_value_from_tuple_low_idx_expr" "(1, 2, 3, 4, 5)[sub1(0)]" "" "index too small to get, got -1";
    terr "get_value_from_tuple_high_idx" "(1, 2, 3, 4, 5)[5]" "" "index too large to get, got 5";
    terr "get_value_from_tuple_high_idx_expr" "(1, 2, 3, 4, 5)[add1(4)]" "" "index too large to get, got 5";
    terr "tuple_access_wrong_type" "1[5]" "" "Error 6: tuple access expected tuple, got 1";
    terr "tuple_access_idx_wrong_type" "(1, 2)[true]" "" "Error 9: get expected numeric index, got true";
    ti "nil_list_1" "(1, nil)" "" "(1, nil)";
    ti "nil_list_2" "(1, (2, nil))" "" "(1, (2, nil))";
    terr "tuple_access_idx_wrong_type_nil_access" "nil[true]" "" "tried to access component of nil";
    terr "tuple_access_idx_wrong_type_nil_idx" "(1, 2)[nil]" "" "Error 9: get expected numeric index, got nil";
    ti "get_value_from_tuple_0_set" "(1, 2, 3, 4, 5)[0] := 3" "" "3";
    ti "get_value_from_tuple_4_set" "(1, 2, 3, 4, 5)[4] := 3" "" "3";
    ti "get_value_from_tuple_expr_set" "(1, 2, 3, 4, 5)[add1(3)] := 3" "" "3";
    ti "get_value_from_tuple_expr2_set" "(1, 2, 3, 4, 5)[sub1(1)] := 3" "" "3";
    ti "get_value_from_tuple_expr2_set_tuple" "(1, 2, 3, 4, 5)[sub1(1)] := (1, 2, 3)" "" "(1, 2, 3)";
    ti "unchanged_modify_new_tuples" "print((1, 2, 3, 4, 5)); (1, 2, 3, 4, 5)[sub1(1)] := (1, 2, 3); (1, 2, 3, 4, 5)" "" "(1, 2, 3, 4, 5)\n(1, 2, 3, 4, 5)";
    terr "get_value_from_tuple_low_idx_set" "(1, 2, 3, 4, 5)[-1] := 3" "" "index too small to get, got -1";
    terr "get_value_from_tuple_low_idx_expr_set" "(1, 2, 3, 4, 5)[sub1(0)] := 3" "" "index too small to get, got -1";
    terr "get_value_from_tuple_high_idx_set" "(1, 2, 3, 4, 5)[5] := 3" "" "index too large to get, got 5";
    terr "get_value_from_tuple_high_idx_expr_set" "(1, 2, 3, 4, 5)[add1(4)] := 3" "" "index too large to get, got 5";
    terr "tuple_access_wrong_type_set" "1[5] := 3" "" "tuple access expected tuple, got 1";
    terr "tuple_access_idx_wrong_type_set" "(1, 2)[true] := 3" "" "Error 9: get expected numeric index, got true";
    terr "tuple_unary_type" "add1((1, 2))" "" "Error 2: arithmetic expected a number, got (1, 2)";
    terr "tuple_binary_type_l" "(1, 2) + 1" "" "Error 2: arithmetic expected a number, got (1, 2)";
    terr "tuple_binary_type_r" "1 + (1, 2)" "" "Error 2: arithmetic expected a number, got (1, 2)";
    ti "equality_ref" "(1, 2, 3) == (1, 2, 3)" "" "false";
    ti "equality_ref_true" "let x = (1, 2, 3) in x == x" "" "true";
    ti "equality_equal_ref" "let x = (1, 2, 3) in equal(x, x)" "" "true";
    ti "equality_equal_structural" "equal((1, 2, 3), (1, 2, 3))" "" "true";
    ti "equality_equal_structural_nest" "equal(((1, 2, 3), 2, 3), ((1, 2, 3), 2, 3))" "" "true";
    ti "equality_equal_structural_prims" "equal(((add1(1), 2, 3), 2, 3), ((2, 2, 3), 2, 3))" "" "true";
    ti "equality_notequal_structural_prims" "equal(((add1(1), 2, 3), 2, 3), ((2, 2, 4), 2, 3))" "" "false";
    (* ti "equality_equal_infinite_loop" "let f = (1,), g = (f,) in f[0] := g; equal(f, g)" "" "true"; *)
    ti "equality_notequal_infinite_loop" "let f = (1,), g = (f, 1) in f[0] := g; equal(f, g)" "" "false";
    ti "istuple_tuple" "istuple((1, 2, 3))" "" "true";
    ti "istuple_nil" "istuple(())" "" "true";
    ti "istuple_num" "istuple(5)" "" "false";
    ti "istuple_bool" "istuple(false)" "" "false";
    ti "isbool_tuple" "isbool((1, 2))" "" "false";
    ti "isbool_nil" "isbool(())" "" "false";
    ti "isnum_tuple" "isnum((1, 2))" "" "false";
    ti "isnum_nil" "isnum(())" "" "false";
    ti "input1" "let x = input() in x + 2" "123" "125";
    ti "input_print_int" "print(input())" "5" "5\n5";
    ti "tup1" "let t = (4, (5, 6)) in
              t[0] := 7;
              t" "" "(7, (5, 6))";
    ti "tup2" "let t = (4, (5, nil)) in
            begin
              t[1] := nil;
              t
            end" "" "(4, nil)";
    ti "tup_cycle" "let t = (4, (5, nil)) in
            begin
              t[1] := t;
              t
            end" "" "(4, <cyclic tuple 1>)";
    ti "tup_cycle_bigger" "let t = (4, (5, nil)), g = (t, 5), h = (g, 6), k = (10, h) in
            begin
              t[1] := k;
              (t, g, h, k)
            end" ""
      "((4, (10, ((<cyclic tuple 2>, 5), 6))), ((4, (10, (<cyclic tuple 6>, 6))), 5), (((4, (10, <cyclic tuple 10>)), 5), 6), (10, (((4, <cyclic tuple 14>), 5), 6)))";
    ti "infinite_loop" "let t = (1,), g = (t,) in
            begin
              t[0] := g;
              (t, g)
            end" "" "(((<cyclic tuple 2>, ), ), ((<cyclic tuple 4>, ), ))";
    ti "infinite_loop_is_tuple" "let t = (1,), g = (t,) in
            begin
              t[0] := g;
              istuple(t)
            end" "" "true";
    ti "nil_is_tuple" "istuple(nil)" "" "true";
    ti "tup4" "let t = (4, 6) in
            (t, t)"
      ""
      "((4, 6), (4, 6))";
    ti "tuple_empty_access" "((),)[0]" "" "()";
    terr "tuple_destructure_invalid" "let temp = (1, 2), (a, b, c) = temp in true" 
      "" "unable to destructure tuple with incorrect length (1, 2)";
    terr "tuple_destructure_invalid_2" "let (a, b) = (1, 2, 3) in (a, b)" "" "";
    terr "tuple_destructure_invalid_3" "let temp = (1, 2, 3), (a, b) = temp in (a, b)" "" "";
    ti "let_blank" "let _ = print(5 * 5) in print(3)" "" "25\n3\n3";
    ti "tuple_modification"
      "let t = (1, 2, 3, 4),
         a = t[1],
         b = t[1] := t[a],
         _ = t[0] := a in
         print(t); print(a); print(b)" ""
      "(2, 3, 3, 4)\n2\n3\n3";
    ti "tuple_double_modify"
      "let t = (1, 2, 3, 4) in
         t[0] := t[1];
         t[1] := t[0]; 
         t" ""
      "(2, 2, 3, 4)";
    ti "destructure_basic"
      "let (a, b, c) = (1, 2, 3) in (a, c, b)"
      ""
      "(1, 3, 2)";
    ti "destructure_complex"
      "let (a, b, (c, d), e) = (1, 2, (3, 4), 5) in (a, b, (d, c), e)"
      ""
      "(1, 2, (4, 3), 5)";
    ti "destructure_expr"
      "let (a, b, (c, d), e) = (1, 2, (add1(3), add1(4)), 5) in (a, b, (d, c), e)"
      ""
      "(1, 2, (5, 4), 5)";
    ti "destructure_print"
      "let (a, _, c) = (1, print(2), 5) in (a, c)"
      ""
      "2\n(1, 5)";
    ti "destructure_print_nested"
      "let (a, (b, _), c) = (1, (2, print(2)), 5) in (a, c)"
      ""
      "2\n(1, 5)";
    ti "destructure_not_nested" 
      "let (a, b, c, d) = (1, (2, 3), (4, 5, 6), ()) in 
      print(a); print(b); print(c); d"
      ""
      "1\n(2, 3)\n(4, 5, 6)\n()";
    ti "let_empty_pair"
      "let a = () in a"
      ""
      "()";
    ti "let_empty_pair_pair"
      "let a = ((), ()) in a[0]"
      ""
      "()";
    ti "print_cyclic_tuple_1"
      "let a = (1, nil) in
      a[1] := a; a"
      ""
      "(1, <cyclic tuple 1>)";
    ti "print_cyclic_tuple_2"
      "let a = (1, nil, 3),
         b = (a, 2, 3) in
      a[1] := b; print(b); a"
      ""
      "((1, <cyclic tuple 1>, 3), 2, 3)\n(1, (<cyclic tuple 3>, 2, 3), 3)";
    ti "print_cyclic_tuple_3"
      "let a = (nil, nil, nil),
         b = (nil, nil, a),
         c = (nil, a, b) in
        a[0] := a; a[1] := b; a[2] := c;
        b[0] := b; b[1] := c;
        c[0] := c;
        a"
      ""
      "(<cyclic tuple 1>, (<cyclic tuple 2>, (<cyclic tuple 3>, <cyclic tuple 1>, <cyclic tuple 2>), <cyclic tuple 1>), (<cyclic tuple 4>, <cyclic tuple 1>, (<cyclic tuple 5>, <cyclic tuple 4>, <cyclic tuple 1>)))";
    ti "deep_equal"
      "let a = (nil, nil, 1),
         b = (a, nil, 1) in
        a[0] := a; a[1] := b; 
        b[1] := b;
        equal(a, b)"
      ""
      "true";
    ti "deep_equal_tuple_len"
      "equal((1, 2, 3, (4, 5)), (1, 2, 3, (4, 5, 6)))"
      ""
      "false";
    ti "deep_equal_tuple_values"
      "equal((1, 2, 3, (4, 5)), (1, 2, 3, (4, 4)))"
      ""
      "false";
    ti "deep_equal_cycles_different_value"
      "let a = (nil, nil, 1),
         b = (a, nil, 2) in
        a[0] := a; a[1] := b; 
        b[1] := b;
        equal(a, b)"
      ""
      "false";
    (* ti "deep_equal_cycles_different_reference_1"
       "let a = (nil, 1),
         b = (a, 1),
         c = (b, 2) in
        a[0] := c; 
        equal(a, b)"
       ""
       "false";
       ti "deep_equal_cycles_different_reference_2"
       "let a = (nil, 1),
         b = (a, 1),
         c = (b, 2) in
        a[0] := c; 
        equal(b, a)"
       ""
       "false"; *)
    ti "deep_equal_cycles_different_reference_3"
      "let a = (nil, 1),
         b = (a, 1) in
        a[0] := a; 
        equal(a, b)"
      ""
      "true";
    ti "let_with_print"
      "let x = print(1) in isnum(x)"
      ""
      "1\ntrue";
    ti "print_add" "print(5 * 5) ; 5 - 2" "" "25\n3";
    ti "add_twice" "5 * 5 ; 5 - 2" "" "3";
    ti "sequencing" "print(5 * 5); print(3)" "" "25\n3\n3";
    terr "overflow" "def f(a): if (a == 0): true else: f(a - 1)\nf(-1)" "" "Signalled with -10 while running output/overflow.";
    t "compile_lambda_1_noapp" "(lambda (x): x)" "<function";
    t "compile_lambda_2_noapp" "(lambda (x): (lambda (x): x))" "<function";
    t "compile_lambda_noarg" "(lambda: 1)()" "1";
    t "compile_lambda_0_in_let" "let a = (lambda: 6) in a()" "6";
    t "compile_lambda_1" "(lambda (x): x)(5)" "5";
    t "compile_lambda_1_in_let" "let a = (lambda (x): x) in a(5)" "5";
    t "compile_lambda_2" "(lambda (x, y): x + y)(5, 10)" "15";
    t "compile_lambda_3" "(lambda (x, y): add1(x) + add1(y))(5, 10)" "17";
    t "compile_lambda_in_lambda" "(lambda (x, y): (lambda (x): x)(5) + x + y)(5, 10)" "20";
    t "compile_decl" "def x(f): f + 3\n(lambda (x, y): x + y)(5, 10) + x(3)" "21";
    te "invalid_arity" "(lambda (x): x)(5, 6)" "arity mismatch in call";
    (* closure tests *)
    t "compile_decl_with_frees"
      "let x = 5, y = (lambda(y): x + y) in y(6)" "11";
    t "compile_frees_2"
      "let x = 5, y = (lambda(y): (lambda(z): x + y + z)) in y(4)(3)"
      "12";
    t "y_combinator" "let y = (lambda (f): (lambda (x): x(x))((lambda (x): f((lambda (y): x(x)(y)))))), 
    fact = (lambda (f): (lambda (x): (if x == 1: 1 else: x * f(x - 1)))) in
    y(fact)(3)" "6";
    t "ocsh" "def our_code_starts_here(): 5\nour_code_starts_here()" "5";
    t "given_1" 
      "let x = 5 in
     let y = 6 in
     let z = y in
     let f = (lambda: x + z) in
     let h = (lambda: z + y) in
     f() # this should return 11, and no function should need more than 2 stack slots"
      "11";
    t "given_2"
      "let a = 1,
       b = 2,
       c = 3,
       d = 4,
       e = 5 in
   let f = (lambda: a + e) in # only two stack slots should be allocated in f's body
   f()"
      "6";
    te "let_rec_shadow_error"
      "let rec a = (lambda(x): x), a = (lambda(y): y - 1) in a(1)"
      "The identifier a, redefined at <let_rec_shadow_error, 1:28-1:29>, duplicates one at <let_rec_shadow_error, 1:8-1:9>
The identifier a, defined at <let_rec_shadow_error, 1:28-1:29>, shadows one defined at <let_rec_shadow_error, 1:8-1:9>
The identifier a, defined at <let_rec_shadow_error, 1:8-1:9>, shadows one defined at <let_rec_shadow_error, 1:28-1:29>
The identifier a, defined at <let_rec_shadow_error, 1:28-1:29>, shadows one defined at <let_rec_shadow_error, 1:8-1:9>";
    te "let_shadow_error"
      "let a = 5, a = (lambda(x): x) in a(a)"
      "The identifier a, redefined at <let_shadow_error, 1:11-1:12>, duplicates one at <let_shadow_error, 1:4-1:5>";
    t "let_letrec_nested_shadow"
      "def a(x): x
    let rec shadow a = (lambda(x): x + 1) in
      let shadow a = 5 in a"
      "5";
    te "def_no_shadow"
      "def x(y): y
  def x(y, z): y + z
  and def x(a, b, c): a + b + c
  a(1)"
      "The function name x, redefined at <def_no_shadow, 2:2-2:20>, duplicates one at <def_no_shadow, 1:0-1:11>
The function name x, redefined at <def_no_shadow, 3:6-3:31>, duplicates one at <def_no_shadow, 2:2-2:20>
The identifier a, used at <def_no_shadow, 4:2-4:3>, is not in scope";
    t "def_with_same_var"
      "def x(x): x
  x(1)"
      "1";
    t "let_rec_same_var"
      "let x = (lambda(x): x) in
  x(1)"
      "1";
    t "let_rec_nested_shadow"
      "let rec x = (lambda(x): x) in
    let rec shadow x = (lambda(x, y): x + y) in
    x(1, 2)"
      "3";
    t "let_rec_in_let"
      "let a = 
    (let rec isdone = (lambda(y): if y == 1: 0 else: b(y - 1)),
      b = (lambda(y): isdone(y)) in b) in
    a(4)"
      "0";
    t "let_rec_in_let_lambda"
      "let a = (lambda(x): 
    let rec isdone = (lambda(y): if y == x: 0 else: b(y - 1)),
      b = (lambda(y): isdone(y))
      in b) in
    a(1)(4)"
      "0";
    t "let_rec_in_let_sequence"
      "let a = (lambda(x): 
    let rec isdone = (lambda(y): if y == x: 0 else: b(y - 1)),
      b = (lambda(y): print(y); isdone(y))
      in b) in
    a(1)(4)"
      "4\n3\n2\n1\n0";
    t "let_in_lambda"
      "(lambda: let a = 5 in a)()"
      "5";
    tcontains "let_rec_in_lambda_simple"
      "(lambda(x): 
    let rec b = (lambda(y): 5)
      in b)"
      "<function";
    tcontains "let_rec_in_lambda_self"
      "(lambda(x): 
    let rec b = (lambda(y): if y == 0: 0 else: 1 + b(1 - y))
      in 5)"
      "<function";
    tcontains "let_rec_in_lambda_mutual"
      "(lambda(x): 
    let rec isdone = (lambda(y): if y == x: 0 else: b(y - 1)),
      b = (lambda(y): isdone(y))
      in b)"
      "<function";
    tcontains "let_rec_in_lambda_native"
      "(lambda(x): 
    let rec isdone = (lambda(y): if y == x: 0 else: b(y - 1)),
      b = (lambda(y): print(y); isdone(y))
      in b)"
      "<function";
    t "map"
      (list_library ^ "let mylist = map((lambda(x): x + 1), generate(4)) in mylist")
      "(2, (3, (4, (5, nil))))";
  ]
