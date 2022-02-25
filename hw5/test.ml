open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Errors
open Libtest

let t name program expected = name>::test_run program name expected;;

let ta name program_and_env expected = name>::test_run_anf program_and_env name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

let tvg name program expected = name>::test_run_valgrind program name expected;;
  
let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf_improved (name : string) (program : string) (expected : string) = name>:: fun _ ->
    assert_equal (expected) (string_of_aprogram (anf (rename (tag (parse_string name program))))) ~printer:(fun s->s);
    (* check_scope_helper (fun _-> "ignored") (parse_string name program) []; *)
;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tanf_tests = [
  tanf_improved "let_in_prim"
    "add1(let x = 5 in x)"
    "(alet x#4 = 5 in add1(x#4))";

  tanf_improved "let_in_prim_with_eval"
    "add1(let x = 5 in add1(x))"
    "(alet x#5 = 5 in (alet unary_3 = add1(x#5) in add1(unary_3)))";

  tanf_improved "let_in_prim2_with_eval"
    "add1(let x = 5 in (x + (let x = 2 in x)))"
    "(alet x#9 = 5 in (alet x#6 = 2 in (alet binop_3 = (x#9 + x#6) in add1(binop_3))))";

  tanf_improved "let_in_let_in_if" 
  ("if (let x = 5, y = (let x = sub1(x), y = (add1(x) - 10) in y) in (y + x)): " ^
     "(let abcd = 10 in add1(abcd)) " ^
     "else: (let x = 0, y = sub1(if x: x else: 1) in y)")
  ("(alet x#21 = 5 in " ^
      "(alet x#26 = sub1(x#21) in " ^
        "(alet unary_32 = add1(x#26) in " ^
          "(alet y#29 = (unary_32 - 10) in " ^
            "(alet y#23 = y#29 in " ^
              "(alet binop_18 = (y#23 + x#21) in " ^
                "(if binop_18: (alet abcd#15 = 10 in " ^
                                  "add1(abcd#15))" ^ 
                "else: (alet x#4 = 0 in " ^
                  "(alet if_8 = (if x#4: x#4 else: 1) in " ^
                    "(alet y#6 = sub1(if_8) in " ^
                      "y#6))))))))))");

  tanf_improved "lets_in_prim"
    "(let x = 1 in x) + (let x = 2 in x)"
    "(alet x#8 = 1 in (alet x#4 = 2 in (x#8 + x#4)))";

  tanf_improved "if_in_if_in_let_in_add1"
    "add1(let x = (if (if 0: 0 else: 1): 2 else: 3) in (if x: 4 else: 5))"
    "(alet if_11 = (if 0: 0 else: 1) in (alet x#7 = (if if_11: 2 else: 3) in (alet if_3 = (if x#7: 4 else: 5) in add1(if_3))))";

  tanf_improved "simple_conditional"
    "(let x = (if 1: 5 + 5 else: 6 * 2) in (let y = (if 0: x * 3 else: x + 5) in x + y))"
    ("(alet x#15 = (if 1: (5 + 5) else: (6 * 2)) in (alet y#6 = (if 0: (x#15 * 3) else: (x#15 + 5)) in (x#15 + y#6)))");

  tanf_improved "complex_conditional"
    ("(let x = (if (5 - 10): add1(5 + 5) else: sub1(6 * 2)) in " ^
     "(let y = sub1(if (x * 0): x * sub1(3) else: add1(x) + 5) in sub1(x + y)))"
    )
    ("(alet binop_31 = (5 - 10) in " ^
     "(alet x#21 = (if binop_31: " ^
        "(alet binop_28 = (5 + 5) in " ^ 
          "add1(binop_28)) " ^ "
        else: " ^ 
        "(alet binop_24 = (6 * 2) in " ^ 
          "sub1(binop_24))) in " ^ 
            "(alet binop_18 = (x#21 * 0) in " ^ 
              "(alet if_9 = (if binop_18: " ^ 
                "(alet unary_15 = sub1(3) in (x#21 * unary_15)) " ^
              "else: " ^ 
                "(alet unary_12 = add1(x#21) in (unary_12 + 5))) in " ^ 
                  "(alet y#7 = sub1(if_9) in " ^ 
                    "(alet binop_4 = (x#21 + y#7) in sub1(binop_4)))))))");
  tanf_improved "expr basic"
    ("def f() : 1\n1")
    ("(fun f(): 1)\n1");
  tanf_improved "expr call"
    ("def f() : 1\nf()")
    ("(fun f(): 1)\n(f())");
  tanf_improved "expr call w imm args"
    ("def f(a, b) : 1\nf(1, 2)")
    ("(fun f(a, b): 1)\n(f(1, 2))");
  tanf_improved "expr call w compound args"
    ("def f(a, b) : 1\nf(add1(1), 2)")
    ("(fun f(a, b): 1)\n(alet unary_2 = add1(1) in (f(unary_2, 2)))");
  tanf_improved "expr call w multiple compound args"
    ("def f(a, b) : 1\nf(add1(1), add1(1))")
    ("(fun f(a, b): 1)\n(alet unary_2 = add1(1) in (alet unary_4 = add1(1) in (f(unary_2, unary_4))))");
  tanf_improved "multiple expr call w multiple compound args"
    ("def f(a, b) : 1\ndef g(a, b, c) : a == b\nlet c = f(add1(1), add1(1)), d = g(add1(2), add1(3), 4 + 3) in d")
    ("(fun f(a, b): 1)\n" ^
    "(fun g(a, b, c): (a == b))" ^
    "(alet unary_5 = add1(1) in (alet unary_7 = add1(1) in (alet c#3 = (f(unary_5, unary_7)) in (alet unary_11 = add1(2) in (alet unary_13 = add1(3) in (alet binop_15 = (4 + 3) in (alet d#9 = (g(unary_11, unary_13, binop_15)) in d#9)))))))");
  tanf_improved "expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\nf(g(1))")
    ("(fun f(a): a)\n(fun g(b): add1(b))\n(alet app_2 = (g(1)) in (f(app_2)))");
  tanf_improved "expr_within_expr_within_expr"
    ("def f(a) : a\ndef g(b) : add1(b)\ndef h(b) : b\nh(f(g(1)))")
    ("(fun f(a): a)\n(fun g(b): add1(b))\n(fun h(b): b)\n(alet app_3 = (g(1)) in (alet app_2 = (f(app_3)) in (h(app_2))))");
]

let create_ss (file : string) (start_l : int) (start_c : int) (end_l : int) (end_c : int) : sourcespan =
  ({pos_fname=file; pos_lnum=start_l; pos_bol=0; pos_cnum=start_c},
   {pos_fname=file; pos_lnum=end_l; pos_bol=0; pos_cnum=end_c})
;;

let print_te (exns : exn list) : string =
  String.concat " " (print_errors exns)
;;

let is_well_formed_tests = [
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
                   (create_ss "dup_binds_let" 1 11 1 16),
                   (create_ss "dup_binds_let" 1 4 1 9))]);
  te "unbound_fun"
    "test()"
    (print_te 
       [UnboundFun("test",
                   (create_ss "unbound_fun" 1 0 1 6))]);
  te "arity"
    "def test(x): x test()"
    (print_te 
       [Arity(1, 0, (create_ss "arity" 1 15 1 21))]);
]

let tests = (
  (* tanf_tests @ *)
  is_well_formed_tests
)

let suite = "suite">:::tests
 
let () =
  run_test_tt_main ("all_tests">:::[suite; (* old_tests; *) input_file_test_suite ()])
;;
