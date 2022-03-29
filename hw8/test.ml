open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Libtest
open ExtLib

let check_name (name : string) : string =
  if String.contains name ' '
  then failwith (sprintf "Test name cannot contain ' ': %s" name)
  else name

let t name program input expected = name>::test_run ~args:[] ~std_input:input program name expected;;
let tcontains name program input expected = name>::test_run ~args:[] ~std_input:input program name expected ~cmp: (fun check result ->
    match check, result with
    | Ok(a), Ok(b) -> (String.exists b a)
    | _ -> false
  );;
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

let te name program expected_err = name>::test_err ~vg:false program name expected_err;;

let print_te (exns : exn list) : string =
  String.concat "\n" (print_errors exns)
;;

let tfvs name ignored program expected = name>::
                                         (fun _ ->
                                            let ast = parse_string name program in
                                            let anfed = anf (tag ast) in
                                            match anfed with
                                            | AProgram(body, _) ->
                                              let vars = free_vars body ignored in
                                              let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
                                              assert_equal (List.sort vars) (List.sort expected) ~printer:str_list_print)
;;

let tdesugar (name : string) (program : string) (expected : string) = (check_name name)>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_program (desugar (tag (parse_string name program)))) ~printer:(fun s->s);;

let tct (name : string) (program : string) (expected : string) = (check_name name)>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_program (rename_and_tag (tag (parse_string name program)))) ~printer:(fun s->s);;

(* Transforms a program into ANF, and compares the output to expected *)
let tanf_improved (name : string) (program : string) (expected : string) = (check_name name)>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_aprogram (anf (tag (desugar (rename_and_tag (tag (parse_string name program))))))) ~printer:(fun s->s)
;;

let forty_one = "41";;

let forty_one_a = (AProgram(ACExpr(CImmExpr(ImmNum(41L, ()))), ()))

let test_prog = "let x = if sub1(55) < 54: (if 1 > 0: add1(2) else: add1(3)) else: (if 0 == 0: sub1(4) else: sub1(5)) in x"
let anf1 = (anf     (tag (parse_string "test" test_prog)))


let desugar_tests = [
  tdesugar "desugar_decl_one" "def f(x): x\nf(1)" "\n(let-rec f = (lam(x) x) in (f(1)))";
  tdesugar "desugar_decl_two" "def f(x): x\ndef g(y, z, e): z + g\nf(1)" "\n(let-rec f = (lam(x) x) in (let-rec g = (lam(y, z, e) (z + g)) in (f(1))))";
  tdesugar "desugar_decl_and" "def f(x): x and def g(y, z, e): z + g\nf(1)" "\n(let-rec f = (lam(x) x), g = (lam(y, z, e) (z + g)) in (f(1)))";
  tdesugar "desugar_decl_with_destructure"
    "def f((a, b), c): ((a, b), c)\nf((1, 2), 3)"
    "\n(let-rec f = (lam(fun_arg#3, c) (let bind_temp3 = (fun_arg#3 check_size 2), a = bind_temp3[0], b = bind_temp3[1] in ((a, b), c))) in (f((1, 2), 3)))";
  tdesugar "desugar_decl_with_destructure_and_blank"
    "def f((a, _), c): ((a,), c)\nf((1, 2), 3)"
    "\n(let-rec f = (lam(fun_arg#3, c) (let bind_temp3 = (fun_arg#3 check_size 2), a = bind_temp3[0], _ = bind_temp3[1] in ((a,), c))) in (f((1, 2), 3)))";
  tdesugar "desugar_letrec"
    "let rec x = 5 in x"
    "\n(let-rec x = 5 in x)";
  tdesugar "desugar_lambda"
    "(lambda (x): x)"
    "\n(lam(x) x)";
  tdesugar "sequence" "print(5); print(5)" "\n(let _ = print(5) in print(5))";
  tdesugar "desugar_native" "input()" "\n((lam() (*input()))())";
  tdesugar "desugar_native_lambda" "let a = (lambda: input()) in a()" "\n(let a = (lam() ((lam() (*input()))())) in (a()))";
]

let default_tests =
  [

    t "test_is_bool1" "isbool(true)" "" "true";
    t "test_is_bool2" "isbool(false)" "" "true";
    t "test_is_bool3" "isbool(0)" "" "false";
    t "test_is_bool4" "isbool(123)" "" "false";
    t "test_is_bool5" "isbool((0,123))" "" "false";
    t "test_is_bool6" "isbool((true,123))" "" "false";
    t "test_is_bool7" "isbool((123,123))" "" "false";
    t "test_is_bool8" "isbool((false,123))" "" "false";

    t "test_is_tuple1" "istuple(true)" "" "false";
    t "test_is_tuple2" "istuple(false)" "" "false";
    t "test_is_tuple3" "istuple(0)" "" "false";
    t "test_is_tuple4" "istuple(123)" "" "false";
    t "test_is_tuple5" "istuple((0,123))" "" "true";
    t "test_is_tuple6" "istuple((true,123))" "" "true";
    t "test_is_tuple7" "istuple((123,123))" "" "true";
    t "test_is_tuple8" "istuple((false,123))" "" "true";

    t "test_is_num1" "isnum(true)" "" "false";
    t "test_is_num2" "isnum(false)" "" "false";
    t "test_is_num3" "isnum(0)" "" "true";
    t "test_is_num4" "isnum(123)" "" "true";
    t "test_is_num5" "isnum((0,123))" "" "false";
    t "test_is_num6" "isnum((true,123))" "" "false";
    t "test_is_num7" "isnum((123,123))" "" "false";
    t "test_is_num8" "isnum((false,123))" "" "false";

    tanf "forty_one_anf"
      (Program([], ENumber(41L, ()), ()))
      "" 
      forty_one_a;

    (* terr "scope_err1" "let x = true in (let y = (let x = false in x) in y)" "" "shadows one defined"; *)

    ta "forty_one_run_anf" ((atag forty_one_a), []) "" "41";

    t "forty_one" forty_one "" "41";


    t "test" test_prog "" "3";

    (* Some useful if tests to start you off *)

    t "if1" "if 7 < 8: 5 else: 3" "" "5";
    t "if2" "if 0 > 1: 4 else: 2" "" "2";

    terr "overflow" "add1(5073741823000000000)" "" "overflow";

    (* tvg "funcalls" "def fact(n): if n < 2: 1 else: n * fact(n - 1)\n\nfact(5)" "" "120" *)
  ]

let free_vars_tests = [
  tfvs "tfvs_simple_none" []
    "let a = 5, b = 10 in a + b"
    [];
  tfvs "tfvs_simple_some" []
    "let a = 5 in a + b"
    ["b"];
  tfvs "tfvs_let_rec" []
    "let rec a = 5 in a + b"
    ["b"];
  tfvs "tfvs_if" []
    "if a: b else: c"
    ["a"; "b"; "c"];
  tfvs "tfvs_prim1" []
    "print(a)"
    ["a"];
  tfvs "tfvs_app" []
    "abcd(efgh(123, r))"
    ["abcd"; "efgh"; "r"];
  tfvs "tfvs_imm" []
    "q"
    ["q"];
  tfvs "tfvs_tuple" []
    "(a, b, 123)"
    ["a"; "b"];
  tfvs "tfvs_get" []
    "(1, 2, 3)[a]"
    ["a"];
  tfvs "tfvs_set" []
    "(1, 2, 3)[1] := a"
    ["a"];
  tfvs "tfvs_lambda" []
    "(lambda(x, y): x + y + z)"
    ["z"];
  tfvs "tfvs_ignored" ["ignored"]
    "(lambda(x, y): x + y + z + ignored)"
    ["z"];
  tfvs "tfvs_lambda_body" ["x"]
    "x"
    [];
  tfvs "tfvs_lambda_body_2" ["x"; "y"]
    "x + y + z"
    ["z"];
  tfvs "lambda_body_with_frees" ["y"]
    "x + y"
    ["x"];
  tfvs "lambda_body_with_frees_2" ["x"; "y"]
    "(lambda (x): x)(5) + x + y"
    [];
];;

let wf_tests = [
  te "wf_lambda_unbound_id" "(lambda (x): y)" (print_te [UnboundId("y",
                                                                   (create_ss "wf_lambda_unbound_id" 1 13 1 14))]);
  te "wf_lambda_app_unbound_id" "(lambda (x): y)(5)" (print_te [UnboundId("y",
                                                                          (create_ss "wf_lambda_app_unbound_id" 1 13 1 14))]);
  te "wf_lambda_dup_args" "(lambda (x, x): x)" (print_te [DuplicateId("x", (create_ss "wf_lambda_dup_args" 1 12 1 13),
                                                                      (create_ss "wf_lambda_dup_args" 1 9 1 10))]);
  te "wf_lambda_app_dup_args" "(lambda (x, x): x)(5, 5)" (print_te [DuplicateId("x", (create_ss "wf_lambda_app_dup_args" 1 12 1 13),
                                                                                (create_ss "wf_lambda_app_dup_args" 1 9 1 10))]);
  te "wf_letrec_dup" "let rec x = 5, x = 6 in x" (print_te [DuplicateId("x", (create_ss "wf_letrec_dup" 1 8 1 13),
                                                                        (create_ss "wf_letrec_dup" 1 15 1 20))]);
  te "wf_letrec_unbound_id" "let rec x = 5 in y" (print_te [UnboundId("y", (create_ss "wf_letrec_unbound_id" 1 17 1 18))]);
  t "wf_letrec" "let rec x = y, y = x in 6" "" "6";
  te "wf_unrelated_in_lambda_in_lambda" "(lambda (x): (lambda (y): (let z = 5, z = 6 in z)))(5, 5)" (print_te [DuplicateId("z", (create_ss "wf_unrelated_in_lambda_in_lambda" 1 38 1 39),
                                                                                                                           (create_ss "wf_unrelated_in_lambda_in_lambda" 1 31 1 32))]);
]

let call_type_tests = [
  tct "tct_prims" 
    "print(5 + 5)"
    "\nprint((5 + 5))";
  tct "tct_natives"
    "equal(5, 25); print(25)"
    "\n(*equal(5, 25)); print(25)";
  tct "tct_non_natives"
    "def test(a, b): a + b
    (lambda(b, a): test(a, b))(5, 25)"
    "(def test(a_3, b_4):
  (a_3 + b_4))
((lam(b_16, a_17) (test(a_17, b_16)))(5, 25))";
]

let tanf_tests = [
  tanf_improved "tct_lambda_frees" 
    "let x = 5, y = (lambda(y): x + y) in y(6)"
    "(alet x_4 = 5 in (alet y_7 = (lam(y_12) (x_4 + y_12)) in (y_7(6))))";
  tanf_improved "native_in_lambda" 
    "(lambda (x): print(x))(5)"
    "(alet lam_4 = (lam(x_7) print(x_7)) in (lam_4(5)))";
  tanf_improved "call_in_lambda"
    "let f = (lambda (x): x) in (lambda (y): f(y))(6)"
    "(alet f_4 = (lam(x_7) x_7) in (alet lam_10 = (lam(y_14) (f_4(y_14))) in (lam_10(6))))";
  tanf_improved "tct_lambda_in_lambda"
    "(lambda (x, y): (lambda (x): x)(5) + x + y)(5, 10)"
    ("(alet lam_5 = (lam(x_15, y_16) (alet lam_10 = (lam(x_12) x_12) in " ^
     "(alet app_8 = (lam_10(5)) in (alet binop_7 = (app_8 + x_15) in " ^
     "(binop_7 + y_16))))) in (lam_5(5, 10)))");
  tanf_improved "sequence" "print(1); print(2)" "(alet unary_5 = print(1) in print(2))";
  tanf_improved "compile_native_in_closure_multiple_args_anf" 
    "(lambda (x, y): print(y))(1, 6)"
    "(alet lam_5 = (lam(x_8, y_9) print(y_9)) in (lam_5(1, 6)))";
  tanf_improved "anf_input" "input()" "(alet lam_3 = (lam() (*input())) in (lam_3()))";
  tanf_improved "anf_lambda" "let lam = (lambda: 1) in lam()" "(alet lam_4 = (lam() 1) in (lam_4()))";
  tanf_improved "anf_native" "let a = (lambda: input()) in a()" "(alet a_4 = (lam() (alet lam_7 = (lam() (*input())) in (lam_7()))) in (a_4()))";
]

let func_call_params_tests = [
  "get_func_call_params_no_closure_args">::(fun _ -> 
      assert_equal [
        ("1", Reg(RDI));
        ("2", Reg(RSI));
        ("3", Reg(RDX));
        ("4", Reg(RCX));
        ("5", Reg(R8));
        ("6", Reg(R9));
        ("7", RegOffset(16, RBP));
      ] (get_func_call_params 
           ["1"; "2"; "3"; "4"; "5"; "6"; "7"] [])
        ~printer:arg_envt_printer);
  "get_func_call_params_closure_args">::(fun _ -> 
      assert_equal [
        ("1", Reg(RDI));
        ("2", Reg(RSI));
        ("3", Reg(RDX));
        ("4", Reg(RCX));
        ("5", Reg(R8));
        ("6", Reg(R9));
        ("7", RegOffset(16, RBP));
        ("8", RegOffset(~-8, RBP));
        ("9", RegOffset(~-16, RBP));
      ] (get_func_call_params 
           ["1"; "2"; "3"; "4"; "5"; "6"; "7"] ["8"; "9"])
        ~printer:arg_envt_printer);
]

let compile_tests = [
  t "compile_lambda_1_noapp" "(lambda (x): x)" "" "<function>";
  t "compile_lambda_2_noapp" "(lambda (x): (lambda (x): x))" "" "<function>";
  t "compile_lambda_noarg" "(lambda: 1)()" "" "1";
  t "compile_lambda_0_in_let" "let a = (lambda: 6) in a()" "" "6";
  t "compile_lambda_1" "(lambda (x): x)(5)" "" "5";
  t "compile_lambda_1_in_let" "let a = (lambda (x): x) in a(5)" "" "5";
  t "compile_lambda_2" "(lambda (x, y): x + y)(5, 10)" "" "15";
  t "compile_lambda_3" "(lambda (x, y): add1(x) + add1(y))(5, 10)" "" "17";
  t "compile_lambda_in_lambda" "(lambda (x, y): (lambda (x): x)(5) + x + y)(5, 10)" "" "20";
  t "compile_decl" "def x(f): f + 3\n(lambda (x, y): x + y)(5, 10) + x(3)" "" "21";
  te "invalid_arity" "(lambda (x): x)(5, 6)" "arity mismatch in call";
  (* closure tests *)
  t "compile_decl_with_frees"
    "let x = 5, y = (lambda(y): x + y) in y(6)" "" "11";
  t "compile_frees_2"
    "let x = 5, y = (lambda(y): (lambda(z): x + y + z)) in y(4)(3)"
    "" "12";
  t "y_combinator" "let y = (lambda (f): (lambda (x): x(x))((lambda (x): f((lambda (y): x(x)(y)))))), 
    fact = (lambda (f): (lambda (x): (if x == 1: 1 else: x * f(x - 1)))) in
    y(fact)(3)" "" "6";
  t "ocsh" "def our_code_starts_here(): 5\nour_code_starts_here()" "" "5";
]

let let_rec_tests = [
  t "compile_lambda_recursion"
    "let rec y = (lambda(arg): if arg == 0: 0 else: 1 + y(1 - arg)) in y(4)"
    "" "4";
  t "compile_lambda_mutual_recursion"
    "let rec x = (lambda(arg): if arg == 0: 0 else: 1 + y(1 - arg)), y = (lambda(arg): if arg == 0: 0 else: 1 + x(1 - arg)) in y(4)"
    "" "4";
  t "compile_decl" "def a(x): x\n a(1)" "" "1";
]

let native_tests = [
  t "compile_native_1" "let _ = print(10) in print(100)" "" "10\n100\n100";
  t "compile_native_2" "let a = print((1, 2, 3)) in equal(a, (1, 2, 3))" "" "(1, 2, 3)\ntrue";
  t "compile_native_in_closure_let" "let a = (lambda (y): print(y)) in a(6)" "" "6\n6";
  t "compile_native_in_closure_noarg" "(lambda: print(6))()" "" "6\n6";
  t "compile_native_in_closure" "(lambda (y): print(y))(6)" "" "6\n6";
  t "compile_native_in_closure_temp" "let f = (lambda (x): x) in (lambda (y): f(y))(6)" "" "6";
  t "compile_native_in_closure_multiple_args" "(lambda (x, y): print(y))(1, 6)" "" "6\n6";
  t "compile_native_in_closure_more_args" "(lambda (x, y, z): print(z))(1, 1, 6)" "" "6\n6";
  tcontains "print_stack" "printStack(1)" "" "Num args: 0\n1";
  t "compile_native_as_free" "let a = input in a()" "1" "1";
  t "compile_input" "input()" "5" "5";
  t "compile_input_in_lambda" "let a = (lambda: input()) in a()" "5" "5";
  terr "arg_count_low" "(lambda (x): x)()" "" "arity mismatch in call";
  terr "arg_count_high" "(lambda: 1)(1)" "" "arity mismatch in call";
  (* will be fixed with closures *)
  terr "arg_count_native_low" "equal(1, 2, 3)" "" "arity mismatch in call";
  terr "arg_count_native_high" "equal(1, 2, 3)" "" "arity mismatch in call";
  terr "print_arity" "print(1, 2)" "" "Parse error at line 1, col 8: token `,`";
]

let sequencing_tests = [
  t "sequencing_1" "print(1); print(2)" "" "1\n2\n2";
  t "sequencing_2" "let _ = print(1) in print(2)" "" "1\n2\n2"
]


let suite =
  "suite">:::
  default_tests @
  free_vars_tests @
  wf_tests @
  compile_tests @
  call_type_tests @
  func_call_params_tests @
  let_rec_tests @
  native_tests @
  desugar_tests @
  tanf_tests @
  sequencing_tests
;;


let () =
  run_test_tt_main ("all_tests">:::[suite; (* old_tests; *) input_file_test_suite ()])
;;
