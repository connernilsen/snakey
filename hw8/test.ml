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
                                              let c = Stdlib.compare in
                                              let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
                                              assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print)
;;

let tdesugar (name : string) (program : string) (expected : string) = (check_name name)>:: fun _ ->
    assert_equal (expected ^ "\n") (string_of_program (desugar (tag (parse_string name program)))) ~printer:(fun s->s);;

let forty_one = "41";;

let forty_one_a = (AProgram(ACExpr(CImmExpr(ImmNum(41L, ()))), ()))

let test_prog = "let x = if sub1(55) < 54: (if 1 > 0: add1(2) else: add1(3)) else: (if 0 == 0: sub1(4) else: sub1(5)) in x"
let anf1 = (anf     (tag (parse_string "test" test_prog)))

let desugar_tests = [
  tdesugar "desugar_decl_one" "def f(x): x\nf(1)" "\n(let-rec f = (lam(x) x) in (?f(1)))";
  tdesugar "desugar_decl_two" "def f(x): x\ndef g(y, z, e): z + g\nf(1)" "\n(let-rec f = (lam(x) x) in (let-rec g = (lam(y, z, e) (z + g)) in (?f(1))))";
  tdesugar "desugar_decl_and" "def f(x): x and def g(y, z, e): z + g\nf(1)" "\n(let-rec f = (lam(x) x), g = (lam(y, z, e) (z + g)) in (?f(1)))";
  tdesugar "desugar_decl_with_destructure"
    "def f((a, b), c): ((a, b), c)\nf((1, 2), 3)"
    "\n(let-rec f = (lam(fun_arg#3, c) (let bind_temp3 = (fun_arg#3 check_size 2), a = bind_temp3[0], b = bind_temp3[1] in ((a, b), c))) in (?f((1, 2), 3)))";
  tdesugar "desugar_decl_with_destructure_and_blank"
    "def f((a, _), c): ((a,), c)\nf((1, 2), 3)"
    "\n(let-rec f = (lam(fun_arg#3, c) (let bind_temp3 = (fun_arg#3 check_size 2), a = bind_temp3[0], _ = bind_temp3[1] in ((a,), c))) in (?f((1, 2), 3)))";
  tdesugar "desugar_letrec"
    "let rec x = 5 in x"
    "\n(let-rec x = 5 in x)";
  tdesugar "desugar_lambda"
    "(lambda (x): x)"
    "\n(lam(x) x)";
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

    terr "scope_err1" "let x = true in (let y = (let x = false in x) in y)" "" "shadows one defined";

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

let compile_tests = [
  t "compile_lambda_1_noapp" "(lambda (x): x)" "" "<function>";
  t "compile_lambda_2_noapp" "(lambda (x): (lambda (x): x))" "" "<function>";
  t "compile_lambda_1" "(lambda (x): x)(5)" "" "5";
  t "compile_lambda_2" "(lambda (x, y): x + y)(5, 10)" "" "15";
  t "compile_lambda_in_lambda" "(lambda (x, y): (lambda (x): x)(5) + x + y)(5, 10)" "" "20";
  t "compile_decl" "def x(f): f + 3\n(lambda (x, y): x + y)(5, 10) + x(3)" "" "21";
  (* let rec tests *)
  (* free variable tests *)
]


let suite =
  "suite">:::
  (* default_tests @ *)
  desugar_tests @
  free_vars_tests @
  wf_tests @
  compile_tests
;;


let () =
  run_test_tt_main ("all_tests">:::[suite; input_file_test_suite ()])
;;
