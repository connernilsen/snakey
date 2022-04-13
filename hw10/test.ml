open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Libtest

let t name program input expected = name>::test_run ~args:[] ~std_input:input Naive program name expected;;
let tr name program input expected = name>::test_run ~args:[] ~std_input:input Register program name expected;;
let ta name program input expected = name>::test_run_anf ~args:[] ~std_input:input program name expected;;
let tgc name heap_size program input expected = name>::test_run ~args:[string_of_int heap_size] ~std_input:input Naive program name expected;;
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

(* let tfvs name program expected = name>:: 
   (fun _ -> 
    let ast = parse_string name program in 
    let anfed = anf (tag ast) in 
    let vars = free_vars anfed [] in 
    let c = Stdlib.compare in 
    let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in 
    assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print) 
   ;;  *)

let tfvcs name program expected = name>:: 
                                  (fun _ -> 
                                     let ast = parse_string name program in 
                                     let anfed = anf (tag ast) in 
                                     let fv = free_vars_cache anfed in 
                                     let str_list_print strs = 
                                       let strs = StringSet.elements strs in
                                       "[" ^ (ExtString.String.join ", " strs) ^ "]" in 
                                     let output = string_of_aprogram_with 1000 (str_list_print) fv in
                                     assert_equal expected output ~printer:(fun s -> s)) 
;; 

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * (List.length Compile.native_fun_bindings)

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

let oom = [
  tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
  tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
  tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation";
]

let gc = [
  tgc "gc_lam1" (10 + builtins_size)
    "let f = (lambda: (1, 2)) in
       begin
         f();
         f();
         f();
         f()
       end"
    ""
    "(1, 2)";
]

let input = [
  t "input1" "let x = input() in x + 2" "123" "125"
]

let test_free_vars_cache = [
  tfvcs "tfvcs_simple_none" 
    "let a = 5, b = 10 in a + b"
    "(alet a = 5[] in (alet b = 10[] in (a[] + b[])[])[])[]\n[]";
  tfvcs "tfvcs_simple_some" 
    "let a = 5 in a + b"
    "(alet a = 5[] in (a[] + b[b])[b])[b]\n[b]";
  tfvcs "tfvcs_let_rec" 
    "let rec a = 5 in a + b"
    "(aletrec a = 5[] in (a[] + b[b])[b])[b]\n[b]";
  tfvcs "tfvcs_if" 
    "if a: b else: c"
    "(if a[a]: b[b] else: c[c])[a, b, c]\n[a, b, c]";
  tfvcs "tfvcs_prim1"
    "print(a)"
    "print(a[a])[a]\n[a]";
  tfvcs "tfvcs_app" 
    "abcd(efgh(123, r))"
    "(alet app_3 = (efgh[efgh](r[r], 123[]))[efgh, r] in (abcd[abcd](app_3[]))[abcd])[abcd, efgh, r]\n[abcd, efgh, r]";
  tfvcs "tfvcs_imm" 
    "q"
    "q[q]\n[q]";
  tfvcs "tfvcs_tuple"
    "(a, b, 123)"
    "(123[], b[b], a[a])[a, b]\n[a, b]";
  tfvcs "tfvcs_get"
    "(1, 2, 3)[a]"
    "(alet tup_4 = (3[], 2[], 1[])[] in tup_4[][a[a]][a])[a]\n[a]";
  tfvcs "tfvcs_set"
    "(1, 2, 3)[1] := a"
    "(alet tup_5 = (3[], 2[], 1[])[] in tup_5[][1[]] := a[a] [a])[a]\n[a]";
  tfvcs "tfvcs_lambda"
    "(lambda(x, y): x + y + z)"
    "(lam(x, y) (alet binop_4 = (x[] + y[])[] in (binop_4[] + z[z])[z])[z])[z]\n[z]";
  tfvcs "tfvcs_ignored"
    "let ignored = 1 in (lambda(x, y): x + y + z + ignored)"
    ("(alet ignored = 1[] in (lam(x, y) (alet binop_9 = (x[] + y[])[] in " ^
     "(alet binop_8 = (binop_9[] + z[z])[z] in (binop_8[] + ignored[])[])[z])[z])[z])[z]\n[z]");
  tfvcs "tfvcs_lambda_body"
    "x"
    "x[x]\n[x]";
  tfvcs "tfvcs_lambda_body_2"
    "x + y + z"
    "(alet binop_3 = (x[x] + y[y])[x, y] in (binop_3[] + z[z])[z])[x, y, z]\n[x, y, z]";
  tfvcs "lambda_body_with_frees"
    "x + y"
    "(x[x] + y[y])[x, y]\n[x, y]";
  tfvcs "lambda_body_with_frees_2"
    "(lambda (x): x)(5) + x + y"
    "(alet lam_6 = (lam(x) x[])[] in (alet app_4 = (lam_6[](5[]))[] in (alet binop_3 = (app_4[] + x[x])[x] in (binop_3[] + y[y])[y])[x, y])[x, y])[x, y]\n[x, y]";
  tfvcs "compile_lambda_recursion_tfvcs"
    "if arg == 0: 0 else: 1 + y(1 - arg)"
    ("(alet binop_3 = (arg[arg] == 0[])[arg] in (if binop_3[]: 0[] else: " ^
     "(alet binop_10 = (1[] - arg[arg])[arg] in (alet app_9 = (y[y](binop_10[]))[y] in " ^
     "(1[] + app_9[])[])[y])[arg, y])[arg, y])[arg, y]\n[arg, y]");
  tfvcs "free_let_rec"
    "let rec x = (lambda: y()), y = (lambda: 6) in x()"
    "(aletrec y = (lam() 6[])[], x = (lam() (y[]())[])[] in (x[]())[])[]\n[]";
  tfvcs "free_let_rec_in_lambda" 
    "(lambda(f): let rec x = (lambda: y()), y = (lambda: 6) in x())"
    "(lam(f) (aletrec y = (lam() 6[])[], x = (lam() (y[]())[])[] in (x[]())[])[])[]\n[]";
]


let suite =
  "unit_tests">:::
  pair_tests 
  @ oom 
  @ gc 
  @ input
  @ test_free_vars_cache



let () =
  run_test_tt_main ("all_tests">:::[
      suite; 
      (* old_tests; *)
      input_file_test_suite ()])
;;
