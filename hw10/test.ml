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

let tgcolor name graph init_env (expected: arg name_envt) = 
  name>::(fun _ -> 
      assert_equal expected (color_graph graph init_env) ~printer:(fun s->string_of_envt s))

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * (List.length Compile.native_fun_bindings)


let test_free_vars_cache = [
  tfvcs "tfvcs_simple_none" 
    "let a = 5, b = 10 in a + b"
    "(alet a = 5[] in (alet b = 10[] in (a[a] + b[b])[a, b])[a])[]\n[]";
  tfvcs "tfvcs_simple_some" 
    "let a = 5 in a + b"
    "(alet a = 5[] in (a[a] + b[b])[a, b])[b]\n[b]";
  tfvcs "tfvcs_let_rec" 
    "let rec a = 5 in a + b"
    "(aletrec a = 5[] in (a[a] + b[b])[a, b])[b]\n[b]";
  tfvcs "tfvcs_if" 
    "if a: b else: c"
    "(if a[a]: b[b] else: c[c])[a, b, c]\n[a, b, c]";
  tfvcs "tfvcs_prim1"
    "print(a)"
    "print(a[a])[a]\n[a]";
  tfvcs "tfvcs_app" 
    "abcd(efgh(123, r))"
    "(alet app_3 = (efgh[efgh](r[r], 123[]))[efgh, r] in (abcd[abcd](app_3[app_3]))[abcd, app_3])[abcd, efgh, r]\n[abcd, efgh, r]";
  tfvcs "tfvcs_imm" 
    "q"
    "q[q]\n[q]";
  tfvcs "tfvcs_tuple"
    "(a, b, 123)"
    "(123[], b[b], a[a])[a, b]\n[a, b]";
  tfvcs "tfvcs_get"
    "(1, 2, 3)[a]"
    "(alet tup_4 = (3[], 2[], 1[])[] in tup_4[tup_4][a[a]][a, tup_4])[a]\n[a]";
  tfvcs "tfvcs_set"
    "(1, 2, 3)[1] := a"
    "(alet tup_5 = (3[], 2[], 1[])[] in tup_5[tup_5][1[]] := a[a] [a, tup_5])[a]\n[a]";
  tfvcs "tfvcs_lambda"
    "(lambda(x, y): x + y + z)"
    "(lam(x, y) (alet binop_4 = (x[x] + y[y])[x, y] in (binop_4[binop_4] + z[z])[binop_4, z])[x, y, z])[z]\n[z]";
  tfvcs "tfvcs_ignored"
    "let ignored = 1 in (lambda(x, y): x + y + z + ignored)"
    ("(alet ignored = 1[] in (lam(x, y) (alet binop_9 = (x[x] + y[y])[x, y] in " ^
     "(alet binop_8 = (binop_9[binop_9] + z[z])[binop_9, z] in (binop_8[binop_8] " ^
     "+ ignored[ignored])[binop_8, ignored])[binop_9, ignored, z])[ignored, x, y, z])[ignored, z])[z]\n[z]");
  tfvcs "tfvcs_lambda_body"
    "x"
    "x[x]\n[x]";
  tfvcs "tfvcs_lambda_body_2"
    "x + y + z"
    "(alet binop_3 = (x[x] + y[y])[x, y] in (binop_3[binop_3] + z[z])[binop_3, z])[x, y, z]\n[x, y, z]";
  tfvcs "lambda_body_with_frees"
    "x + y"
    "(x[x] + y[y])[x, y]\n[x, y]";
  tfvcs "lambda_body_with_frees_2"
    "(lambda (x): x)(5) + x + y"
    ("(alet lam_6 = (lam(x) x[x])[] in (alet app_4 = (lam_6[lam_6](5[]))[lam_6] in (alet binop_3 = " ^
     "(app_4[app_4] + x[x])[app_4, x] in (binop_3[binop_3] + y[y])[binop_3, y])[app_4, x, y])[lam_6, x, y])[x, y]\n[x, y]");
  tfvcs "compile_lambda_recursion_tfvcs"
    "if arg == 0: 0 else: 1 + y(1 - arg)"
    ("(alet binop_3 = (arg[arg] == 0[])[arg] in (if binop_3[binop_3]: 0[] else: " ^
     "(alet binop_10 = (1[] - arg[arg])[arg] in (alet app_9 = (y[y](binop_10[binop_10]))[binop_10, y] in " ^
     "(1[] + app_9[app_9])[app_9])[binop_10, y])[arg, y])[arg, binop_3, y])[arg, y]\n[arg, y]");
  tfvcs "free_let_rec"
    "let rec x = (lambda: y()), y = (lambda: 6) in x()"
    "(aletrec y = (lam() 6[])[], x = (lam() (y[y]())[y])[y] in (x[x]())[x])[]\n[]";
  tfvcs "free_let_rec_in_lambda" 
    "(lambda(f): let rec x = (lambda: y()), y = (lambda: 6) in x())"
    "(lam(f) (aletrec y = (lam() 6[])[], x = (lam() (y[y]())[y])[y] in (x[x]())[x])[])[]\n[]";
  tfvcs "free_let_rec_in_lambda2" 
    "(lambda(f): let rec x = (lambda: y()), y = (lambda: 6) in x() + f)"
    ("(lam(f) (aletrec y = (lam() 6[])[], x = (lam() (y[y]())[y])[y] in " ^
     "(alet app_14 = (x[x]())[x] in (app_14[app_14] + f[f])[app_14, f])[f, x])[f])[]\n[]");
]


let test_graph_coloring = [
  tgcolor "color_empty" empty [] [];
  tgcolor "color_single" (add_node empty "1") [] [("1", Reg(R13))];
  tgcolor "color_two_larger_first" 
    (add_edge(add_edge (add_node (add_node (add_node empty "1") "2") "3")"1" "2") "1" "3")
    [] [("2", Reg(R14));("3", Reg(R14));("1", Reg(R13));];
  tgcolor "color_five_all_interference" 
    (add_edge (add_edge (add_edge (add_edge (add_edge(add_edge (add_edge (add_edge (add_edge (add_edge(add_edge (add_edge (add_edge (add_edge (add_edge(add_edge
                                                                                                                                                          (add_node (add_node (add_node (add_node (add_node empty "1") "2") "3") "4") "5") 
                                                                                                                                                          "1" "2") "1" "3") "1" "4") "1" "5")"2" "1") "2" "3") "2" "4") "2" "5")"3" "2") "3" "1") "3" "4") "3" "5")"4" "2") "4" "3") "4" "1") "4" "5")
    [] [("1", RegOffset(-16, RBP));("2", RegOffset(-8, RBP));("3", Reg(RBX)); ("4", Reg(R14));("5", Reg(R13))];
  tgcolor "color_five_no_interferes" 
    (add_node (add_node (add_node (add_node (add_node empty "1") "2") "3") "4") "5") 
    [] [("1", Reg(R13));("2", Reg(R13));("3", Reg(R13)); ("4", Reg(R13));("5", Reg(R13))];
]

let suite =
  "unit_tests">:::
  test_free_vars_cache
  @ test_graph_coloring



let () =
  run_test_tt_main ("all_tests">:::[
      suite; 
      (* old_tests; *)
      input_file_test_suite ()])
;;
