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
let te name program expected_err = name>::test_err ~vg:false Naive program name expected_err;;
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
                                     let tagged = atag anfed in
                                     let fv: (Compile.StringSet.t * Exprs.tag) Exprs.aprogram = free_vars_cache tagged in 
                                     let str_list_print (strs, _) = 
                                       let strs = NeighborSet.elements strs in
                                       "[" ^ (ExtString.String.join ", " strs) ^ "]" in 
                                     let output = string_of_aprogram_with 1000 (str_list_print) fv in
                                     assert_equal expected output ~printer:(fun s -> s)) 
;; 

let tgcolor name graph init_env (expected: arg name_envt) = 
  name>::(fun _ -> 
      assert_equal expected (color_graph graph init_env) ~printer:(fun s->string_of_envt s))
let tgcolorint name program (expected: arg name_envt) = 
  name>::(fun _ -> 
      assert_equal expected (color_graph (let ast = parse_string name program in 
                                          let anfed = anf (rename_and_tag (tag ast)) in 
                                          let tagged = atag anfed in
                                          let fv = free_vars_cache tagged in 
                                          match fv with 
                                          | AProgram(body, _) -> 
                                            (interfere body StringSet.empty)) []) ~printer:(fun s->string_of_envt s))

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * (List.length Compile.native_fun_bindings)

let tstring = [
  t "tstring_simple" "\"test\"" "" "test";
  t "tstring_complex" "\"\"\"test
  test\"\"\"" "" "test\n  test";
  t "tstring_quotes" "\"test\\\"\"" ""
    "test\"";
  t "tstring_newline" "\"test\ntest\"" ""
    "test\ntest";
  t "tstring_seq" "\"t1\"; print(\"hey\"); \"t2\"" ""
    "heyt2";
  t "input_test" "input()" "hello" "hello";
  t "isstr_str" "isstr(\"hello\")" "" "true";
  t "isstr_num" "isstr(5)" "" "false";
  t "isstr_bool_t" "isstr(true)" "" "false";
  t "isstr_bool_f" "isstr(false)" "" "false";
  t "isstr_tuple" "isstr((1, 2, 3))" "" "false";
  t "isnum_str" "isnum(\"1\")" "" "false";
  t "isbool_str" "isnum(\"true\")" "" "false";
  t "istuple_str" "istuple(\"1\")" "" "false";
  t "tonum_int" "tonum(1)" "" "1";
  t "tonum_str" "tonum(\"1\")" "" "1";
  t "tonum_bool_f" "tonum(false)" "" "0";
  t "tonum_bool_t" "tonum(true)" "" "1";
  te "tonum_invalid_str" "tonum(\"a\")" "Error: invalid converseion \"a\"";
  t "tonum_empty_str" "tonum(\"\")" "" "0";
  t "tobool_boolf" "tobool(false)" "" "false";
  t "tobool_bool_t" "tobool(true)" "" "true";
  t "tobool_num_0" "tobool(0)" "" "false";
  t "tobool_num_1" "tobool(1)" "" "true";
  t "tobool_num_5" "tobool(5)" "" "true";
  t "tobool_str_t" "tobool(\"true\")" "" "true";
  t "tobool_str_f" "tobool(\"false\")" "" "false";
  te "tobool_invalid_str" "tobool(\"truee\")" "Error: invalid conversion \"truee\"";
]

let suite =
  "unit_tests">:::
  tstring

let () =
  run_test_tt_main ("all_tests">:::[
      suite; 
      (* old_tests; *)
      input_file_test_suite ()])
;;
