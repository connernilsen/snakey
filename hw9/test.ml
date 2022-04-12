open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Libtest

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

(* let tfvs name program expected = name>:: *)
(*   (fun _ -> *)
(*     let ast = parse_string name program in *)
(*     let anfed = anf (tag ast) in *)
(*     let vars = free_vars_P anfed [] in *)
(*     let c = Stdlib.compare in *)
(*     let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in *)
(*     assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print) *)
(* ;; *)

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
    "((4, 6), (4, 6))";
  t "tuple_of_function" "let t = ((lambda: 5),) in t[0]()" "" "5";
  terr "bad_destruct_func" "def new_func((a, v, bong, (e, w)), tree):
   if a: true else: bong + tree 
new_func((1, 2, 1, true), 1)" "" "unable to destructure tuple with incorrect length, got true";
  terr "bad_destruct" "let ((a, b), _) = (true, 0) in 0" "" "unable to destructure tuple with incorrect length, got true";
  terr "bad_tuple" "(true, 0)[0][0]" "" "get expected tuple, got true";
  terr "bad_destruct_2" "let (a, _) = true in 0" "" "unable to destructure tuple with incorrect length, got true";
  terr "nil_destruct" "let (a, b) = nil in a" "" "tried to access component of nil";
  terr "nil_tuple" "nil[0]" "" "tried to access component of nil";
]

let oom = [
  tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory";
  tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))";
  tvgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)";
  tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4)" "" "Allocation";
  tgcerr "oomgc5_in_let" (3 + builtins_size) "let x = (1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4) in x" "" "Allocation";
  tgcerr "oomgc5_in_blank_let" (3 + builtins_size) "let _ = (1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4) in 1" "" "Allocation";
  tgc "oomgc6" (6 + builtins_size)
    "let a = (1, 2, nil),
         _ = a[2] := a,
         _ = (9,),
         c = (3,) in 
        print(c);
        a"
    "" "(3, )\n(1, 2, <cyclic tuple 2>)";
  tgcerr "oomgc7" (5 + builtins_size)
    "let a = (1, 2, nil),
         _ = a[2] := a,
         _ = (9,),
         c = (3,) in 
        print(c);
        a"
    "" "Out of memory";
  tgc "oomgc8" (16 + builtins_size)
    "let ctr1 = (8,), # 2
         fn = (lambda(dummy):
            let rec 
               fn1 = # 6
                 (lambda(x): 
                   if ctr1[0] == 0: 
                     ctr1[0] := 50;
                     fn2(x, 72)
                   else:
                     ctr1[0] := ctr1[0] - 1;
                     fn1(x + 1)),
               fn2 = # 4
                 (lambda(y, z):
                   print(y);
                   print(z);
                   ctr1[0]) in
               fn1)(1) in 
      fn(1)"
    "" "9\n72\n50";
  tgcerr "oomgc9" (16 + builtins_size)
    "let ctr1 = (8,), # 2
         fn = (lambda(dummy):
            let rec 
               fn1 = # 6
                 (lambda(x): 
                   if ctr1[0] == 0: 
                     ctr1[0] := 50;
                     fn2(x, 72)
                   else:
                     ctr1[0] := ctr1[0] - 1;
                     fn1(x + 1)),
               fn2 = # 4
                 (lambda(y, z):
                   print(y);
                   print(z);
                   ctr1[0]) in
               fn1)(1) in 
      print(fn(1));
      print(ctr1);
      (1, 2, 3)"
    "" "Out of memory";
  tvgc "oomgc10" (20 + builtins_size)
    "let ctr1 = (8,), # 2
         fn = (lambda(dummy):
            let rec 
               fn1 = # 6
                 (lambda(x): 
                   if ctr1[0] == 0: 
                     ctr1[0] := 50;
                     fn2(x, 72)
                   else:
                     ctr1[0] := ctr1[0] - 1;
                     fn1(x + 1)),
               fn2 = # 4
                 (lambda(y, z):
                   print(y);
                   print(z);
                   ctr1[0]) in
               fn1)(1) in 
      print(fn(1));
      print(ctr1);
      (1, 2, 3)"
    "" "9\n72\n50\n(50, )\n(1, 2, 3)";
  tgc "oomgc11" (16 + builtins_size)
    "let ctr1 = (8,), # 2
         fn = (lambda(dummy):
            let rec 
               fn1 = # 6
                 (lambda(x): 
                   if ctr1[0] == 0: 
                     ctr1[0] := 50;
                     x
                   else:
                     ctr1[0] := ctr1[0] - 1;
                     fn1(x + 1)),
               fn2 = # 4
                 (lambda(y, z):
                   print(y);
                   print(z);
                   ctr1[0]) in
               fn1)(1) in 
      print(fn(1));
      print(ctr1);
      (1, 2, 3)"
    "" "9\n(50, )\n(1, 2, 3)";
  tgcerr "oomgc12" (15 + builtins_size)
    "let ctr1 = (8,), # 2
         fn = (lambda(dummy):
            let rec 
               fn1 = # 6
                 (lambda(x): 
                   if ctr1[0] == 0: 
                     ctr1[0] := 50;
                     x
                   else:
                     ctr1[0] := ctr1[0] - 1;
                     fn1(x + 1)),
               fn2 = # 4
                 (lambda(y, z):
                   print(y);
                   print(z);
                   ctr1[0]) in
               fn1)(1) in 
      fn(1)"
    "" "Out of memory";

  tgcerr "y_combinator_10_recursions_fails" (27 + builtins_size)
    "let y = (lambda (f): (lambda (x): x(x))((lambda (x): f((lambda (y): x(x)(y)))))), 
     fact = (lambda (f): (lambda (x): (if x == 1: 1 else: x * f(x - 1)))) in
    y(fact)(10)"  "" "Out of memory";

  tgcerr "tuple_of_function_in_closure_2_slots" (10 + builtins_size - 1)
    "let f = ((lambda: 5),) in (lambda: f[0]())"  "" "Out of memory";
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
  tgc "copy_nil_on_heap" (6 + builtins_size)
    "let a = (1, 2, nil),
             _ = (9,),
             c = (3,) in 
print(c);
a"
    "" "(3, )\n(1, 2, nil)";
  tgc "gcc_many_refs" (16 + builtins_size)
    "let x = (5,), # 2
         y = (1, nil), # 4
         _ = (y, y, y), # 4, should get gc'd
         z = (3, x, nil, y) in # 5
         y[1] := z;
z[2] := z;
(1,); # 2
         print(x);
print(y);
z"
    "" "(5, )\n(1, (3, (5, ), <cyclic tuple 3>, <cyclic tuple 2>))
(3, (5, ), <cyclic tuple 5>, (1, <cyclic tuple 5>))";
  tgc "copy_lambda_values" (18 + builtins_size)
    "let x = (lambda(x): 
         let y = (1, 2, x), 
             z = (4, 5, 6, 7) in 
           (lambda(x): y)) in
         let a = x(123), 
             b = (8, 9, 10) in 
         print(b);
         a(1)"
    "" "(8, 9, 10)\n(1, 2, 123)";

  tgc "one_hundred_gecs" (4 + 100 * 2 + builtins_size)
    "let rec x = (lambda(n): if n == 0: n else: let f = (1,) in x(n - 1))
      in x(100); x(100)" "" "0";

  tgc "one_thousand_gecs" (4 + 1000 * 2 + builtins_size)
    "let rec x = (lambda(n): if n == 0: n else: let f = (1,) in x(n - 1))
      in x(1000); x(1000)" "" "0";

  tgc "y_combinator_10_recursions" (28 * 4 + builtins_size)
    "let y = (lambda (f): (lambda (x): x(x))((lambda (x): f((lambda (y): x(x)(y)))))), 
     fact = (lambda (f): (lambda (x): (if x == 1: 1 else: x * f(x - 1)))) in
    y(fact)(10)"  "" "3628800";

  tgc "tuple_of_function" (6 + builtins_size)
    "((lambda: 5),)[0]()"  "" "5";

  tgc "tuple_of_function_in_closure" (6 + 4 + builtins_size)
    "let f = ((lambda: 5),) in (lambda: f[0]())()"  "" "5";

  tgc "tuple_of_function_in_closure_with_gc" (6 + 4 + 4 + builtins_size)
    "let f = ((lambda: 5),) in 
      (lambda(x): print((x, )))(4);
      print((6, 7, 8));
      f[0]()"  "" "(4, )\n(6, 7, 8)\n5";

  tgc "tuple_replace_memory" (12 + builtins_size) 
    "let x = (lambda: (1, 2, (1, 2, 3)))() in
         print(x);
         x[2] := 5;
         print(x);
         print((4, 5, 6));
         x"
    "" "(1, 2, (1, 2, 3))\n(1, 2, 5)\n(4, 5, 6)\n(1, 2, 5)";
  tgcerr "tuple_replace_memory_invalid" (8 + builtins_size) 
    "let x = (1, 2, (1, 2, 3)) in
         (4,)"
    "" "Out of memory";
]

let native = [
  t "input0" "input() + 2" "123" "125";
  t "print0" "print(125) + 2" "" "125\n127";
  t "input1" "let x = input() in x + 2" "123" "125";
  t "input2" "let x = input() in print(x + 2)" "123" "125\n125";
]

let prim = [
  t "prim1_in_lambda" "(lambda: 1 + 1)()" "" "2";
]

let nested = [
  t "lambda" "(lambda: 1)()" "" "1";
  t "nested_lambda" "(lambda: (lambda: 1)())()" "" "1";
  t "free_in_nested_fun" "let x = 5 in (lambda: (lambda: x)())()" "" "5";
]

let suite =
  "unit_tests">:::
  pair_tests 
  @ oom 
  @ gc 
  @ native 
  @ prim 
  @ nested



let () =
  run_test_tt_main ("all_tests">:::[
      suite;
      (* old_tests; *)
      input_file_test_suite ()])
;;
