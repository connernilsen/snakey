open Compile
open Runner
open Printf
open OUnit2
open ExtLib
open Sexp

(* make sure test names are valid, and return the passed in test name *)
let t_name (name : string) : string =
  if (String.contains name ' ') then
    failwith (sprintf "Invalid test name, must contain no spaces: %s" name)
  else name 
;;

(* A helper for testing primitive values (won't print datatypes well) *)
let t_any name value expected = (t_name name) >:: fun _ -> assert_equal expected value ~printer:dump

(* Runs a program, given as a source string, and compares its output to expected *)
let t (name : string) (program : string) (expected : string) : OUnit2.test =
  (t_name name) >:: test_run program name expected

(* Runs a program, given as a source string, and compares its error to expected *)
let te (name : string) (program : string) (expected_err : string) : OUnit2.test =
  (t_name name) >:: test_err program name expected_err

(* Runs a program, given as the name of a file in the input/ directory, and compares its output to
   expected *)
let ti (filename : string) (expected : string) = filename >:: test_run_input filename expected

(* Runs a program, given as the name of a file in the input/ directory, and compares its error to
   expected *)
let tie (filename : string) (expected_err : string) =
  filename >:: test_err_input filename expected_err

let expr_of_sexp_tests =
  [ t_any "expr_of_sexp0" (expr_of_sexp (parse "1")) (Number (1L, (0, 0, 0, 1)));
    t_any "expr_of_sexp_add" (expr_of_sexp (parse "(add1 0)")) (Prim1 (Add1, Number (0L, (0, 6, 0, 7)), (0, 0, 0, 8))); 
    t_any "expr_of_sexp1"
      (expr_of_sexp (parse "(let ((x 1)) x)"))
      (Let ([("x", Number (1L, (0, 9, 0, 10)))], Id ("x", (0, 13, 0, 14)), (0, 0, 0, 15))); 
    t_any "expr_of_sexp2"
      (expr_of_sexp (parse "(let ((x (add1 5)) (y (sub1 x))) (add1 y))"))
      (Let
         ( [ ("x", Prim1 (Add1, Number (5L, (0, 15, 0, 16)), (0, 9, 0, 17))); 
             ("y", Prim1 (Sub1, Id ("x", (0, 28, 0, 29)), (0, 22, 0, 30))) ], 
           Prim1 (Add1, Id ("y", (0, 39, 0, 40)), (0, 33, 0, 41)), 
           (0, 0, 0, 42) ) ); 
    t_any "expr_of_let_empty" (expr_of_sexp (parse "(let () (add1 5))"))
      (Let ([], Prim1 (Add1, Number (5L, (0, 14, 0, 15)), (0, 8, 0, 16)), (0, 0, 0, 17)));
    t_any "expr_of_let_unknown_var" (expr_of_sexp (parse "(let () (add1 x))"))
      (Let ([], Prim1 (Add1, Id ("x", (0, 14, 0, 15)), (0, 8, 0, 16)), (0, 0, 0, 17)));
    t_any "expr_of_nested_let" (expr_of_sexp (parse "(let ((x (add1 5)) (y (let ((z (add1 x))) (add1 z)))) y)"))
      (Let ([("x", Prim1 (Add1, Number (5L, (0, 15, 0, 16)), (0, 9, 0, 17))); 
             ("y", Let (
                 [("z", Prim1 (Add1, Id ("x", (0, 37, 0, 38)), (0, 31, 0, 39)))], 
                 Prim1 (Add1, Id ("z", (0, 48, 0, 49)), (0, 42, 0, 50)), (0, 22, 0, 51)))],
            Id ("y", (0, 54, 0, 55)), (0, 0, 0, 56)));
    te "expr_of_sexp_bool_t" "true" 
      "Booleans not defined in lang found at line 0, col 0--line 0, col 4"; 
    te "expr_of_sexp_bool_f" "false" 
      "Booleans not defined in lang found at line 0, col 0--line 0, col 5"; 
    te "expr_of_sexp_bind_number" "(let ((2 5)) 5)" 
      "Incorrect let syntax at line 0, col 6--line 0, col 11. Expected `(Sym(id) expression)`, found `(Int{2} Int{5})`"; 
    te "expr_of_sexp_nums" "(2 5)" 
      "Incorrect syntax. Expected logical expression in parens, found `(Int{2} Int{5})` at line 0, col 0--line 0, col 5"; 
    te "expr_of_sexp_let_bad_bindings" "(let (5) 5)" 
      "Incorrect let syntax at line 0, col 6--line 0, col 7. Expected `(Sym(id) expression)`, found `Int{5}`";
    te "expr_of_sexp_empty_nest" "()" 
      "Incorrect syntax. Expected logical expression in parens, found `()` at line 0, col 0--line 0, col 2";
    te "expr_of_nested_nest" "((1))" "Incorrect syntax. Expected logical expression in parens, found `(Parens{(Int{1})})` at line 0, col 0--line 0, col 5"; 
    te "expr_of_sexp_empty_add1" "(add1)" "Incorrect syntax. Expected logical expression in parens, found `(Sym{add1})` at line 0, col 0--line 0, col 6";
    te "expr_of_sexp_empty_sub1" "(sub1)" "Incorrect syntax. Expected logical expression in parens, found `(Sym{sub1})` at line 0, col 0--line 0, col 6";
    te "expr_of_sexp_literal_in_let_args" "(let ((x 1) 5) x)"
      "Incorrect let syntax at line 0, col 12--line 0, col 13. Expected `(Sym(id) expression)`, found `Int{5}`";
    te "expr_of_sexp_add1_too_many_args" "(add1 1 2)"
      "Incorrect syntax. Expected logical expression in parens, found `(Sym{add1} Int{1} Int{2})` at line 0, col 0--line 0, col 10";
    te "expr_of_sexp_sub1_too_many_args" "(sub1 1 2)"
      "Incorrect syntax. Expected logical expression in parens, found `(Sym{sub1} Int{1} Int{2})` at line 0, col 0--line 0, col 10";
    te "expr_of_sexp_let_too_few_args" "(let 5)"
      "Incorrect syntax. Expected logical expression in parens, found `(Sym{let} Int{5})` at line 0, col 0--line 0, col 7";
    te "expr_of_sexp_let_too_many_args" "(let () 5 5)"
      "Incorrect syntax. Expected logical expression in parens, found `(Sym{let} Parens{()} Int{5} Int{5})` at line 0, col 0--line 0, col 12";
    te "expr_of_sexp_invalid_bind_args_type" "(let abcd (add1 2))"
      "Incorrect syntax. Expected logical expression in parens, found `(Sym{let} Sym{abcd} Parens{(Sym{add1}, Int{2})})` at line 0, col 0--line 0, col 19";
    t_any "expr_of_sexp_shadowing" (expr_of_sexp (parse "(let ((x 5) (x (add1 x))) (let ((x (add1 x))) x))"))
      (Let ([("x", Number(5L, (0, 9, 0, 10))); ("x", Prim1 (Add1, Id ("x", (0, 21, 0, 22)), (0, 15, 0, 23)))],
            Let ([("x", Prim1 (Add1, Id ("x", (0, 41, 0, 42)), (0, 35, 0, 43)))], Id ("x", (0, 46, 0, 47)), (0, 26, 0, 48)),
            (0, 0, 0, 49)));
  ]

let compile_env_tests =
  [t_any "compile_env_simple" (compile (Number (1L, (0, 9, 0, 10)))) [IMov (Reg RAX, Const 1L)];
   t_any "compile_env_add1" (compile (expr_of_sexp (parse "(add1 1)"))) [IMov (Reg RAX, Const 1L);IAdd (Reg RAX, Const 1L)];
   t_any "compile_env_simple_let" (compile (expr_of_sexp (parse "(let ((x 1)) x)"))) [IMov (Reg RAX, Const 1L);IMov (RegOffset (~-1, RSP), Reg RAX);IMov  (Reg RAX, RegOffset (~-1, RSP));];
   t_any "compile_env_multi_let" (compile (expr_of_sexp (parse "(let ((x 10) (y (add1 x)) (z (add1 y))) (add1 z))")))
     [IMov (Reg RAX, Const 10L); IMov (RegOffset (~-1, RSP), Reg RAX); 
      IMov (Reg RAX, RegOffset (~-1, RSP)); IAdd (Reg RAX, Const 1L); 
      IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L);
      IMov (RegOffset (~-3, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-3, RSP)); IAdd (Reg RAX, Const 1L)];
   t_any "compile_env_nested_let" (compile (expr_of_sexp (parse "(let ((a 10) (c (let ((b (add1 a)) (d (add1 b))) (add1 b)))) (add1 c))")))
     [IMov (Reg RAX, Const 10L); IMov (RegOffset (~-1, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-1, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-3, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L); 
      IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L)
     ];
   t_any "compile_env_nested_adds_and_subs" (compile (expr_of_sexp (parse "(sub1 (add1 (add1 42)))")))
     [IMov (Reg RAX, Const 42L); IAdd (Reg RAX, Const 1L); IAdd (Reg RAX, Const 1L); IAdd (Reg RAX, Const (Int64.neg 1L))];
   t_any "compile_env_empty_let" (compile (expr_of_sexp (parse "(let () (add1 5))")))
     [IMov (Reg RAX, Const 5L); IAdd (Reg RAX, Const 1L)];
   t_any "compile_env_let_with_empty_let" (compile (expr_of_sexp (parse "(let ((abcd (let () 5))) abcd)")))
     [IMov (Reg RAX, Const 5L); IMov (RegOffset (~-1, RSP), Reg RAX); IMov (Reg RAX, RegOffset (~-1, RSP))];
   te "compile_env_unbound" "x" "Unbound variable `x` referenced at line 0, col 0--line 0, col 1";
   te "compile_env_unbound_with_others_bound" "(let ((x 5)) y)" "Unbound variable `y` referenced at line 0, col 13--line 0, col 14";
   t_any "compile_env_let_in_let_expr" (compile (expr_of_sexp (parse "(let ((a 10)) (let ((b (add1 a))) (let ((c (add1 b))) (let ((d (add1 b))) (add1 c)))))")))
     [IMov (Reg RAX, Const 10L); IMov (RegOffset (~-1, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-1, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-3, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-4, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-3, RSP)); IAdd (Reg RAX, Const 1L); 
     ];
   t_any "compile_env_atom" (compile (expr_of_sexp (parse "5"))) [IMov (Reg RAX, Const 5L)];
   t_any "compile_env_x_in_scope_with_y_let" (compile (expr_of_sexp (parse "(let ((x (add1 5)) (y (let ((z (add1 x))) (add1 z)))) y)")))
     [IMov (Reg RAX, Const 5L); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-1, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-1, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP))
     ];
   te "compile_env_y_not_in_scope_in_y_let" "(let ((x (add1 5)) (y (let ((z (add1 y))) (add1 z)))) y)"
     "Unbound variable `y` referenced at line 0, col 37--line 0, col 38";
   te "compile_env_z_not_in_scope_after_y_let" "(let ((x (add1 5)) (y (let ((z (add1 x))) (add1 z)))) z)"
     "Unbound variable `z` referenced at line 0, col 54--line 0, col 55";
   t_any "compile_env_shadowing" (compile (expr_of_sexp (parse "(let ((x 5) (y 6)) (let ((y 7)) y))")))
     [IMov (Reg RAX, Const 5L); IMov (RegOffset (~-1, RSP), Reg RAX);
      IMov (Reg RAX, Const 6L); IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, Const 7L); IMov (RegOffset (~-3, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-3, RSP))
     ];
   t_any "compile_env_shadowing2" (compile (expr_of_sexp (parse "(let ((x 5) (x (add1 x))) (let ((x (add1 x))) x))")))
     [IMov (Reg RAX, Const 5L); IMov (RegOffset (~-1, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-1, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-2, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-2, RSP)); IAdd (Reg RAX, Const 1L); IMov (RegOffset (~-3, RSP), Reg RAX);
      IMov (Reg RAX, RegOffset (~-3, RSP))
     ];
  ]

let integration_tests =
  [t "test.simple" "1" "1";
   t "test.let" "(let ((x 5)) x)" "5";
   t "test.let.complex" "(let ((x 5) (y 6)) y)" "6";
   t "test.let.nested_let" "(let ((a 10) (c (let ((b (add1 a)) (d (add1 b))) (add1 b)))) (add1 c))" "13";
   t "test.let.emtpy_let" "(let () (add1 5))" "6";
   t "test.let.let_with_empty_let" "(let ((a (let () 5)) (b a)) b)" "5";
   t "test.compile_env_atom" "5" "5";
   ti "test1.adder" "2";
   ti "test2.adder" "1008";
   ti "test3.adder" "13";
   t "test.let.shadowing" "(let ((x 5) (y 6)) (let ((y 7)) y))" "7";
   t "test.let.rec1" "(let ((x 5) (y x)) y)" "5";
   t "test.let.rec2" "(let ((x 5) (y x)) x)" "5";
   t "test.let.scope" "(let ((x 5) (y x) (x y)) x)" "5";
   tie "test_error1.adder"
     "Unbound variable `y` referenced at line 0, col 37--line 0, col 38";
   tie "test_error2.adder"
     "Unbound variable `z` referenced at line 0, col 54--line 0, col 55";
   tie "test_error3.adder" 
     "Incorrect syntax. Expected logical expression in parens, found `(Sym{add1})` at line 0, col 0--line 0, col 6";
   tie "test_error4.adder" 
     "Unbound variable `sub1` referenced at line 0, col 0--line 0, col 4";
  ]

let all_tests = expr_of_sexp_tests @ compile_env_tests @ integration_tests

let suite : OUnit2.test = "suite" >::: all_tests

let () = run_test_tt_main suite
