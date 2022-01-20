open OUnit2
open Functions

(* This file contains some example tests.  Feel free to delete and reorganize
the unnecessary parts of this file; it is provided to match up with the given
writeup initially. *)

let check_fun _ = (* a function of one argument containing a successful test *)
  assert_equal (2 + 2) 4;;

let check_fun2 _ = (* a failing test *)
  assert_equal (2 + 2) 5;;

(* a helper for testing integers *)
let t_int name value expected = name>::
  (fun _ -> assert_equal expected value ~printer:string_of_int);;

(* Feel free to add any new testing functions you may need *)


let my_first_test = "my_first_test">::check_fun;;
let my_second_test = "my_second_test">::check_fun2;;
let my_third_test = t_int "my_third_test" (2 + 2) 7;;
let my_fourth_test = t_int "my_fourth_test" (2 + 2) 4;;

(* Max tests *)
let max_test_0_0 = t_int "max_test_0_0" (max 0 0) 0;;
let max_test_1_0 = t_int "max_test_1_0" (max 1 0) 1;;
let max_test_0_1 = t_int "max_test_0_1" (max 0 1) 1;;
let max_test_11_5 = t_int "max_test_11_5" (max 11 5) 11;;
let max_test_5_11 = t_int "max_test_5_11" (max 5 11) 11;;
let max_test_1123_1123 = t_int "max_test_1123_1123" (max 1123 1123) 1123;;


(* Fibonacci tests *)
let fib_test_0 = t_int "fib_test_0" (fibonacci 0) 0;;
let fib_test_1 = t_int "fib_test_1" (fibonacci 1) 1;;
let fib_test_2 = t_int "fib_test_2" (fibonacci 2) 1;;
let fib_test_3 = t_int "fib_test_3" (fibonacci 3) 2;;
let fib_test_9 = t_int "fib_test_9" (fibonacci 9) 34;;
let fib_test_12 = t_int "fib_test_12" (fibonacci 12) 144;;


let suite = "suite">:::[
  my_first_test;
  (* my_second_test; *)
  (* my_third_test; *)
  (* my_fourth_test; *)
  (* add more tests here *)
  max_test_0_0;
  max_test_0_1;
  max_test_1_0;
  max_test_11_5;
  max_test_5_11;
  max_test_1123_1123;
  fib_test_0;
  fib_test_1;
  fib_test_2;
  fib_test_3;
  fib_test_9;
  fib_test_12;
  ];;

run_test_tt_main suite