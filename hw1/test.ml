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

(* max tests *)
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

let t_string name value expected = name>::
  (fun _ -> assert_equal value expected ~printer:(fun str -> str));;

let a_node = Node("a", Leaf, Leaf);;
let b_node = Node("b", Leaf, Leaf);;
let c_node = Node("c", Leaf, Leaf);;
let a_left = Node("b", a_node, Leaf);;
let c_right = Node("b", Leaf, c_node);;
let balanced = Node("b", a_node, c_node);;
let deep_left = Node("c", a_left, Leaf);;
let deep_right = Node("a", Leaf, c_right);;
let balanced_deep = 
  Node("d", Node("c", Node("a", Leaf, Leaf), Node("b", Leaf, Leaf)), 
    Node("f", Node("e", Leaf, Leaf), Node("g", Leaf, Leaf)));;

(* inorder_str tests *)
let inorder_str_empty = 
  t_string "inorder_str_empty" (inorder_str Leaf) "";;
let inorder_str_empty_node =
  t_string "inorder_str_empty_node" (inorder_str (Node("", Leaf, Leaf))) "";;
let inorder_str_root_val =
  t_string "inorder_str_a_node" (inorder_str a_node) "a";;
let inorder_str_root_left_val =
  t_string "inorder_str_a_left" (inorder_str a_left) "ab";;
let inorder_str_root_right_val =
  t_string "inorder_str_a_right" (inorder_str c_right) "bc";;
let inorder_str_right_left_val = 
  t_string "inorder_str_balanced" (inorder_str balanced) "abc";;
let inorder_str_deep_left =
  t_string "inorder_str_deep_left" (inorder_str deep_left) "abc";;
let inorder_str_deep_right = 
  t_string "inorder_str_deep_right" (inorder_str deep_right) "abc";;
let inorder_str_balanced_deep = 
  t_string "inorder_str_balanced_deep" (inorder_str balanced_deep) "abcdefg";;

(* size tests *)
let size_empty = t_int "size_empty" (size Leaf) 0;;
let size_root = t_int "size_root" (size a_node) 1;;
let size_nested_left = t_int "size_nested_left" (size a_left) 2;;
let size_nested_right = t_int "size_nested_right" (size c_right) 2;;
let size_balanced = t_int "size_balanced" (size balanced) 3;;
let size_deep_left = t_int "size_deep_left" (size deep_left) 3;;
let size_deep_right = t_int "size_deep_right" (size deep_right) 3;;
let size_balanced_deep = t_int "size_balanced_deep" (size balanced_deep) 7;;

(* depth tests *)
let height_empty = t_int "height_empty" (height Leaf) 0;;
let height_root = t_int "height_root" (height a_node) 1;;
let height_nested_left = t_int "height_nested_left" (height a_left) 2;;
let height_nested_right = t_int "height_nested_right" (height c_right) 2;;
let height_balanced = t_int "height_balanced" (height balanced) 2;;
let height_deep_left = t_int "height_deep_left" (height deep_left) 3;;
let height_deep_right = t_int "height_deep_right" (height deep_right) 3;;
let height_balanced_deep = t_int "height_balanced_deep" (height balanced_deep) 3;;
let height_unbalanced_deep = 
  t_int "height_unbalanced_deep" (height (Node("h", balanced_deep, Node("i", Leaf, Leaf)))) 4;;

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
  inorder_str_empty;
  inorder_str_empty_node;
  inorder_str_root_val;
  inorder_str_root_left_val;
  inorder_str_root_right_val;
  inorder_str_right_left_val;
  inorder_str_deep_left;
  inorder_str_deep_right;
  size_empty;
  size_root;
  size_nested_left;
  size_nested_right;
  size_balanced;
  size_deep_left;
  size_deep_right;
  size_balanced_deep;
  height_empty;
  height_root;
  height_nested_left;
  height_nested_right;
  height_balanced;
  height_deep_left;
  height_deep_right;
  height_balanced_deep;
  height_unbalanced_deep;
  ];;

run_test_tt_main suite