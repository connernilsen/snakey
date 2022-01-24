
(* Return the larger of the two provided numbers *)
let max (n : int) (m : int) : int =
  if n > m then n else m;;

(* Determines the nth number in the Fibonacci sequence *)
let rec fibonacci (n : int) : int =
  if n <= 1 then n
  else (fibonacci (n - 1)) + (fibonacci (n - 2));;

(* Fibonacci Evaluation
(fibonacci 3)

if 3 <= 1 then 3 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))

if false then 3 else (fibonacci (3 - 1)) + (fibonacci (3 - 2))

(fibonacci (3 - 1)) + (fibonacci (3 - 2))

(fibonacci 2) + (fibonacci 1)

(if 2 <= 1 then 2 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci 1)

(if false then 2 else (fibonacci (2 - 1)) + (fibonacci (2 - 2))) + (fibonacci 1)

((fibonacci 2 - 1) + (fibonacci 2 - 2)) + (fibonacci 1)

((fibonacci 1) + (fibonacci 0)) + (fibonacci 1)

(((if 1 <= 1 then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))) + (fibonacci 0))) + (fibonacci 1)

(((if true then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))) + (fibonacci 0))) + (fibonacci 1)

(1 + (fibonacci 0)) + (fibonacci 1)

(1 + (if 0 <= 1 then 0 else (fibonacci (0 - 1)) + (fibonacci (0 - 2)))) + (fibonacci 1)

(1 + (if true then 0 else (fibonacci (0 - 1)) + (fibonacci (0 - 2)))) + (fibonacci 1)

(1 + 0) + (fibonacci 1)

1 + (fibonacci 1)

1 + (if 1 <= 1 then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))))

1 + (if true then 1 else (fibonacci (1 - 1)) + (fibonacci (1 - 2))))

1 + 1

2
*)

(* A data structure representing a binary tree *)
type btnode =
  | Leaf
  | Node of string * btnode * btnode;;

(* Converts a btnode into a string, ordering the values as they're converted;
  if the given btnode is a Node, then the leftmost values are inserted into the returned
  string before the node's value, and the rightmost values are concatenated after *)
let rec inorder_str (bt : btnode) : string =
  match bt with
    | Leaf -> ""
    | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right);;

(* inorder_str evaluation 
let bt = Node("b", Node("a", Leaf, Leaf), Node("c", Leaf, Leaf))

(inorder_str bt)

match Node("b", Node("a", Leaf, Leaf), Node("c", Leaf, Leaf)) with
  | Leaf -> ""
  | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)

(inorder_str Node("a", Leaf, Leaf)) ^ "b" ^ (inorder_str Node("c", Leaf, Leaf))

(match Node("a", Leaf, Leaf) with
  | Leaf -> ""
  | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)
  ) ^ "b" ^ (inorder_str Node("c", Leaf, Leaf))

((inorder_str Leaf) ^ "a" ^ (inorder_str Leaf)) ^ "b" ^ (inorder_str Node("c", Leaf, Leaf))

((match Leaf with
  | Leaf -> ""
  | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)
  ) ^ "a" ^ (inorder_str Leaf)) ^ "b" ^ (inorder_str Node("c", Leaf, Leaf))

("" ^ "a" ^ (inorder_str Leaf)) ^ "b" ^ (inorder_str Node("c", Leaf, Leaf))

("a" ^ 
(match Leaf with
  | Leaf -> ""
  | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)
  )) ^ "b" ^ (inorder_str Node("c", Leaf, Leaf))

("a" ^ "") ^ "b" ^ (inorder_str Node("c", Leaf, Leaf))

"ab" ^ (inorder_str Node("c", Leaf, Leaf))

"ab" ^ 
(match Node("c", Leaf, Leaf) with
  | Leaf -> ""
  | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)
  ) 

"ab" ^ ((inorder_str Leaf) ^ "c" ^ (inorder_str Leaf))

"ab" ^
(match Leaf with
  | Leaf -> ""
  | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)
  ) ^ "c" ^ (inorder_str Leaf)

"ab" ^ ("" ^ "c" ^ (inorder_str Leaf))

"ab" ^
("c" ^ 
(match Leaf with
  | Leaf -> ""
  | Node(s, left, right) -> (inorder_str left) ^ s ^ (inorder_str right)
  )) 

"ab" ^ ("c" ^ "")

"abc"
*)

(* Counts the number of nodes in a btnode *)
let rec size (bt : btnode) : int =
  match bt with
  | Leaf -> 0
  | Node(_, left, right) -> 1 + (size left) +  (size right);;

(* Determines the height of a btnode by counting the longest path from the 
  root to any Node *)
let rec height (bt : btnode) : int =
  match bt with
  | Leaf -> 0
  (* add 1 to the larger of the height of the left and right nodes *)
  | Node(_, left, right) -> 1 + (max (height left) (height right));;

(* Returns a new list with the values of the given list incremented by 1 *)
let rec increment_all (ls : int list): int list =
  match ls with
  | [] -> []
  | first :: rest -> first + 1 :: (increment_all rest);;

(* Returns a new list where the strings in the given list have length greater than the given len *)
let rec long_strings (ls : string list) (len : int): string list = 
  match ls with
  | [] -> []
  | first :: rest ->
    (* keep first if it's greater than len, otherwise omit it *)
    if (String.length first) > len then first :: (long_strings rest len) else (long_strings rest len);;

(* Returns a new list containing every other element starting with the first 
  E.g 
  - [] should return []
  - [1] should return [1]
  - [1; 2] should return [1]
  - [1; 2; 3] should return [1; 3]
*)
let rec every_other (ls : 'a list): 'a list =
  match ls with
  | [] -> []
  (* match a list containing only one item *)
  | first :: [] -> first :: []
  (* match a list containing at least two items and drop the second item *)
  | first :: second :: rest -> first :: (every_other rest);;

(* Returns a list containing sums of integers from the nested list 
  E.g. 
  - [] should return []
  - [[]] should return [0]
  - [[1; 2]; [3]; []; [4; 5; 6]] should return [3; 3; 0; 15]
*)
let rec sum_all (ls : int list list): int list =
  match ls with
  | [] -> []
  | first :: rest -> 
    (* sum_list sums the int values of the given list 
      E.g. 
      - [] should return 0
      - [5] should return 5
      - [1; 2; 3] should return [6]
    *)
    let rec sum_list sub_ls =
      match sub_ls with
      | [] -> 0
      | first :: rest -> first + (sum_list rest) in
    (* sum the values in first with sum_list and continue handling rest with sum_all*)
    (sum_list first) :: (sum_all rest);;

(* An alternate version of sum_all that uses higher order functions
  Maps each sub-list using a fold on sub-list items to add them
*)
let sum_all_alternate (ls : int list list) : int list =
  (List.map (List.fold_left (+) 0) ls);;
