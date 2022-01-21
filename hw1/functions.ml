
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
  | Node(_, left, right) -> 1 + (max (height left) (height right));;

(* Returns a new list with the values of the given list incremented by 1 *)
let rec increment_all (ls : int list): int list =
  match ls with
  | [] -> []
  | first :: rest -> first + 1 :: (increment_all rest);;
