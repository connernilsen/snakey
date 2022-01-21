open Printf

(*

  This is a datatype that describes simple algebra expressions.

  For example, the expression

    5 * 3 + y
  
  would be represented as

    Plus(Times(Num(5), Num(3)), Variable("y"))

  Note that the multiplication is inside the addition because the order of
  operations demands that we do it first.


  Here are some other examples:

    1 + x               Plus(Num(1), Variable("x"))
    x + x               Plus(Variable("x"), Variable("x"))
    5(y + 10)           Times(Num(5), Plus(Variable("y"), Num(10)))

*)

type arith =
  | Plus of arith * arith
  | Times of arith * arith
  | Variable of string
  | Num of int


(**
  To represent the set of known variables, we're going to use a 
  simple list representation: (string * int) list
 *)
type env = (string * int) list

(**
  To use such an environment, we need to be able to `add` new variables
  to an environment (which produces a *new* environment), and we need
  to `get` the values of variables in an environment. We may also want
  to check whether an environment `contains` a particular variable.

  Notice that I described this as a *set*, which implies no duplicate
  variable names, but the list type above can certainly have such
  duplicates.  You need to decide how to handle such duplication.
  One solution will be markedly easier than the alternatives!

  Additionally, for `get`, we need to handle the case where the variable 
  is not found.
 *)

(* Implement the following three functions.  If needed, you may define them
   recursively, so uncomment out the `rec` keyword. *)

(* Get the given variable named x in the given env; if it is not found, return None;
  If there are duplicate keys in the env, then the first key found will be returned 
*)
let rec get (env : env) (x : string) : int option =
  match env with
  | [] -> None
  | (name, value) :: rest -> if name = x then Some(value) else (get rest x)
;;
(* Determine if the given env contains a variable named x *)
let rec contains (env : env) (x : string) : bool =
  match env with
  | [] -> false
  | (name, _) :: rest -> if name = x then true else (contains rest x)
;;
(* Add the given key-value pair to a copy of the given env;
  If the key being added already exists in the env, then the already
    existing key will be replaced;
  If the key does not exist, it is added at the end of the env list 
*)
let rec add (env : env) (x : string) (xVal : int) : env =
  match env with
  | [] -> (x, xVal) :: []
  | (name, itemVal) :: rest -> 
    (* if x is this key, then replace it, otherwise continue on *)
    if name = x then (x, xVal) :: rest else (name, itemVal) :: (add rest x xVal)
;;
             
(*
  Next, write evaluate, which takes an arithmetic expression and 
  an environment mapping from strings to integers, and evaluate the expression,
  using the given integer value for the variable.
  
  For example
  
     evaluate
       (Times(Plus(Variable("x"), Variable("y")), Num(5)))
       [("x", 5); ("y", 7)]

  should produce 60, and

     evaluate (Plus(Num(4), Num(5))) []

  should produce 9.
  
  If there is a variable not contained in vars in the expression, throw an
  exception with failwith.

*)

(* Evaluate the given arithmetic expression, given the variables 
    provided in the environment;
  If a variable appears in the given arith that is not found in the given env,
    then a Failure exception will be raised
*)
let rec evaluate (a : arith) (vars : env) : int =
  match a with
  (* return x *)
  | Num(x) -> x
  (* find and return x or raise exception *)
  | Variable(x) -> 
    (match get vars x with
    (* If var can't be found, raise exception *)
     | None -> failwith (sprintf "Could not find name %s in env" x)
     | Some(value) -> value)
  (* add a and b after evaluation *)
  | Plus(a, b) -> (evaluate a vars) + (evaluate b vars)
  (* multiply a and b after evaluation *)
  | Times(a, b) -> (evaluate a vars) * (evaluate b vars)
;;

(*
  Next, write pretty, which takes an arithmetic expression and renders it in
  mathematical notation.

  It should print with minimal parentheses, assuming standard order of
  operations where multiplication binds more tightly than addition.

  Further, if there is a multiplication of a variable, it should be
  pretty-printed by putting the coefficient adjacent, for example:

    pretty (Plus(Plus(Times(Plus(Num(5), Variable("y")), Variable("x")), Num(2)), Num(1)))
  
  should pretty-print as

    (5 + y)x + 2 + 1

  HINT: it may be helpful to write a helper that keeps track of whether the
  current expression is part of of plus or times expression as an additional
  argument.

  NOTE: I expect lots of questions about "how pretty" your solution "has" to
  be.  See how well you can do – I'm not giving a formal specification of
  exactly what form you need to produce, though examples like the one above
  should work nicely.  There are several reasonable answers here.
*)

(* Determine if the given arith's edge most node is a num type (nested
    within 0 or more Times types);
  The left-most node will only be followed recursively through Times types, 
    so if a Plus recursive type is found, then false is returned;
  find_left specifies whether to search whether the left-most node
    is a num, otherwise the right-most node is checked;
  This function is useful for determining if two number nodes are adjacent
    to each other in the given arith tree, even if there are nested 
    sub-trees (e.g. (is_mult_edge_num left false) && (is_mult_edge_num right true)
    means that there will be two nums next to each other being multiplied)
*)
let rec is_mult_edge_num (a : arith) (find_left : bool) : bool =
  match find_left with
  (* check the left-most node *)
  | true -> 
    (match a with
     | Num(_) -> true
     (* search the left node of the Times type *)
     | Times(left, _) -> (is_mult_edge_num left find_left)
     (* don't search Variable or Plus types, since they're not relevant *)
     | _ -> false)
  (* check the right-most node *)
  | false ->
    (match a with
     | Num(_) -> true
     (* search the right node of the Times type *)
     | Times(_, right) -> (is_mult_edge_num right find_left)
     (* don't search Variable or Plus types, since they're not relevant *)
     | _ -> false)
;;

(* A helper for pretty that helps formatting Plusses nested in Times types 
  - Nums are converted to strings and returned
  - Variables are returned immediately
  - Plusses are formatted with parentheses if they're nested in a times type 
    (specified with mult_expr), and the nested values are converted to strings 
    with a " + " Between them in the returned string
  - Times values are placed directly next to each other unless the nested types
    would place two Nums adjacent to each other, in which case a " * " is placed in between
*)
let rec pretty_helper (a : arith) (mult_expr : bool) : string =
  match a with
  (* convert to string and return *)
  | Num(x) -> string_of_int x
  | Variable(x) -> x
  | Plus(x, y) -> 
    (match mult_expr with 
     (* if nested in a Times expression, parentheses are placed around the added values *)
     | true -> sprintf "(%s + %s)" (pretty_helper x false) (pretty_helper y false)
     (* if not nested, no parentheses are added *)
     | false -> sprintf "%s + %s" (pretty_helper x false) (pretty_helper y false))
  | Times(left, right) -> 
    (* if two nums would end up being placed next to each other, then add a " * " between the values *)
    if (is_mult_edge_num left false) && (is_mult_edge_num right true)
      then sprintf "%s * %s" (pretty_helper left true) (pretty_helper right true)
    (* otherwise, just print the values directly adjacent to each other *)
    else sprintf "%s%s" (pretty_helper left true) (pretty_helper right true)
;;

(* Pretty print the given arithmetic as a string;
  If variables are being multiplied by something, they're placed directly adjacent to
    what they're being multiplied by;
  If Nums are being multiplied by another Num, they're separated by " * ";
  If a Plus occurs within a Times, then the plus expression is wrapped by parentheses
*)
let pretty (a : arith) : string =
  pretty_helper a false
;;
