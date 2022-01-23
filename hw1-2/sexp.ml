open Unix
open Str
open Printf

type 'a tok =
  | LPAREN of 'a
  | RPAREN of 'a
  | TSym of string * 'a
  | TInt of int * 'a
  | TBool of bool * 'a
let tok_info t =
  match t with
  | LPAREN x -> x
  | RPAREN x -> x
  | TSym (_, x) -> x
  | TInt (_, x) -> x
  | TBool (_, x) -> x
;;

(* startline, startcol, endline, endcol *)
type pos = int * int * int * int
let pos_to_string (startline, startcol, endline, endcol) range =
  if range then
    Printf.sprintf "line %d, col %d--line %d, col %d" startline startcol endline endcol
  else
    Printf.sprintf "line %d, col %d" startline startcol
;;
  
(* This function tokenizes a string into a list of pos toks.
  This occurs by creating a regex using (regexp "[()\n\t ]"), which splits on "(", ")", or 
  whitespace, then splitting the given string into Delims and Text, and finally folding
  over each item in the split list of tokens to create a list of tokens containing tok
  values and position information. Top-level current line number and col number are also incremented
  when returning from a fold_left 'iteration', so that the next fold_left 'iteration' will know
  where this token appears in the given string. In the fold_left call, if the current token
  is Text and not a boolean value, the function will try to convert it to an int in a try/with
  statement. If the value cannot be converted to an int, a Failure will be raised by
  string_of_int, caught by the with statement, and identified as a TSym.

  In depth explanation:
  - calling regexp with "[()\n\t ]" to create a regex matching parens and whitespace
  - calling full_split with that regex and the given string to separate it into a list of
    Delims (which are strings that matched the split regex) and Text (strings that didn't 
    match the regex)
  - folding over the returned list of Delims and Text from full_split and for each token, 
    using a match and if statements:
    (this passes the return value from each fold statement into the next fold statement, in
    which the list of tokens is prepended to, and the line and col are updated depending on 
    the token's value; it is initially called with an empty list and line/col values of 0)
    - if the token is whitespace, increment the line number or col number appropriately
      to be passed into the next fold_left call
    - if the token is "(" or ")", prepend the appropriate PAREN type onto the list of tokens
      with the token's pos and increment the col by 1 to be passed into the next fold_left call
    - if the token is "true" or "false", prepend a TBOOL containing the token's boolean value
      onto the list of tokens with the token's pos and increment col by the length of the token
    - otherwise, try to convert the token to an int using a try/with construct; if it succeeds,
      then prepend a TInt containing the token's int value onto the list of tokens with 
      col incremented by the length of the token; if it fails, then prepend a 
      TSym with the symbol's value and col incremented by the length of the token
  - reversing the tok list returned by fold_left, since new elements were prepended,
    leaving the returned toks list in reverse order
*)
let tokenize (str : string) : pos tok list =
  let (toks, _, _) = List.fold_left
    (fun ((toks : pos tok list), (line : int), (col : int)) (tok : Str.split_result) ->
      match tok with
      | Delim t ->
         if t = " " then (toks, line, col + 1)
         else if t = "\t" then (toks, line, col + 1)
         else if t = "\n" then (toks, line + 1, 0)
         else if t = "(" then (LPAREN (line, col, line, col + 1) :: toks, line, col + 1)
         else if t = ")" then (RPAREN (line, col, line, col + 1) :: toks, line, col + 1)
         else
           let tLen = String.length t
           in ((TSym (t, (line, col, line, col + tLen))) :: toks, line, col + tLen)
      | Text t ->
         if t = "true" then (TBool (true, (line, col, line, col + 4)) :: toks, line, col + 4)
         else if t = "false" then (TBool (false, (line, col, line, col + 5)) :: toks, line, col + 5)
         else
           let tLen = String.length t
           in try ((TInt (int_of_string t, (line, col, line, col + tLen))) :: toks, line, col + tLen) with
              | Failure _ -> (TSym (t, (line, col, line, col + tLen)) :: toks, line, col + tLen)
    )
    ([], 0, 0)
    (full_split (regexp "[()\n\t ]") str)
  in List.rev toks
;;

type 'a sexp =
  | Sym of string * 'a
  | Int of int * 'a
  | Bool of bool * 'a
  | Nest of 'a sexp list * 'a
let sexp_info s =
  match s with
  | Sym (_, x) -> x
  | Int (_, x) -> x
  | Bool (_, x) -> x
  | Nest (_, x) -> x
;;

type p_sexp_list = pos sexp list;;
type nest_acc_type = (p_sexp_list * pos) list;;



let rec parse_toks_helper (toks : pos tok list) (nest_acc : nest_acc_type) (ret_acc : p_sexp_list) : p_sexp_list =
  let append_and_continue (rest : pos tok list) (t_nest_acc : nest_acc_type) (t_ret_acc : p_sexp_list) (value : pos sexp) =
    match t_nest_acc with
    | [] -> parse_toks_helper rest [] (value :: t_ret_acc)
    | (nest_first, o_pos) :: nest_rest -> 
      parse_toks_helper rest ((value :: nest_first, o_pos) :: nest_rest) t_ret_acc
    in
  let rparen_helper (rest : pos tok list) (t_nest_acc : nest_acc_type) (t_ret_acc : p_sexp_list) (position : pos) (values : p_sexp_list) : p_sexp_list =
    append_and_continue rest t_nest_acc t_ret_acc (Nest((List.rev values), position))
    in
  match toks with 
  | [] -> 
    (match nest_acc with
     | [] -> ret_acc
     | (_, unmatched_pos) :: _ -> failwith (sprintf "Unmatched left paren at %s" (pos_to_string unmatched_pos false)))
  | first :: rest ->
    (match first with
     | LPAREN x -> parse_toks_helper rest (([], x) :: nest_acc) ret_acc
     | RPAREN x -> 
      (match nest_acc with
       | [] -> failwith (sprintf "Unmatched right paren at %s" (pos_to_string x false))
       | (nest_first, start_pos) :: nest_rest -> 
        (let (from_line, from_col, _, _) = start_pos in 
         let (_, _, to_line, to_col) = x in
         rparen_helper rest nest_rest ret_acc (from_line, from_col, to_line, to_col)) nest_first)
     | TBool(value, x) -> append_and_continue rest nest_acc ret_acc (Bool(value, x))
     | TInt(value, x)-> append_and_continue rest nest_acc ret_acc (Int(value, x))
     | TSym(value, x)-> append_and_continue rest nest_acc ret_acc (Sym(value, x)))
;;

let parse_toks (toks : pos tok list) : (pos sexp list, string) result =
  try Ok(List.rev (parse_toks_helper toks [] [])) with 
  | Failure msg -> Error(msg)
;;
let parse str = Error "Not yet implemented"
;;
