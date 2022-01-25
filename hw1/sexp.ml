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
  string_of_int, caught by the with statement, and identified as a TSym. If the token
  value is whitespace, then only line and col nums are updated corresponding to the whitespace
  value. If, finally, the token is a "(" or ")", then the corresponding LPAREN or RPAREN
  is created. The final tuple returned from fold_left gets and returns only the first 
  toks value, representing the tokens created.

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

(* A defined type for a list of pos sexps *)
type p_sexp_list = pos sexp list;;
(* A defined type for the nest accumulator used in parse_toks_helper;
  This is a list of (list of pos sexps paired with the open paren pos);
  Each (p_sexp_list * pos) item represents a an LPAREN found, where
    each item in the p_sexp_list is an item that should be nested in the 
    Nest that eventually gets created, and the pos represents the position
    of the opening LPAREN for the Nest
*)
type nest_acc_type = (p_sexp_list * pos) list;;

(* Accumulator helper for parsing tokens into a list of pos sexps;
  This works using two accumulators, one for tokens that should be nested (nest_acc),
    and one for top-level tokens that should be returned in the Ok list by the 
    parse_toks call (ret_acc);
  Syntax errors raise a Failure exception containing a message to alert the caller 
    that there was an error with parsing, the caller should be prepared to react to this;
  For functionality, when a top-level value is found (other than an LPAREN) (detected
    by whether or not nest_acc has any elements), the value is added directly to ret_acc;
    when a nested value is found (nest_acc has 1 or more elements), then the value is
    added to the first nest_acc sub-list
*)
let rec parse_toks_helper (toks : pos tok list) (nest_acc : nest_acc_type) (ret_acc : p_sexp_list) : p_sexp_list =
  (* Prepends the given value onto either the first sub-list of t_nest_acc (if one exists for a Nest currently 
      being built) or ret_acc and continues processing by passing the updated list values into parse_toks_helper 
      with the remaining tokens;
    t_nest_acc is required instead of using the already-available nest_acc because the list may
      be updated when creating the value param
  *)
  let prepend_and_continue (tok_rest : pos tok list) (t_nest_acc : nest_acc_type) (value : pos sexp) =
    match t_nest_acc with
    (* if t_nest_acc is empty, append the value to ret_acc as a top-level value and call parse_toks_helper*)
    | [] -> parse_toks_helper tok_rest [] (value :: ret_acc)
    (* if t_nest_acc is not empty, append the value to the first sub-list of t_nest_acc,
      keeping the same open_position value for the Nest currently being created and call parse_toks_helper
    *)
    | (nest_first, open_position) :: nest_rest -> 
      parse_toks_helper tok_rest ((value :: nest_first, open_position) :: nest_rest) ret_acc
    in
  (* Handle closing a Nest when a RPAREN is encoutered by either:
    - raising a Fail if there is no Nest currently being created (unmatched right paren), or
    - calling prepend_and_continue with the value being a new Nest to continue parsing new tokens;
    In the case a new Nest is created, it uses the first value available in the nest_acc for information,
    - the Nest list contents use the reversed nest_acc's first value's p_sexp_list, since the values
      are prepended, creating the list in reverse order
    - the pos information takes the start LPAREN info from the first value in nest_acc, and uses the
      end position information from the RPAREN to construct a new pos spanning the LPAREN to the RPAREN
  *)
  let rparen_helper (tok_rest : pos tok list) (end_pos : pos) : p_sexp_list =
    match nest_acc with
    (* if nest_acc is empty, but an RPAREN was encountered, then this is an unmatched RPAREN *)
    | [] -> failwith (sprintf "Unmatched right paren at %s" (pos_to_string end_pos false))
    (* otherwise, construct the pos information spanning the matched LPAREN to this RPAREN, and create a new NEST;
      call prepend_and_continue with the new nest *)
    | (nest_first, start_pos) :: nest_rest -> 
     (* get the from_line and from_col from the corresponding LPAREN *)
     let (from_line, from_col, _, _) = start_pos in 
     (* get the to_line and to_col from this RPAREN *)
     let (_, _, to_line, to_col) = end_pos in
     (* call prepend_and_continue with the remaining tok values, nest_acc values, and created Nest object *)
     (prepend_and_continue tok_rest nest_rest 
       (Nest((List.rev nest_first), (from_line, from_col, to_line, to_col))))
    in
  match toks with 
  (* no tokens remain *)
  | [] -> 
    (match nest_acc with
    (* if nest_acc is empty, then all LPARENS had a matching RPAREN*)
     | [] -> List.rev ret_acc
    (* if nest_acc has a first value, then get the unmatched LPAREN info and raise an exception *)
     | (_, unmatched_pos) :: _ -> failwith (sprintf "Unmatched left paren at %s" (pos_to_string unmatched_pos false)))
  (* some tokens remain *)
  | tok_first :: tok_rest ->
    (* handle creating a sexp for the given token *)
    (match tok_first with
    (* LPAREN is a special case, instead of creating a new sexp, prepend new LPAREN info onto nest_acc to mark 
      the start of this
    *)
     | LPAREN position -> parse_toks_helper tok_rest (([], position) :: nest_acc) ret_acc
     | RPAREN position -> rparen_helper tok_rest position
     | TBool(value, position) -> prepend_and_continue tok_rest nest_acc (Bool(value, position))
     | TInt(value, position)-> prepend_and_continue tok_rest nest_acc (Int(value, position))
     | TSym(value, position)-> prepend_and_continue tok_rest nest_acc (Sym(value, position)))
;;

(* Parse the given pos tok list into an Ok list of pos sexp or Error containing a
  message describing the parse error
*)
let parse_toks (toks : pos tok list) : (p_sexp_list, string) result =
  try Ok(parse_toks_helper toks [] []) with 
  | Failure msg -> Error(msg)
;;
(* Parse the given string into an OK list of pos sexp or Error containing a message
  describing a parsing error;
  Done by tokenizing it and calling parse_toks on the returned tokens
*)
let parse str = (parse_toks (tokenize str))
;;
