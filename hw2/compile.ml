open Printf
open Sexp

(* Abstract syntax of (a small subset of) x86 assembly instructions *)

let word_size = 8

type reg = RAX | RSP

type arg = Const of int64 | Reg of reg | RegOffset of int * reg (* int is # words of offset *)

type instruction = IMov of arg * arg | IAdd of arg * arg | IRet

(* Concrete syntax of the Adder language:

   ‹expr›: | NUMBER | IDENTIFIER | ( let ( ‹bindings› ) ‹expr› ) | ( add1 ‹expr› ) | ( sub1 ‹expr› )

   ‹bindings›: | ( IDENTIFIER ‹expr› ) | ( IDENTIFIER ‹expr› ) ‹bindings› *)

(* Abstract syntax of the Adder language *)

type prim1 = Add1 | Sub1

type 'a expr =
  | Number of int64 * 'a
  | Id of string * 'a
  | Let of (string * 'a expr) list * 'a expr * 'a
  | Prim1 of prim1 * 'a expr * 'a

let expr_info e = match e with Number (_, x) | Id (_, x) | Let (_, _, x) | Prim1 (_, _, x) -> x

let create_wrapped_loc ((start_line, start_col, _, _) : pos) ((_, _, end_line, end_col) : pos) : pos
    =
  (start_line, start_col, end_line, end_col)

(* Function to convert from unknown s-expressions to Adder exprs Throws a SyntaxError message if

   there's a problem *)

exception SyntaxError of string

let rec expr_of_sexp (s : pos sexp) : pos expr =
  match s with
  | Sym (sym, position) -> Id (sym, position)
  | Int (value, position) -> Number (value, position)
  | Bool (_, position) ->
      failwith (sprintf "Booleans not defined in lang found at %s" (pos_to_string position false))
      (* TODO: do we want let pos? *)
      (* Handle let *)
  | Nest ([Sym ("let", _); Nest (bindings, _); expr], nest_pos) ->
      Let (handle_let_bindings bindings, expr_of_sexp expr, nest_pos) (* Handle add1 *)
  | Nest ([Sym ("add1", add_loc); add], nest_pos) ->
      let e = expr_of_sexp add in
      Prim1 (Add1, e, nest_pos)
  | Nest ([Sym ("sub1", sub1_pos); sub], nest_pos) ->
      let e = expr_of_sexp sub in
      Prim1 (Sub1, e, nest_pos)
  | Nest (_, nest_pos) -> failwith "failed nest TODO MESSAGE"

and handle_let_bindings (bindings : pos sexp list) : (string * 'a expr) list =
  match bindings with
  | [] -> []
  | Nest ([Sym (id, id_pos); value], pos) :: rest ->
      (id, expr_of_sexp value) :: handle_let_bindings rest
  | Nest (_, nest_pos) :: _ -> failwith "Incorrect nest signature TODO fix message"
  | _ -> failwith "TODO fix this"

(* Functions that implement the compiler *)

(* The next four functions convert assembly instructions into strings, one datatype at a time. Only

   one function has been fully implemented for you. *)

let reg_to_asm_string (r : reg) : string = match r with RAX -> "RAX" | RSP -> "RSP"

let arg_to_asm_string (a : arg) : string =
  match a with
  | Const n -> sprintf "%Ld" n
  | Reg r -> reg_to_asm_string r
  | RegOffset (o, r) -> sprintf "[%s + %d * %d]" (reg_to_asm_string r) word_size o

let instruction_to_asm_string (i : instruction) : string =
  match i with
  | IMov (dest, value) -> sprintf "\tmov %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IAdd (dest, value) -> sprintf "\tadd %s, %s" (arg_to_asm_string dest) (arg_to_asm_string value)
  | IRet -> "\tret"

let to_asm_string (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (instruction_to_asm_string i)) "" is

(* A helper function for looking up a name in a "dictionary" and returning the associated value if

   possible. This is definitely not the most efficient data structure for this, but it is nice and

   simple... *)

let rec find (ls : (string * 'a) list) (x : string) : 'a option =
  match ls with [] -> None | (y, v) :: rest -> if y = x then Some v else find rest x

(* The exception to be thrown when some sort of problem is found with names *)
exception BindingError of string

type env = (string * int) list

let rec add (name : string) (slot : int) (env : env) : env = (name, slot) :: env

(* The actual compilation process. The `compile` function is the primary function, and uses

   `compile_env` as its helper. In a more idiomatic OCaml program, this helper would likely be a

   local definition within `compile`, but separating it out makes it easier for you to test it. *)

let rec compile_env (p : pos expr) (* the program, currently annotated with source location info *)
    (stack_index : int) (* the next available stack index *) (env : (string * int) list) :
    instruction list =
  (* the current binding environment of names to stack slots *)

  (* the instructions that would execute this program *)
  match p with
  | Number (n, x) -> [IMov (Reg RAX, Const n)]
  | Id (id, x) -> (
      let lex = find env id in
      match lex with
      | Some lex -> [IMov (Reg RAX, RegOffset (~-stack_index * lex, RSP))]
      | None -> failwith "Unknown variable" )
  | Let ([], e, loc) -> compile_env e stack_index env
  | Let ((id, expr) :: bindings, body, loc) ->
      let env' = add id stack_index env in
      (* Assuming you can't have a let in the right side of a let binding *)
      compile_env expr (stack_index + 1) env
      @ [IMov (RegOffset (~-1 * (stack_index + 1), RSP), Reg RAX)]
      @ compile_env (Let (bindings, body, loc)) (stack_index + 1) env'
  | Prim1 (_, _, x) -> []

let compile (p : pos expr) : instruction list = compile_env p 1 []

(* Start at the first stack slot, with an empty environment *)

(* The entry point for the compiler: a function that takes a expr and creates an assembly-program

   string representing the compiled version *)

let compile_to_string (prog : pos expr) : string =
  let prelude = "\nsection .text\nglobal our_code_starts_here\nour_code_starts_here:" in
  let asm_string = to_asm_string (compile prog @ [IRet]) in
  let asm_program = sprintf "%s%s\n" prelude asm_string in
  asm_program
