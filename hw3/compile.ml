open Printf
open Exprs
open Pretty

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
    List.for_all (fun (_, e, _) -> is_anf e) binds
    && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EId _ -> true
  | _ -> false
;;

(* PROBLEM 1 *)
(* This function should encapsulate the binding-error checking from Boa *)
exception BindingError of string

let rec check_scope_helper (e : (Lexing.position * Lexing.position) expr) (b: string list) : unit =
  match e with
  | ELet(binds, body, _) -> 
    check_dupes binds b body
  | EPrim1(_, e, _) -> (check_scope_helper e b)
  | EPrim2(_, e1, e2, _) -> 
    check_scope_helper e1 b; 
    ignore (check_scope_helper e2 b)
  | EIf(cond, thn, els, _) -> 
    check_scope_helper cond b; 
    check_scope_helper thn b; 
    ignore (check_scope_helper els b)
  | ENumber _ -> ()
  | EId (id, pos) -> (match List.exists (fun b -> b = id) b with
      | false -> raise (BindingError (sprintf "Unbound variable %s at %s" id (string_of_pos pos)))
      | true -> ()) 
(* Check for duplicates in a bind list *)
and check_dupes 
    (b : (Lexing.position * Lexing.position) bind list) 
    (bindings : string list) 
    (body : (Lexing.position * Lexing.position) expr) =
  match b with 
  | [] -> ignore (check_scope_helper body bindings)
  | (id, b, pos)::rest -> (match (List.exists (fun (b, _, _) -> b = id) rest) with
      | true -> raise (BindingError (sprintf "Duplicate bindings in let at %s" (string_of_pos pos)))
      | false -> 
        check_scope_helper b bindings; 
        ignore (check_dupes rest (id :: bindings) body))

(* Checks scope of e. Confirms: 1. Let contains no two let ids with same name 2. No unbound identifiers *)
let rec check_scope (e : (Lexing.position * Lexing.position) expr) : unit =
  check_scope_helper e []

type tag = int
(* PROBLEM 2 *)
(* This function assigns a unique tag to every subexpression and let binding *)
let tag (e : 'a expr) : tag expr =
  let rec helper (e : 'a expr) (curr_tag : tag) : (tag expr * tag) =
    match e with
    | ELet (binds, e, _) -> 
      let (bind_exprs, curr_tag) = (let_helper binds curr_tag []) in
      let (sub_expr, curr_tag) = (helper e curr_tag) in
      (ELet (bind_exprs, sub_expr, curr_tag), curr_tag + 1)
    | EPrim1 (prim, e, _) -> 
      let (sub_expr, curr_tag) = (helper e curr_tag) in
      (EPrim1 (prim, sub_expr, curr_tag), curr_tag + 1)
    | EPrim2 (prim, e1, e2, _) -> 
      let (sub_expr1, curr_tag) = (helper e1 curr_tag) in
      let (sub_expr2, curr_tag) = (helper e2 curr_tag) in
      (EPrim2 (prim, sub_expr1, sub_expr2, curr_tag), curr_tag + 1)
    | EIf (c, eT, eF, _) ->
      let (c_expr, curr_tag) = (helper c curr_tag) in
      let (t_expr, curr_tag) = (helper eT curr_tag) in
      let (f_expr, curr_tag) = (helper eF curr_tag) in
      (EIf (c_expr, t_expr, f_expr, curr_tag), curr_tag + 1)
    | ENumber (num, _) -> (ENumber (num, curr_tag), curr_tag + 1)
    | EId (id, _) -> (EId (id, curr_tag), curr_tag + 1)
  and let_helper (e : 'a bind list) (curr_tag : tag) (acc : tag bind list) : (tag bind list * tag) =
    match e with
    | [] -> (List.rev acc, curr_tag)
    | (name, first, _) :: rest -> 
      let (tag_bind, curr_tag) = (helper first curr_tag) in
      let_helper rest (curr_tag + 1) ((name, tag_bind, curr_tag) :: acc)
  in
  let (result, _) = (helper e 1) in
  result
;;

(* This function removes all tags, and replaces them with the unit value.
   This might be convenient for testing, when you don't care about the tag info. *)
let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId(x, _) -> EId(x, ())
  | ENumber(n, _) -> ENumber(n, ())
  | EPrim1(op, e, _) ->
    EPrim1(op, untag e, ())
  | EPrim2(op, e1, e2, _) ->
    EPrim2(op, untag e1, untag e2, ())
  | ELet(binds, body, _) ->
    ELet(List.map(fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf(cond, thn, els, _) ->
    EIf(untag cond, untag thn, untag els, ())
;;

type env = (string * string) list
(* PROBLEM 3 *)
let rename (e : tag expr) : tag expr =
  let rec help (env : env) (e : tag expr): tag expr =
    match e with
    | EId(x, tag) -> let _, name = (List.find (fun (e, b) -> (String.equal x e)) env) in EId (name, tag)
    | ELet(binds, body, tag) ->
      let (binds_renamed, new_env) = (let_helper env binds) in let body_renamed = (help new_env body) in ELet(binds_renamed, body_renamed, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EPrim1(op, e, tag) ->
      EPrim1(op, help env e, tag)
    | EPrim2(op, e1, e2, tag) ->
      EPrim2(op, help env e1, help env e2, tag)
    | EIf(cond, thn, els, tag) ->
      EIf(help env cond, help env thn, help env els, tag)
  (* Renames all bindings in a let string and returns them with new env *)
  and let_helper (env : env) (binds : 'a bind list) =
    match binds with
    | [] -> ([], env)
    | (first, binding, tag)::rest -> let binding_renamed = (help env binding) 
      and (acc, env) = (let_helper env rest) 
      and new_name = (sprintf "%s%n" first tag) in 
      ((new_name, binding_renamed, tag)::acc, (first, new_name)::env)
  in help [] e
;;

(* PROBLEM 4 & 5 *)
(* This function converts a tagged expression into an untagged expression in A-normal form *)
let anf (e : tag expr) : unit expr =
  failwith "anf: Implement this"
;;


(* Helper functions *)
let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "rax"
  | RSP -> "rsp"

let arg_to_asm (a : arg) : string =
  match a with
  | Const(n) -> sprintf "QWORD %Ld" n
  | Reg(r) -> r_to_asm r
  | RegOffset(n, r) ->
    if n >= 0 then
      sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
    else
      sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)

let i_to_asm (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
    sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd(dest, to_add) ->
    sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | IRet ->
    "  ret"
  | _ -> failwith "i_to_asm: Implement this"

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
    if y = x then v else find rest x

(* PROBLEM 5 *)
(* This function actually compiles the tagged ANF expression into assembly *)
(* The si parameter should be used to indicate the next available stack index for use by Lets *)
(* The env parameter associates identifier names to stack indices *)
let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  match e with
  | ENumber(n, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EId(x, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EPrim1(op, e, _) ->
    let e_reg = compile_imm e env in
    begin match op with
      | Add1 -> [
          IMov(Reg(RAX), e_reg);
          IAdd(Reg(RAX), Const(1L))
        ]
      | Sub1 -> [
          IMov(Reg(RAX), e_reg);
          IAdd(Reg(RAX), Const(Int64.minus_one))
        ]
    end
  | EPrim2(op, left, right, _) ->
    failwith "compile_expr:eprim2: Implement this"
  | EIf(cond, thn, els, tag) ->
    failwith "compile_expr:eif: Implement this"
  | ELet([id, e, _], body, _) ->
    failwith "compile_expr:elet: Implement this"
  | _ -> failwith "Impossible: Not in ANF"
and compile_imm e env =
  match e with
  | ENumber(n, _) -> Const(n)
  | EId(x, _) -> RegOffset(~-(find env x), RSP)
  | _ -> failwith "Impossible: not an immediate"


let compile_anf_to_string anfed =
  let prelude =
    "section .text
global our_code_starts_here
our_code_starts_here:" in
  let compiled = (compile_expr anfed 1 []) in
  let as_assembly_string = (to_asm (compiled @ [IRet])) in
  sprintf "%s%s\n" prelude as_assembly_string


let compile_to_string prog =
  check_scope prog;
  let tagged : tag expr = tag prog in
  let renamed : tag expr = rename tagged in
  let anfed : tag expr = tag (anf renamed) in
  (* printf "Prog:\n%s\n" (ast_of_expr prog); *)
  (* printf "Tagged:\n%s\n" (format_expr tagged string_of_int); *)
  (* printf "ANFed/tagged:\n%s\n" (format_expr anfed string_of_int); *)
  compile_anf_to_string anfed

