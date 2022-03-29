open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
(* Add at least one of these two *)

type 'a envt = (string * 'a) list

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
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;

let const_true       = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false      = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask        = HexConst(0x8000000000000000L)
let bool_tag         = 0x0000000000000007L
let bool_tag_mask    = 0x0000000000000007L
let num_tag          = 0x0000000000000000L
let num_tag_mask     = 0x0000000000000001L
let closure_tag      = 0x0000000000000005L
let closure_tag_mask = 0x0000000000000007L
let tuple_tag        = 0x0000000000000001L
let tuple_tag_mask   = 0x0000000000000007L
let const_nil        = HexConst(tuple_tag)


(* error codes *)
let err_COMP_NOT_NUM        = 1L
let err_ARITH_NOT_NUM       = 2L
let err_NOT_BOOL            = 3L
let err_OVERFLOW            = 4L
let err_GET_NOT_TUPLE       = 5L
let err_GET_LOW_INDEX       = 6L
let err_GET_HIGH_INDEX      = 7L
let err_NIL_DEREF           = 8L
let err_GET_NOT_NUM         = 9L
let err_DESTRUCTURE_INVALID_LEN         = 10L
let err_SHOULD_BE_FUN         = 16L
let err_ARITY         = 17L

(* let err_COMP_NOT_NUM     = 1L
   let err_ARITH_NOT_NUM    = 2L
   let err_LOGIC_NOT_BOOL   = 3L
   let err_IF_NOT_BOOL      = 4L
   let err_OVERFLOW         = 5L
   let err_GET_NOT_TUPLE    = 6L
   let err_GET_LOW_INDEX    = 7L
   let err_GET_HIGH_INDEX   = 8L
   let err_GET_NOT_NUM      = 9L
   let err_NIL_DEREF        = 10L
   let err_OUT_OF_MEMORY    = 11L
   let err_SET_NOT_TUPLE    = 12L
   let err_SET_LOW_INDEX    = 13L
   let err_SET_NOT_NUM      = 14L
   let err_SET_HIGH_INDEX   = 15L
   let err_CALL_NOT_CLOSURE = 16L
   let err_CALL_ARITY_ERR   = 17L *)

(* label names for errors *)
let label_COMP_NOT_NUM         = "error_comp_not_num"
let label_ARITH_NOT_NUM        = "error_arith_not_num"
let label_TUPLE_ACCESS_NOT_NUM = "error_tuple_access_not_num"
let label_NOT_BOOL             = "error_not_bool"
let label_NOT_TUPLE            = "error_not_tuple"
let label_OVERFLOW             = "error_overflow"
let label_GET_LOW_INDEX        = "error_get_low_index"
let label_GET_HIGH_INDEX       = "error_get_high_index"
let label_NIL_DEREF            = "error_nil_deref"
let label_DESTRUCTURE_INVALID_LEN         = "destructure_invalid_len"
let label_SHOULD_BE_FUN         = "error_should_be_fun"
let label_ARITY         = "error_arity"

(* label names for conditionals *)
let label_IS_NOT_BOOL  = "is_not_bool"
let label_IS_NOT_NUM   = "is_not_num"
let label_IS_NOT_TUPLE = "is_not_tuple"
let label_DONE         = "done"

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11

let prelude = "section .text
extern error
extern print
extern print_stack
extern input
extern equal
global our_code_starts_here"

module StringSet = Set.Make(String)
let nil = HexConst(tuple_tag)

(* You may find some of these helpers useful *)

let stringset_of_list : (string list -> StringSet.t) =
  List.fold_left 
    (fun acc arg -> StringSet.add arg acc)
    StringSet.empty
;;

let rec find_helper orig_ls ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found in %s" x (List.fold_right (fun (s, _) acc -> acc ^ " " ^ s) orig_ls "")))
  | (y,v)::rest ->
    if y = x then v else find_helper orig_ls rest x

let rec find ls x =
  find_helper ls ls x

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ALetRec(binds, body, _) ->
      (List.length binds) + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))


let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun(fname, _, _, _) as d)::ds_rest ->
    if name = fname then Some(d) else find_decl ds_rest name

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x::xs -> (elt = x) || (find_one xs elt)

let rec find_dups_by (l : 'a list) (eq : ('a -> 'a -> bool)) : ('a * 'a) list =
  match l with
  | [] -> []
  | x :: [] -> []
  | first :: rest -> let (dups, other) = (List.partition (eq first) rest) in
    (List.map (fun dup -> (dup, first)) dups) @ (find_dups_by other eq)
;;

let rec find_dup_exns_by_env (e : (string * sourcespan) list) : exn list =
  let rec find_dups_by_env (e : (string * sourcespan) list) : ((string * sourcespan) * (string * sourcespan)) list =
    (find_dups_by e (fun e1 e2 -> match e1 with (name, loc) -> match e2 with (name2, loc) -> name = name2))
  in (List.map 
        (fun (e1, e2) -> 
           match e1 with (name, span) -> match e2 with (_, span2) -> DuplicateId(name, span2, span))
        (find_dups_by_env e))

let rec binds_to_env (binds : sourcespan bind list) : (string * sourcespan) list =
  let bind_to_env (acc : (string * sourcespan) list) (bind : sourcespan bind) : (string * sourcespan) list =
    match bind with 
    | BBlank(_) -> acc
    | BName(name, _, pos) -> (name, pos)::acc
    | BTuple(vals, _) -> (binds_to_env vals) @ acc
  in List.fold_left bind_to_env [] binds

type funenvt = call_type envt;;
let initial_fun_env : funenvt = [
  ("input", Native);
  ("equal", Native);
];;
let initial_fun_env_env : arg envt = (List.map (fun (name, _) -> (name, Label(name))) initial_fun_env)
let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program(decls, body, tag) ->
      Program(List.map (fun group -> List.map (helpD env) group) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun(name, args, body, tag) ->
      let (newArgs, env') = helpBS env args in
      DFun(name, newArgs, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank tag -> (b, env)
    | BName(name, allow_shadow, tag) ->
      let name' = sprintf "%s_%d" name tag in
      (BName(name', allow_shadow, tag), (name, name') :: env)
    | BTuple(binds, tag) ->
      let (binds', env') = helpBS env binds in
      (BTuple(binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b::bs ->
      let (b', env') = helpB env b in
      let (bs', env'') = helpBS env' bs in
      (b'::bs', env'')
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a)::bindings ->
      let (b', env') = helpB env b in
      let e' = helpE env e in
      let (bindings', env'') = helpBG env' bindings in
      ((b', e', a)::bindings', env'')
  and helpE env e =
    match e with
    | ESeq(e1, e2, tag) -> ESeq(helpE env e1, helpE env e2, tag)
    | ETuple(es, tag) -> ETuple(List.map (helpE env) es, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE env e, helpE env idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE env e, helpE env idx, helpE env newval, tag)
    | EPrim1(op, arg, tag) -> EPrim1(op, helpE env arg, tag)
    | EPrim2(op, left, right, tag) -> EPrim2(op, helpE env left, helpE env right, tag)
    | EIf(c, t, f, tag) -> EIf(helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId(name, tag) ->
      (try
         EId(find env name, tag)
       with InternalCompilerError _ -> e)
    | EApp(func, args, native, tag) ->
      let func = helpE env func in
      let call_type =
        match List.assoc_opt (get_func_name func) initial_fun_env with 
        | None -> Snake
        | Some(_) -> Native
      in
      EApp(func, List.map (helpE env) args, call_type, tag)
    | ELet(binds, body, tag) ->
      let (binds', env') = helpBG env binds in
      let body' = helpE env' body in
      ELet(binds', body', tag)
    | ELetRec(bindings, body, tag) ->
      let (revbinds, env) = List.fold_left (fun (revbinds, env) (b, e, t) ->
          let (b, env) = helpB env b in ((b, e, t)::revbinds, env)) ([], env) bindings in
      let bindings' = List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag)::bindings) [] revbinds in
      let body' = helpE env body in
      ELetRec(bindings', body', tag)
    | ELambda(binds, body, tag) ->
      let (binds', env') = helpBS env binds in
      let body' = helpE env' body in
      ELambda(binds', body', tag)
  in (rename [] p)
;;

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let rec deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet(name, bind, body, _) -> List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALetRec(binds, body, _) -> List.fold_left max (helpA body) (List.map (fun (_, bind) -> helpC bind) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1(_, i, _) -> helpI i
    | CPrim2(_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp(_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple(vals, _) -> List.fold_left max 0 (List.map helpI vals)
    | CGetItem(t, _, _) -> helpI t
    | CSetItem(t, _, v, _) -> max (helpI t) (helpI v)
    | CLambda(args, body, _) -> 0
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId(name, _) -> name_to_offset name
  and name_to_offset name =
    match (find env name) with
    | RegOffset(bytes, RBP) -> bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

(* IMPLEMENT EVERYTHING BELOW *)
let prim2_to_sprim2 (p : prim2): sprim2 =
  match p with
  | And | Or -> raise (InternalCompilerError (sprintf "prim2 %s not allowed in desugared expr" (name_of_op2 p)))
  | Plus -> SPlus
  | Minus -> SMinus
  | Times -> STimes
  | Greater -> SGreater
  | GreaterEq -> SGreaterEq
  | Less -> SLess
  | LessEq -> SLessEq
  | Eq -> SEq
  | CheckSize -> SCheckSize

(* This data type lets us keep track of how a binding was introduced.
   We'll use it to discard unnecessary Seq bindings, and to distinguish 
   letrec from let. Essentially, it accumulates just enough information 
   in our binding list to tell us how to reconstruct an appropriate aexpr. *)
type 'a anf_bind =
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program([], body, _) -> AProgram(helpA body, ())
    | _ -> raise (InternalCompilerError "Top-level declarations should have been desugared away")
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) = 
    match e with
    | EPrim1(op, arg, _) ->
      let (arg_imm, arg_setup) = helpI arg in
      (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (CPrim2(prim2_to_sprim2 op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
      let (cond_imm, cond_setup) = helpI cond in
      (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet([], body, _) -> helpC body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpI exp in
      let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
      (* TODO: confirm this is OK.  *)
      (body_ans, exp_setup @ body_setup)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
      raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ESeq(e1, e2, _) -> raise (InternalCompilerError "Should not have seq after desugaring")
    | EApp(func, args, ct, _) ->
      let (new_args, new_setup) = List.split (List.map helpI args) in
      let (fun_name, fun_setup) = helpI func in
      (CApp(fun_name, new_args, ct, ()), fun_setup @ (List.concat new_setup))
    | ETuple(e, _) -> 
      let id_setup = List.map helpI e in 
      let ids = (List.map (fun (id, _) -> id) id_setup) in
      let setups = (List.map (fun (_, setup) -> setup) id_setup) in 
      (CTuple(ids, ()), List.flatten setups)
    | EGetItem(tuple, index, _) -> 
      let (tuple_id, tuple_setup) = helpI tuple 
      and (index_id, index_setup) = helpI index in 
      (CGetItem(tuple_id, index_id, ()), tuple_setup @ index_setup)
    | ESetItem(tuple, index, set, _) -> 
      let (tuple_id, tuple_setup) = helpI tuple 
      and (index_id, index_setup) = helpI index
      and (set_id, set_setup) = helpI set in 
      (CSetItem(tuple_id, index_id, set_id, ()), tuple_setup @ index_setup @ set_setup)
    | ELambda(binds, body, _) ->
      let binds = List.map (fun a ->
          match a with
          | BName(a, _, _) -> a
          | BBlank(_) | BTuple(_) ->  raise (InternalCompilerError "Tuple destructuring should have been desugared away")) binds
      in 
      (CLambda(binds, helpA body, ()), [])
    | ELetRec(binds, body, pos) ->
      let bind_setup, binds =
        List.fold_right 
          (fun (bind, exp, _) (bind_setup, binds) ->
             let (exp_ans, exp_setup) = helpC exp in
             match bind with 
             | BName(name, _, _) -> 
               (exp_setup @ bind_setup, (name, exp_ans) :: binds)
             | BBlank(_) | BTuple(_) -> raise (InternalCompilerError "Tuple destructuring not allowed in let rec")
          )
          binds
          ([], [])
      in 
      let body_ans, body_setup = helpC body in
      (body_ans, bind_setup @ [BLetRec(binds)] @ body_setup)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)
  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil _ -> (ImmNil(), [])
    | ESeq(e1, e2, _) -> raise (InternalCompilerError "Should not have seq after desugaring")
    | ETuple(e, tag) ->
      let tmp = sprintf "tuple_%d" tag 
      and id_setup = List.map helpI e in 
      let ids = (List.map (fun (id, _) -> id) id_setup) 
      and setups = (List.map (fun (_, setup) -> setup) id_setup) in 
      (ImmId(tmp, ()), (List.flatten setups) @ [BLet(tmp, CTuple(ids, ()))])
    | EGetItem(tuple, index, tag) ->
      let tmp = sprintf "get_%d" tag 
      and (tuple_id, tuple_setup) = helpI tuple 
      and (index_id, index_setup) = helpI index in 
      (ImmId(tmp, ()), tuple_setup 
                       @ index_setup 
                       @ [BLet(tmp, CGetItem(tuple_id, index_id, ()))])
    | ESetItem(tuple, index, newval, tag) ->
      let tmp = sprintf "get_%d" tag 
      and (tuple_id, tuple_setup) = helpI tuple 
      and (index_id, index_setup) = helpI index in 
      (ImmId(tmp, ()), tuple_setup 
                       @ index_setup 
                       @ [BLet(tmp, CGetItem(tuple_id, index_id, ()))])
    | EPrim1(op, arg, tag) ->
      let tmp = sprintf "unary_%d" tag in
      let (arg_imm, arg_setup) = helpI arg in
      (ImmId(tmp, ()), arg_setup @ [BLet(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
      let tmp = sprintf "binop_%d" tag in
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (ImmId(tmp, ()), left_setup @ right_setup @ [BLet(tmp, CPrim2(prim2_to_sprim2 op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
      let tmp = sprintf "if_%d" tag in
      let (cond_imm, cond_setup) = helpI cond in
      (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, ct, tag) ->
      let tmp = sprintf "app_%d" tag in
      let (new_args, new_setup) = List.split (List.map helpI args) in
      let (fun_name, fun_setup) = helpI func in
      (ImmId(tmp, ()), (List.concat new_setup) 
                       @ fun_setup
                       @ [BLet(tmp, CApp(fun_name, new_args, ct, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpI exp in (* MUST BE helpI, to avoid any missing final steps *)
      let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ body_setup)
    | ELambda(binds, body, tag) ->
      let binds = List.map (fun a ->
          match a with
          | BName(a, _, _) -> a
          | BBlank(_) | BTuple(_) ->  raise (InternalCompilerError "Tuple destructuring should have been desugared away")) binds
      in 
      let tmp = sprintf "lam_%d" tag in
      (ImmId(tmp, ()), [BLet(tmp, CLambda(binds, helpA body, ()))])
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
      raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | ELetRec(binds, body, tag) ->
      let tmp = sprintf "let_rec_%d" tag in
      let bind_setup, binds =
        List.fold_right 
          (fun (bind, exp, _) (bind_setup, binds) ->
             let (exp_ans, exp_setup) = helpC exp in
             match bind with 
             | BName(name, _, _) -> 
               (exp_setup @ bind_setup, (name, exp_ans) :: binds)
             | BBlank(_) | BTuple(_) -> raise (InternalCompilerError "Tuple destructuring not allowed in let rec")
          )
          binds
          ([], [])
      in 
      let body_ans, body_setup = helpC body in
      (ImmId(tmp, ()), bind_setup @ [BLetRec(binds)] @ body_setup @ [BLet(tmp, body_ans)])
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
         (* Here's where the anf_bind datatype becomes most useful:
              BSeq binds get dropped, and turned into ASeq aexprs.
              BLet binds get wrapped back into ALet aexprs.
              BLetRec binds get wrapped back into ALetRec aexprs.
            Syntactically it looks like we're just replacing Bwhatever with Awhatever,
            but that's exactly the information needed to know which aexpr to build. *)
         match bind with
         | BLet(name, exp) -> ALet(name, exp, body, ())
         | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
;;


let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E (e : sourcespan expr) (env : (string * sourcespan) list) =
    match e with
    | EBool _ -> []
    | ENumber(n, loc) -> 
      if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L)
      then [Overflow(n, loc)]
      else []
    | EId (x, loc) ->
      begin 
        match (List.assoc_opt x env) with
        | None -> [UnboundId(x, loc)]
        | Some(_) -> []
      end
    | ENil(_) -> []
    | EPrim1(_, e, _) -> (wf_E e env)
    | EPrim2(_, l, r, _) -> (wf_E l env) @ (wf_E r env)
    | EIf(c, t, f, _) -> (wf_E c env) @ (wf_E t env) @ (wf_E f env)
    | ELet(bindings, body, _) ->
      let (env, bindings_env, errors) =
        (List.fold_left
           (fun (env, bindings_env, found_errors) (bind, expr, loc) ->
              let curr_errors = (wf_E expr env) @ found_errors in
              let new_binds = (binds_to_env [bind])
              in (new_binds @ env, new_binds @ bindings_env, curr_errors))
           (env, [], []) bindings) in
      errors @ find_dup_exns_by_env bindings_env @ (wf_E body env)
    | EApp(f, args, _, loc) -> 
      let args_errors = List.flatten (List.map (fun expr -> wf_E expr env) args) in
      let fun_errors = wf_E f env in
      fun_errors @ args_errors
    | ESeq(s1, s2, _) -> (wf_E s1 env) @ (wf_E s2 env)
    | ETuple(elements, _) -> List.flatten (List.map (fun e -> wf_E e env) elements)
    | EGetItem(tuple, idx, _) -> (wf_E tuple env) @ (wf_E idx env)
    | ESetItem(tuple, idx, set, _) -> (wf_E tuple env) @ (wf_E idx env) @ (wf_E set env)
    | ELambda(binds, body, _) -> 
      let binds_env = (binds_to_env binds) in 
      find_dup_exns_by_env binds_env @ (wf_E body (binds_env @ env))
    | ELetRec(binds, body, _) -> 
      (* get the bind env first so that function recursion is allowed *)
      let bind_env = List.map 
          (fun (bind, _, span) -> 
             match bind with 
             | BName(name, _, _) -> (name, span)
             | BBlank(_) | BTuple(_) -> raise (InternalCompilerError "let rec binds must not contain blanks or destructuring"))
          binds
      in
      let bind_errors = 
        List.concat 
          (List.map
             (fun (bind, body, ss) -> 
                begin
                  match body with 
                  | ELambda(_) -> []
                  |_ -> [(LetRecNonFunction(bind, ss))]
                end
                @ (wf_E body (env @ bind_env)))
             binds)
      in
      find_dup_exns_by_env bind_env @ bind_errors @ (wf_E body bind_env)
  and wf_D (d : sourcespan decl) (env : (string * sourcespan) list): exn list =
    match d with 
    | DFun(_, binds, body, _) ->
      let binds_env = (binds_to_env binds) in 
      find_dup_exns_by_env binds_env @ (wf_E body (binds_env @ env))
  and get_env (decls : sourcespan decl list) : sourcespan envt = 
    (List.map (fun x -> 
         begin 
           match x with 
           | DFun(name, args, _, ss) -> 
             (name, ss)
         end) decls)
  and builtin_env : sourcespan envt = List.map (fun (name, _) -> (name, (create_ss "builtin" 0 0 0 0))) initial_fun_env
  and d_errors (decls : sourcespan decl list) (env: sourcespan envt): exn list = 
    (List.flatten (List.map (fun (decl) -> (wf_D decl env)) decls))
  in
  match p with
  | Program(decls, body, _) ->
    let envs = (List.map (fun decls -> (get_env decls)) decls) in 
    (* TODO: do we need this? we allow shadowing *)
    (* let dup_fun_errors = dup_d_errors decls in *)
    let d_errs = (List.flatten (List.map2 (fun (decls) (env) -> (d_errors decls env)) decls envs)) in
    let e_errs = wf_E body (List.flatten (builtin_env::envs)) in 
    begin
      match d_errs @ e_errs with 
      | [] -> Ok p
      | e -> Error e
    end
;;

let free_vars (e: 'a aexpr) (args : string list) : string list =
  let rec help_imm (e : 'a immexpr) (env : StringSet.t) : StringSet.t = 
    match e with
    | ImmId(name, _) -> 
      if StringSet.mem name env
      then StringSet.empty
      else StringSet.singleton name
    | _ -> StringSet.empty
  and help_cexpr (e : 'a cexpr) (env : StringSet.t) : StringSet.t =
    match e with 
    | CIf(cnd, thn, els, _) -> 
      StringSet.(union (help_imm cnd env) (help_aexpr thn env) 
                 |> union (help_aexpr els env))
    | CPrim1(_, e, _) -> help_imm e env 
    | CPrim2(_, e1, e2, _) ->
      StringSet.union (help_imm e1 env) (help_imm e2 env)
    | CApp(func, args, _, _) -> 
      StringSet.union 
        (help_imm func env) 
        (List.fold_left 
           (fun acc arg -> StringSet.union acc (help_imm arg env)) 
           StringSet.empty 
           args)
    | CImmExpr(e) -> help_imm e env
    | CTuple(exprs, _) ->
      List.fold_left 
        (fun acc arg -> StringSet.union acc (help_imm arg env))
        StringSet.empty
        exprs
    | CGetItem(tuple, pos, _) -> 
      StringSet.union (help_imm tuple env) (help_imm pos env)
    | CSetItem(tuple, pos, value, _) ->
      StringSet.(union (help_imm tuple env) (help_imm pos env)
                 |> union (help_imm value env))
    | CLambda(args, body, _) ->
      let newenv = StringSet.union (stringset_of_list args) env in 
      help_aexpr body newenv 
  and help_aexpr (e : 'a aexpr) (env : StringSet.t) : StringSet.t = 
    match e with 
    | ALet(name, bind, body, _) -> 
      let newenv = StringSet.add name env in 
      StringSet.union (help_cexpr bind newenv) (help_aexpr body newenv)
    | ALetRec(name_binds, body, _) -> 
      let newenv, bind_frees =
        List.fold_left
          (fun (newenv, frees) (name, bind) ->
             (StringSet.add name newenv, 
              StringSet.union (help_cexpr bind newenv) frees))
          (env, StringSet.empty)
          name_binds
      in 
      StringSet.union bind_frees (help_aexpr body newenv)
    | ACExpr(e) ->
      help_cexpr e env
  in 
  let arg_set = stringset_of_list args in
  StringSet.(diff (help_aexpr e arg_set) arg_set |> elements)
;;

(** Gets an environment mapping id names to register names or stack offsets.
 * This makes it easy for callee functions to use args *)
let get_func_call_params (params : string list) (closure_args : string list) : arg envt =
  let rec pair_stack (params : string list) (next_off : int) (direction : int) : arg envt =
    match params with 
    | [] -> []
    | first :: rest ->
      (first, RegOffset(next_off * word_size * direction, RBP))
      :: (pair_stack rest (next_off + 1) direction)
  and pair_regs (params : string list) (regs : reg list) : arg envt =
    match regs with 
    | [] -> 
      begin 
        match params with 
        | [] -> [] 
        | _ -> (pair_stack params 2 1)
      end 
    | reg_first :: reg_rest ->
      begin
        match params with 
        | [] -> []
        | param_first :: param_rest ->
          (param_first, Reg(reg_first))
          :: (pair_regs param_rest reg_rest)
      end
  in
  (pair_regs params first_six_args_registers) @ (pair_stack closure_args 1 ~-1)
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let rec naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg envt =
  match prog with 
  | AProgram(expr, _) ->
    (prog, 
     (get_aexpr_envt expr 1))
and get_aexpr_envt (expr : tag aexpr) (si : int) : arg envt =
  match expr with 
  | ALet(name, bind, body, _) ->
    (name, RegOffset(~-si * word_size, RBP))
    :: (get_cexpr_envt bind (si + 1))
    @ (get_aexpr_envt body (si + 1))
  | ACExpr(body) ->
    (get_cexpr_envt body si)
  | ALetRec(binds, body, _) -> 
    let num_binds = List.length binds in
    List.mapi (fun i (name, bind) -> (name, RegOffset(~-(si + i) * word_size, RBP))) binds
    @ List.flatten (List.map (fun (_, bind) -> get_cexpr_envt bind (si + 1 + num_binds)) binds)
    (* (List.flatten (List.mapi (fun i (name, bind) -> (name, RegOffset(~-(si + i) * word_size, RBP))::(get_cexpr_envt bind (si + i + 1))) binds)) *)
    @ (get_aexpr_envt body (si + num_binds + 1))
and get_cexpr_envt (expr : tag cexpr) (si : int) : arg envt =
  match expr with 
  | CIf(_, l, r, _) -> 
    (get_aexpr_envt l si)
    @ (get_aexpr_envt r si)
  | CLambda(_) | CPrim1(_) | CPrim2(_) | CApp(_) | CImmExpr(_) | CTuple(_) | CGetItem(_) | CSetItem(_) -> []
and get_lambda_envt (binds : string list) (body : tag aexpr) frees : arg envt =
  (get_func_call_params binds frees) @ get_aexpr_envt body (1 + List.length frees) 
;;

(* Jumps to to_label if not a num *)
let num_tag_check (to_label : string) : instruction list =
  [IMov(Reg(R10), HexConst(num_tag_mask)); ITest(Reg(RAX), Reg(R10)); IJnz(Label(to_label))]

(* Jumps to to_label if not type and puts final_rax_value in RAX on exiting.
 * final_rax_value does not have to be the original RAX value, but
 * in *most* cases should be (except for isbool())
 *
 * Note: the value to test should be in RAX before calling
*)
let tag_check (final_rax_value : arg) (to_label : string) (tag_mask : int64) (tag : int64) : instruction list = [
  IMov(Reg(R10), HexConst(tag_mask)); 
  IAnd(Reg(RAX), Reg(R10)); 
  IMov(Reg(R10), HexConst(tag));
  ICmp(Reg(RAX), Reg(R10));
  IMov(Reg(RAX), final_rax_value); 
  IJnz(Label(to_label));
] 

(* generates the instructions for comparing the args e1_reg and e2_reg and 
  * constructs an auto-generated jump label using the jmp_instr_constructor.
  * jump_instr_constructor should take in a label name and create the appropriate jump instruction.
*)
let generate_cmp_func_with
    (e1_reg : arg)
    (e2_reg : arg)
    (jmp_instr_constructor : (string -> instruction))
    (if_true: instruction list)
    (if_false: instruction list)
    (tag : int)
    (tag_suffix : string)
    (tag_checks : bool)
  : (instruction list) =
  let label_done = (sprintf "%s%n%s_cmp" label_DONE tag tag_suffix) in
  let body = ([IMov(Reg(R10), e2_reg); ICmp(Reg(RAX), Reg(R10));]
              @ if_true
              @ [(jmp_instr_constructor label_done);]
              @ if_false @ 
              [ILabel(label_done)]) in
  if tag_checks then
    IMov(Reg(RAX), e2_reg) ::
    (num_tag_check label_COMP_NOT_NUM)
    @ [(IMov(Reg(RAX), e1_reg))] 
    @ (num_tag_check label_COMP_NOT_NUM)
    @ body
  else body
(* generates the instructions for comparing the args e1_reg and e2_reg and 
  * constructs an auto-generated jump label using the jmp_instr_constructor.
  * jump_instr_constructor should take in a label name and create the appropriate jump instruction
*)
let generate_cmp_func
    (e1_reg : arg) 
    (e2_reg : arg) 
    (jmp_instr_constructor : (string -> instruction)) 
    (tag : int)
  : (instruction list) =
  generate_cmp_func_with e1_reg e2_reg jmp_instr_constructor [IMov(Reg(RAX), const_true)] [IMov(Reg(RAX), const_false)] tag "" true
;;

(* sets up a function call (x64) by putting args in the proper registers/stack positions, 
 * calling the given function, and cleaning up the stack after 
*)
let setup_call_to_func (num_regs_to_save : int) (args : arg list) (func : arg) (snake_call : bool) : (instruction list) =
  let func_call_comment = ILineComment(
      if snake_call
      then sprintf "Setup snake call (%d args)" num_regs_to_save
      else sprintf "Setup native call (%d args)" num_regs_to_save
    ) in
  (* gets the num of args for the function and the possible snake func reference *)
  let num_args = ((List.length args) - 6) in
  let call = if snake_call then (ICall(RegOffset(1 * word_size, RAX))) else (ICall(func)) in
  (* how many call args must go on the stack *)
  let stack_args = max num_args 0 in
  (* whether an extra stack align var should be used 
   * (are there an odd number of stack args and registers being pushed? ) *)
  let should_stack_align = ((stack_args + num_regs_to_save) mod 2) != 0 in
  (* how many args should be popped off the stack before possible register 
   * restoration? *)
  let cleanup_stack = if should_stack_align 
  (* if stack alignment was needed, then pop off pushed args + the extra align value *)
    then Int64.of_int ((stack_args + 1) * word_size)
    (* otherwise, just pop off pushed args *)
    else Int64.of_int (stack_args * word_size)
  in
  (* Backs up all registers used by the function we're in *)
  let rec backup_caller_saved_registers (rem_args : int) (registers : reg list) : (instruction list) =
    if rem_args = 0
    then []
    else
      begin
        match registers with 
        | [] -> []
        | next_reg :: rest_regs -> 
          IPush(Reg(next_reg)) 
          :: (backup_caller_saved_registers (rem_args - 1) rest_regs)
      end in
  (* Restores all registers used by the function we're in. Reverse of backup_caller_saved_registers *)
  let rec restore_caller_saved_registers (args_to_skip : int) (registers : reg list) : (instruction list) =
    match registers with 
    | [] -> []
    | next_reg :: rest_regs -> 
      if args_to_skip = 0
      then IPop(Reg(next_reg)) :: (restore_caller_saved_registers 0 rest_regs) 
      else (restore_caller_saved_registers (args_to_skip - 1) rest_regs)
  in
  (* sets up args by putting them in the first 6 registers needed for a call
   * and placing any remaining values on the stack 
  *)
  let rec setup_args (args : arg list) (registers : reg list) : (instruction list) =
    (* assoc list of args to their position in the call regs list *)
    let reg_assoc_list = List.mapi (fun pos value -> (value, pos + 1)) first_six_args_registers in
    (* put the next argument in the appropriate register or onto the stack.
     * reverses the args list before pushing on the stack so they're in the right order *)
    let use_reg (next_arg : arg) (rest_args : arg list) : instruction list =
      match registers with 
      | [] -> IPush(next_arg) :: (setup_args rest_args registers)
      | last_reg :: [] -> 
        IMov(Reg(last_reg), next_arg) :: (setup_args (List.rev rest_args) [])
      | next_reg :: rest_regs -> IMov(Reg(next_reg), next_arg) :: (setup_args rest_args rest_regs)
    in
    (* if a value being passed into the next function is an arg passed into this
     * function by a register, then convert that reference to 
     * the stack offset of the arg pushed previously.
     * if the register isn't one of first_six_args_registers, then just use the register *)
    let swap_reg (register : reg) (rest_args : arg list) : instruction list =
      match List.assoc_opt register reg_assoc_list with 
      | Some(idx) -> 
        (* skip the extra stack align spot if applicable *)
        let align_off = if should_stack_align then 1 else 0 in
        (* get the offset = RSP + 8 * (number of spots to get to the pushed reg value) *)
        let off = (align_off + num_regs_to_save - idx) in
        use_reg (RegOffset(off * word_size, RSP)) rest_args
      | None -> use_reg (Reg(register)) rest_args
    in
    match args with 
    | [] -> []
    (* replace the register if it's one passed in *)
    | Reg(some_reg) :: rest_args ->
      swap_reg some_reg rest_args
    (* just use the arg *)
    | next_arg :: rest_args ->
      use_reg next_arg rest_args
  in 
  let check_call_type = if snake_call 
    then 
      IMov(Reg(RAX), func) :: (tag_check func label_SHOULD_BE_FUN closure_tag_mask closure_tag)
      @ [
        ILineComment("Check call type for lambda");
        (* remove tag *)
        ISub(Reg(RAX), Const(5L));
        (* check arity *)
        IMov(Reg(R10), RegOffset(0, RAX));
        ICmp(Reg(R10), Const(Int64.of_int (List.length args)));
        IJne(Label(label_ARITY))
      ]
    else [ILineComment("Skip call type check for native func")] 
  in
  func_call_comment
  (* push args passed into this function so they don't get overwritten *)
  :: (backup_caller_saved_registers num_regs_to_save first_six_args_registers)
  (* align the stack if necessary *)
  @ (if should_stack_align 
     then [IInstrComment(IPush(Const(0L)), "Stack align")] 
     else [ILineComment("No stack align")])
  @ check_call_type
  @ [ILineComment("Setup args")]
  (* put the args for the next function in registers/on the stack *)
  @ (setup_args args first_six_args_registers) 
  (* call *)
  @ [IInstrComment(call, "Do call"); ILineComment("Cleanup stack and restore caller saved registers")]
  (* pop off values added to the stack up to pushed register values *)
  @ (if Int64.equal cleanup_stack 0L then [] else [IAdd(Reg(RSP), Const(cleanup_stack))])
  (* restore register values for the rest of this function to use *)
  @ (restore_caller_saved_registers ((List.length first_six_args_registers) - num_regs_to_save) (List.rev first_six_args_registers))
;;

let rec compile_fun (fun_name : string) args frees body env : instruction list =
  (* get max allocation needed as an even value, possibly rounded up *)
  let parity_offset = (List.length frees) mod 2 in
  let stack_alloc_space = (((deepest_stack body env) + 1 + parity_offset) / 2 ) * 2 in
  [
    IJmp(Label(sprintf "%s_end" fun_name));
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    (* TODO: change to maybe when implementing tail recursion *)
  ]
  @ (List.mapi (fun (i: int) (f: string) -> IPush(Sized(QWORD_PTR, RegOffset((i + 3) * word_size, RAX)))) frees)
  @ [
    ISub(Reg(RSP), Const(Int64.of_int (stack_alloc_space * word_size)));
  ] 
  @ (compile_aexpr body env (List.length args) false) @ [
    IMov(Reg(RSP), Reg(RBP));
    IPop(Reg(RBP));
    IRet;
    ILabel(sprintf "%s_end" fun_name);
  ]
and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with
  | ALet(id, bind, body, _) ->
    let prelude = compile_cexpr bind env num_args is_tail in
    let body = compile_aexpr body env num_args is_tail in
    prelude
    @ [ IMov(find env id, Reg(RAX)) ]
    @ body
  | ACExpr(body) -> 
    (compile_cexpr body env num_args is_tail)
  | ALetRec(binds, body, _) -> 
    let lambda_setups = List.map (fun lambda -> 
        (match lambda with 
         | CLambda(name, args, body) -> setup_lambda n))
        (List.flatten 
           (List.map (fun (name, bind) -> (compile_cexpr bind env num_args is_tail) @ [IMov(find env name, Reg(RAX))]) binds))
                        @ compile_aexpr body env num_args is_tail
    and compile_cexpr (e : tag cexpr) env num_args is_tail =
      match e with 
      | CIf(cond, thn, els, tag) ->
        let if_t = (sprintf "if_true_%n" tag) and
        if_f = (sprintf "if_false_%n" tag) and
        done_txt = (sprintf "done_%n" tag) and
        thn = compile_aexpr thn env num_args is_tail and
        els = compile_aexpr els env num_args is_tail and
        cond_value = compile_imm cond env in
        IMov(Reg(RAX), cond_value) ::
        (tag_check cond_value label_NOT_BOOL bool_tag_mask bool_tag)
        @ [
          IMov(Reg(R10), bool_mask); ITest(Reg(RAX), Reg(R10));
          IJz(Label(if_f));
          ILabel(if_t);
        ] @ thn @ [
          IJmp(Label(done_txt));
          ILabel(if_f); 
        ] @ els @ [
          ILabel(done_txt);
        ]
      | CPrim1(op, body, tag) ->
        let e_reg = compile_imm body env in
        begin match op with
          | Add1 -> 
            IMov(Reg(RAX), e_reg) ::
            (num_tag_check label_ARITH_NOT_NUM)
            @ [IAdd(Reg(RAX), Sized(QWORD_PTR, Const(2L))); IJo(Label(label_OVERFLOW))]
          | Sub1 -> 
            IMov(Reg(RAX), e_reg) ::
            (num_tag_check label_ARITH_NOT_NUM)
            @ [IAdd(Reg(RAX), Sized(QWORD_PTR, Const(Int64.neg 2L))); IJo(Label(label_OVERFLOW))]
          | IsBool -> 
            let label_not_bool = (sprintf "%s%n" label_IS_NOT_BOOL tag) in 
            let label_done = (sprintf "%s%n_bool" label_DONE tag) in
            IMov(Reg(RAX), e_reg) ::
            (* check if value is a bool, and if not, then jump to label_not_bool *)
            (tag_check const_true label_not_bool bool_tag_mask bool_tag)
            @ [
              IJmp(Label(label_done));
              ILabel(label_not_bool);
              IMov(Reg(RAX), const_false);
              ILabel(label_done);
            ]
          | IsNum ->
            let label_not_num = (sprintf "%s%n" label_IS_NOT_NUM tag) in 
            let label_done = (sprintf "%s%n_num" label_DONE tag) in
            IMov(Reg(RAX), e_reg) :: 
            (* check if value is a num, and if not, then jump to label_not_num *)
            (num_tag_check label_not_num)
            @ [
              IMov(Reg(RAX), const_true);
              IJmp(Label(label_done));
              ILabel(label_not_num);
              IMov(Reg(RAX), const_false);
              ILabel(label_done);
            ]
          | IsTuple ->
            let label_not_tuple = (sprintf "%s%n" label_IS_NOT_TUPLE tag) in 
            let label_done = (sprintf "%s%n_tuple" label_DONE tag) in
            IMov(Reg(RAX), e_reg) :: 
            (* check if value is a tuple, and if not, then jump to label_not_tuple *)
            (tag_check const_true label_not_tuple tuple_tag_mask tuple_tag)
            @ [
              IJmp(Label(label_done));
              ILabel(label_not_tuple);
              IMov(Reg(RAX), const_false);
              ILabel(label_done);
            ]
          | Not -> 
            IMov(Reg(RAX), e_reg) ::
            (tag_check e_reg label_NOT_BOOL bool_tag_mask bool_tag)
            @ [ 
              IMov(Reg(R10), bool_mask);
              IXor(Reg(RAX), Reg(R10));
            ]
          | Print -> (setup_call_to_func num_args [e_reg] (Label("print")) false)
          | PrintStack -> (setup_call_to_func num_args [e_reg; Reg(RSP); Reg(RBP); Const(Int64.of_int num_args)] (Label("print_stack")) false)
        end
      | CPrim2(op, l, r, tag) ->
        let e1_reg = (compile_imm l env) in
        let e2_reg = (compile_imm r env) in
        (* generates the instructions for performing a Prim2 arith operation on args e1_reg and e2_reg.
         * the body should perform operations using RAX and R10, where e1_reg and e2_reg 
         * will be moved to respectively.
         * after the arith operation completes, the result is checked for overflow.
        *)
        let generate_arith_func 
            (e1_reg : arg) 
            (e2_reg : arg) 
            (body : instruction list) : instruction list =
          IMov(Reg(RAX), e2_reg) :: 
          (num_tag_check label_ARITH_NOT_NUM) @ [IMov(Reg(RAX), e1_reg)]
          @ (num_tag_check label_ARITH_NOT_NUM) @ [IMov(Reg(R10), e2_reg)]
          @ body
          @ [IJo(Label(label_OVERFLOW))]
        in
        begin match op with
          | SPlus -> 
            (generate_arith_func e1_reg e2_reg [IAdd(Reg(RAX), Reg(R10))])
          | SMinus -> 
            (generate_arith_func e1_reg e2_reg [ISub(Reg(RAX), Reg(R10))])
          | STimes -> 
            (generate_arith_func e1_reg e2_reg 
               [ISar(Reg(RAX), Const(1L)); IMul(Reg(RAX), Reg(R10))])
          | SGreater -> 
            (generate_cmp_func e1_reg e2_reg (fun l -> IJg(Label(l))) tag)
          | SGreaterEq -> 
            (generate_cmp_func e1_reg e2_reg (fun l -> IJge(Label(l))) tag)
          | SLess -> 
            (generate_cmp_func e1_reg e2_reg (fun l -> IJl(Label(l))) tag)
          | SLessEq ->
            (generate_cmp_func e1_reg e2_reg (fun l -> IJle(Label(l))) tag)
          | SEq ->
            let label_done = (sprintf "%s%n_eq" label_DONE tag) in
            [IMov(Reg(RAX), e1_reg); IMov(Reg(R10), e2_reg); 
             ICmp(Reg(RAX), Reg(R10)); IMov(Reg(RAX), const_true);
             IJe(Label(label_done)); IMov(Reg(RAX), const_false);
             ILabel(label_done)]
          | SCheckSize ->
            (* convert to snake val then compare *)
            (* Then move to RAX *)
            [IMov(Reg(R11), Sized(QWORD_PTR, e1_reg)); ISub(Reg(R11), Const(1L)); IMov(Reg(R11), RegOffset(0, R11)); IShl(Reg(R11), Const(1L));
             ICmp(Reg(R11), Sized(QWORD_PTR, e2_reg)); IJne(Label(label_DESTRUCTURE_INVALID_LEN));
             IMov(Reg(RAX), Sized(QWORD_PTR, e1_reg));]
        end
      | CApp(func, args, Native, _) -> 
        let arg_regs = (List.map (fun (a) -> (compile_imm a env)) args) in 
        (setup_call_to_func num_args arg_regs (Label(get_func_name_imm func)) false)
      | CApp(func, args, Snake, _) -> 
        (setup_call_to_func num_args (List.map (fun e -> compile_imm e env) args) (compile_imm func env) true)
      | CApp(func, args, _, _) -> (raise (InternalCompilerError "unknown function type"))
      | CImmExpr(value) -> [IMov(Reg(RAX), compile_imm value env)]
      | CTuple(vals, _) ->
        let length = List.length vals in
        (* length at [0] *)
        IMov(Sized(QWORD_PTR, RegOffset(0, heap_reg)), Const(Int64.of_int length)) :: 
        (* items at [1:length + 1] *)
        List.flatten (List.mapi (fun idx v -> 
            [
              IMov(Reg(R11), compile_imm v env);
              IMov(Sized(QWORD_PTR, RegOffset((idx + 1) * word_size, heap_reg)), Reg(R11));
            ]) vals)
        (* filler at [length + 1:16 byte alignment]?*)
        @ [
          (* Move result to result place *)
          IMov(Reg(RAX), Reg(heap_reg));
          IAdd(Reg(RAX), Const(tuple_tag));
          (* mov heap_reg to new aligned heap_reg 1 space later *)
          IAdd(Reg(heap_reg), Const(Int64.of_int (16 * (Int.max length 1) + 1)));
          IAnd(Reg(heap_reg), HexConst(0xfffffffffffffff0L));
        ]
      | CGetItem(tuple, idx, tag) -> 
        let tuple = compile_imm tuple env in
        let idx = compile_imm idx env in
        (* Check tuple is tuple *)
        (IMov(Reg(RAX), tuple) :: (tag_check tuple label_NOT_TUPLE tuple_tag_mask tuple_tag)
         (* Check index is num *)
         @ [ (* ensure tuple isn't nil *)
           IMov(Reg(R11), nil);
           ICmp(Reg(RAX), Reg(R11));
           IJe(Label(label_NIL_DEREF));
           IMov(Reg(RAX), idx) 
         ] @ (num_tag_check label_TUPLE_ACCESS_NOT_NUM)
         @ [ (* convert to machine num *)
           IMov(Reg(RAX), tuple);
           IMov(Reg(R11), idx);
           ISar(Reg(R11), Const(1L));
           (* check bounds *)
           ISub(Reg(RAX), Const(tuple_tag));
           IMov(Reg(RAX), RegOffset(0, RAX));
           ICmp(Reg(R11), Reg(RAX));
           IMov(Reg(RAX), tuple);
           IJge(Label(label_GET_HIGH_INDEX));
           ICmp(Reg(R11), Sized(QWORD_PTR, Const(0L)));
           IJl(Label(label_GET_LOW_INDEX));
           ISub(Reg(RAX), Const(tuple_tag));
           (* get value *)
           IMov(Reg(RAX), RegOffsetReg(RAX, R11, word_size, word_size))])
      | CSetItem(tuple, idx, set, _) -> 
        let tuple = compile_imm tuple env in
        let idx = compile_imm idx env in
        let set = compile_imm set env in
        (* Check tuple is tuple *)
        (IMov(Reg(RAX), tuple) :: (tag_check tuple label_NOT_TUPLE tuple_tag_mask tuple_tag)
         (* Check index is num *)
         @ [ (* ensure tuple isn't nil *)
           IMov(Reg(R11), nil);
           ICmp(Reg(RAX), Reg(R11));
           IJe(Label(label_NIL_DEREF));
           IMov(Reg(RAX), idx) 
         ] @ (num_tag_check label_TUPLE_ACCESS_NOT_NUM)
         @ [ (* convert to machine num *)
           IMov(Reg(RAX), tuple);
           IMov(Reg(R11), idx);
           ISar(Reg(R11), Const(1L));
           (* check bounds *)
           ISub(Reg(RAX), Const(tuple_tag));
           IMov(Reg(RAX), RegOffset(0, RAX));
           ICmp(Reg(R11), Reg(RAX));
           IMov(Reg(RAX), tuple);
           IJge(Label(label_GET_HIGH_INDEX));
           ICmp(Reg(R11), Sized(QWORD_PTR, Const(0L)));
           IJl(Label(label_GET_LOW_INDEX));
           ISub(Reg(RAX), Const(tuple_tag));
           (* get value *)
           IMov(Reg(R12), set);
           IMov(Sized(QWORD_PTR, RegOffsetReg(RAX, R11, word_size, word_size)), Reg(R12));
           IMov(Reg(RAX), set)])
      | CLambda(_) -> compile_lambda e env false
    and compile_imm e env =
      match e with
      | ImmNum(n, _) -> Const(Int64.shift_left n 1)
      | ImmBool(true, _) -> const_true
      | ImmBool(false, _) -> const_false
      | ImmId(x, _) -> (find env x)
      | ImmNil(_) -> nil
    and setup_lambda name args frees =
      [
        ILineComment("Setup lambda");
        (* store arity in first slot as a machine number since it's never accessed in our language *)
        IMov(Sized(QWORD_PTR, RegOffset(0, heap_reg)), Const(Int64.of_int (List.length args)));
        (* store the function address in the second slot TODO: is name good?*)
        IMov(Sized(QWORD_PTR, RegOffset(word_size, heap_reg)), Label(name));
        (* store the # of free variables in the 3rd slot as a machine # since it's never accessed in our language *)
        IMov(Sized(QWORD_PTR, RegOffset(word_size * 2, heap_reg)), Const(Int64.of_int (List.length frees)));
        ILineComment("Save lambda");
        (* Move result to result place *)
        IMov(Reg(RAX), Reg(heap_reg));
      ]
    and compile_lambda lam env do_setup =
      match lam with
      | CLambda(args, body, tag) -> 
        let name = sprintf "fun_%d" tag in
        let frees = free_vars body args in
        let newenv = (get_lambda_envt args body frees) @ env in
        ILineComment(sprintf "Compile lambda (%d args)" (List.length args))
        :: compile_fun name args frees body newenv
        @ (if do_setup 
           then setup_lambda name args frees
           else [])
        @ [ILineComment("Move free vars into lambda")]
        (* store free variables at [3:] *)
        @ List.flatten (List.mapi (fun idx (id: string) -> 
            [
              IMov(Reg(R11), (find env id));
              IMov(Sized(QWORD_PTR, RegOffset((idx + 3) * word_size, heap_reg)), Reg(R11));
            ]) frees)
        @ [
          ILineComment("Tag lambda");
          IAdd(Reg(RAX), Const(closure_tag));
          (* mov heap_reg to new aligned heap_reg *)
          IAdd(Reg(heap_reg), Const(Int64.of_int (16 * ((List.length frees) + 3) + 1)));
          IAnd(Reg(heap_reg), HexConst(0xfffffffffffffff0L));
          ILineComment("Lambda done");
        ]
      | _ -> raise (InternalCompilerError "Compile lambda called with non-lambda")

let compile_error_handler ((err_name : string), (err_code : int64)) : instruction list =
  ILabel(err_name) :: setup_call_to_func 0 [Const(err_code); Reg(RAX)] (Label("error")) false

let rec compile_ocsh (body : tag aexpr) (env: arg envt) : instruction list =
  (* get max allocation needed as an even value, possibly rounded up *)
  let stack_alloc_space = (((deepest_stack body env) + 1) / 2 ) * 2 in
  [
    ILabel("our_code_starts_here");
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    ISub(Reg(RSP), Const(Int64.of_int (stack_alloc_space * word_size)));
    ILineComment("heap start");
    IInstrComment(IMov(Reg(heap_reg), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
    IInstrComment(IAdd(Reg(heap_reg), Const(15L)), "Align it to the nearest multiple of 16");
    IInstrComment(IAnd(Reg(heap_reg), HexConst(0xFFFFFFFFFFFFFFF0L)), "by adding no more than 15 to it")
  ] @ (compile_aexpr body env 0 false) @ [
    IMov(Reg(RSP), Reg(RBP));
    IPop(Reg(RBP));
    IRet;
  ]

let compile_prog ((anfed : tag aprogram), (env: arg envt)) : string =
  match anfed with
  | AProgram(body, _) ->
    let comp_body = compile_ocsh body (env @ initial_fun_env_env) in 
    let body_epilogue = (List.flatten (List.map compile_error_handler [
        (label_COMP_NOT_NUM, err_COMP_NOT_NUM);
        (label_ARITH_NOT_NUM, err_ARITH_NOT_NUM);
        (label_NOT_BOOL, err_NOT_BOOL);
        (label_NOT_TUPLE, err_GET_NOT_TUPLE);
        (label_GET_LOW_INDEX, err_GET_LOW_INDEX);
        (label_GET_HIGH_INDEX, err_GET_HIGH_INDEX);
        (label_TUPLE_ACCESS_NOT_NUM, err_GET_NOT_NUM);
        (label_OVERFLOW, err_OVERFLOW);
        (label_NIL_DEREF, err_NIL_DEREF);
        (label_DESTRUCTURE_INVALID_LEN, err_DESTRUCTURE_INVALID_LEN);
        (label_SHOULD_BE_FUN, err_SHOULD_BE_FUN);
        (label_ARITY, err_ARITY);
      ])) in

    let main = to_asm (comp_body @ body_epilogue) in
    sprintf "%s%s\n" prelude main

let desugar (p : tag program) : unit program =
  let rec helpBind (bind : 'a bind) (exp : 'a expr) : unit binding list =
    match bind with
    | BBlank(_) | BName(_, _, _) -> [(untagB bind, helpE exp, ())]
    | BTuple(bindings, tag) ->
      let original_tuple_id = sprintf "bind_temp%d" tag in
      let updated_bindings = List.flatten (List.mapi 
                                             (fun (i : int) (b : tag bind) -> (helpBind b (EGetItem(EId(original_tuple_id, tag), ENumber(Int64.of_int i, tag), tag)))) 
                                             bindings) in
      let tuple = helpE exp in
      (BName(original_tuple_id, false, ()), EPrim2(CheckSize, tuple, ENumber(Int64.of_int (List.length bindings), ()), ()), ()) :: updated_bindings
  and helpLetRecBinding (bind, expr, _ : 'a binding) : unit binding =
    match bind with
    | BName(name, _, _) -> (untagB bind, helpE expr, ())
    | BBlank(_) | BTuple(_) -> raise (InternalCompilerError "Unable to have blanks or destructure in let rec")
  and helpE (e : tag expr) : unit expr (* other parameters may be needed here *) =
    match e with 
    | ESeq(e1, e2, _) -> ELet([(BBlank(()), helpE e1, ())], helpE e2, ())
    | ETuple(e, _) -> ETuple(List.map helpE e, ())
    | EGetItem(item, idx, _) -> EGetItem(helpE item, helpE idx, ())
    | ESetItem(item, idx, set, _) -> ESetItem(helpE item, helpE idx, helpE set, ())
    | ELet(bindings, body, _) -> 
      ELet(
        List.flatten (List.map (fun (bind, exp, _) -> helpBind bind exp) bindings),
        helpE body, 
        ())
    | EPrim1(op, e, _) ->
      EPrim1(op, helpE e, ())
    | EPrim2(op, e1, e2, a) ->
      begin
        match op with
        | And -> EIf(
            helpE e1,
            EIf(
              helpE e2,
              EBool(true, ()),
              EBool(false, ()),
              ()),
            EBool(false, ()),
            ())
        | Or -> EIf(
            helpE e1,
            EBool(true, ()),
            EIf(
              helpE e2,
              EBool(true, ()),
              EBool(false, ()),
              ()),
            ())
        | p -> EPrim2(p, helpE e1, helpE e2, ())
      end
    | EIf(cond, thn, els, _) ->
      EIf(helpE cond, helpE thn, helpE els, ())
    | ENumber(n, _) -> ENumber(n, ())
    | EBool(b, _) -> EBool(b, ())
    | ENil(_) -> ENil(())
    | EId(id, _) -> EId(id, ())
    | EApp(f, args, ct, _) -> EApp(helpE f, List.map helpE args, ct, ())
    | ELambda(args, body, _) -> ELambda(List.map untagB args, helpE body, ())
    | ELetRec(bindings, body, _) -> ELetRec(List.map helpLetRecBinding bindings, helpE body, ())
  and helpD (d : tag decl) : unit decl =
    match d with
    | DFun(name, args, body, tag) -> 
      let (env, new_binds) = List.fold_right (fun bind (env, new_binds) ->
          match bind with 
          | BBlank(_) | BName(_, _, _) -> (env, (untagB bind) :: new_binds)
          | BTuple(_, tag) -> 
            let new_name = sprintf "fun_arg#%d" tag in
            let prologue_binds = helpBind bind (EId(new_name, tag)) in
            (prologue_binds @ env, (BName(new_name, false, ())) :: new_binds)
        ) args ([], []) in
      match env with 
      | [] -> DFun(name, new_binds, helpE body, ())
      | _::_ -> DFun(name, new_binds, ELet(env, helpE body, ()), ())
  and helpDs (d : tag decl list) : unit decl list =
    (List.map helpD d)
  and decl_list_to_bind_list (d : unit decl list): unit binding list =
    (List.map (fun (d: unit decl) -> match d with | DFun(name, args, body, _) -> (BName(name, false, ()), ELambda(args, body, ()), ())) d)
  and combine_decls_into_letrec (decls : unit decl list list) (body : unit expr) : unit expr =
    (List.fold_right (fun (d: unit decl list) (acc: unit expr) -> ELetRec((decl_list_to_bind_list d), acc, ())) decls body)
  in
  match p with
  | Program(decls, body, _) ->
    Program([], combine_decls_into_letrec (List.map helpDs decls) (helpE body), ())
;;


let run_if should_run f =
  if should_run then f else no_op_phase
;;

(* Add at least one desugaring phase somewhere in here *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase desugared desugar)
  |> (add_phase tagged tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
