open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors

module StringSet = Set.Make(String)


type 'a name_envt = (string * 'a) list
type 'a tag_envt  = (tag * 'a) list


let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env;;


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

let err_COMP_NOT_NUM     = 1L
let err_ARITH_NOT_NUM    = 2L
let err_NOT_BOOL         = 3L
let err_DESTRUCTURE_INVALID_LEN = 4L
let err_OVERFLOW         = 5L
let err_GET_NOT_TUPLE    = 6L
let err_GET_LOW_INDEX    = 7L
let err_GET_HIGH_INDEX   = 8L
let err_NIL_DEREF        = 9L
let err_OUT_OF_MEMORY    = 10L
let err_SET_NOT_TUPLE    = 11L
let err_SET_LOW_INDEX    = 12L
let err_SET_HIGH_INDEX   = 13L
let err_CALL_NOT_CLOSURE = 14L
let err_CALL_ARITY_ERR   = 15L
let err_GET_NOT_NUM      = 16L
let err_SET_NOT_NUM      = 17L

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

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos);;

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11

let nil = HexConst(tuple_tag)

(* you can add any functions or data defined by the runtime here for future use *)
let prim_bindings = [];;
let native_fun_bindings = [
  ("input", (Native, 0));
  ("equal", (Native, 2));
];;

let initial_fun_env = prim_bindings @ native_fun_bindings;;

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
    | ASeq(e1, e2, _) -> max (helpC e1) (helpA e2)
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

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | [x] -> None
  | x::xs ->
    if find_one xs x then Some(x) else find_dup xs
;;

let rec find_opt (env : 'a name_envt) (elt: string) : 'a option =
  match env with
  | [] -> None
  | (x, v) :: rst -> if x = elt then Some(v) else find_opt rst elt
;;

(* Prepends a list-like env onto an name_envt *)
let merge_envs list_env1 list_env2 =
  list_env1 @ list_env2
;;

(* Combines two name_envts into one, preferring the first one *)
let prepend env1 env2 =
  let rec help env1 env2 =
    match env1 with
    | [] -> env2
    | ((k, _) as fst)::rst ->
      let rst_prepend = help rst env2 in
      if List.mem_assoc k env2 then rst_prepend else fst::rst_prepend
  in
  help env1 env2
;;

let env_keys e = List.map fst e;;

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let rec deepest_stack e (env: arg name_envt name_envt) current_env =
  let rec helpA e =
    match e with
    | ALet(name, bind, body, _) -> List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ALetRec(binds, body, _) -> List.fold_left max (helpA body) (List.map (fun (_, bind) -> helpC bind) binds)
    | ASeq(expr1, expr2, _) -> helpC expr1 + helpA expr2
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
    | CLambda(args, body, _) -> 1
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId(name, _) -> name_to_offset name
  and name_to_offset name =
    match find (find env current_env) name with
    | RegOffset(bytes, RBP) -> bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;


(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = (sourcespan * int option * int option)
let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E e (env : scope_info name_envt) =
    debug_printf "In wf_E: %s\n" (ExtString.String.join ", " (env_keys env));
    match e with
    | ESeq(e1, e2, _) -> wf_E e1 env @ wf_E e2 env
    | ETuple(es, _) -> List.concat (List.map (fun e -> wf_E e env) es)
    | EGetItem(e, idx, pos) ->
      wf_E e env @ wf_E idx env
    | ESetItem(e, idx, newval, pos) ->
      wf_E e env @ wf_E idx env @ wf_E newval env
    | ENil _ -> []
    | EBool _ -> []
    | ENumber(n, loc) ->
      if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
        [Overflow(n, loc)]
      else
        []
    | EId (x, loc) -> if (find_one (List.map fst env) x) then [] else [UnboundId(x, loc)]
    | EPrim1(_, e, _) -> wf_E e env
    | EPrim2(_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf(c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ELet(bindings, body, _) ->
      let rec find_locs x (binds : 'a bind list) : 'a list =
        match binds with
        | [] -> []
        | BBlank _::rest -> find_locs x rest
        | BName(y, _, loc)::rest ->
          if x = y then loc :: find_locs x rest
          else  find_locs x rest
        | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
      let rec find_dupes (binds : 'a bind list) : exn list =
        match binds with
        | [] -> []
        | (BBlank _::rest) -> find_dupes rest
        | (BName(x, _, def)::rest) -> (List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)) @ (find_dupes rest)
        | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
      let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
      let rec process_binds (rem_binds : 'a bind list) (env : scope_info name_envt) =
        match rem_binds with
        | [] -> (env, [])
        | BBlank _::rest -> process_binds rest env
        | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
        | BName(x, allow_shadow, xloc)::rest ->
          let shadow =
            if allow_shadow then []
            else match find_opt env x with
              | None -> []
              | Some (existing, _, _) -> [ShadowId(x, xloc, existing)] in
          let new_env = (x, (xloc, None, None))::env in
          let (newer_env, errs) = process_binds rest new_env in
          (newer_env, (shadow @ errs)) in
      let rec process_bindings bindings (env : scope_info name_envt) =
        match bindings with
        | [] -> (env, [])
        | (b, e, loc)::rest ->
          let errs_e = wf_E e env in
          let (env', errs) = process_binds [b] env in
          let (env'', errs') = process_bindings rest env' in
          (env'', errs @ errs_e @ errs') in
      let (env2, errs) = process_bindings bindings env in
      dupeIds @ errs @ wf_E body env2
    | EApp(func, args, native, loc) ->
      let rec_errors = List.concat (List.map (fun e -> wf_E e env) (func :: args)) in
      (match func with
       | EId(funname, _) -> 
         (match (find_opt env funname) with
          | Some(_, _, Some arg_arity) ->
            let actual = List.length args in
            if actual != arg_arity then [Arity(arg_arity, actual, loc)] else []
          | _ -> [])
       | _ -> [])
      @ rec_errors
    | ELetRec(binds, body, _) ->
      let nonfuns = List.find_all (fun b -> match b with | (BName _, ELambda _, _) -> false | _ -> true) binds in
      let nonfun_errs = List.map (fun (b, _, where) -> LetRecNonFunction(b, where)) nonfuns in


      let rec find_locs x (binds : 'a bind list) : 'a list =
        match binds with
        | [] -> []
        | BBlank _::rest -> find_locs x rest
        | BName(y, _, loc)::rest ->
          if x = y then loc :: find_locs x rest
          else  find_locs x rest
        | BTuple(binds, _)::rest -> find_locs x binds @ find_locs x rest in
      let rec find_dupes (binds : 'a bind list) : exn list =
        match binds with
        | [] -> []
        | (BBlank _::rest) -> find_dupes rest
        | (BName(x, _, def)::rest) -> List.map (fun use -> DuplicateId(x, use, def)) (find_locs x rest)
        | (BTuple(binds, _)::rest) -> find_dupes (binds @ rest) in
      let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) binds) in
      let rec process_binds (rem_binds : sourcespan bind list) (env : scope_info name_envt) =
        match rem_binds with
        | [] -> (env, [])
        | BBlank _::rest -> process_binds rest env
        | BTuple(binds, _)::rest -> process_binds (binds @ rest) env
        | BName(x, allow_shadow, xloc)::rest ->
          let shadow =
            if allow_shadow then []
            else match (find_opt env x) with
              | None -> []
              | Some (existing, _, _) -> if xloc = existing then [] else [ShadowId(x, xloc, existing)] in
          let new_env = (x, (xloc, None, None))::env in
          let (newer_env, errs) = process_binds rest new_env in
          (newer_env, (shadow @ errs)) in

      let (env, bind_errs) = process_binds (List.map (fun (b, _, _) -> b) binds) env in

      let rec process_bindings bindings env =
        match bindings with
        | [] -> (env, [])
        | (b, e, loc)::rest ->
          let (env, errs) = process_binds [b] env in
          let errs_e = wf_E e env in
          let (env', errs') = process_bindings rest env in
          (env', errs @ errs_e @ errs') in
      let (new_env, binding_errs) = process_bindings binds env in

      let rhs_problems = List.map (fun (_, rhs, _) -> wf_E rhs new_env) binds in
      let body_problems = wf_E body new_env in
      nonfun_errs @ dupeIds @ bind_errs @ binding_errs @ (List.flatten rhs_problems) @ body_problems
    | ELambda(binds, body, _) ->
      let rec dupe x args =
        match args with
        | [] -> None
        | BName(y, _, loc)::_ when x = y -> Some loc
        | BTuple(binds, _)::rest -> dupe x (binds @ rest)
        | _::rest -> dupe x rest in
      let rec process_args rem_args =
        match rem_args with
        | [] -> []
        | BBlank _::rest -> process_args rest
        | BName(x, _, loc)::rest ->
          (match dupe x rest with
           | None -> []
           | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
        | BTuple(binds, loc)::rest ->
          process_args (binds @ rest)
      in
      let rec flatten_bind (bind : sourcespan bind) : (string * scope_info) list =
        match bind with
        | BBlank _ -> []
        | BName(x, _, xloc) -> [(x, (xloc, None, None))]
        | BTuple(args, _) -> List.concat (List.map flatten_bind args) in
      (process_args binds) @ wf_E body (merge_envs (List.concat (List.map flatten_bind binds)) env)
  and wf_D d (env : scope_info name_envt) (tyenv : StringSet.t) =
    match d with
    | DFun(_, args, body, _) ->
      let rec dupe x args =
        match args with
        | [] -> None
        | BName(y, _, loc)::_ when x = y -> Some loc
        | BTuple(binds, _)::rest -> dupe x (binds @ rest)
        | _::rest -> dupe x rest in
      let rec process_args rem_args =
        match rem_args with
        | [] -> []
        | BBlank _::rest -> process_args rest
        | BName(x, _, loc)::rest ->
          (match dupe x rest with
           | None -> []
           | Some where -> [DuplicateId(x, where, loc)]) @ process_args rest
        | BTuple(binds, loc)::rest ->
          process_args (binds @ rest)
      in
      let rec arg_env args (env : scope_info name_envt) =
        match args with
        | [] -> env
        | BBlank _ :: rest -> arg_env rest env
        | BName(name, _, loc)::rest -> (name, (loc, None, None))::(arg_env rest env)
        | BTuple(binds, _)::rest -> arg_env (binds @ rest) env in
      (process_args args) @ (wf_E body (arg_env args env))
  and wf_G (g : sourcespan decl list) (env : scope_info name_envt) (tyenv : StringSet.t) =
    let add_funbind (env : scope_info name_envt) d =
      match d with
      | DFun(name, args, _, loc) ->
        (name, (loc, Some (List.length args), Some (List.length args)))::env in
    let env = List.fold_left add_funbind env g in
    let errs = List.concat (List.map (fun d -> wf_D d env tyenv) g) in
    (errs, env)
  in
  match p with
  | Program(decls, body, _) ->
    let initial_env = List.fold_left
        (fun env (name, (_, arg_count)) -> (name, (dummy_span, Some arg_count, Some arg_count))::env)
        [] initial_fun_env in
    let rec find name (decls : 'a decl list) =
      match decls with
      | [] -> None
      | DFun(n, args, _, loc)::rest when n = name -> Some(loc)
      | _::rest -> find name rest in
    let rec dupe_funbinds decls =
      match decls with
      | [] -> []
      | DFun(name, args, _, loc)::rest ->
        (match find name rest with
         | None -> []
         | Some where -> [DuplicateFun(name, where, loc)]) @ dupe_funbinds rest in
    let all_decls = List.flatten decls in
    let initial_tyenv = StringSet.of_list ["Int"; "Bool"] in
    let help_G (env, exns) g =
      let (g_exns, funbinds) = wf_G g env initial_tyenv in
      (List.fold_left (fun xs x -> x::xs) env funbinds, exns @ g_exns) in
    let (env, exns) = List.fold_left help_G (initial_env, dupe_funbinds all_decls) decls in
    debug_printf "In wf_P: %s\n" (ExtString.String.join ", " (env_keys env));
    let exns = exns @ (wf_E body env)
    in match exns with
    | [] -> Ok p
    | _ -> Error exns
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    (fun name ->
       next := !next + 1;
       sprintf "%s_%d" name (!next)) in
  let rec helpP (p : sourcespan program) =
    match p with
    | Program(decls, body, tag) ->
      (* This particular desugaring will convert declgroups into ELetRecs *)
      let merge_sourcespans ((s1, _) : sourcespan) ((_, s2) : sourcespan) : sourcespan = (s1, s2) in
      let wrap_G g body =
        match g with
        | [] -> body
        | f :: r ->
          let span = List.fold_left merge_sourcespans (get_tag_D f) (List.map get_tag_D r) in
          ELetRec(helpG g, body, span) in
      Program([], List.fold_right wrap_G decls (helpE body), tag)
  and helpG g =
    List.map helpD g
  and helpD d =
    match d with
    | DFun(name, args, body, tag) ->
      let helpArg a =
        match a with
        | BTuple(_, tag) ->
          let name = gensym "argtup" in
          let newbind = BName(name, false, tag) in
          (newbind, [(a, EId(name, tag), tag)])
        | _ -> (a, []) in
      let (newargs, argbinds) = List.split (List.map helpArg args) in
      let newbody = ELet(List.flatten argbinds, body, tag) in
      (BName(name, false, tag), ELambda(newargs, helpE newbody, tag), tag)
  and helpBE bind =
    let (b, e, btag) = bind in
    let e = helpE e in
    match b with
    | BTuple(binds, ttag) ->
      (match e with
       | EId _ ->
         expandTuple binds ttag e
       | _ ->
         let newname = gensym "tup" in
         (BName(newname, false, ttag), e, btag) :: expandTuple binds ttag (EId(newname, ttag)))
    | _ -> [(b, e, btag)]
  and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank btag -> []
      | BName(_, _, btag) ->
        [(b, EGetItem(source, ENumber(Int64.of_int(i), dummy_span), tag), btag)]
      | BTuple(binds, tag) ->
        let newname = gensym "tup" in
        let newexpr = EId(newname, tag) in
        (BName(newname, false, tag), EGetItem(source, ENumber(Int64.of_int(i), dummy_span), tag), tag) :: expandTuple binds tag newexpr
    in
    let size_check = EPrim2(CheckSize, source, ENumber(Int64.of_int(List.length binds), dummy_span), dummy_span) in
    let size_check_bind = (BBlank(dummy_span), size_check, dummy_span) in
    size_check_bind::(List.flatten (List.mapi tupleBind binds))
  and helpE e =
    match e with
    | ESeq(e1, e2, tag) -> ELet([(BBlank(tag), helpE e1, tag)], helpE e2, tag)
    | ETuple(exprs, tag) -> ETuple(List.map helpE exprs, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE e, helpE idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE e, helpE idx, helpE newval, tag)
    | EId(x, tag) -> EId(x, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EBool(b, tag) -> EBool(b, tag)
    | ENil(t, tag) -> ENil(t, tag)
    | EPrim1(op, e, tag) ->
      EPrim1(op, helpE e, tag)
    | EPrim2(op, e1, e2, tag) ->
      EPrim2(op, helpE e1, helpE e2, tag)
    | ELet(binds, body, tag) ->
      let newbinds = (List.map helpBE binds) in
      List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body)
    | ELetRec(bindexps, body, tag) ->
      (* ASSUMES well-formed letrec, so only BName bindings *)
      let newbinds = (List.map (fun (bind, e, tag) -> (bind, helpE e, tag)) bindexps) in
      ELetRec(newbinds, helpE body, tag)
    | EIf(cond, thn, els, tag) ->
      EIf(helpE cond, helpE thn, helpE els, tag)
    | EApp(name, args, native, tag) ->
      EApp(helpE name, List.map helpE args, native, tag)
    | ELambda(binds, body, tag) ->
      let expandBind bind =
        match bind with
        | BTuple(_, btag) ->
          let newparam = gensym "tuparg" in
          (BName(newparam, false, btag), helpBE (bind, EId(newparam, btag), btag))
        | _ -> (bind, []) in
      let (params, newbinds) = List.split (List.map expandBind binds) in
      let newbody = List.fold_right (fun binds body -> ELet(binds, body, tag)) newbinds (helpE body) in
      ELambda(params, newbody, tag)

  in helpP p
;;

(* ASSUMES desugaring is complete *)
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
    | EApp(func, args, Snake, tag) ->
      let func = helpE env func in
      EApp(func, List.map (helpE env) args, Snake, tag)
    | EApp(func, args, Native, tag) ->
      EApp(func, List.map (helpE env) args, Native, tag)
    | EApp(func, args, call_type, tag) ->
      let func = helpE env func in
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


(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; ANFING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)


type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program([], body, _) -> AProgram(helpA body, ())
    | Program _ -> raise (InternalCompilerError "decls should have been desugared away")
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) = 
    match e with
    | EPrim1(op, arg, _) ->
      let (arg_imm, arg_setup) = helpI arg in
      (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
      let (cond_imm, cond_setup) = helpI cond in
      (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet([], body, _) -> helpC body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, _) ->
      let processBind (bind, rhs, _) =
        match bind with
        | BName(name, _, _) -> (name, helpC rhs)
        | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                                              (string_of_bind bind))) in
      let (names, new_binds_setup) = List.split (List.map processBind binds) in
      let (new_binds, new_setup) = List.split new_binds_setup in
      let (body_ans, body_setup) = helpC body in
      (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    | ELambda(args, body, _) ->
      let processBind bind =
        match bind with
        | BName(name, _, _) -> name
        | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                                              (string_of_bind bind))) in
      (CLambda(List.map processBind args, helpA body, ()), [])
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
      raise (InternalCompilerError("Tuple bindings should have been desugared away"))
    | EApp(func, args, native, _) ->
      let ct = if native = Native
        then Native
        else Snake in
      let (func_ans, func_setup) = helpI func in
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (CApp(func_ans, new_args, ct, ()), func_setup @ List.concat new_setup)
    | ESeq(e1, e2, _) ->
      let (e1_ans, e1_setup) = helpC e1 in
      let (e2_ans, e2_setup) = helpC e2 in
      (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | ETuple(args, _) ->
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (CTuple(new_args, ()), List.concat new_setup)
    | EGetItem(tup, idx, _) ->
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      (CGetItem(tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem(tup, idx, newval, _) ->
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      let (new_imm, new_setup) = helpI newval in
      (CSetItem(tup_imm, idx_imm, new_imm, ()), tup_setup @ idx_setup @ new_setup)


    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])
    | ENil _ -> (ImmNil(), [])

    | ESeq(e1, e2, _) ->
      let (e1_imm, e1_setup) = helpI e1 in
      let (e2_imm, e2_setup) = helpI e2 in
      (e2_imm, e1_setup @ e2_setup)


    | ETuple(args, tag) ->
      let tmp = sprintf "tup_%d" tag in
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (ImmId(tmp, ()), (List.concat new_setup) @ [BLet (tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, tag) ->
      let tmp = sprintf "get_%d" tag in
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      (ImmId(tmp, ()), tup_setup @ idx_setup @ [BLet (tmp, CGetItem(tup_imm, idx_imm, ()))])
    | ESetItem(tup, idx, newval, tag) ->
      let tmp = sprintf "set_%d" tag in
      let (tup_imm, tup_setup) = helpI tup in
      let (idx_imm, idx_setup) = helpI idx in
      let (new_imm, new_setup) = helpI newval in
      (ImmId(tmp, ()), tup_setup @ idx_setup @ new_setup @ [BLet (tmp, CSetItem(tup_imm, idx_imm, new_imm,()))])

    | EPrim1(op, arg, tag) ->
      let tmp = sprintf "unary_%d" tag in
      let (arg_imm, arg_setup) = helpI arg in
      (ImmId(tmp, ()), arg_setup @ [BLet (tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
      let tmp = sprintf "binop_%d" tag in
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (ImmId(tmp, ()), left_setup @ right_setup @ [BLet (tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
      let tmp = sprintf "if_%d" tag in
      let (cond_imm, cond_setup) = helpI cond in
      (ImmId(tmp, ()), cond_setup @ [BLet (tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, native, tag) ->
      let ct = if native = Native
        then Native
        else Snake in
      let tmp = sprintf "app_%d" tag in
      let (new_func, func_setup) = helpI func in
      let (new_args, new_setup) = List.split (List.map helpI args) in
      (ImmId(tmp, ()), func_setup @ (List.concat new_setup) @ [BLet (tmp, CApp(new_func, new_args, ct, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((BBlank _, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELetRec(binds, body, tag) ->
      let tmp = sprintf "lam_%d" tag in
      let processBind (bind, rhs, _) =
        match bind with
        | BName(name, _, _) -> (name, helpC rhs)
        | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                                              (string_of_bind bind))) in
      let (names, new_binds_setup) = List.split (List.map processBind binds) in
      let (new_binds, new_setup) = List.split new_binds_setup in
      let (body_ans, body_setup) = helpC body in
      (ImmId(tmp, ()), (List.concat new_setup)
                       @ [BLetRec (List.combine names new_binds)]
                       @ body_setup
                       @ [BLet(tmp, body_ans)])
    | ELambda(args, body, tag) ->
      let tmp = sprintf "lam_%d" tag in
      let processBind bind =
        match bind with
        | BName(name, _, _) -> name
        | _ -> raise (InternalCompilerError(sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                                              (string_of_bind bind))) in
      (ImmId(tmp, ()), [BLet(tmp, CLambda(List.map processBind args, helpA body, ()))])
    | ELet((BName(bind, _, _), exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet((BTuple(binds, _), exp, _)::rest, body, pos) ->
      raise (InternalCompilerError("Tuple bindings should have been desugared away"))
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right
      (fun bind body ->
         match bind with
         | BSeq(exp) -> ASeq(exp, body, ())
         | BLet(name, exp) -> ALet(name, exp, body, ())
         | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ACExpr ans)
  in
  helpP p
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
    | ASeq(expr1, expr2, _) -> StringSet.union (help_cexpr expr1 env) (help_aexpr expr2 env)
    | ALet(name, bind, body, _) -> 
      let newenv = StringSet.add name env in 
      StringSet.union (help_cexpr bind newenv) (help_aexpr body newenv)
    | ALetRec(name_binds, body, _) ->
      (* Add all the binds *)
      let env = List.fold_right (fun (bind, _) acc -> StringSet.add bind acc) name_binds env in
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
  let new_args = List.map (fun (name, _) -> sprintf "?%s" name) native_fun_bindings @ args in
  let arg_set = stringset_of_list new_args in
  StringSet.(diff (help_aexpr e arg_set) arg_set |> elements)
;;

type flat_nested_envt = (tag * string * arg) list;;
(** Gets an environment mapping id names to register names or stack offsets.
 * This makes it easy for callee functions to use args *)
let get_func_call_params (params : string list) (closure_args : string list) (wrapping_tag : tag) : flat_nested_envt =
  let rec pair_stack (params : string list) (next_off : int) (direction : int) : flat_nested_envt =
    match params with 
    | [] -> []
    | first :: rest ->
      (wrapping_tag, first, RegOffset(next_off * word_size * direction, RBP))
      :: (pair_stack rest (next_off + 1) direction)
  and pair_regs (params : string list) (regs : reg list) : flat_nested_envt =
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
          (wrapping_tag, param_first, Reg(reg_first))
          :: (pair_regs param_rest reg_rest)
      end
  in
  (pair_regs params first_six_args_registers) @ (pair_stack closure_args 1 ~-1)
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let rec naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg name_envt name_envt =
  let rec add_to_assoc_list 
      (key : string) 
      (name : string) 
      (value : arg) 
      (ls : arg name_envt name_envt) : arg name_envt name_envt =
    match ls with
    | [] -> [(key, [(name, value)])]
    | (found, others) :: rest -> 
      if found = key 
      then (found, (name, value) :: others) :: rest
      else (found, others) :: add_to_assoc_list key name value rest
  in
  match prog with 
  | AProgram(expr, tag) ->
    (prog, List.fold_left 
       (fun acc (t, name, value) -> add_to_assoc_list (string_of_int t) name value acc) 
       [] 
       (get_aexpr_envt expr 1 tag))
and get_aexpr_envt (expr : tag aexpr) (si : int) (wrapping_tag : tag) :  flat_nested_envt =
  match expr with 
  (* TODO: confirm this is correct *)
  | ASeq(expr1, expr2, _) -> (merge_envs (get_cexpr_envt expr1 si wrapping_tag) (get_aexpr_envt expr2 si wrapping_tag))
  | ALet(name, bind, body, _) ->
    (wrapping_tag, name, RegOffset(~-si * word_size, RBP))
    :: (get_cexpr_envt bind (si + 1) wrapping_tag)
    @ (get_aexpr_envt body (si + 1) wrapping_tag)
  | ACExpr(body) ->
    (get_cexpr_envt body si wrapping_tag)
  | ALetRec(binds, body, _) -> 
    let num_binds = List.length binds in
    List.mapi (fun i (name, bind) -> (wrapping_tag, name, RegOffset(~-(si + i) * word_size, RBP))) binds
    @ List.flatten (List.map (fun (_, bind) -> get_cexpr_envt bind (si + 1 + num_binds) wrapping_tag) binds)
    @ (get_aexpr_envt body (si + num_binds + 1) wrapping_tag)
and get_cexpr_envt (expr : tag cexpr) (si : int) (wrapping_tag : tag) : flat_nested_envt =
  match expr with 
  | CIf(_, l, r, _) -> 
    (get_aexpr_envt l si wrapping_tag)
    @ (get_aexpr_envt r si wrapping_tag)
  | CLambda(binds, body, tag) ->
    let frees = free_vars body binds in
    (get_func_call_params binds frees tag)
    @ get_aexpr_envt body (1 + List.length frees) tag
  | CPrim1(_) | CPrim2(_) | CApp(_) | CImmExpr(_) | CTuple(_) | CGetItem(_) | CSetItem(_) -> []


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
     then [ILineComment("Stack align"); IPush(Const(0L))] 
     else [ILineComment("No stack align")])
  @ check_call_type
  @ [ILineComment("Setup args")]
  (* put the args for the next function in registers/on the stack *)
  @ (setup_args args first_six_args_registers) 
  (* call *)
  @ [call; ILineComment("Cleanup stack and restore caller saved registers")]
  (* pop off values added to the stack up to pushed register values *)
  @ (if Int64.equal cleanup_stack 0L then [] else [IAdd(Reg(RSP), Const(cleanup_stack))])
  (* restore register values for the rest of this function to use *)
  @ (restore_caller_saved_registers ((List.length first_six_args_registers) - num_regs_to_save) (List.rev first_six_args_registers))
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq(e1, e2, _) -> max (helpC e1) (helpA e2)
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

and reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [
    IInstrComment(IMov(Reg(RAX), LabelContents("?HEAP_END")),
                  sprintf "Reserving %d words" (size / word_size));
    ISub(Reg(RAX), Const(Int64.of_int size));
    ICmp(Reg(RAX), Reg(heap_reg));
    IJge(Label ok);
  ]
  @ (setup_call_to_func 4 [
      (Sized(QWORD_PTR, Reg(heap_reg))); (* alloc_ptr in C *)
      (Sized(QWORD_PTR, Const(Int64.of_int size))); (* bytes_needed in C *)
      (Sized(QWORD_PTR, Reg(RBP))); (* first_frame in C *)
      (Sized(QWORD_PTR, Reg(RSP))); (* stack_top in C *)
    ] (Label "?try_gc") false)
  @ [
    IInstrComment(IMov(Reg(heap_reg), Reg(RAX)), "assume gc success if returning here, so RAX holds the new heap_reg value");
    ILabel(ok);
  ]

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)

and compile_fun (fun_name : string) args body (env: arg name_envt name_envt) current_env : (instruction list * instruction list * instruction list) =
  (* get max allocation needed as an even value, possibly rounded up *)
  let frees = free_vars body args in 
  let parity_offset = (List.length frees) mod 2 in
  let stack_alloc_space = (((deepest_stack body env current_env) + 1 + parity_offset) / 2 ) * 2 in
  let fun_prologue = [
    IJmp(Label(sprintf "%s_end" fun_name));
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    (* TODO: change to maybe when implementing tail recursion *)
  ]
    @ (List.mapi (fun (i: int) (f: string) -> IPush(Sized(QWORD_PTR, RegOffset((i + 3) * word_size, RAX)))) frees)
    @ [
      ISub(Reg(RSP), Const(Int64.of_int (stack_alloc_space * word_size)));
    ] in 
  let fun_body = (compile_aexpr body env (List.length args) false current_env) in 
  let fun_epilogue = [
    IMov(Reg(RSP), Reg(RBP));
    IPop(Reg(RBP));
    IRet;
    ILabel(sprintf "%s_end" fun_name);
  ] in (fun_prologue, fun_body, fun_epilogue)
and compile_aexpr (e : tag aexpr) (env : arg name_envt name_envt) (num_args : int) (is_tail : bool) current_env : instruction list =
  match e with
  | ALet(id, bind, body, _) ->
    let prelude = compile_cexpr bind env num_args is_tail current_env in
    let body = compile_aexpr body env num_args is_tail current_env in
    prelude
    @ [ IInstrComment(IMov(find (find env current_env) id, Reg(RAX)), sprintf "save %s" id) ]
    @ body
  | ASeq(expr1, expr2, _) -> compile_cexpr expr1 env num_args is_tail current_env  @ compile_aexpr expr2 env num_args is_tail current_env
  | ACExpr(body) -> 
    (compile_cexpr body env num_args is_tail current_env)
  | ALetRec(binds, body, _) -> 
    let lambda_setups = List.flatten (List.map (fun (name, bind) -> 
        match bind with 
        | CLambda(args, body, tag) -> 
          let newname = sprintf "fun_%d" tag in
          let frees = free_vars body args in
          (setup_lambda newname args frees)
          @ [IInstrComment(IMov(find (find env current_env) name, Reg(RAX)), sprintf "save (rec) %s" name)]
        | _ -> raise (InternalCompilerError "Tried to compile non lambda in let rec")) binds)
    in 
    let lambda_comps = List.flatten (List.map (fun (name, bind) ->
        IMov(Reg(RAX), find (find env current_env) name)
        :: (compile_lambda bind env false current_env)) binds)
    in 
    lambda_setups 
    @ lambda_comps
    @ (compile_aexpr body env num_args is_tail current_env)
and compile_cexpr (e : tag cexpr) env num_args is_tail current_env =
  match e with 
  | CIf(cond, thn, els, tag) ->
    let if_t = (sprintf "if_true_%n" tag) and
    if_f = (sprintf "if_false_%n" tag) and
    done_txt = (sprintf "done_%n" tag) and
    thn = compile_aexpr thn env num_args is_tail current_env and
    els = compile_aexpr els env num_args is_tail current_env and
    cond_value = compile_imm cond env current_env in
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
    let e_reg = compile_imm body env current_env in
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
      | Print -> (setup_call_to_func num_args [e_reg] (Label("?print")) false)
      | PrintStack -> (setup_call_to_func num_args [e_reg; Reg(RSP); Reg(RBP); Const(Int64.of_int num_args)] (Label("?print_stack")) false)
    end
  | CPrim2(op, l, r, tag) ->
    let e1_reg = (compile_imm l env current_env) in
    let e2_reg = (compile_imm r env current_env) in
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
      | And -> raise (InternalCompilerError "And should be desugared")
      | Or -> raise (InternalCompilerError "Or should be desugared")
      | Plus -> 
        (generate_arith_func e1_reg e2_reg [IAdd(Reg(RAX), Reg(R10))])
      | Minus -> 
        (generate_arith_func e1_reg e2_reg [ISub(Reg(RAX), Reg(R10))])
      | Times -> 
        (generate_arith_func e1_reg e2_reg 
           [ISar(Reg(RAX), Const(1L)); IMul(Reg(RAX), Reg(R10))])
      | Greater -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJg(Label(l))) tag)
      | GreaterEq -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJge(Label(l))) tag)
      | Less -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJl(Label(l))) tag)
      | LessEq ->
        (generate_cmp_func e1_reg e2_reg (fun l -> IJle(Label(l))) tag)
      | Eq ->
        let label_done = (sprintf "%s%n_eq" label_DONE tag) in
        [IMov(Reg(RAX), e1_reg); IMov(Reg(R10), e2_reg); 
         ICmp(Reg(RAX), Reg(R10)); IMov(Reg(RAX), const_true);
         IJe(Label(label_done)); IMov(Reg(RAX), const_false);
         ILabel(label_done)]
      | CheckSize ->
        (* compare *)
        (* Then move to RAX *)
        [IMov(Reg(R11), Sized(QWORD_PTR, e1_reg)); ISub(Reg(R11), Const(1L)); IMov(Reg(R11), RegOffset(0, R11));
         ICmp(Reg(R11), Sized(QWORD_PTR, e2_reg)); IJne(Label(label_DESTRUCTURE_INVALID_LEN));
         IMov(Reg(RAX), Sized(QWORD_PTR, e1_reg));]
    end
  | CApp(func, args, Native, _) -> 
    let arg_regs = (List.map (fun (a) -> (compile_imm a env current_env)) args) in 
    (setup_call_to_func num_args arg_regs (Label(get_func_name_imm func)) false)
  | CApp(func, args, Snake, _) -> 
    (setup_call_to_func num_args (List.map (fun e -> compile_imm e env current_env) args) (compile_imm func env current_env) true)
  | CApp(func, args, _, _) -> (raise (InternalCompilerError (sprintf "unknown function type for %s" (get_func_name_imm func))))
  | CImmExpr(value) -> [IMov(Reg(RAX), compile_imm value env current_env)]
  | CTuple(vals, _) ->
    let length = List.length vals in
    (* snake length at [0] *)
    IMov(Sized(QWORD_PTR, RegOffset(0, heap_reg)), Const(Int64.of_int (length * 2))) :: 
    (* items at [1:length + 1] *)
    List.flatten (List.mapi (fun idx v -> 
        [
          IMov(Reg(R11), compile_imm v env current_env);
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
    let tuple = compile_imm tuple env current_env in
    let idx = compile_imm idx env current_env in
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
       IShr(Reg(RAX), Const(1L));
       ICmp(Reg(R11), Reg(RAX));
       IMov(Reg(RAX), idx);
       IJge(Label(label_GET_HIGH_INDEX));
       ICmp(Reg(R11), Sized(QWORD_PTR, Const(0L)));
       IJl(Label(label_GET_LOW_INDEX));
       IMov(Reg(RAX), tuple);
       ISub(Reg(RAX), Const(tuple_tag));
       (* get value *)
       IMov(Reg(RAX), RegOffsetReg(RAX, R11, word_size, word_size))])
  | CSetItem(tuple, idx, set, _) -> 
    let tuple = compile_imm tuple env current_env in
    let idx = compile_imm idx env current_env in
    let set = compile_imm set env current_env in
    (* Check tuple is tuple *)
    (IMov(Reg(RAX), tuple) :: (tag_check tuple label_NOT_TUPLE tuple_tag_mask tuple_tag)
     (* Check index is num *)
     @ [ 
       ILineComment("ensure tuple isn't nil");
       IMov(Reg(R11), nil);
       ICmp(Reg(RAX), Reg(R11));
       IJe(Label(label_NIL_DEREF));
       IMov(Reg(RAX), idx) 
     ] @ (num_tag_check label_TUPLE_ACCESS_NOT_NUM)
     @ [ 
       ILineComment("convert to machine num");
       IMov(Reg(RAX), tuple);
       IMov(Reg(R11), idx);
       ISar(Reg(R11), Const(1L));
       ILineComment("check bounds");
       ISub(Reg(RAX), Const(tuple_tag));
       IMov(Reg(RAX), RegOffset(0, RAX));
       IShr(Reg(RAX), Const(1L));
       ICmp(Reg(R11), Reg(RAX));
       IMov(Reg(RAX), idx);
       IJge(Label(label_GET_HIGH_INDEX));
       ICmp(Reg(R11), Sized(QWORD_PTR, Const(0L)));
       IJl(Label(label_GET_LOW_INDEX));
       IMov(Reg(RAX), tuple);
       ISub(Reg(RAX), Const(tuple_tag));
       ILineComment("get and set value");
       IMov(Reg(R12), set);
       IMov(Sized(QWORD_PTR, RegOffsetReg(RAX, R11, word_size, word_size)), Reg(R12));
       IMov(Reg(RAX), set)])
  | CLambda(_) -> compile_lambda e env true current_env
and compile_imm e env current_env =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find (find env current_env) x)
  | ImmNil(_) -> nil
and setup_lambda name args frees =
  [
    ILineComment("Setup lambda");
    (* store arity in first slot as a machine number since it's never accessed in our language *)
    IMov(Sized(QWORD_PTR, RegOffset(0, heap_reg)), Const(Int64.of_int (List.length args)));
    (* store the function address in the second slot *)
    IMov(Sized(QWORD_PTR, RegOffset(word_size, heap_reg)), Label(name));
    (* store the # of free variables in the 3rd slot as a machine # since it's never accessed in our language *)
    IMov(Sized(QWORD_PTR, RegOffset(word_size * 2, heap_reg)), Const(Int64.of_int (List.length frees)));
    ILineComment("Save lambda");
    (* Move result to result place *)
    IMov(Reg(RAX), Reg(heap_reg));
    (* mov heap_reg to new aligned heap_reg *)
    IAdd(Reg(heap_reg), Const(Int64.of_int (16 * ((List.length frees) + 3) + 1)));
    IAnd(Reg(heap_reg), HexConst(0xfffffffffffffff0L));
    ILineComment("Tag lambda");
    IAdd(Reg(RAX), Const(closure_tag));
  ]
and compile_lambda lam env do_setup current_env =
  match lam with
  | CLambda(args, body, tag) -> 
    let name = sprintf "fun_%d" tag in
    let frees = free_vars body args in
    let fun_prologue, fun_body, fun_epilogue = (compile_fun name args body env (string_of_int tag)) in
    ILineComment(sprintf "Compile lambda (%d args)" (List.length args))
    :: (fun_prologue @ fun_body @ fun_epilogue)
    @ (if do_setup 
       then setup_lambda name args frees
       else [])
    @ [
      (* remove tag *)
      ISub(Reg(RAX), Const(closure_tag));
      ILineComment("Move free vars into lambda");
    ]
    (* store free variables at [3:] *)
    @ List.flatten (List.mapi (fun idx (id: string) -> 
        [
          IMov(Reg(R11), (find (find env current_env) id));
          IMov(Sized(QWORD_PTR, RegOffset((idx + 3) * word_size, RAX)), Reg(R11));
        ]) frees)
    @ [
      ILineComment("Tag lambda");
      IAdd(Reg(RAX), Const(closure_tag));
      ILineComment("Lambda done");
    ]
  | _ -> raise (InternalCompilerError "Compile lambda called with non-lambda")

and args_help args regs =
  match args, regs with
  | arg :: args, reg :: regs ->
    IMov(Sized(QWORD_PTR, Reg(reg)), arg) :: args_help args regs
  | args, [] ->
    List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [DFun(name, 
          List.map (fun name -> 
              BName(name, false, dummy_span)) argnames, 
          EApp(EId("?" ^ name, dummy_span), 
               List.map(fun name -> 
                   EId(name, dummy_span)) argnames, 
               Native, dummy_span), 
          dummy_span)]
  in
  match p with
  | Program(declss, body, tag) ->
    let new_decls = List.fold_left 
        (fun declss (name, (_, arity)) -> (wrap_native name arity)::declss) 
        declss 
        native_fun_bindings
    in
    Program(new_decls, body, tag)


let compile_error_handler ((err_name : string), (err_code : int64)) : instruction list =
  ILabel(err_name) :: setup_call_to_func 0 [Const(err_code); Reg(RAX)] (Label("?error")) false

let compile_prog (anfed, (env : arg name_envt name_envt)) =
  let prelude =
    "section .text
extern ?error
extern ?input
extern ?print
extern ?print_stack
extern ?equal
extern ?try_gc\n" ^ 
    (* extern ?naive_print_heap *)
    " extern ?HEAP
extern ?HEAP_END
extern ?set_stack_bottom
global ?our_code_starts_here" in
  let suffix = (List.flatten (List.map compile_error_handler [
      (label_COMP_NOT_NUM, err_COMP_NOT_NUM);
      (label_ARITH_NOT_NUM, err_ARITH_NOT_NUM);
      (label_NOT_BOOL, err_NOT_BOOL);
      (label_NOT_TUPLE, err_GET_NOT_TUPLE);
      (label_GET_LOW_INDEX, err_GET_LOW_INDEX);
      (label_GET_HIGH_INDEX, err_GET_HIGH_INDEX);
      (label_TUPLE_ACCESS_NOT_NUM, err_NIL_DEREF);
      (label_OVERFLOW, err_OVERFLOW);
      (label_NIL_DEREF, err_NIL_DEREF);
      (label_DESTRUCTURE_INVALID_LEN, err_DESTRUCTURE_INVALID_LEN);
      (label_SHOULD_BE_FUN, err_CALL_NOT_CLOSURE);
      (label_ARITY, err_CALL_ARITY_ERR);
    ]))
  in
  match anfed with
  | AProgram(body, tag) ->
    (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
    let (prologue, comp_main, epilogue) = compile_fun "?our_code_starts_here" ["$heap"; "$size"] body env (string_of_int tag) in
    let heap_start =
      [
        ILineComment("heap start");
        IInstrComment(IMov(Sized(QWORD_PTR, Reg(heap_reg)), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
        IInstrComment(IAdd(Sized(QWORD_PTR, Reg(heap_reg)), Const(15L)), "Align it to the nearest multiple of 16");
        IMov(Reg scratch_reg, HexConst(0xFFFFFFFFFFFFFFF0L));
        IInstrComment(IAnd(Sized(QWORD_PTR, Reg(heap_reg)), Reg scratch_reg), "by adding no more than 15 to it");
      ] in
    let set_stack_bottom =
      [
        IMov(Reg R12, Reg RDI);
      ]
      @ (setup_call_to_func 1 [Reg(RBP)] (Label "?set_stack_bottom") false)
      @ [
        IMov(Reg RDI, Reg R12)
      ] in
    let main = (prologue @ set_stack_bottom @ heap_start @ comp_main @ epilogue) in
    sprintf "%s%s%s\n" prelude (to_asm main) (to_asm suffix)
;;

let run_if should_run f =
  if should_run then f else no_op_phase
;;

let compile_to_string ?no_builtins:(no_builtins=false) (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (run_if (not no_builtins) (add_phase add_natives add_native_lambdas))
  |> (add_phase desugared desugar)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename_and_tag)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
