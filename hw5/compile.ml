open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
       
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

let const_true    = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false   = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask     = HexConst(0x8000000000000000L)
let bool_tag      = 0x0000000000000007L
let bool_tag_mask = 0x0000000000000007L
let num_tag       = 0x0000000000000000L
let num_tag_mask  = 0x0000000000000001L

let err_COMP_NOT_NUM   = 1L
let err_ARITH_NOT_NUM  = 2L
let err_LOGIC_NOT_BOOL = 3L
let err_IF_NOT_BOOL    = 4L
let err_OVERFLOW       = 5L

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]


(* You may find some of these helpers useful *)
let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let deepest_stack e env =
  let rec helpA e =
    match e with
    | ALet(name, bind, body, _) -> List.fold_left max 0 [name_to_offset name; helpC bind; helpA body]
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(c, t, f, _) -> List.fold_left max 0 [helpI c; helpA t; helpA f]
    | CPrim1(_, i, _) -> helpI i
    | CPrim2(_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp(_, args, _) -> List.fold_left max 0 (List.map helpI args)
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId(name, _) -> name_to_offset name
  and name_to_offset name =
    match (find env name) with
    | RegOffset(bytes, RBP) -> bytes / (-1 * word_size)  (* negative because stack direction *)
    | _ -> 0
  in max (helpA e) 0 (* if only parameters are used, helpA might return a negative value *)
;;

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

(* IMPLEMENT EVERYTHING BELOW *)

let rename_expr (e : tag expr) : tag expr =
  let rec help (env : (string * string) list) (e : tag expr) : tag expr =
    match e with
    | EId(x, tag) -> 
      let _, name = (List.find (fun (e, b) -> (String.equal x e)) env) in 
      EId (name, tag)
    | ELet(binds, body, tag) ->
      let (binds_renamed, new_env) = (let_helper env binds) in 
      let body_renamed = (help new_env body) in 
      ELet(binds_renamed, body_renamed, tag)
    | ENumber(n, tag) -> ENumber(n, tag)
    | EPrim1(op, e, tag) ->
      EPrim1(op, help env e, tag)
    | EPrim2(op, e1, e2, tag) ->
      EPrim2(op, help env e1, help env e2, tag)
    | EIf(cond, thn, els, tag) ->
      EIf(help env cond, help env thn, help env els, tag)
    | EBool(b, tag) -> EBool(b, tag)
    (* Todo: maybe add character start/end so their functions don't overlap *)
    | EApp(funname, args, tag) -> EApp(funname, args, tag)
  (* Renames all bindings in a let string and returns them with new env *)
  and let_helper (env : (string * string) list) (binds : tag bind list) : (tag bind list * (string * string) list) =
    match binds with
    | [] -> ([], env)
    | (first, binding, tag)::rest -> 
      let binding_renamed = (help env binding)
      and new_name = (sprintf "%s#%n" first tag) in 
      let (acc, env) = (let_helper ((first, new_name)::env) rest) in
      ((new_name, binding_renamed, tag)::acc, env)
  in help [] e
;;

(* Todo: We don't need to rename decls since their names have to be unique, right? *)
let rename (e : tag program) : tag program =
  match e with
  | Program(decls, expr, tag) -> Program(decls, rename_expr expr, tag)
;;



let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(decls, body, _) -> AProgram(List.map helpD decls, helpA body, ())
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, body, _) -> ADFun(name, List.map fst args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) = 
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
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EApp(funname, args, _) ->
      let imms_and_setups = List.map helpI args in
        (CApp(funname, List.map (fun (imm, _)->imm) imms_and_setups, ()),
        (List.fold_left (fun acc (_, setup) -> acc @ setup) [] imms_and_setups))
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * (string * unit cexpr) list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, tag) ->
       let tmp = sprintf "app_%d" tag in
       let imms_and_setups = List.map helpI args in 
       let imms = List.map (fun (imm, _) -> imm) imms_and_setups in 
       let setups = List.flatten (List.map (fun (_, setup) -> setup) imms_and_setups) in
       (ImmId(tmp, ()), setups @ [(tmp, CApp(funname, imms, ()))])
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;

(* A wf_env is a list of binding name to arity. arities of 0 are for variables *)
type wf_env = (string * int) list

let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E (e : sourcespan expr) (env : (string * sourcespan) list) (fun_env : wf_env) : exn list =
    match e with
    | EBool _ -> []
    | ENumber _ -> []
    | EId (x, loc) ->
      begin 
      match (List.assoc_opt x env) with
      | None -> [UnboundId(x, loc)]
      | Some(_) -> []
      end
    | EPrim1(_, e, _) -> (wf_E e env fun_env)
    | EPrim2(_, l, r, _) -> (wf_E l env fun_env) @ (wf_E r env fun_env)
    | EIf(c, t, f, _) -> (wf_E c env fun_env) @ (wf_E t env fun_env) @ (wf_E f env fun_env)
    | ELet(binds, body, _) ->
      let (env2, _, errors) =
        (List.fold_left
          (fun (scope_env, shadow_env, found_errors) (x, e, loc) ->
              let curr_errors = (wf_E e scope_env fun_env) @ found_errors in
              match List.assoc_opt x shadow_env with
              | None -> ((x, loc) :: scope_env, (x, loc) :: shadow_env, curr_errors)
              | Some(existing) -> 
                (scope_env, shadow_env, DuplicateId(x, loc, existing) :: curr_errors))
          (env, [], []) binds) in
      errors @ (wf_E body env2 fun_env)
    | EApp(name, args, loc) -> 
      let args_errors = List.flatten (List.map (fun expr -> wf_E expr env fun_env) args) in
      begin
      match (List.assoc_opt name fun_env) with
      | Some(arity) ->
        if (List.length args) != arity
          then [Arity(arity, (List.length args), loc)] @ args_errors
          else args_errors
      | None -> [UnboundFun(name, loc)] @ args_errors
      end
  and wf_D (env : wf_env) (d : sourcespan decl) : exn list =
    match d with
    | DFun(name, params, body, span) ->
      let dup_bindings = 
      (List.map (fun ((n1, span1), (_, span2)) -> DuplicateId(n1, span1, span2))
        (find_dups_by params (fun (n1, _) (n2, _) -> n1 = n2))) in 
      dup_bindings @ (wf_E body params env)
  and get_env (decls : sourcespan decl list) : wf_env = 
    (List.map (fun x -> begin match x with DFun(name, args, _, _) -> (name, (List.length args)) end) decls)
  and dup_d_errors (decls : sourcespan decl list) = 
    List.map (fun x -> begin match x with (DFun(name, _, _, span1), DFun(_, _, _, span2)) -> 
      DuplicateFun(name, span1, span2) end) (find_dups_by decls (fun d1 d2 -> begin match (d1, d2) with (DFun(n1, _, _, _), DFun(n2, _, _, _)) -> n1 = n2 end))
  and d_errors (decls : sourcespan decl list) (env: wf_env) = List.flatten (List.map (wf_D env) decls)
  in match p with
    | Program(decls, body, _) ->
      let env = get_env decls in 
      let dup_fun_errors = dup_d_errors decls in
      let d_errs = d_errors decls env in
      let e_errs = wf_E body [] env in 
      begin
      match dup_fun_errors @ d_errs @ e_errs with 
      | [] -> Ok p
      | e -> Error e
      end
;;

(* sets up a function call (x64) by putting args in the proper registers/stack positions, 
 * calling the given function, and cleaning up the stack after 
 *)
let setup_call_to_func (args : arg list) (label : string) : (instruction list) =
  let leftover_args = Int64.max (Int64.of_int ((((List.length args) - 5) / 2) * 2 * word_size)) 0L in
  (* aligns the stack by adding an extra value if the number of values 
   * needed for the stack is odd
   *)
  let align_stack (remaining_args : arg list) : (instruction list) =
    if ((List.length remaining_args) mod 2) != 0 
    then [IPush(Const(0L))]
    else [] in
  (* sets up args by putting them in the first 6 registers needed for a call,
   * optionally aligning the stack, and placing any remaining values on the stack 
   *)
  let rec setup_args (args : arg list) (registers : reg list) : (instruction list) =
    match args with 
    | [] -> []
    | next_arg :: rest_args ->
      begin match registers with 
        | [] -> IPush(next_arg) :: (setup_args rest_args registers)
        | last_reg :: [] -> 
          IMov(Reg(last_reg), next_arg) :: (align_stack rest_args) @ (setup_args (List.rev rest_args) [])
        | next_reg :: rest_regs -> IMov(Reg(next_reg), next_arg) :: (setup_args rest_args rest_regs)
      end
  in 
  (setup_args args first_six_args_registers) 
  @ [ICall(label)]
  (* pop off values added to the stack *)
  @ (if (Int64.equal leftover_args 0L) then [] else [IAdd(Reg(RSP), Const(leftover_args))])
;;

let get_func_call_params (expected_num_args : int) : arg list =
  let arg_regs_len = List.length first_six_args_registers in
  (List.map 
     (fun reg -> Reg(reg))
     (List.filteri (fun idx _ -> idx < expected_num_args) first_six_args_registers))
  @ (List.init (max 0 (expected_num_args - arg_regs_len)) 
       (fun pos -> RegOffset((pos + 2) * word_size, RBP)))
;;

let setup_enter_func 
    (stack_allocation_space : int)
    (body : instruction list) : instruction list =
  [
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    ISub(Reg(RSP), Const(Int64.of_int (stack_allocation_space * word_size)));
  ] @ body @ [
    IMov(Reg(RSP), Reg(RBP));
    IPop(Reg(RBP));
    IRet;
  ]
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg envt =
  (* In Cobra, you had logic somewhere that tracked the stack index, starting at 1 and incrementing it
     within the bodies of let-bindings.  It built up an environment that mapped each let-bound name to
     a stack index, so that RegOffset(~-8 * stackIndex, RBP) stored the value of that let-binding.
     In this function, you should build up that environment, and return a pair of the already-ANF'ed 
     program and that environment, which can then both be passed along to compile_prog to finish compilation.

     Since this environment-building step comes *after* renaming, you may rely on the invariant that every
     name in the program appears bound exactly once, and therefore those names can be used as keys in 
     an environment without worry of shadowing errors.
  *)
  (* get max allocation needed as an even value, possibly rounded up *)
  let get_var_alloc_space space = ((space + 1) / 2) * 2 in
  let rec get_aexpr_envt (expr : tag aexpr) (si : int) : arg envt =
    match expr with 
    | ALet(name, bind, body, tag) ->
      (name, RegOffset(RBP, ~-si))
      :: (get_cexpr_envt bind (si + 1))
      @ (get_aexpr_envt body (si + 1))
    | ACExpr(body, tag) ->
      (get_cexpr_envt body si)
  and get_cexpr_envt (expr : tag cexpr) (si : int) : arg envt =
    match expr with 
    | CIf(_, l, r, tag) -> 
      (get_aexpr_envt l si)
      @ (get_aexpr_envt r si)
    | _ -> []
  in
  let get_decl_envts (decls : tag adecl list) : arg envt =
    match decls with 
    | [] -> []
    | ADFun(_, params, body, tag) :: rest ->
      (List.map2 (fun l r -> (l, r))
         params
        (get_func_call_params (List.length params)))
      @ (get_aexpr_envt body 1)
      @ (get_decl_envts rest)
  in
  match prog with 
  | AProgram(decls, expr, tag) ->
    (get_aexpr_envt expr 1)
    @ get_decl_envts decls
;;

let rec compile_fun (fun_name : string) (args : string list) (env : arg envt) : instruction list =
  raise (NotYetImplemented "Compile funs not yet implemented")
and compile_aexpr (e : tag aexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  raise (NotYetImplemented "Compile aexpr not yet implemented")
and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) =
  raise (NotYetImplemented "Compile cexpr not yet implemented")
and compile_imm e (env : arg envt) =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)

let compile_decl (d : tag adecl) (env : arg envt): instruction list =
  raise (NotYetImplemented "Compile decl not yet implemented")

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  raise (NotYetImplemented "Compiling programs not implemented yet")

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)
let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_err_phase well_formed is_well_formed)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename)
  |> (add_phase anfed (fun p -> atag (anf p)))
  |> (add_phase locate_bindings naive_stack_allocation)
  |> (add_phase result compile_prog)
;;
