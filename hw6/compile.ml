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

(* constants representing TRUE/FALSE, tag masks, and value masks *)
let const_true     = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false    = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask      = HexConst(0x8000000000000000L)
let bool_tag       = 0x0000000000000007L
let bool_tag_mask  = 0x0000000000000007L
let num_tag        = 0x0000000000000000L
let num_tag_mask   = 0x0000000000000001L

let tuple_tag      = 0x0000000000000001L

let tuple_tag_mask = 0x0000000000000006L

(* error codes *)
let err_COMP_NOT_NUM   = 1L
let err_ARITH_NOT_NUM  = 2L
let err_NOT_BOOL = 3L
let err_OVERFLOW       = 4L
let err_GET_NOT_TUPLE  = 5L
let err_GET_LOW_INDEX  = 6L
let err_GET_HIGH_INDEX = 7L
let err_NIL_DEREF      = 8L

(* label names for errors *)
let label_COMP_NOT_NUM  = "error_comp_not_num"
let label_ARITH_NOT_NUM = "error_arith_not_num"
let label_NOT_BOOL      = "error_not_bool"
let label_OVERFLOW      = "error_overflow"

(* label names for conditionals *)
let label_IS_NOT_BOOL = "is_not_bool"
let label_IS_NOT_NUM  = "is_not_num"
let label_DONE        = "done"

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]
let heap_reg = R15
let scratch_reg = R11


(* You may find some of these helpers useful *)
let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
     if y = x then v else find rest x
let rec find_opt ls x =
  match ls with
  | [] -> None
  | (y,v)::rest ->
     if y = x then Some v else find_opt rest x

let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
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

type funenvt = call_type envt;;
let initial_fun_env : funenvt = [
  (* call_types indicate whether a given function is implemented by something in the runtime,
     as a snake function, as a primop (in case that's useful), or just unknown so far *)
];;


let rename_and_tag (p : tag program) : tag program =
  let rec rename (env : string envt) p =
    match p with
    | Program(decls, body, tag) ->
       let rec addToEnv funenv decl =
         match decl with
         | DFun(name, _, _, _) -> (name, Snake)::funenv in
       let initial_funenv = List.map (fun (name, ct) -> (name, ct)) initial_fun_env in
       let funenv = List.fold_left addToEnv initial_funenv decls in
       Program(List.map (helpD funenv env) decls, helpE funenv env body, tag)
  and helpD funenv env decl =
    match decl with
    | DFun(name, args, body, tag) ->
       let (newArgs, env') = helpBS env args in
       DFun(name, newArgs, helpE funenv env' body, tag)
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
  and helpBG funenv env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a)::bindings ->
       let (b', env') = helpB env b in
       let e' = helpE funenv env e in
       let (bindings', env'') = helpBG funenv env' bindings in
       ((b', e', a)::bindings', env'')
  and helpE funenv env e =
    match e with
    | ESeq(e1, e2, tag) -> ESeq(helpE funenv env e1, helpE funenv env e2, tag)
    | ETuple(es, tag) -> ETuple(List.map (helpE funenv env) es, tag)
    | EGetItem(e, idx, tag) -> EGetItem(helpE funenv env e, helpE funenv env idx, tag)
    | ESetItem(e, idx, newval, tag) -> ESetItem(helpE funenv env e, helpE funenv env idx, helpE funenv env newval, tag)
    | EPrim1(op, arg, tag) -> EPrim1(op, helpE funenv env arg, tag)
    | EPrim2(op, left, right, tag) -> EPrim2(op, helpE funenv env left, helpE funenv env right, tag)
    | EIf(c, t, f, tag) -> EIf(helpE funenv env c, helpE funenv env t, helpE funenv env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId(name, tag) ->
       (try
         EId(find env name, tag)
       with Not_found -> e)
    | EApp(name, args, native, tag) ->
       let call_type = match find_opt funenv name with None -> native | Some ct -> ct in
       EApp(name, List.map (helpE funenv env) args, call_type, tag)
    | ELet(binds, body, tag) ->
       let (binds', env') = helpBG funenv env binds in
       let body' = helpE funenv env' body in
       ELet(binds', body', tag)
  in (rename [] p)
;;


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
    | CApp(_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple(elms, _) -> List.fold_left max 0 (List.map helpI elms)
    | CGetItem(tup, idx, _) -> max (helpI tup) (helpI idx)
    | CSetItem(tup, idx, newval, _) -> List.fold_left max 0 [helpI tup; helpI idx; helpI newval]
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmNil _ -> 0
    | ImmId(name, _) -> name_to_offset name
  and name_to_offset name =
    match (find env name) with
    | RegOffset(bytes, RBP) -> bytes / (-1 * word_size)  (* negative because stack direction *)
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

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program(decls, body, _) -> AProgram(List.map helpD decls, helpA body, ())
  and helpG (g : tag decl list) : unit adecl list =
    List.map helpD g
  and helpD (d : tag decl) : unit adecl =
    match d with
    | DFun(name, args, body, _) ->
       let args = List.map (fun a ->
                      match a with
                      | BName(a, _, _) -> a
                      | _ -> raise (NotYetImplemented("Finish this"))) args in
       ADFun(name, args, helpA body, ())
  and helpC (e : tag expr) : (unit cexpr * (string * unit cexpr) list) = 
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
    | ELet(_::_, body, _) -> raise (NotYetImplemented "Finish this")
    (* | ELet(((bind, _, _), exp, _)::rest, body, pos) ->
     *    let (exp_ans, exp_setup) = helpC exp in
     *    let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
     *    (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup) *)
    | EApp(funname, args, ct, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(funname, new_args, ct, ()), List.concat new_setup)
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
    | ESeq(exp1, exp2, _) -> raise (NotYetImplemented "Finish this")
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
       (ImmId(tmp, ()), left_setup @ right_setup @ [(tmp, CPrim2(prim2_to_sprim2 op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(funname, args, ct, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [(tmp, CApp(funname, new_args, ct, ()))])
    | ELet([], body, _) -> helpI body
    | ELet(_::_, body, _) -> raise (NotYetImplemented "Finish this")
    (* | ELet(((bind, _, _), exp, _)::rest, body, pos) ->
     *    let (exp_ans, exp_setup) = helpC exp in
     *    let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
     *    (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup) *)
    | ETuple(e, tag) -> 
      let tmp = sprintf "tuple_%d" tag 
      and id_setup = List.map helpI e in 
      let ids = (List.map (fun (id, _) -> id) id_setup) 
      and setups = (List.map (fun (_, setup) -> setup) id_setup) in 
      (ImmId(tmp, ()), (List.flatten setups) @ [(tmp, CTuple(ids, ()))])
    | EGetItem(tuple, index, tag) -> 
      let tmp = sprintf "get_%d" tag 
      and (tuple_id, tuple_setup) = helpI tuple 
      and (index_id, index_setup) = helpI index in 
      (ImmId(tmp, ()), tuple_setup @ index_setup @ [(tmp, CGetItem(tuple_id, index_id, ()))])
    | ESetItem(tuple, index, set, tag) -> 
      let tmp = sprintf "set_%d" tag 
      and (tuple_id, tuple_setup) = helpI tuple 
      and (index_id, index_setup) = helpI index
      and (set_id, set_setup) = helpI set in 
      (ImmId(tmp, ()), tuple_setup @ index_setup @ set_setup @ [(tmp, CSetItem(tuple_id, index_id, set_id, ()))])
    | ESeq(exp1, exp2, _) -> raise (NotYetImplemented "Finish this")
  and helpA e : unit aexpr = 
    let (ans, ans_setup) = helpC e in
    List.fold_right (fun (bind, exp) body -> ALet(bind, exp, body, ())) ans_setup (ACExpr ans)
  in
  helpP p
;;


let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E (e : sourcespan expr) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for expressions"])
  and wf_D (d : sourcespan decl) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for definitions"])
  and wf_G (g : sourcespan decl list) (* other parameters may be needed here *) =
    Error([NotYetImplemented "Implement well-formedness checking for definition groups"])
  in
  match p with
  | Program(decls, body, _) ->
     Error([NotYetImplemented "Implement well-formedness checking for programs"])
;;


let desugar (p : tag program) : unit program =
  let gensym =
    let next = ref 0 in
    (fun name ->
      next := !next + 1;
      sprintf "%s_%d" name (!next)) in
  let rec helpE (e : tag expr) : unit expr (* other parameters may be needed here *) =
    match e with 
    | ESeq(e1, e2, _) -> raise (NotYetImplemented "Finish the remaining cases")
    | ETuple(e, _) -> ETuple(List.map helpE e, ())
    | EGetItem(item, idx, _) -> EGetItem(helpE item, helpE idx, ())
    | ESetItem(item, idx, set, _) -> ESetItem(helpE item, helpE idx, helpE set, ())
    | ELet(binds, body, _) -> raise (NotYetImplemented "Finish the remaining cases")
       (* ELet(List.map (fun (name, expr, _) -> (name, helpE expr, ())) binds, helpE body, ()) *)
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
            ()
          ),
          EBool(false, ()),
          ()
        )
       | Or -> EIf(
          helpE e1,
          EBool(true, ()),
          EIf(
          helpE e2,
          EBool(true, ()),
          EBool(false, ()),
          ()
          ),
        ()
        )
        | p -> EPrim2(p, helpE e1, helpE e2, ())
      end
    | EIf(cond, thn, els, _) ->
       EIf(helpE cond, helpE thn, helpE els, ())
    | ENumber(n, _) -> ENumber(n, ())
    | EBool(b, _) -> EBool(b, ())
    | ENil(_) -> raise (NotYetImplemented "Finish the remaining cases")
    | EId(id, _) -> EId(id, ())
    | EApp(_, _, _, _) -> raise (NotYetImplemented "Finish the remaining cases")
  and helpD (d : tag decl) : unit decl (* other parameters may be needed here *) =
    match d with
    | DFun(_, _, _, _) -> raise (NotYetImplemented "Finish the remaining cases")
      (* DFun(name, List.map (fun (name, _) -> (name, ())) args, helpE body, ()) *)
  in
  match p with
  | Program(decls, body, _) ->
      Program(List.map helpD decls, helpE body, ())
;;

(* sets up a function call (x64) by putting args in the proper registers/stack positions, 
 * calling the given function, and cleaning up the stack after 
 *)
let setup_call_to_func (num_regs_to_save : int) (args : arg list) (label : string) : (instruction list) =
  (* how many call args must go on the stack *)
  let stack_args = max ((List.length args) - 6) 0 in
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
  (* push args passed into this function so they don't get overwritten *)
  (backup_caller_saved_registers num_regs_to_save first_six_args_registers)
  (* align the stack if necessary *)
  @ (if should_stack_align then [IPush(Const(0L))] else [])
  (* put the args for the next function in registers/on the stack *)
  @ (setup_args args first_six_args_registers) 
  (* call *)
  @ [ICall(label)]
  (* pop off values added to the stack up to pushed register values *)
  @ (if Int64.equal cleanup_stack 0L then [] else [IAdd(Reg(RSP), Const(cleanup_stack))])
  (* restore register values for the rest of this function to use *)
  @ (restore_caller_saved_registers ((List.length first_six_args_registers) - num_regs_to_save) (List.rev first_six_args_registers))
;;

(** Gets an environment mapping id names to register names or stack offsets.
 * This makes it easy for callee functions to use args *)
let get_func_call_params (params : string list) : arg envt =
  let rec pair_stack (params : string list) (next_off : int) : arg envt =
    match params with 
    | [] -> []
    | first :: rest ->
      (first, RegOffset(next_off * word_size, RBP))
      :: (pair_stack rest (next_off + 1))
  and pair_regs (params : string list) (regs : reg list) : arg envt =
    match regs with 
    | [] -> 
      begin 
        match params with 
        | [] -> [] 
        | _ -> (pair_stack params 2)
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
  (pair_regs params first_six_args_registers)
;;

(* ASSUMES that the program has been alpha-renamed and all names are unique *)
let naive_stack_allocation (prog: tag aprogram) : tag aprogram * arg envt =
  let rec get_aexpr_envt (expr : tag aexpr) (si : int) : arg envt =
    match expr with 
    | ALet(name, bind, body, _) ->
      (name, RegOffset(~-si * word_size, RBP))
      :: (get_cexpr_envt bind (si + 1))
      @ (get_aexpr_envt body (si + 1))
    | ACExpr(body) ->
      (get_cexpr_envt body si)
  and get_cexpr_envt (expr : tag cexpr) (si : int) : arg envt =
    match expr with 
    | CIf(_, l, r, _) -> 
      (get_aexpr_envt l si)
      @ (get_aexpr_envt r si)
    | _ -> []
  in
  let rec get_decl_envts (decls : tag adecl list) : arg envt =
    match decls with 
    | [] -> []
    | ADFun(_, params, body, _) :: rest ->
      (* put call args in the environment too *)
      (get_func_call_params params)
      @ (get_aexpr_envt body 1)
      @ (get_decl_envts rest)
  in
  match prog with 
  | AProgram(decls, expr, _) ->
    (prog, 
     ((get_decl_envts decls)
     @ (get_aexpr_envt expr 1)))
;;

(* creates a jump instruction to to_instr if testing the value in RAX with mask 
 * satisifies the to_instr jump condition
 *
 * Note: the value to test should be in RAX before calling
*)
let create_test_jump_instrs (mask : int64) (to_instr : instruction) : instruction list =
  [IMov(Reg(R10), HexConst(mask)); ITest(Reg(RAX), Reg(R10)); to_instr] 

(* Jumps to to_label if not a num *)
let num_tag_check (to_label : string) (body : instruction list) : instruction list =
  (create_test_jump_instrs num_tag_mask (IJnz(to_label)))
  @ body 

(* Jumps to to_label if not type and puts final_rax_value in RAX on exiting.
 * final_rax_value does not have to be the original RAX value, but
 * in *most* cases should be (except for isbool())
 *
 * Note: the value to test should be in RAX before calling
*)
let bool_tag_check (final_rax_value : arg) (to_label : string) : instruction list = [
  IMov(Reg(R10), HexConst(bool_tag_mask)); 
  IAnd(Reg(RAX), Reg(R10)); ICmp(Reg(RAX), Reg(R10));
  IMov(Reg(RAX), final_rax_value); IJnz(to_label);
] 

(* Jumps to to_label if not type and puts final_rax_value in RAX on exiting.
 *
 * Note: the value to test should be in RAX before calling
*)
let tuple_tag_check (to_label : string) : instruction list =
  (create_test_jump_instrs tuple_tag_mask (IJnz(to_label)))


let rec compile_fun (fun_name : string) (body : tag aexpr) (args: string list) (env: arg envt) : instruction list =
  (* get max allocation needed as an even value, possibly rounded up *)
  let stack_alloc_space = (((deepest_stack body env) + 1) / 2 ) * 2 in
  [
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    ISub(Reg(RSP), Const(Int64.of_int (stack_alloc_space * word_size)));
    (* TODO: change to maybe when implementing tail recursion *)
  ] @ (compile_aexpr body env (List.length args) false) @ [
    IMov(Reg(RSP), Reg(RBP));
    IPop(Reg(RBP));
    IRet;
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
and compile_cexpr (e : tag cexpr) (env: arg envt) (num_args: int) (is_tail: bool) =
  match e with 
  | CIf(cond, thn, els, tag) ->
    let if_t = (sprintf "if_true_%n" tag) and
    if_f = (sprintf "if_false_%n" tag) and
    done_txt = (sprintf "done_%n" tag) and
    thn = compile_aexpr thn env num_args is_tail and
    els = compile_aexpr els env num_args is_tail and
    cond_value = compile_imm cond env in
    IMov(Reg(RAX), cond_value) ::
    (bool_tag_check cond_value label_NOT_BOOL)
    @ [
      IMov(Reg(R10), bool_mask); ITest(Reg(RAX), Reg(R10));
      IJz(if_f);
      ILabel(if_t);
    ] @ thn @ [
      IJmp(done_txt);
      ILabel(if_f); 
    ] @ els @ [
      ILabel(done_txt);
    ]
  | CPrim1(op, body, tag) ->
    let e_reg = compile_imm body env in
    begin match op with
      | Add1 -> 
        IMov(Reg(RAX), e_reg) ::
        (num_tag_check label_ARITH_NOT_NUM 
          [IAdd(Reg(RAX), Sized(QWORD_PTR, Const(2L))); IJo(label_OVERFLOW)])
      | Sub1 -> 
        IMov(Reg(RAX), e_reg) ::
        (num_tag_check label_ARITH_NOT_NUM 
           [IAdd(Reg(RAX), Sized(QWORD_PTR, Const(Int64.neg 2L))); IJo(label_OVERFLOW)])
      | Print -> (setup_call_to_func num_args [e_reg] "print") 
      | IsBool -> 
        let label_not_bool = (sprintf "%s%n" label_IS_NOT_BOOL tag) in 
        let label_done = (sprintf "%s%n" label_DONE tag) in
        IMov(Reg(RAX), e_reg) ::
        (* check if value is a bool, and if not, then jump to label_not_bool *)
        (bool_tag_check const_true label_not_bool)
        @ [
          IJmp(label_done);
          ILabel(label_not_bool);
          IMov(Reg(RAX), const_false);
          ILabel(label_done);
          ]
      | IsNum ->
        let label_not_num = (sprintf "%s%n" label_IS_NOT_NUM tag) in 
        let label_done = (sprintf "%s%n" label_DONE tag) in
        IMov(Reg(RAX), e_reg) :: 
        (* check if value is a num, and if not, then jump to label_not_num *)
        (num_tag_check label_not_num 
          [
            IMov(Reg(RAX), const_true);
            IJmp(label_done);
            ILabel(label_not_num);
            IMov(Reg(RAX), const_false);
            ILabel(label_done);
          ])
      | Not -> 
        IMov(Reg(RAX), e_reg) ::
        (bool_tag_check e_reg label_NOT_BOOL)
        @ [ 
          IMov(Reg(R10), bool_mask);
          IXor(Reg(RAX), Reg(R10));
          ]
      | PrintStack -> raise (NotYetImplemented "Fill in here")
    end
  | CPrim2(op, l, r, tag) ->
    let e1_reg = (compile_imm l env) in
    let e2_reg = (compile_imm r env) in
    (* generates the instructions for comparing the args e1_reg and e2_reg and 
     * constructs an auto-generated jump label using the jmp_instr_constructor.
     * jump_instr_constructor should take in a label name and create the appropriate jump instruction
    *)
    let generate_cmp_func 
        (e1_reg : arg) 
        (e2_reg : arg) 
        (jmp_instr_constructor : (string -> instruction)) 
        tag : instruction list =
      let label_done = (sprintf "%s%n" label_DONE tag) in
      IMov(Reg(RAX), e2_reg) ::
      (num_tag_check label_COMP_NOT_NUM 
         (IMov(Reg(RAX), e1_reg) ::
          (num_tag_check label_COMP_NOT_NUM 
             [IMov(Reg(R10), e2_reg); ICmp(Reg(RAX), Reg(R10));
              IMov(Reg(RAX), const_true); (jmp_instr_constructor label_done);
              IMov(Reg(RAX), const_false); ILabel(label_done)])))
    in
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
      (num_tag_check label_ARITH_NOT_NUM [IMov(Reg(RAX), e1_reg)])
      @ (num_tag_check label_ARITH_NOT_NUM [IMov(Reg(R10), e2_reg)])
      @ body
      @ [IJo(label_OVERFLOW)]
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
        (generate_cmp_func e1_reg e2_reg (fun l -> IJg(l)) tag)
      | SGreaterEq -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJge(l)) tag)
      | SLess -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJl(l)) tag)
      | SLessEq ->
        (generate_cmp_func e1_reg e2_reg (fun l -> IJle(l)) tag)
      | SEq ->
        let label_done = (sprintf "%s%n" label_DONE tag) in
        [IMov(Reg(RAX), e1_reg); IMov(Reg(R10), e2_reg); 
         ICmp(Reg(RAX), Reg(R10)); IMov(Reg(RAX), const_true);
         IJe(label_done); IMov(Reg(RAX), const_false);
         ILabel(label_done)]
    end
    (* todo: figure out what to do with native call types vs not native *)
  | CApp(fun_name, args, _, _) -> (setup_call_to_func num_args (List.map (fun e -> compile_imm e env) args) fun_name)
  | CImmExpr(value) -> [IMov(Reg(RAX), compile_imm value env)]
and compile_imm e env =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
  | ImmNil(_) -> raise (NotYetImplemented "Finish this")

let compile_decl (d : tag adecl) (env: arg envt) : instruction list =
  match d with 
  | ADFun(name, params, body, _) ->
    compile_fun name body params env

let compile_prog ((anfed : tag aprogram), (env: arg envt)) : string =
  match anfed with
  | AProgram(decls, body, _) ->
     let comp_decls = raise (NotYetImplemented "... do stuff with decls ...") in
     let (body_prologue, comp_body, body_epilogue) = raise (NotYetImplemented "... do stuff with body ...") in
     
     let heap_start = [
         ILineComment("heap start");
         IInstrComment(IMov(Reg(heap_reg), Reg(List.nth first_six_args_registers 0)), "Load heap_reg with our argument, the heap pointer");
         IInstrComment(IAdd(Reg(heap_reg), Const(15L)), "Align it to the nearest multiple of 16");
         IInstrComment(IAnd(Reg(heap_reg), HexConst(0xFFFFFFFFFFFFFFF0L)), "by adding no more than 15 to it")
       ] in
     let main = to_asm (body_prologue @ heap_start @ comp_body @ body_epilogue) in
     
     raise (NotYetImplemented "... combine comp_decls and main with any needed extra setup and error handling ...")

(* Feel free to add additional phases to your pipeline.
   The final pipeline phase needs to return a string,
   but everything else is up to you. *)

;;

let run_if should_run f =
  if should_run then f else no_op_phase
;;

(* Add a desugaring phase somewhere in here *)
(* Todo: Add comment explaining (1) why you chose the particular ordering of desguaring relative to the other phases that you did, and (2) what syntactic invariants each phase of your compiler expects. You may want to enforce those invariants by throwing InternalCompilerErrors if they’re violated. *)
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
