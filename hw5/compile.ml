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
let const_true    = HexConst(0xFFFFFFFFFFFFFFFFL)
let const_false   = HexConst(0x7FFFFFFFFFFFFFFFL)
let bool_mask     = HexConst(0x8000000000000000L)
let bool_tag      = 0x0000000000000007L
let bool_tag_mask = 0x0000000000000007L
let num_tag       = 0x0000000000000000L
let num_tag_mask  = 0x0000000000000001L

(* error codes *)
let err_COMP_NOT_NUM   = 1L
let err_ARITH_NOT_NUM  = 2L
let err_LOGIC_NOT_BOOL = 3L
let err_IF_NOT_BOOL    = 4L
let err_OVERFLOW       = 5L

(* label names for errors *)
let label_COMP_NOT_NUM   = "error_comp_not_num"
let label_ARITH_NOT_NUM  = "error_arith_not_num"
let label_LOGIC_NOT_BOOL = "error_logic_not_bool"
let label_IF_NOT_BOOL    = "error_if_not_bool"
let label_OVERFLOW       = "error_overflow"

(* label names for conditionals *)
let label_IS_NOT_BOOL    = "is_not_bool"
let label_IS_NOT_NUM     = "is_not_num"
let label_DONE           = "done"

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

let rename (e : tag program) : tag program =
  let rec get_fun_env (decls : tag decl list) : (string * string) list =
    match decls with 
    | [] -> []
    | DFun(name, _, _, tag) :: rest ->
      let renamed = (sprintf "%s#%n" name tag) in 
      (name, renamed) :: get_fun_env rest 
  in 
  let fun_env = match e with
    | Program(decls, expr, tag) -> 
      get_fun_env decls 
  in
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
    | EApp(funname, args, tag) -> 
      let new_name = (find fun_env funname) in
      EApp(new_name, List.map (help env) args, tag)
  (* Renames all bindings in a let string and returns them with new env *)
  and let_helper (env : (string * string) list) (binds : tag bind list) : (tag bind list * (string * string) list) =
    match binds with
    | [] -> ([], env)
    | (first, binding, tag)::rest -> 
      let binding_renamed = (help env binding)
      and new_name = (sprintf "%s#%n" first tag) in 
      let (acc, env) = (let_helper ((first, new_name)::env) rest) in
      ((new_name, binding_renamed, tag)::acc, env)
  in
  let rec rename_decl_args ((renamed, env) : (string * tag) list * (string * string) list) (args : (string * tag) list) : ((string * tag) list * (string * string) list) = 
    match args with 
    | [] -> (List.rev renamed, env)
    | (fname, tag) :: rest ->
      let new_name = (sprintf "%s#%n" fname tag) in 
      (rename_decl_args (((new_name, tag) :: renamed), ((fname, new_name) :: env)) rest)
  in
  let help_decl (e : tag decl) : tag decl =
    (* Todo: We don't need to rename decls since their names have to be unique, right? *)
    match e with 
    | DFun(name, args, body, tag) ->
      let new_name = (find fun_env name) in
      let new_args, env = (rename_decl_args ([], []) args) in
      let new_body = (help env body) in 
      DFun(new_name, new_args, new_body, tag)
  in
  match e with
  | Program(decls, expr, tag) -> 
    let new_decls = List.map help_decl decls in
    let new_body = (help [] expr) in
    Program(new_decls, new_body, tag)
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

let is_well_formed (p : sourcespan program) : (sourcespan program) fallible =
  let rec wf_E (e : sourcespan expr) (env : (string * sourcespan) list) (fun_env : int envt) : exn list =
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
  and wf_D (env : int envt) (d : sourcespan decl) : exn list =
    match d with
    | DFun(name, params, body, span) ->
      let dup_bindings = 
      (List.map (fun ((n1, span1), (_, span2)) -> DuplicateId(n1, span1, span2))
        (find_dups_by params (fun (n1, _) (n2, _) -> n1 = n2))) in 
      dup_bindings @ (wf_E body params env)
  and get_env (decls : sourcespan decl list) : int envt = 
    (List.map (fun x -> 
         begin 
           match x with 
           | DFun(name, args, _, _) -> 
             (name, (List.length args)) 
         end) decls)
  and dup_d_errors (decls : sourcespan decl list) = 
    List.map (fun x -> 
        begin 
          match x with 
          | (DFun(name, _, _, span1), DFun(_, _, _, span2)) -> 
            DuplicateFun(name, span1, span2) 
        end) 
      (find_dups_by decls 
         (fun d1 d2 -> 
            begin 
              match (d1, d2) with 
              | (DFun(n1, _, _, _), DFun(n2, _, _, _)) -> 
                n1 = n2 
            end))
  and d_errors (decls : sourcespan decl list) (env: int envt) = 
    List.flatten (List.map (wf_D env) decls) in 
  match p with
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
let setup_call_to_func (num_regs_to_save : int) (args : arg list) (label : string) : (instruction list) =
  let leftover_args = max ((((List.length args) - 5) / 2) * 2) 0 in
  let should_stack_align = ((leftover_args + num_regs_to_save) mod 2) != 0 in
  (* Backs up ALL registers *)
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
  (* Restores ALL registers. Reverse of backup_caller_saved_registers *)
  let rec restore_caller_saved_registers (args_to_skip : int) (registers : reg list) : (instruction list) =
    match registers with 
    | [] -> []
    | next_reg :: rest_regs -> 
      if args_to_skip = 0
      then IPop(Reg(next_reg)) :: (restore_caller_saved_registers 0 rest_regs) 
      else (restore_caller_saved_registers (args_to_skip - 1) rest_regs)
  in
  (* sets up args by putting them in the first 6 registers needed for a call,
   * optionally aligning the stack, and placing any remaining values on the stack 
   *)
  let rec setup_args (args : arg list) (registers : reg list) : (instruction list) =
    let reg_assoc_list = List.mapi (fun pos value -> (value, pos + 1)) first_six_args_registers in
    let use_reg (next_arg : arg) (rest_args : arg list) : instruction list =
      match registers with 
        | [] -> IPush(next_arg) :: (setup_args rest_args registers)
        | last_reg :: [] -> 
          IMov(Reg(last_reg), next_arg) :: (setup_args (List.rev rest_args) [])
        | next_reg :: rest_regs -> IMov(Reg(next_reg), next_arg) :: (setup_args rest_args rest_regs)
    in
    let swap_reg (register : reg) (rest_args : arg list) : instruction list =
      match List.assoc_opt register reg_assoc_list with 
      | Some(idx) -> 
        let align_off = if should_stack_align then 1 else 0 in
        let off = (align_off + num_regs_to_save - idx) in
        use_reg (RegOffset(off * word_size, RSP)) rest_args
      | None -> use_reg (Reg(register)) rest_args
    in
    match args with 
    | [] -> []
    | Reg(some_reg) :: rest_args ->
      swap_reg some_reg rest_args
    | next_arg :: rest_args ->
      use_reg next_arg rest_args
  in 
  (backup_caller_saved_registers num_regs_to_save first_six_args_registers)
  @ (if should_stack_align then [IPush(Const(0L))] else [])
  @ (setup_args args first_six_args_registers) 
  @ [ICall(label)]
  (* pop off values added to the stack *)
  @ (if leftover_args = 0 then [] else [IAdd(Reg(RSP), Const((Int64.of_int (leftover_args * word_size))))])
  @ (if should_stack_align then [IPop(Reg(RSI))] else [])
  @ (restore_caller_saved_registers ((List.length first_six_args_registers) - num_regs_to_save) (List.rev first_six_args_registers))
;;

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

let rec compile_fun (fun_name : string) (body : tag aexpr) (args : string list) (env : arg envt) : instruction list =
  (* get max allocation needed as an even value, possibly rounded up *)
  let stack_alloc_space = (((deepest_stack body env) + 1) / 2 ) * 2 in
  [
    ILabel(fun_name);
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP));
    ISub(Reg(RSP), Const(Int64.of_int (stack_alloc_space * word_size)));
    (* TODO: change to true when implementing tail recursion *)
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
and compile_cexpr (e : tag cexpr) (env : arg envt) (num_args : int) (is_tail : bool) : instruction list =
  match e with 
  | CIf(cond, thn, els, tag) ->
    let if_t = (sprintf "if_true_%n" tag) and
    if_f = (sprintf "if_false_%n" tag) and
    done_txt = (sprintf "done_%n" tag) and
    thn = compile_aexpr thn env num_args is_tail and
    els = compile_aexpr els env num_args is_tail and
    cond_value = compile_imm cond env in
    IMov(Reg(RAX), cond_value) ::
    (bool_tag_check cond_value label_IF_NOT_BOOL)
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
        (bool_tag_check e_reg label_LOGIC_NOT_BOOL)
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
    (* generates the instructions for performing a logical and/or on args e1_reg and e2_reg.
     * if create_and is true, then the instructions are created for an and op, otherwise an or op is created. 
    *)
    let generate_logic_func 
        (e1_reg : arg) 
        (e2_reg : arg) 
        (create_and : bool) tag : instruction list =
      let label_done = (sprintf "%s%n" label_DONE tag) in
      let jump_instr = if create_and then IJz(label_done) else IJnz(label_done) in 
      let pass_test = if create_and then const_true else const_false in 
      let fail_test = if create_and then const_false else const_true in
      IMov(Reg(RAX), e1_reg) ::
      (bool_tag_check e1_reg label_LOGIC_NOT_BOOL)
      @ [
        IMov(Reg(R10), bool_mask); ITest(Reg(RAX), Reg(R10)); IMov(Reg(RAX), fail_test); jump_instr;
        IMov(Reg(RAX), e2_reg)]
      @ (bool_tag_check e2_reg label_LOGIC_NOT_BOOL)
      @ [
        IMov(Reg(R10), bool_mask); ITest(Reg(RAX), Reg(R10)); IMov(Reg(RAX), fail_test); jump_instr;
        IMov(Reg(RAX), pass_test)]
      @ [ILabel(label_done)]
    in
    begin match op with
      | Plus -> 
        (generate_arith_func e1_reg e2_reg [IAdd(Reg(RAX), Reg(R10))])
      | Minus -> 
        (generate_arith_func e1_reg e2_reg [ISub(Reg(RAX), Reg(R10))])
      | Times -> 
        (generate_arith_func e1_reg e2_reg 
           [ISar(Reg(RAX), Const(1L)); IMul(Reg(RAX), Reg(R10))])
      | And -> 
        (generate_logic_func e1_reg e2_reg true tag)
      | Or -> 
        (generate_logic_func e1_reg e2_reg false tag)
      | Greater -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJg(l)) tag)
      | GreaterEq -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJge(l)) tag)
      | Less -> 
        (generate_cmp_func e1_reg e2_reg (fun l -> IJl(l)) tag)
      | LessEq ->
        (generate_cmp_func e1_reg e2_reg (fun l -> IJle(l)) tag)
      | Eq ->
        let label_done = (sprintf "%s%n" label_DONE tag) in
        [IMov(Reg(RAX), e1_reg); IMov(Reg(R10), e2_reg); 
         ICmp(Reg(RAX), Reg(R10)); IMov(Reg(RAX), const_true);
         IJe(label_done); IMov(Reg(RAX), const_false);
         ILabel(label_done)]
    end
  | CApp(fun_name, args, _) -> (setup_call_to_func num_args (List.map (fun e -> compile_imm e env) args) fun_name)
  | CImmExpr(value) -> [IMov(Reg(RAX), compile_imm value env)]
and compile_imm (e : tag immexpr) (env : arg envt) =
  match e with
  | ImmNum(n, _) -> Const(Int64.shift_left n 1)
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)

let compile_decl (d : tag adecl) (env : arg envt): instruction list =
  match d with 
  | ADFun(name, params, body, _) ->
    compile_fun name body params env

let compile_error_handler ((err_name : string), (err_code : int64)) : instruction list =
  ILabel(err_name) :: setup_call_to_func 0 [Const(err_code); Reg(RAX)] "error"

let compile_prog ((anfed : tag aprogram), (env : arg envt)) : string =
  match anfed with
  | AProgram(decls, expr, _) ->
    let prelude =
      "section .text
extern error
extern print
global our_code_starts_here" in
    let body = to_asm 
        ((List.flatten (List.map (fun decl -> compile_decl decl env) decls)
          @ (compile_fun "our_code_starts_here" expr [] env))
         @ (List.flatten (List.map compile_error_handler [
             (* TODO: which of these errors do we still need? *)
             (label_COMP_NOT_NUM, err_COMP_NOT_NUM);
             (label_ARITH_NOT_NUM, err_ARITH_NOT_NUM);
             (label_LOGIC_NOT_BOOL, err_LOGIC_NOT_BOOL);
             (label_IF_NOT_BOOL, err_IF_NOT_BOOL);
             (label_OVERFLOW, err_OVERFLOW);
           ])))
    in 
    sprintf "%s%s\n" prelude body

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
