open Printf
open Errors
open Exprs
open Pretty
open Phases

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

let err_COMP_NOT_NUM     = 1L
let err_ARITH_NOT_NUM    = 2L
let err_LOGIC_NOT_BOOL   = 3L
let err_IF_NOT_BOOL      = 4L
let err_OVERFLOW         = 5L
let label_COMP_NOT_NUM   = "error_comp_not_num"
let label_ARITH_NOT_NUM  = "error_arith_not_num"
let label_LOGIC_NOT_BOOL = "error_logic_not_bool"
let label_IF_NOT_BOOL    = "error_if_not_bool"
let label_OVERFLOW       = "error_overflow"
let label_IS_NOT_BOOL    = "is_not_bool"
let label_IS_NOT_NUM     = "is_not_num"
let label_DONE           = "done"

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]


let check_scope (e : sourcespan expr) : sourcespan expr =
  let rec help e env =
    match e with
    | EBool _ -> ()
    | ENumber _ -> ()
    | EId (x, loc) ->
      (try ignore (List.assoc x env)
       with Not_found ->
         raise (BindingError(sprintf "The identifier %s, used at <%s>, is not in scope" x (string_of_sourcespan loc))))
    | EPrim1(_, e, _) -> help e env
    | EPrim2(_, l, r, _) -> help l env; help r env
    | EIf(c, t, f, _) -> help c env; help t env; help f env
    | ELet(binds, body, _) ->
      let (env2, _) =
        (List.fold_left
           (fun (scope_env, shadow_env) (x, e, loc) ->
              try
                let existing = List.assoc x shadow_env in
                raise (BindingError(sprintf "The identifier %s, defined at <%s>, shadows one defined at <%s>"
                                      x (string_of_sourcespan loc) (string_of_sourcespan existing)))
              with Not_found ->
                help e scope_env;
                ((x, loc)::scope_env, (x, loc)::shadow_env))
           (env, []) binds) in
      help body env2
  in help e []; e

let rename (e : tag expr) : tag expr =
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


let tag (e : 'a expr) : tag expr =
  let rec help (e : 'a expr) (num : int) : (tag expr * tag) =
    match e with
    | EId(x, _) -> (EId(x, num), num + 1)
    | ENumber(n, _) -> (ENumber(n, num), num + 1)
    | EBool(b, _) -> (EBool(b, num), num + 1)
    | EPrim1(op, e, _) ->
      let (tag_e, new_n) = help e (num + 1) in
      (EPrim1(op, tag_e, num), new_n)
    | EPrim2(op, e1, e2, _) ->
      let (tag_e1, num_e1) = help e1 (num + 1) in
      let (tag_e2, num_e2) = help e2 (num_e1) in
      (EPrim2(op, tag_e1, tag_e2, num), num_e2)
    | ELet(binds, body, _) ->
      let (new_binds, num_binds) =
        List.fold_left
          (fun (rev_binds, next_num) (x, b, _) ->
             let (tag_b, num_b) = help b (next_num + 1) in
             ((x, tag_b, next_num)::rev_binds, num_b))
          ([], num + 1) binds in
      let (tag_body, num_body) = help body num_binds in
      (ELet(List.rev new_binds, tag_body, num), num_body)
    | EIf(cond, thn, els, _) ->
      let (tag_cond, num_cond) = help cond (num + 1) in
      let (tag_thn, num_thn) = help thn (num_cond) in
      let (tag_els, num_els) = help els (num_thn) in
      (EIf(tag_cond, tag_thn, tag_els, num), num_els)
  in let (ans, _) = help e 1
  in ans

let rec untag (e : 'a expr) : unit expr =
  match e with
  | EId(x, _) -> EId(x, ())
  | ENumber(n, _) -> ENumber(n, ())
  | EBool(b, _) -> EBool(b, ())
  | EPrim1(op, e, _) ->
    EPrim1(op, untag e, ())
  | EPrim2(op, e1, e2, _) ->
    EPrim2(op, untag e1, untag e2, ())
  | ELet(binds, body, _) ->
    ELet(List.map(fun (x, b, _) -> (x, untag b, ())) binds, untag body, ())
  | EIf(cond, thn, els, _) ->
    EIf(untag cond, untag thn, untag els, ())

let anf (e : tag expr) : unit expr =
  let rec helpC (e : tag expr) : (unit expr * (string * unit expr) list) = 
    match e with
    | EPrim1(op, arg, _) ->
      let (arg_imm, arg_setup) = helpI arg in
      (EPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (EPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
      let (cond_imm, cond_setup) = helpI cond in
      (EIf(cond_imm, anf _then, anf _else, ()), cond_setup)
    | ENumber(n, _) -> (ENumber(n, ()), [])
    | EBool(b, _) -> (EBool(b, ()), [])
    | ELet([], body, _) -> helpC body
    | ELet((bind, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId(name, _) -> (EId(name, ()), [])
  and helpI (e : tag expr) : (unit expr * (string * unit expr) list) =
    match e with
    | EPrim1(op, arg, tag) ->
      let tmp = sprintf "unary_%d" tag in
      let (arg_imm, arg_setup) = helpI arg in
      (EId(tmp, ()), arg_setup @ [(tmp, EPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
      let tmp = sprintf "binop_%d" tag in
      let (left_imm, left_setup) = helpI left in
      let (right_imm, right_setup) = helpI right in
      (EId(tmp, ()), left_setup @ right_setup @ [(tmp, EPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
      let tmp = sprintf "if_%d" tag in
      let (cond_imm, cond_setup) = helpI cond in
      (EId(tmp, ()), cond_setup @ [(tmp, EIf(cond_imm, anf _then, anf _else, ()))])
    | ENumber(n, _) -> (ENumber(n, ()), [])
    | EBool(b, _) -> (EBool(b, ()), [])
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
      let (exp_ans, exp_setup) = helpC exp in
      let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
      (body_ans, exp_setup @ [(bind, exp_ans)] @ body_setup)
    | EId(name, _) -> (EId(name, ()), [])
  and anf e = 
    let (ans, ans_setup) = helpI e in
    List.fold_right (fun (bind, exp) body -> ELet([bind, exp, ()], body, ())) ans_setup ans
  in
  anf e
;;


let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "RAX"
  | RSI -> "RSI"
  | RDI -> "RDI"
  | RCX -> "RCX"
  | RDX -> "RDX"
  | RSP -> "RSP"
  | RBP -> "RBP"
  | R8  -> "R8"
  | R9  -> "R9"
  | R11  -> "R11"

let rec arg_to_asm (a : arg) : string =
  match a with
  | Const(n) -> sprintf "%Ld" n
  | HexConst(n) -> sprintf "QWORD 0x%Lx" n
  | Reg(r) -> r_to_asm r
  | RegOffset(n, r) ->
    if n >= 0 then
      sprintf "[%s+%d]" (r_to_asm r) (word_size * n)
    else
      sprintf "[%s-%d]" (r_to_asm r) (-1 * word_size * n)
  | Sized(size, a) ->
    sprintf "%s %s"
      (match size with | QWORD_PTR -> "QWORD" | DWORD_PTR -> "DWORD" | WORD_PTR -> "WORD" | BYTE_PTR -> "BYTE")
      (arg_to_asm a)

let rec i_to_asm (i : instruction) : string =
  match i with
  | IMov(dest, value) ->
    sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd(dest, to_add) ->
    sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub(dest, to_sub) ->
    sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul(dest, to_mul) ->
    sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ICmp(left, right) ->
    sprintf "  cmp %s, %s" (arg_to_asm left) (arg_to_asm right)
  | ILabel(name) ->
    name ^ ":"
  | IJo(label) ->
    sprintf "  jo %s" label
  | IJe(label) ->
    sprintf "  je %s" label
  | IJne(label) ->
    sprintf "  jne %s" label
  | IJl(label) ->
    sprintf "  jl %s" label
  | IJle(label) ->
    sprintf "  jle %s" label
  | IJg(label) ->
    sprintf "  jg %s" label
  | IJge(label) ->
    sprintf "  jge %s" label
  | IJmp(label) ->
    sprintf "  jmp %s" label
  | IJz(label) ->
    sprintf "  jz %s" label
  | IJnz(label) ->
    sprintf "  jnz %s" label
  | IAnd(dest, value) ->
    sprintf "  and %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IOr(dest, value) ->
    sprintf "  or %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IXor(dest, value) ->
    sprintf "  xor %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShl(dest, value) ->
    sprintf "  shl %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShr(dest, value) ->
    sprintf "  shr %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ISar(dest, value) ->
    sprintf "  sar %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IPush(value) ->
    sprintf "  push %s" (arg_to_asm value)
  | IPop(dest) ->
    sprintf "  pop %s" (arg_to_asm dest)
  | ICall(label) ->
    sprintf "  call %s" label
  | IRet ->
    "  ret"
  | ITest(arg, comp) ->
    sprintf "  test %s, %s" (arg_to_asm arg) (arg_to_asm comp)
  | ILineComment(str) ->
    sprintf "  ;; %s" str
  | IInstrComment(instr, str) ->
    sprintf "%s ; %s" (i_to_asm instr) str

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is

let rec find (ls : (string * 'a) list) (x : string) : 'a =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y,v)::rest ->
    if y = x then v else find rest x

(* NOTE: Assumes that e is in ANF *)
let rec count_vars (e : 'a expr) =
  match e with
  | EIf(_, t, f, _) -> max (count_vars t) (count_vars f)
  | ELet([_, b, _], body, _) ->
    1 + (max (count_vars b) (count_vars body))
  | _ -> 0
  
let setup_func_call (args : arg list) (label : string) : (instruction list) =
  let align_stack (remaining_args : arg list) : (instruction list) =
    if (List.length remaining_args) mod 2 != 0 
    then []
    else [IPush(Const(0L))] in
  let rec setup_args (args : arg list) (registers : reg list) : (instruction list) =
    match args with 
    | [] -> []
    | next_arg :: rest_args ->
      begin match registers with 
        | [] -> IPush(next_arg) :: (setup_args rest_args registers)
        | last_reg :: [] -> 
          IMov(Reg(last_reg), next_arg) :: (align_stack rest_args) @ (setup_args rest_args [])
        | next_reg :: rest_regs -> IMov(Reg(next_reg), next_arg) :: (setup_args rest_args rest_regs)
      end
  in 
  (setup_args (List.rev args) first_six_args_registers) 
  @ [ICall(label)]
  @ [IAdd(Reg(RSP), Const(Int64.of_int ((((List.length args) - 5) / 2) * 16)))]

let setup_err_call (err_name : string) (args : arg list) : (instruction list) =
  ILabel(err_name) :: (setup_func_call args "error")

let rec compile_expr (e : tag expr) (si : int) (env : (string * int) list) : instruction list =
  (* TODO: probably refactor these helpers better later *)
  let create_test_jump_instrs (mask : int64) (to_instr : instruction) : instruction list =
    [IMov(Reg(R11), HexConst(mask)); ITest(Reg(RAX), Reg(R11)); to_instr] 
  in
  (* Jumps to to_label if not type *)
  let num_tag_check (to_label : string) (body : instruction list) : instruction list =
    (create_test_jump_instrs num_tag_mask (IJnz(to_label)))
    @ body @ [IJo(label_OVERFLOW)]
  in
  (* Jumps to to_label if not type and puts final_rax_value in RAX on exiting *)
  (* TODO: is this the best way to do this? *)
  let bool_tag_check (final_rax_value : arg) (to_label : string) : instruction list = [
    IMov(Reg(R11), HexConst(bool_tag_mask)); 
    IAnd(Reg(RAX), Reg(R11)); ICmp(Reg(RAX), Reg(R11));
    IMov(Reg(RAX), final_rax_value); IJnz(to_label);
  ] 
  in
  let generate_cmp_func (e1_reg : arg) (e2_reg : arg) (jmp_instr_constructor : (string -> instruction)) tag : instruction list =
    let label_done = (sprintf "%s%n" label_DONE tag) in
    IMov(Reg(RAX), e2_reg) ::
    (num_tag_check label_COMP_NOT_NUM 
       (IMov(Reg(RAX), e1_reg) ::
        (num_tag_check label_COMP_NOT_NUM 
           [IMov(Reg(R11), e2_reg); ICmp(Reg(RAX), Reg(R11));
            IMov(Reg(RAX), const_true); (jmp_instr_constructor label_done);
            IMov(Reg(RAX), const_false); ILabel(label_done)])))
  in
  match e with
  | ELet([id, e, _], body, _) ->
    let prelude = compile_expr e (si + 1) env in
    let body = compile_expr body (si + 1) ((id, si)::env) in
    prelude
    @ [ IMov(RegOffset(~-si, RBP), Reg(RAX)) ]
    @ body
  | EPrim1 (op, e, tag) -> 
    let e_reg = compile_imm e env in
    begin match op with
      | Add1 -> 
        IMov(Reg(RAX), e_reg) ::
        (num_tag_check label_ARITH_NOT_NUM 
          [IAdd(Reg(RAX), Sized(QWORD_PTR, Const(2L)))])
      | Sub1 -> 
        IMov(Reg(RAX), e_reg) ::
        (num_tag_check label_ARITH_NOT_NUM 
          [IAdd(Reg(RAX), Sized(QWORD_PTR, Const(Int64.neg 2L)))])
      | Print -> (setup_func_call [e_reg] "print") 
      | IsBool -> 
        let label_not_bool = (sprintf "%s%n" label_IS_NOT_BOOL tag) in 
        let label_done = (sprintf "%s%n" label_DONE tag) in
        IMov(Reg(RAX), e_reg) ::
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
        IMov(Reg(RAX), e_reg) :: (num_tag_check label_not_num 
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
          IMov(Reg(R11), bool_mask);
          IXor(Reg(RAX), Reg(R11));
          ]
      | PrintStack -> raise (NotYetImplemented "Fill in here")
    end
  | EPrim2 (op, e1, e2, tag) ->
    let e1_reg = compile_imm e1 env in
    let e2_reg = compile_imm e2 env in
    begin match op with
      | Plus -> 
        IMov(Reg(RAX), e2_reg) ::
        (num_tag_check label_ARITH_NOT_NUM 
          (IMov(Reg(RAX), e1_reg) ::
          (num_tag_check label_ARITH_NOT_NUM 
          [IAdd(Reg(RAX), e2_reg)])))
      | Minus -> 
        IMov(Reg(RAX), e2_reg) :: 
        (num_tag_check label_ARITH_NOT_NUM 
          (IMov(Reg(RAX), e1_reg) ::
          (num_tag_check label_ARITH_NOT_NUM 
          [ISub(Reg(RAX), e2_reg)])))
      | Times -> 
        IMov(Reg(RAX), e2_reg) :: 
        (num_tag_check label_ARITH_NOT_NUM 
          (IMov(Reg(RAX), e1_reg) ::
          (num_tag_check label_ARITH_NOT_NUM 
          [ISar(Reg(RAX), Const(1L)); IMul(Reg(RAX), e2_reg)])))
      | And -> 
        let label_done = (sprintf "%s%n" label_DONE tag) in
        IMov(Reg(RAX), e1_reg) ::
        (bool_tag_check e1_reg label_LOGIC_NOT_BOOL)
        @ [
          IMov(Reg(R11), bool_mask); ITest(Reg(RAX), Reg(R11)); IMov(Reg(RAX), const_false); IJz(label_done); 
          IMov(Reg(RAX), e2_reg)]
        @ (bool_tag_check e2_reg label_LOGIC_NOT_BOOL)
        @ [
          IMov(Reg(R11), bool_mask); ITest(Reg(RAX), Reg(R11)); IMov(Reg(RAX), const_false); IJz(label_done);
          IMov(Reg(RAX), const_true)]
        @ [ILabel(label_done)]
      | Or -> 
        let label_done = (sprintf "%s%n" label_DONE tag) in
        IMov(Reg(RAX), e1_reg) ::
        (bool_tag_check e1_reg label_LOGIC_NOT_BOOL)
        @ [
          IMov(Reg(R11), bool_mask); ITest(Reg(RAX), Reg(R11)); IMov(Reg(RAX), const_true); IJnz(label_done); 
          IMov(Reg(RAX), e2_reg)]
        @ (bool_tag_check e2_reg label_LOGIC_NOT_BOOL)
        @ [
          IMov(Reg(R11), bool_mask); ITest(Reg(RAX), Reg(R11)); IMov(Reg(RAX), const_true); IJnz(label_done);
          IMov(Reg(RAX), const_false)]
        @ [ILabel(label_done)]
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
        [IMov(Reg(RAX), e1_reg); IMov(Reg(R11), e2_reg); 
         ICmp(Reg(RAX), Reg(R11)); IMov(Reg(RAX), const_true);
         IJe(label_done); IMov(Reg(RAX), const_false);
         ILabel(label_done)]
    end
  | EIf(cond, thn, els, tag) -> let if_t = (sprintf "if_true_%n" tag) and
    if_f = (sprintf "if_false_%n" tag) and
    done_txt = (sprintf "done_%n" tag) and
    thn = compile_expr thn si env and
    els = compile_expr els si env and
    cond_value = compile_imm cond env in
    IMov(Reg(RAX), cond_value) ::
    (bool_tag_check cond_value label_IF_NOT_BOOL)
    @ [
      IMov(Reg(R11), bool_mask); ITest(Reg(RAX), Reg(R11));
      IJz(if_f);
      ILabel(if_t);
    ] @ thn @ [
      IJmp(done_txt);
      ILabel(if_f); 
    ] @ els @ [
      ILabel(done_txt);
    ]
  | ENumber(n, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EBool(n, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | EId(x, _) -> [ IMov(Reg(RAX), compile_imm e env) ]
  | _ -> raise (InternalCompilerError "Impossible: Not in ANF")
and compile_imm (e : tag expr) (env : (string * int) list) : arg =
  match e with
  | ENumber(n, _) ->
    if n > (Int64.div Int64.max_int 2L) || n < (Int64.div Int64.min_int 2L) then
      (* TODO: raise a better error of your choosing here *)
      failwith ("Integer overflow: " ^ (Int64.to_string n))
    else
      Sized(QWORD_PTR, Const(Int64.mul n 2L))
  | EBool(true, _) -> const_true
  | EBool(false, _) -> const_false
  | EId(x, _) -> RegOffset(~-(find env x), RBP)
  | _ -> raise (InternalCompilerError "Impossible: not an immediate")
;;

let rec repeat (v : 'a) (n : int) : 'a list = 
  match n with
  | 0 -> []
  | _ -> v::(repeat v (n - 1))

let compile_prog (anfed : tag expr) : string =
  let prelude =
    "section .text
extern error
extern print
global our_code_starts_here
our_code_starts_here:" in
  (* get max allocation needed as an even value, possibly rounded up *)
  let variable_allocation_space = (((count_vars anfed) + 1) / 2) * 2 in
  let stack_setup = [
    (* Save old RBP on the stack *)
    IPush(Reg(RBP));
    IMov(Reg(RBP), Reg(RSP))
  ] 
    (* Push 0 on stack count_var times *)
    @ (repeat (IPush(Const(0L))) variable_allocation_space) in 
  let postlude = [
    (* Undo save old RBP onto stack *)
    IMov(Reg(RSP),Reg(RBP));
    IPop(Reg(RBP));
    IRet
  ]
    @ (setup_err_call label_COMP_NOT_NUM [Reg(RAX); Const(err_COMP_NOT_NUM)])
    @ (setup_err_call label_ARITH_NOT_NUM [Reg(RAX); Const(err_ARITH_NOT_NUM)])
    @ (setup_err_call label_LOGIC_NOT_BOOL [Reg(RAX); Const(err_LOGIC_NOT_BOOL)])
    @ (setup_err_call label_IF_NOT_BOOL [Reg(RAX); Const(err_IF_NOT_BOOL)])
    @ (setup_err_call label_OVERFLOW [Reg(RAX); Const(err_OVERFLOW)])
  in
  let body = (compile_expr anfed 1 []) in
  let as_assembly_string = (to_asm (stack_setup @ body @ postlude)) in
  sprintf "%s%s\n" prelude as_assembly_string

let compile_to_string (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> (add_phase well_formed check_scope)
  |> (add_phase tagged tag)
  |> (add_phase renamed rename)
  |> (add_phase anfed (fun p -> tag (anf p)))
  |> (add_phase result compile_prog)
;;
