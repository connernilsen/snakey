open Printf

type expr =
  | Num of int64
  | Add1 of expr
  | Sub1 of expr
  | Id of string
  | Let of string * expr * expr

type reg = RAX | RSP

type arg = Const of int64 | Reg of reg | RegOffset of reg * int

type instr = IMov of arg * arg | IAdd of arg * arg | ISub of arg * arg

type env = (string * int) list

let rec lookup name env =
  match env with
  | [] -> failwith (sprintf "Identifier %s not found in env" name)
  | (n, i) :: rest -> if n = name then i else lookup name rest

let rec add name env : env * int =
  let slot = 1 + List.length env in
  ((name, slot) :: env, slot)

let rec compile_expr (e : expr) (env : env) : instr list =
  match e with
  | Num n -> [IMov (Reg RAX, Const n)]
  | Add1 e -> compile_expr e env @ [IAdd (Reg RAX, Const 1L)]
  | Sub1 e -> compile_expr e env @ [ISub (Reg RAX, Const (Int64.neg 1L))]
  | Let (x, e, b) ->
      let env', slot = add x env in
      compile_expr e env @ [IMov (RegOffset (RSP, ~-1 * slot), Reg RAX)] @ compile_expr b env'
  | Id i -> [IMov (Reg RAX, RegOffset (RSP, ~-1 * lookup i env))]

let rec asm_to_string (instrs : instr list) : string =
  let rec arg_to_string (arg : arg) =
    match arg with
    | Const x -> Int64.to_string x
    | Reg RAX -> "RAX"
    | Reg RSP -> "RSP"
    | RegOffset (reg, offset) ->
        sprintf "[%s + 8 * %s]" (arg_to_string (Reg reg)) (string_of_int offset)
  in
  match instrs with
  | [] -> ""
  | IMov (t, f) :: rest ->
      sprintf "mov %s, %s\n%s" (arg_to_string t) (arg_to_string f) (asm_to_string rest)
  | IAdd (t, f) :: rest ->
      sprintf "add %s, %s\n%s" (arg_to_string t) (arg_to_string f) (asm_to_string rest)
  | ISub (t, f) :: rest ->
      sprintf "sub %s, %s\n%s" (arg_to_string t) (arg_to_string f) (asm_to_string rest)

let compile_prog (e : expr) : string =
  let instrs = compile_expr e [] in
  let asm_string = asm_to_string instrs in
  let prelude = "\nsection .text\nglobal our_code_starts_here\nour_code_starts_here:" in
  let suffix = "ret" in
  prelude ^ "\n" ^ asm_string ^ "\n" ^ suffix

let () =
  printf "%s"
    (compile_prog
       (Let
          ( "a"
          , Num 10L
          , Let
              ("c", Let ("b", Add1 (Id "a"), Let ("d", Add1 (Id "b"), Add1 (Id "b"))), Add1 (Id "c"))
          ) ) )
