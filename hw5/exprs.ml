open Printf
open Int64
;;
       
type sourcespan = (Lexing.position * Lexing.position)

type tag = int

type prim1 =
  | Add1
  | Sub1
  | Print
  | IsBool
  | IsNum
  | Not
  | PrintStack

type prim2 =
  | Plus
  | Minus
  | Times
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq

type sprim2 = (* Sugared prim *)
  | Plus
  | Minus
  | Times
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq

type 'a bind = (string * 'a expr * 'a)

and 'a expr =
  | ELet of 'a bind list * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ENumber of int64 * 'a
  | EBool of bool * 'a
  | EId of string * 'a
  | EApp of string * 'a expr list * 'a

type 'a sbind = (string * 'a sexpr * 'a)
and 'a sprogram =
  | SProgram of 'a sdecl list * 'a sexpr * 'a
and 'a sexpr = (* Sugared expression *)
  | SLet of 'a sbind list * 'a sexpr * 'a
  | SPrim1 of prim1 * 'a sexpr * 'a
  | SPrim2 of sprim2 * 'a sexpr * 'a sexpr * 'a
  | SIf of 'a sexpr * 'a sexpr * 'a sexpr * 'a
  | SNumber of int64 * 'a
  | SBool of bool * 'a
  | SId of string * 'a
  | SApp of string * 'a sexpr list * 'a
and 'a sdecl =
  | SDFun of string * (string * 'a) list * 'a sexpr * 'a

type 'a decl =
  | DFun of string * (string * 'a) list * 'a expr * 'a

type 'a program =
  | Program of 'a decl list * 'a expr * 'a

type 'a immexpr = (* immediate expressions *)
  | ImmNum of int64 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
and 'a cexpr = (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of sprim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of string * 'a immexpr list * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
and 'a aexpr = (* anf expressions *)
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ACExpr of 'a cexpr
and 'a adecl =
  | ADFun of string * string list * 'a aexpr * 'a

and 'a aprogram =
  | AProgram of 'a adecl list * 'a aexpr * 'a


let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next in
  let rec helpE (e : 'a expr) : tag expr =
    match e with
    | EId(x, _) -> EId(x, tag())
    | ENumber(n, _) -> ENumber(n, tag())
    | EBool(b, _) -> EBool(b, tag())
    | EPrim1(op, e, _) ->
       let prim_tag = tag() in
       EPrim1(op, helpE e, prim_tag)
    | EPrim2(op, e1, e2, _) ->
       let prim_tag = tag() in
       EPrim2(op, helpE e1, helpE e2, prim_tag)
    | ELet(binds, body, _) ->
       let let_tag = tag() in
       ELet(List.map (fun (x, b, _) -> let t = tag() in (x, helpE b, t)) binds, helpE body, let_tag)
    | EIf(cond, thn, els, _) ->
       let if_tag = tag() in
       EIf(helpE cond, helpE thn, helpE els, if_tag)
    | EApp(name, args, _) ->
       let app_tag = tag() in
       EApp(name, List.map helpE args, app_tag)
  and helpD d =
    match d with
    | DFun(name, args, body, _) ->
       let fun_tag = tag() in
       DFun(name, List.map (fun (a, _) -> (a, tag())) args, helpE body, fun_tag)
  and helpP p =
    match p with
    | Program(decls, body, _) ->
       Program(List.map helpD decls, helpE body, 0)
  in helpP p

let rec untag (p : 'a program) : unit program =
  let rec helpE e =
    match e with
    | EId(x, _) -> EId(x, ())
    | ENumber(n, _) -> ENumber(n, ())
    | EBool(b, _) -> EBool(b, ())
    | EPrim1(op, e, _) ->
       EPrim1(op, helpE e, ())
    | EPrim2(op, e1, e2, _) ->
       EPrim2(op, helpE e1, helpE e2, ())
    | ELet(binds, body, _) ->
       ELet(List.map(fun (x, b, _) -> (x, helpE b, ())) binds, helpE body, ())
    | EIf(cond, thn, els, _) ->
       EIf(helpE cond, helpE thn, helpE els, ())
    | EApp(name, args, _) ->
       EApp(name, List.map helpE args, ())
  and helpD d =
    match d with
    | DFun(name, args, body, _) ->
       DFun(name, List.map (fun (a, _) -> (a, ())) args, helpE body, ())
  and helpP p =
    match p with
    | Program(decls, body, _) ->
       Program(List.map helpD decls, helpE body, ())
  in helpP p

let stag (p : 'a sprogram) : tag sprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next in
  let rec helpE (e : 'a sexpr) : tag sexpr =
    match e with
    | SId(x, _) -> SId(x, tag())
    | SNumber(n, _) -> SNumber(n, tag())
    | SBool(b, _) -> SBool(b, tag())
    | SPrim1(op, e, _) ->
       let prim_tag = tag() in
       SPrim1(op, helpE e, prim_tag)
    | SPrim2(op, e1, e2, _) ->
       let prim_tag = tag() in
       SPrim2(op, helpE e1, helpE e2, prim_tag)
    | SLet(binds, body, _) ->
       let let_tag = tag() in
       SLet(List.map (fun (x, b, _) -> let t = tag() in (x, helpE b, t)) binds, helpE body, let_tag)
    | SIf(cond, thn, els, _) ->
       let if_tag = tag() in
       SIf(helpE cond, helpE thn, helpE els, if_tag)
    | SApp(name, args, _) ->
       let app_tag = tag() in
       SApp(name, List.map helpE args, app_tag)
  and helpD d =
    match d with
    | SDFun(name, args, body, _) ->
       let fun_tag = tag() in
       SDFun(name, List.map (fun (a, _) -> (a, tag())) args, helpE body, fun_tag)
  and helpP p =
    match p with
    | SProgram(decls, body, _) ->
       SProgram(List.map helpD decls, helpE body, 0)
  in helpP p

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ALet(x, c, b, _) ->
       let let_tag = tag() in
       ALet(x, helpC c, helpA b, let_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1(op, e, _) ->
       let prim_tag = tag() in
       CPrim1(op, helpI e, prim_tag)
    | CPrim2(op, e1, e2, _) ->
       let prim_tag = tag() in
       CPrim2(op, helpI e1, helpI e2, prim_tag)
    | CIf(cond, thn, els, _) ->
       let if_tag = tag() in
       CIf(helpI cond, helpA thn, helpA els, if_tag)
    | CApp(name, args, _) ->
       let app_tag = tag() in
       CApp(name, List.map helpI args, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmId(x, _) -> ImmId(x, tag())
    | ImmNum(n, _) -> ImmNum(n, tag())
    | ImmBool(b, _) -> ImmBool(b, tag())
  and helpD d =
    match d with
    | ADFun(name, args, body, _) ->
       let fun_tag = tag() in
       ADFun(name, args, helpA body, fun_tag)
  and helpP p =
    match p with
    | AProgram(decls, body, _) ->
       AProgram(List.map helpD decls, helpA body, 0)
  in helpP p

let desugar (p : tag program) : unit sprogram =
  let rec helpE (e : tag expr) : unit sexpr =
    match e with
    | EId(x, _) -> SId(x, ())
    | ENumber(n, _) -> SNumber(n, ())
    | EBool(b, _) -> SBool(b, ())
    | EPrim1(op, e, _) ->
       SPrim1(op, helpE e, ())
    | EPrim2(op, e1, e2, a) ->
      begin
       match op with
       | And -> SIf(
          helpE e1,
          SIf(
            helpE e2,
            SBool(true, ()),
            SBool(false, ()),
            ()
          ),
          SBool(false, ()),
          ()
        )
       | Or -> SIf(
          helpE e1,
          SBool(true, ()),
          SIf(
          helpE e2,
          SBool(true, ()),
          SBool(false, ()),
          ()
          ),
        ()
        )
       | Plus -> SPrim2(Plus, helpE e1, helpE e2, ())
       | Minus -> SPrim2(Minus, helpE e1, helpE e2, ())
       | Times -> SPrim2(Times, helpE e1, helpE e2, ())
       | Greater -> SPrim2(Greater, helpE e1, helpE e2, ())
       | GreaterEq -> SPrim2(GreaterEq, helpE e1, helpE e2, ())
       | Less -> SPrim2(Less, helpE e1, helpE e2, ())
       | LessEq -> SPrim2(LessEq, helpE e1, helpE e2, ())
       | Eq -> SPrim2(Eq, helpE e1, helpE e2, ())
      end
    | ELet(binds, body, _) ->
       SLet(List.map (fun (name, expr, _) -> (name, helpE expr, ())) binds, helpE body, ())
    | EIf(cond, thn, els, _) ->
       SIf(helpE cond, helpE thn, helpE els, ())
    | EApp(name, args, _) ->
       SApp(name, List.map helpE args, ())
  and helpD d =
    match d with
    | DFun(name, args, body, _) ->
       SDFun(name, List.map (fun (name, _) -> (name, ())) args, helpE body, ())
  and helpP p =
    match p with
    | Program(decls, body, _) ->
       SProgram(List.map helpD decls, helpE body, ())
  in helpP p
