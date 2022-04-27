{
  open Lexing
  open Parser
  open Printf

let ignore_new_line lexbuf =
  let lcp = lexbuf.lex_curr_p in
  if lcp != dummy_pos then
    lexbuf.lex_curr_p <-
      { lcp with
        pos_lnum = lcp.pos_lnum + 1;
        pos_bol = lcp.pos_cnum;
      };
    lexbuf.lex_start_p <- lexbuf.lex_curr_p
}

let dec_digit = ['0'-'9']
let signed_int = dec_digit+ | ('-' dec_digit+)

let ident = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let blank = [' ' '\t']+

let tyident = "'"['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let space = [' ' '\t' '\n']+

rule token = parse
  | '#' [^ '\n']+ { token lexbuf }
  | blank "(" { LPARENSPACE }
  | '\n' "(" { ignore_new_line lexbuf; LPARENSPACE }
  | blank "<=" { LESSEQ }
  | '\n' "<=" { ignore_new_line lexbuf; LESSEQ }
  | blank "<" { LESSSPACE }
  | '\n' "<" { ignore_new_line lexbuf; LESSSPACE }
  | blank { token lexbuf }
  | '\n' { new_line lexbuf; token lexbuf }
  | signed_int as x { NUM (Int64.of_string x) }
  | '"' '"' '"' { parse_string (Buffer.create 100) true lexbuf}
  | '"' { parse_string (Buffer.create 100) false lexbuf }
  | "def" { DEF }
  | "and" { ANDDEF }
  | "print" { PRINT }
  | "printStack" { PRINTSTACK }
  | "nil" { NIL }
  | "true" { TRUE }
  | "false" { FALSE }
  | "istuple" { ISTUPLE }
  | "isbool" { ISBOOL }
  | "isnum" { ISNUM }
  | "isstr" { ISSTR }
  | "tonum" { TONUM }
  | "tostr" { TOSTR }
  | "tobool" { TOBOOL }
  | "add1" { ADD1 }
  | "sub1" { SUB1 }
  | "lambda" { LAMBDA }
  | "λ" { LAMBDA }
  | "if" { IF }
  | ":" { COLON }
  | "else:" { ELSECOLON }
  | "let" { LET }
  | "in" { IN }
  | "=" { EQUAL }
  | "," { COMMA }
  | "(" { LPARENNOSPACE }
  | ")" { RPAREN }
  | "[" { LBRACK }
  | "]" { RBRACK }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | ":=" { COLONEQ }
  | "==" { EQEQ }
  | ">" { GREATER }
  | "<=" { LESSEQ }
  | ">=" { GREATEREQ }
  | "&&" { AND }
  | "||" { OR }
  | "!" { NOT }
  | ";" { SEMI }
  | "begin" { BEGIN }
  | "end" { END }
  | "rec" { REC }
  | "shadow" { SHADOW }
  | ident as x { if x = "_" then UNDERSCORE else ID x }
  | eof { EOF }
  | _ as c { failwith (sprintf "Unrecognized character: %c" c) }
and parse_string str is_herestring =
  parse
  | '"' '"' '"' { 
    if is_herestring 
    then STR (Buffer.contents str) 
    else failwith "Herestring terminated in non-herestring literal"
  }
  | '"' { 
    if is_herestring
    then (Buffer.add_char str '"'; parse_string str is_herestring lexbuf)
    else (STR (Buffer.contents str))
  }
  | '\\' '"' { Buffer.add_char str '"'; parse_string str is_herestring lexbuf }
  | _ as c { Buffer.add_char str c; parse_string str is_herestring lexbuf }
  | eof { failwith "Unterminated string" }

