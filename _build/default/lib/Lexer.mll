{
  open Parser
}

rule token = parse
  | [' ' '\t' '\n'] { token lexbuf }
  | ['a'-'z']+ { VAR (Lexing.lexeme lexbuf) }
  | "BOOL" { BOOLTYPE }
  | "IF" { IF }
  | "THEN" { THEN }
  | "ELSE" { ELSE }
  | "#t" { TRUE }
  | "#f" { FALSE }
  | ':' { ANNOTATION }
  | "->" { ARROW }
  | '\\' { LAMBDA }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '.' { DOT }
  | eof { EOF }
  | _ { raise (Failure ("Invalid Character")) }



