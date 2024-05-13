{
  open Parser
}

let white = [' ' '\t' '\n']+

let string = ['a'-'z']+

rule token = parse
  | white { token lexbuf }
  | string { VAR (Lexing.lexeme lexbuf) }
  | '\\' { LAMBDA }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '.' { DOT }
  | eof { EOF }
  | _ { raise (Failure ("Invalid Character")) }



