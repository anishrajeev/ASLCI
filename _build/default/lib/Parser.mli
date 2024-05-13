
(* The type of tokens. *)

type token = 
  | VAR of (string)
  | RPAREN
  | LPAREN
  | LAMBDA
  | EOF
  | DOT

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.ord)
