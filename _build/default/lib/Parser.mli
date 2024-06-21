
(* The type of tokens. *)

type token = 
  | ZERO
  | VAR of (string)
  | TRUE
  | THEN
  | SUCC
  | RPAREN
  | PRED
  | NATTYPE
  | LPAREN
  | LAMBDA
  | ISZERO
  | IF
  | FALSE
  | EOF
  | ELSE
  | DOT
  | BOOLTYPE
  | ARROW
  | ANNOTATION

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.ord)
