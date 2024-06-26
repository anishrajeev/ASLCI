%{
    open Ast
%}

%token <string> VAR
%token TRUE
%token FALSE
%token ANNOTATION
%token ARROW
%token BOOLTYPE
%token IF
%token THEN
%token ELSE
%token NATTYPE
%token ZERO
%token SUCC
%token PRED
%token ISZERO
%token LAMBDA
%token LPAREN
%token RPAREN
%token DOT
%token EOF

%start program
%type <Ast.ord> program
%type <Ast.abstype> types
%type <Ast.ord> term
%type <Ast.ord> appterm
%type <Ast.ord> simpleterm

%%

program:
  | t=term; EOF { t }

types:
  | BOOLTYPE { Boolean }
  | NATTYPE { Natural }
  | t1=types; ARROW; t2=types { TAbs (t1, t2) }

term:
  | LAMBDA; v=VAR; ANNOTATION; tt=types; DOT; t=term
    { OAbs (v, t, tt) }
  | a=appterm { a }

appterm:
  | s=simpleterm { s }
  | a=appterm; s=simpleterm { OApp (a, s)  }

simpleterm:
  | v=VAR { OVar v }
  | LPAREN; t=term; RPAREN { t }
  | TRUE { OBool true }
  | FALSE { OBool false }
  | ZERO { OZero }
  | IF; c=term; THEN; t1=term; ELSE; t2=term
    { Oite (c, t1, t2) }
  | SUCC; LPAREN; t=simpleterm; RPAREN { OSucc t }
  | PRED; LPAREN; t=simpleterm; RPAREN { OPred t }
| ISZERO; LPAREN; t=simpleterm; RPAREN { OIsZero t }



