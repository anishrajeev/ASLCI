%{
open Ast
%}

%token <string> VAR
%token LAMBDA
%token LPAREN
%token RPAREN
%token DOT
%token EOF

%type <Ast.ord> program
%start program
%nonassoc LPAREN VAR DOT LAMBDA
%left APP
%%

program:
  | t=term; EOF { t }

term:
  | v=VAR { OVar v }
  | LAMBDA; v=VAR; DOT; t=term { OAbs (v, t) }
  | LPAREN; t=term; RPAREN { t }
  | t1=term; t2=term; %prec APP { OApp (t1, t2) }


