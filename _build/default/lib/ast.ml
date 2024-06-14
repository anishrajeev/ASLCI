type abstype =
  | Natural
  | Boolean
  | TAbs of abstype*abstype

type ord =
  | OVar of string
  | OAbs of string*ord*abstype
  | OApp of ord*ord
  | OBool of bool
  | Oite of ord*ord*ord

type nameless =
  | Var of int
  | Abs of nameless
  | App of nameless*nameless
  | Bool of bool
  | Ite of nameless*nameless*nameless

let rec toString = function 
  | Var v -> Int.to_string v
  | Abs body -> "(\\." ^ (toString body) ^ ")"
  | App (t1, t2) -> "(" ^
                    (toString t1) ^ " " ^
                    (toString t2) ^ ")"
  | Bool b -> if b then "#t" else "#f"
  | Ite (c, t1, t2) -> "if " ^
                          (toString c) ^ " then " ^
                          (toString t1) ^ " else " ^
                          (toString t2)
  
