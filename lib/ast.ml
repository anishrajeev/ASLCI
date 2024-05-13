type ord =
  | OVar of string
  | OAbs of string*ord
  | OApp of ord*ord

type nameless =
  | Var of int
  | Abs of nameless
  | App of nameless*nameless

let rec toString = function 
  | Var v -> Int.to_string v
  | Abs body -> "(\\." ^ (toString body) ^ ")"
  | App (t1, t2) -> "(" ^
                    (toString t1) ^ " " ^
                    (toString t2) ^ ")"

