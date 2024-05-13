open Parsing.Ast

exception WrongArguments of string
exception Stuck

module StringSet = Set.Make( 
  struct
    let compare = compare
    type t = string
  end )

let fileconverter (fn : string) : ord =
  let file = open_in fn in
  let code = In_channel.input_all file in
  let tree = Parsing.ParserInterface.parse code in
  tree              

let rec lookup : string -> string list -> int =
  fun v nc ->
  match nc with
  | [] -> Int.min_int
  | x::xs -> if x = v then 0 else (1 + (lookup v xs))

let rec deBruijner : ord -> string list -> nameless =
  fun ast nc ->
  match ast with
  | OVar v -> Var (lookup v nc)
  | OAbs (v, t) -> Abs (deBruijner t (v::nc))
  | OApp (t1, t2) -> App (deBruijner t1 nc,
                          deBruijner t2 nc)

let contextGen : ord -> string list = fun ast ->
  let rec setGen = function
  | OVar v -> StringSet.singleton v
  | OAbs (id, t) -> StringSet.remove id (setGen t)
  | OApp (t1, t2) -> StringSet.union (setGen t1) (setGen t2)
  in
  StringSet.elements (setGen ast)

let isVal : nameless -> bool = function
  | Abs _ -> true
  | _ -> false

let shift : int -> nameless -> nameless = fun d ast ->
  let rec inner = fun c ast ->
    match ast with
    | Var i -> if i >= c then Var (i+d) else Var i
    | Abs t -> Abs (inner (c+1) t)
    | App (t1, t2) -> App (inner c t1, inner c t2)
  in
  inner 0 ast

let rec sub : int -> nameless -> nameless -> nameless =
  fun i s t ->
  match t with
  | Var j -> if i=j then s else Var j
  | Abs t -> Abs (sub (i+1) (shift 1 s) t)
  | App (t1, t2) -> App (sub i s t1, sub i s t2)

let rec evalstep : nameless  -> nameless =
  fun ast -> match ast with
    | App (Abs t1, t2) when isVal t2 ->
      shift (-1) (sub 0 (shift 1 t2) t1)
    | App (t1, t2) when isVal t1 ->
      App (t1, evalstep t2)
    | App (t1, t2) -> App (evalstep t1, t2)
    | _ -> raise Stuck

let rec eval (ast : nameless) : nameless =
  try let ast' = (evalstep ast)
    in eval ast'
  with Stuck -> ast

let () = if Array.length Sys.argv != 2
  then raise (WrongArguments "Didn't provide a valid file")
  else
    let oast = fileconverter Sys.argv.(1) in
    let bruijned = deBruijner oast (contextGen oast) in
    let evaled = eval bruijned in
    Printf.printf "%s\n" (toString evaled)
