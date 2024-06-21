exception WrongArguments of string
exception Stuck

module StringSet = Set.Make( 
  struct
    let compare = compare
    type t = string
  end)

let fileconverter (fn : string) : Ast.ord =
  let file = open_in fn in
  let code = In_channel.input_all file in
  let tree = ParserInterface.parse code in
  let _ = Type.typer tree in
  tree

let rec lookup : string -> string list -> int =
  fun v nc ->
  match nc with
  | [] -> Int.min_int
  | x::xs -> if x = v then 0 else (1 + (lookup v xs))

let rec deBruijner : Ast.ord -> string list -> Ast.nameless =
  fun ast nc ->
  match ast with
  | Ast.OBool b -> Ast.Bool b
  | Ast.Oite (c, t1, t2) -> Ast.Ite (deBruijner c nc,
                                     deBruijner t1 nc,
                                     deBruijner t2 nc)
  | Ast.OZero -> Ast.Zero
  | Ast.OSucc t -> Ast.Succ (deBruijner t nc)
  | Ast.OPred t -> Ast.Pred (deBruijner t nc)
  | Ast.OIsZero t -> Ast.IsZero (deBruijner t nc)
  | Ast.OVar v -> Var (lookup v nc)
  | Ast.OAbs (v, t, _) -> Ast.Abs (deBruijner t (v::nc))
  | Ast.OApp (t1, t2) -> Ast.App (deBruijner t1 nc,
                                  deBruijner t2 nc)

let contextGen : Ast.ord -> string list = fun ast ->
  let rec setGen = function
    | Ast.OVar v -> StringSet.singleton v
    | Ast.OAbs (id, t, _) -> StringSet.remove id (setGen t)
    | Ast.OApp (t1, t2) -> StringSet.union (setGen t1) (setGen t2)
    | Ast.OBool _ -> StringSet.empty
    | Ast.Oite (t1, t2, t3) -> StringSet.union
                                 (setGen t1)
                                 (StringSet.union
                                    (setGen t2)
                                    (setGen t3))
    | Ast.OZero -> StringSet.empty
    | Ast.OSucc t -> setGen t
    | Ast.OPred t -> setGen t
    | Ast.OIsZero t -> setGen t
  in
  StringSet.elements (setGen ast)

let rec isVal : Ast.nameless -> bool = function
  | Ast.Abs _ -> true
  | Ast.Bool _ -> true
  | Zero -> true
  | Ast.Succ t when (isVal t) -> true
  | _ -> false

let shift : int -> Ast.nameless -> Ast.nameless =
  fun d ast ->
  let rec inner = fun c ast ->
    match ast with
    | Ast.Var i ->
      if i >= c
      then Ast.Var (i+d)
      else Ast.Var i
    | Ast.Abs t -> Ast.Abs (inner (c+1) t)
    | Ast.App (t1, t2) -> Ast.App (inner c t1, inner c t2)
    | Ast.Bool b -> Ast.Bool b
    | Ast.Ite (t1, t2, t3) ->
      Ast.Ite (inner c t1, inner c t2, inner c t3)
    | Ast.Zero -> Ast.Zero
    | Ast.Succ t -> Ast.Succ (inner c t)
    | Ast.Pred t -> Ast.Pred (inner c t)
    | Ast.IsZero t -> Ast.IsZero (inner c t)
  in
  inner 0 ast

let rec sub : int -> Ast.nameless -> Ast.nameless -> Ast.nameless =
  fun i s t ->
  match t with
  | Ast.Var j -> if i=j then s else Ast.Var j
  | Ast.Abs t -> Ast.Abs (sub (i+1) (shift 1 s) t)
  | Ast.App (t1, t2) -> Ast.App (sub i s t1, sub i s t2)
  | Ast.Bool b -> Ast.Bool b
  | Ast.Ite (t1, t2, t3) -> Ast.Ite (sub i s t1,
                                     sub i s t2,
                                     sub i s t3)
  | Ast.Zero -> Ast.Zero
  | Ast.Succ t -> Ast.Succ (sub i s t)
  | Ast.Pred t -> Ast.Pred (sub i s t)
  | Ast.IsZero t -> Ast.IsZero (sub i s t)

let rec evalstep : Ast.nameless  -> Ast.nameless =
  fun ast -> match ast with
    | Ast.App (Abs t1, t2) when isVal t2 ->
      shift (-1) (sub 0 (shift 1 t2) t1)
    | Ast.App (t1, t2) when isVal t1 ->
      Ast.App (t1, evalstep t2)
    | Ast.App (t1, t2) -> Ast.App (evalstep t1, t2)
    | Ast.Ite (Ast.Bool true, t1, _) -> t1
    | Ast.Ite (Ast.Bool false, _, t2) -> t2
    | Ast.Ite (c, t2, t3) ->
      (try let c' = evalstep c in
        Ast.Ite (c', t2, t3)
       with Stuck -> Ast.Ite (c, t2, t3))
    | Ast.Pred (Ast.Zero) -> Ast.Zero
    | Ast.Pred (Ast.Succ t) when (isVal t) -> t
    | Ast.Pred t -> Ast.Pred (evalstep t)
    | Ast.Succ t when (not (isVal t)) -> Ast.Succ (evalstep t)
    | Ast.IsZero Zero -> Ast.Bool true
    | Ast.IsZero t when (isVal t) -> Ast.Bool false
    | Ast.IsZero t -> Ast.IsZero (evalstep t)
    | _ -> raise Stuck

let rec eval (ast : Ast.nameless) : Ast.nameless =
  try let ast' = (evalstep ast)
    in eval ast'
  with Stuck -> ast
