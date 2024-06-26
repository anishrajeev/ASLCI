exception IllTyped

let rec lookup
    (tc : (string*Ast.abstype) list)
    (v : string) : Ast.abstype =
  match tc with
  | [] -> raise IllTyped
  | (v', ty')::tcs -> if v = v' then ty' else lookup tcs v

let typer : Ast.ord -> Ast.abstype = fun ast ->
  let rec liltyper =
    fun tc ast -> match ast with
      | Ast.OVar v -> lookup tc v
      | Ast.OAbs (v, b, t) ->
        Ast.TAbs (t, liltyper ((v, t)::tc) b)
      | Ast.OApp (t1, t2) ->
        (let ty1 = liltyper tc t1 in
         let ty2 = liltyper tc t2 in
         (match (ty1, ty2) with
          | (Ast.TAbs (ty11, ty12), ty22) when ty11=ty22 -> ty12
          | _ -> raise IllTyped))
      | Ast.OBool _ -> (Boolean)
      | Ast.Oite (c, t1, t2) ->
        (let cty = liltyper tc c in
         let ty1 = liltyper tc t1 in
         let ty2 = liltyper tc t2 in
         if (cty == Ast.Boolean) && ty1==ty2
         then ty1
         else raise IllTyped)
      | Ast.OZero -> Ast.Natural
      | Ast.OSucc t when ((liltyper tc t) == Ast.Natural) -> Ast.Natural
      | Ast.OPred t when ((liltyper tc t) == Ast.Natural) -> Ast.Natural
      | Ast.OIsZero t when ((liltyper tc t) == Ast.Natural) ->
        Ast.Boolean
      | _ -> raise IllTyped
  in
  liltyper [] ast

      

