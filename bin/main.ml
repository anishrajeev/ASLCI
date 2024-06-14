open Lib

let () = if Array.length Sys.argv != 2
  then raise (Eval.WrongArguments "Didn't provide a valid file")
  else
    let oast = Eval.fileconverter Sys.argv.(1) in
    let bruijned = Eval.deBruijner oast (Eval.contextGen oast) in
    let evaled = Eval.eval bruijned in
    Printf.printf "%s\n" (Ast.toString evaled)
