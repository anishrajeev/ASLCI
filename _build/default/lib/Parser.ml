
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | ZERO
    | VAR of (
# 5 "lib/Parser.mly"
       (string)
# 16 "lib/Parser.ml"
  )
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
  
end

include MenhirBasics

# 1 "lib/Parser.mly"
  
    open Ast

# 44 "lib/Parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_program) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: program. *)

  | MenhirState05 : (('s, _menhir_box_program) _menhir_cell1_SUCC, _menhir_box_program) _menhir_state
    (** State 05.
        Stack shape : SUCC.
        Start symbol: program. *)

  | MenhirState07 : (('s, _menhir_box_program) _menhir_cell1_PRED, _menhir_box_program) _menhir_state
    (** State 07.
        Stack shape : PRED.
        Start symbol: program. *)

  | MenhirState08 : (('s, _menhir_box_program) _menhir_cell1_LPAREN, _menhir_box_program) _menhir_state
    (** State 08.
        Stack shape : LPAREN.
        Start symbol: program. *)

  | MenhirState11 : (('s, _menhir_box_program) _menhir_cell1_LAMBDA _menhir_cell0_VAR, _menhir_box_program) _menhir_state
    (** State 11.
        Stack shape : LAMBDA VAR.
        Start symbol: program. *)

  | MenhirState15 : ((('s, _menhir_box_program) _menhir_cell1_LAMBDA _menhir_cell0_VAR, _menhir_box_program) _menhir_cell1_types, _menhir_box_program) _menhir_state
    (** State 15.
        Stack shape : LAMBDA VAR types.
        Start symbol: program. *)

  | MenhirState17 : (('s, _menhir_box_program) _menhir_cell1_ISZERO, _menhir_box_program) _menhir_state
    (** State 17.
        Stack shape : ISZERO.
        Start symbol: program. *)

  | MenhirState18 : (('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_state
    (** State 18.
        Stack shape : IF.
        Start symbol: program. *)

  | MenhirState21 : ((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_term, _menhir_box_program) _menhir_state
    (** State 21.
        Stack shape : IF term.
        Start symbol: program. *)

  | MenhirState23 : (((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_term, _menhir_box_program) _menhir_cell1_term, _menhir_box_program) _menhir_state
    (** State 23.
        Stack shape : IF term term.
        Start symbol: program. *)

  | MenhirState26 : (('s, _menhir_box_program) _menhir_cell1_appterm, _menhir_box_program) _menhir_state
    (** State 26.
        Stack shape : appterm.
        Start symbol: program. *)

  | MenhirState31 : (('s, _menhir_box_program) _menhir_cell1_types, _menhir_box_program) _menhir_state
    (** State 31.
        Stack shape : types.
        Start symbol: program. *)


and ('s, 'r) _menhir_cell1_appterm = 
  | MenhirCell1_appterm of 's * ('s, 'r) _menhir_state * (Ast.ord)

and ('s, 'r) _menhir_cell1_term = 
  | MenhirCell1_term of 's * ('s, 'r) _menhir_state * (Ast.ord)

and ('s, 'r) _menhir_cell1_types = 
  | MenhirCell1_types of 's * ('s, 'r) _menhir_state * (Ast.abstype)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_ISZERO = 
  | MenhirCell1_ISZERO of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LAMBDA = 
  | MenhirCell1_LAMBDA of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PRED = 
  | MenhirCell1_PRED of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SUCC = 
  | MenhirCell1_SUCC of 's * ('s, 'r) _menhir_state

and 's _menhir_cell0_VAR = 
  | MenhirCell0_VAR of 's * (
# 5 "lib/Parser.mly"
       (string)
# 139 "lib/Parser.ml"
)

and _menhir_box_program = 
  | MenhirBox_program of (Ast.ord) [@@unboxed]

let _menhir_action_01 =
  fun s ->
    (
# 48 "lib/Parser.mly"
                 ( s )
# 150 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_02 =
  fun a s ->
    (
# 49 "lib/Parser.mly"
                            ( OApp (a, s)  )
# 158 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_03 =
  fun t ->
    (
# 35 "lib/Parser.mly"
                ( t )
# 166 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_04 =
  fun v ->
    (
# 52 "lib/Parser.mly"
          ( OVar v )
# 174 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_05 =
  fun t ->
    (
# 53 "lib/Parser.mly"
                           ( t )
# 182 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_06 =
  fun () ->
    (
# 54 "lib/Parser.mly"
         ( OBool true )
# 190 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_07 =
  fun () ->
    (
# 55 "lib/Parser.mly"
          ( OBool false )
# 198 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_08 =
  fun () ->
    (
# 56 "lib/Parser.mly"
         ( OZero )
# 206 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_09 =
  fun c t1 t2 ->
    (
# 58 "lib/Parser.mly"
    ( Oite (c, t1, t2) )
# 214 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_10 =
  fun t ->
    (
# 59 "lib/Parser.mly"
                                       ( OSucc t )
# 222 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_11 =
  fun t ->
    (
# 60 "lib/Parser.mly"
                                       ( OPred t )
# 230 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_12 =
  fun t ->
    (
# 61 "lib/Parser.mly"
                                       ( OIsZero t )
# 238 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_13 =
  fun t tt v ->
    (
# 44 "lib/Parser.mly"
    ( OAbs (v, t, tt) )
# 246 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_14 =
  fun a ->
    (
# 45 "lib/Parser.mly"
              ( a )
# 254 "lib/Parser.ml"
     : (Ast.ord))

let _menhir_action_15 =
  fun () ->
    (
# 38 "lib/Parser.mly"
             ( Boolean )
# 262 "lib/Parser.ml"
     : (Ast.abstype))

let _menhir_action_16 =
  fun () ->
    (
# 39 "lib/Parser.mly"
            ( Natural )
# 270 "lib/Parser.ml"
     : (Ast.abstype))

let _menhir_action_17 =
  fun t1 t2 ->
    (
# 40 "lib/Parser.mly"
                              ( TAbs (t1, t2) )
# 278 "lib/Parser.ml"
     : (Ast.abstype))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ANNOTATION ->
        "ANNOTATION"
    | ARROW ->
        "ARROW"
    | BOOLTYPE ->
        "BOOLTYPE"
    | DOT ->
        "DOT"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | FALSE ->
        "FALSE"
    | IF ->
        "IF"
    | ISZERO ->
        "ISZERO"
    | LAMBDA ->
        "LAMBDA"
    | LPAREN ->
        "LPAREN"
    | NATTYPE ->
        "NATTYPE"
    | PRED ->
        "PRED"
    | RPAREN ->
        "RPAREN"
    | SUCC ->
        "SUCC"
    | THEN ->
        "THEN"
    | TRUE ->
        "TRUE"
    | VAR _ ->
        "VAR"
    | ZERO ->
        "ZERO"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_39 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _v _tok ->
      match (_tok : MenhirBasics.token) with
      | EOF ->
          let t = _v in
          let _v = _menhir_action_03 t in
          MenhirBox_program _v
      | _ ->
          _eRR ()
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_08 () in
      _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_simpleterm : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState05 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState07 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState17 ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState26 ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState00 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState08 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState15 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState18 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState23 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_37 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_SUCC -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_SUCC (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_10 t in
          _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_35 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_PRED -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_PRED (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_11 t in
          _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_28 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_ISZERO -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_ISZERO (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_12 t in
          _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_27 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_appterm -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_appterm (_menhir_stack, _menhir_s, a) = _menhir_stack in
      let s = _v in
      let _v = _menhir_action_02 a s in
      _menhir_goto_appterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_appterm : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | VAR _v_0 ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState26
      | TRUE ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | SUCC ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | PRED ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | LPAREN ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | ISZERO ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | IF ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | FALSE ->
          let _menhir_stack = MenhirCell1_appterm (_menhir_stack, _menhir_s, _v) in
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
      | ELSE | EOF | RPAREN | THEN ->
          let a = _v in
          let _v = _menhir_action_14 a in
          _menhir_goto_term _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_02 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let v = _v in
      let _v = _menhir_action_04 v in
      _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_06 () in
      _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_04 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SUCC (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState05 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | VAR _v ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TRUE ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SUCC ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PRED ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ISZERO ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FALSE ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PRED (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState07 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | VAR _v ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TRUE ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SUCC ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PRED ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ISZERO ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FALSE ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState08 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | VAR _v ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TRUE ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SUCC ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PRED ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LAMBDA ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ISZERO ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FALSE ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_09 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LAMBDA (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR _v ->
          let _menhir_stack = MenhirCell0_VAR (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ANNOTATION ->
              let _menhir_s = MenhirState11 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | NATTYPE ->
                  _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | BOOLTYPE ->
                  _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_16 () in
      _menhir_goto_types _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_types : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState31 ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState11 ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_32 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_types as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _menhir_stack = MenhirCell1_types (_menhir_stack, _menhir_s, _v) in
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let MenhirCell1_types (_menhir_stack, _menhir_s, t1) = _menhir_stack in
          let t2 = _v in
          let _v = _menhir_action_17 t1 t2 in
          _menhir_goto_types _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_31 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_types -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState31 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | NATTYPE ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | BOOLTYPE ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_13 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_15 () in
      _menhir_goto_types _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_14 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_LAMBDA _menhir_cell0_VAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_types (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | DOT ->
          let _menhir_s = MenhirState15 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | VAR _v ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TRUE ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SUCC ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PRED ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LAMBDA ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ISZERO ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FALSE ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | ARROW ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_16 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ISZERO (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState17 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | VAR _v ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TRUE ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SUCC ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PRED ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ISZERO ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FALSE ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_18 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState18 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | VAR _v ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TRUE ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SUCC ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PRED ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LAMBDA ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ISZERO ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FALSE ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_19 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_07 () in
      _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_term : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_39 _menhir_stack _v _tok
      | MenhirState08 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState15 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState23 ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState21 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState18 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_33 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_LPAREN -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let t = _v in
          let _v = _menhir_action_05 t in
          _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_30 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_LAMBDA _menhir_cell0_VAR, _menhir_box_program) _menhir_cell1_types -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_types (_menhir_stack, _, tt) = _menhir_stack in
      let MenhirCell0_VAR (_menhir_stack, v) = _menhir_stack in
      let MenhirCell1_LAMBDA (_menhir_stack, _menhir_s) = _menhir_stack in
      let t = _v in
      let _v = _menhir_action_13 t tt v in
      _menhir_goto_term _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_24 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_term, _menhir_box_program) _menhir_cell1_term -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_term (_menhir_stack, _, t1) = _menhir_stack in
      let MenhirCell1_term (_menhir_stack, _, c) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let t2 = _v in
      let _v = _menhir_action_09 c t1 t2 in
      _menhir_goto_simpleterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_22 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_term as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_term (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _menhir_s = MenhirState23 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | VAR _v ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TRUE ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SUCC ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PRED ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LAMBDA ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ISZERO ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FALSE ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_20 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_term (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _menhir_s = MenhirState21 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ZERO ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | VAR _v ->
              _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | TRUE ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SUCC ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | PRED ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAREN ->
              _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LAMBDA ->
              _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | ISZERO ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IF ->
              _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | FALSE ->
              _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_25 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let s = _v in
      let _v = _menhir_action_01 s in
      _menhir_goto_appterm _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState00 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ZERO ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | VAR _v ->
          _menhir_run_02 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | TRUE ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SUCC ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | PRED ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAREN ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LAMBDA ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | ISZERO ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IF ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | FALSE ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
end

let program =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_program v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
