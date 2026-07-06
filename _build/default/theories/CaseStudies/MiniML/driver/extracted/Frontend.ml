open Elaborator
open Signature
open Syntax

let __ = let rec f _ = Obj.repr f in Obj.repr f

module Cst =
 struct
  type obj =
  | Coq_st
  | Coq_pi of string * obj * obj
  | Coq_fn of string * obj * obj * obj
  | Coq_app of obj * obj
  | Coq_var of string
  | Coq_nat
  | Coq_zero
  | Coq_succ of obj
  | Coq_natrec of obj * string * obj * obj * string * string * obj
 end

(** val annotate' : Cst.obj -> CstAnn.obj **)

let rec annotate' = function
| Cst.Coq_st -> CstAnn.Coq_st (Obj.magic Coq_s_typ)
| Cst.Coq_pi (s, t, c) ->
  CstAnn.Coq_pi ((Obj.magic Coq_s_typ), (Obj.magic Coq_s_typ),
    (Obj.magic Coq_s_typ), (Obj.magic __), s, (annotate' t), (annotate' c))
| Cst.Coq_fn (s, t, b, c) ->
  CstAnn.Coq_fn ((Obj.magic Coq_s_typ), (Obj.magic Coq_s_typ),
    (Obj.magic Coq_s_typ), (Obj.magic __), s, (annotate' t), (annotate' b),
    (annotate' c))
| Cst.Coq_app (c1, c2) -> CstAnn.Coq_app ((annotate' c1), (annotate' c2))
| Cst.Coq_var x -> CstAnn.Coq_var x
| Cst.Coq_nat -> CstAnn.Coq_nat
| Cst.Coq_zero -> CstAnn.Coq_zero
| Cst.Coq_succ c -> CstAnn.Coq_succ (annotate' c)
| Cst.Coq_natrec (n, mx, m, z, sx, sr, s) ->
  CstAnn.Coq_natrec ((annotate' n), mx, (annotate' m), (annotate' z), sx, sr,
    (annotate' s))

(** val elaborate' : Cst.obj -> string list -> exp option **)

let elaborate' cst ctx =
  elaborate coq_MiniML_Sig (annotate' cst) ctx
