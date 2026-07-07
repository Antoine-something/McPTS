open Elaborator
open Signature
open Syntax

module Cst =
 struct
  type obj =
  | Coq_s_typ
  | Coq_s_knd
  | Coq_pi of string * obj * obj * obj
  | Coq_fn of string * obj * obj * obj * obj
  | Coq_app of obj * obj
  | Coq_var of string
  | Coq_nat
  | Coq_zero
  | Coq_succ of obj
  | Coq_natrec of obj * string * obj * obj * string * string * obj
 end

(** val annotate' : Cst.obj -> CstAnn.obj option **)

let rec annotate' = function
| Cst.Coq_s_typ -> Some (CstAnn.Coq_st (Obj.magic Coq_s_typ))
| Cst.Coq_s_knd -> Some (CstAnn.Coq_st (Obj.magic Coq_s_knd))
| Cst.Coq_pi (s, s2, t, c) ->
  (match annotate' t with
   | Some t0 ->
     (match annotate' c with
      | Some c0 ->
        (match s2 with
         | Cst.Coq_s_typ ->
           Some (CstAnn.Coq_pi ((Obj.magic Coq_s_typ), (Obj.magic Coq_s_typ),
             (Obj.magic Coq_s_typ), (Obj.magic Coq_f_simple), s, t0, c0))
         | Cst.Coq_s_knd ->
           Some (CstAnn.Coq_pi ((Obj.magic Coq_s_typ), (Obj.magic Coq_s_knd),
             (Obj.magic Coq_s_knd), (Obj.magic Coq_f_dep), s, t0, c0))
         | _ -> None)
      | None -> None)
   | None -> None)
| Cst.Coq_fn (s, s2, t, b, c) ->
  (match annotate' t with
   | Some t0 ->
     (match annotate' b with
      | Some b0 ->
        (match annotate' c with
         | Some c0 ->
           (match s2 with
            | Cst.Coq_s_typ ->
              Some (CstAnn.Coq_fn ((Obj.magic Coq_s_typ),
                (Obj.magic Coq_s_typ), (Obj.magic Coq_s_typ),
                (Obj.magic Coq_f_simple), s, t0, b0, c0))
            | Cst.Coq_s_knd ->
              Some (CstAnn.Coq_fn ((Obj.magic Coq_s_typ),
                (Obj.magic Coq_s_knd), (Obj.magic Coq_s_knd),
                (Obj.magic Coq_f_dep), s, t0, b0, c0))
            | _ -> None)
         | None -> None)
      | None -> None)
   | None -> None)
| Cst.Coq_app (c1, c2) ->
  (match annotate' c1 with
   | Some c3 ->
     (match annotate' c2 with
      | Some c4 -> Some (CstAnn.Coq_app (c3, c4))
      | None -> None)
   | None -> None)
| Cst.Coq_var x -> Some (CstAnn.Coq_var x)
| Cst.Coq_nat -> Some CstAnn.Coq_nat
| Cst.Coq_zero -> Some CstAnn.Coq_zero
| Cst.Coq_succ c ->
  (match annotate' c with
   | Some c0 -> Some (CstAnn.Coq_succ c0)
   | None -> None)
| Cst.Coq_natrec (n, mx, m, z, sx, sr, s) ->
  (match annotate' n with
   | Some n0 ->
     (match annotate' m with
      | Some m0 ->
        (match annotate' z with
         | Some z0 ->
           (match annotate' s with
            | Some s0 -> Some (CstAnn.Coq_natrec (n0, mx, m0, z0, sx, sr, s0))
            | None -> None)
         | None -> None)
      | None -> None)
   | None -> None)

(** val elaborate' : Cst.obj -> string list -> exp option **)

let elaborate' cst ctx =
  match annotate' cst with
  | Some cst0 -> elaborate coq_LF_Sig cst0 ctx
  | None -> None
