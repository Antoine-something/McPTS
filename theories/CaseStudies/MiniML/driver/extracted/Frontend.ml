open Nat
open Signature
open Syntax

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val lookup : string -> string list -> int option **)

let rec lookup s = function
| [] -> None
| c :: cs ->
  if (=) c s
  then Some 0
  else (match lookup s cs with
        | Some n -> Some (add n (Stdlib.Int.succ 0))
        | None -> None)

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

(** val elaborate' : Cst.obj -> string list -> exp option **)

let rec elaborate' cst ctx =
  match cst with
  | Cst.Coq_st -> Some (Coq_a_st (Obj.magic Coq_s_typ))
  | Cst.Coq_pi (s, t, c) ->
    (match elaborate' c (s :: ctx) with
     | Some a ->
       (match elaborate' t ctx with
        | Some t0 ->
          Some (Coq_a_pi ((Obj.magic Coq_s_typ), (Obj.magic Coq_s_typ),
            (Obj.magic Coq_s_typ), (Obj.magic __), t0, a))
        | None -> None)
     | None -> None)
  | Cst.Coq_fn (s, t, b, c) ->
    (match elaborate' c (s :: ctx) with
     | Some a ->
       (match elaborate' b (s :: ctx) with
        | Some b0 ->
          (match elaborate' t ctx with
           | Some t0 ->
             Some (Coq_a_fn ((Obj.magic Coq_s_typ), (Obj.magic Coq_s_typ),
               (Obj.magic Coq_s_typ), (Obj.magic __), t0, b0, a))
           | None -> None)
        | None -> None)
     | None -> None)
  | Cst.Coq_app (c1, c2) ->
    (match elaborate' c1 ctx with
     | Some a1 ->
       (match elaborate' c2 ctx with
        | Some a2 -> Some (Coq_a_app (a1, a2))
        | None -> None)
     | None -> None)
  | Cst.Coq_var x ->
    (match lookup x ctx with
     | Some n -> Some (Coq_a_var n)
     | None -> None)
  | Cst.Coq_nat -> Some Coq_a_nat
  | Cst.Coq_zero -> Some Coq_a_zero
  | Cst.Coq_succ c ->
    (match elaborate' c ctx with
     | Some a -> Some (Coq_a_succ a)
     | None -> None)
  | Cst.Coq_natrec (n, mx, m, z, sx, sr, s) ->
    (match elaborate' m (mx :: ctx) with
     | Some m0 ->
       (match elaborate' z ctx with
        | Some z0 ->
          (match elaborate' s (sr :: (sx :: ctx)) with
           | Some s0 ->
             (match elaborate' n ctx with
              | Some n0 -> Some (Coq_a_natrec (m0, z0, s0, n0))
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
