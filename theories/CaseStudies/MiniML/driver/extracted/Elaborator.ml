open Nat
open Signatures
open Syntax

(** val lookup : string -> string list -> int option **)

let rec lookup s = function
| [] -> None
| c :: cs ->
  if (=) c s
  then Some 0
  else (match lookup s cs with
        | Some n -> Some (add n (Stdlib.Int.succ 0))
        | None -> None)

module CstAnn =
 struct
  type obj =
  | Coq_st of coq_St
  | Coq_pi of coq_St * coq_St * coq_St * coq_Ru_pi * string * obj * obj
  | Coq_fn of coq_St * coq_St * coq_St * coq_Ru_pi * string * obj * obj * obj
  | Coq_app of obj * obj
  | Coq_var of string
  | Coq_nat
  | Coq_zero
  | Coq_succ of obj
  | Coq_natrec of obj * string * obj * obj * string * string * obj
 end

(** val elaborate : coq_PtsSig -> CstAnn.obj -> string list -> exp option **)

let rec elaborate p cst ctx =
  match cst with
  | CstAnn.Coq_st s -> Some (Coq_a_st s)
  | CstAnn.Coq_pi (s1, s2, s3, r, s, t, c) ->
    (match elaborate p c (s :: ctx) with
     | Some a ->
       (match elaborate p t ctx with
        | Some t0 -> Some (Coq_a_pi (s1, s2, s3, r, t0, a))
        | None -> None)
     | None -> None)
  | CstAnn.Coq_fn (s1, s2, s3, r, s, t, b, c) ->
    (match elaborate p c (s :: ctx) with
     | Some a ->
       (match elaborate p b (s :: ctx) with
        | Some b0 ->
          (match elaborate p t ctx with
           | Some t0 -> Some (Coq_a_fn (s1, s2, s3, r, t0, b0, a))
           | None -> None)
        | None -> None)
     | None -> None)
  | CstAnn.Coq_app (c1, c2) ->
    (match elaborate p c1 ctx with
     | Some a1 ->
       (match elaborate p c2 ctx with
        | Some a2 -> Some (Coq_a_app (a1, a2))
        | None -> None)
     | None -> None)
  | CstAnn.Coq_var s ->
    (match lookup s ctx with
     | Some n -> Some (Coq_a_var n)
     | None -> None)
  | CstAnn.Coq_nat -> Some Coq_a_nat
  | CstAnn.Coq_zero -> Some Coq_a_zero
  | CstAnn.Coq_succ c ->
    (match elaborate p c ctx with
     | Some a -> Some (Coq_a_succ a)
     | None -> None)
  | CstAnn.Coq_natrec (n, mx, m, z, sx, sr, s) ->
    (match elaborate p m (mx :: ctx) with
     | Some m0 ->
       (match elaborate p z ctx with
        | Some z0 ->
          (match elaborate p s (sr :: (sx :: ctx)) with
           | Some s0 ->
             (match elaborate p n ctx with
              | Some n0 -> Some (Coq_a_natrec (m0, z0, s0, n0))
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
