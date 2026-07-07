open Nat
open Signatures
open Syntax

val lookup : string -> string list -> int option

module CstAnn :
 sig
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

val elaborate : coq_PtsSig -> CstAnn.obj -> string list -> exp option
