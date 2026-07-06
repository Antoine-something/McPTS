open Elaborator
open Signature
open Syntax

module Cst :
 sig
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

val annotate' : Cst.obj -> CstAnn.obj

val elaborate' : Cst.obj -> string list -> exp option
