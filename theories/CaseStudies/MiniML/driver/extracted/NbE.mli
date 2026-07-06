open Datatypes
open Domain
open Evaluation
open Readback
open Signatures
open Syntax

val initial_env_impl : coq_PtsSig -> exp list -> domain list

val nbe_impl : coq_PtsSig -> exp list -> exp -> exp -> nf

val nbe_ty_impl : coq_PtsSig -> exp list -> exp -> nf
