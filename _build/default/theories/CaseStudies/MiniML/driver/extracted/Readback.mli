open Domain
open Evaluation
open Nat
open Signatures
open Syntax

val read_nf_impl : coq_PtsSig -> int -> domain_nf -> nf

val read_ne_impl : coq_PtsSig -> int -> domain_ne -> ne

val read_typ_impl : coq_PtsSig -> int -> domain -> nf
