open Decidability
open NbE
open Signatures
open Syntax

val subtyping_nf_impl : coq_PtsSig -> coq_DecidableSig -> nf -> nf -> bool

val subtyping_impl :
  coq_PtsSig -> coq_DecidableSig -> exp list -> exp -> exp -> bool
