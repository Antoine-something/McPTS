open Domain
open Signatures
open Syntax

val eval_env_lookup_impl_obligations_obligation_1 :
  coq_PtsSig -> int -> domain

val eval_env_lookup_impl : coq_PtsSig -> domain list -> int -> domain

val eval_exp_impl : coq_PtsSig -> exp -> domain list -> domain

val eval_app_impl : coq_PtsSig -> domain -> domain -> domain

val eval_natrec_impl :
  coq_PtsSig -> exp -> exp -> exp -> domain -> domain list -> domain

val eval_sub_impl : coq_PtsSig -> sub -> domain list -> domain list
