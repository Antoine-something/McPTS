open Decidability
open Signatures

type exp =
| Coq_a_st of coq_St
| Coq_a_pi of coq_St * coq_St * coq_St * coq_Ru_pi * exp * exp
| Coq_a_fn of coq_St * coq_St * coq_St * coq_Ru_pi * exp * exp * exp
| Coq_a_app of exp * exp
| Coq_a_var of int
| Coq_a_sub of exp * sub
| Coq_a_nat
| Coq_a_zero
| Coq_a_succ of exp
| Coq_a_natrec of exp * exp * exp * exp
and sub =
| Coq_a_id
| Coq_a_weaken
| Coq_a_compose of sub * sub
| Coq_a_extend of sub * exp

type nf =
| Coq_nf_st of coq_St
| Coq_nf_pi of coq_St * coq_St * coq_St * coq_Ru_pi * nf * nf
| Coq_nf_fn of coq_St * coq_St * coq_St * coq_Ru_pi * nf * nf * nf
| Coq_nf_nat
| Coq_nf_zero
| Coq_nf_succ of nf
| Coq_nf_neut of ne
and ne =
| Coq_ne_app of ne * nf
| Coq_ne_var of int
| Coq_ne_natrec of nf * nf * nf * ne

val nf_to_exp : coq_PtsSig -> nf -> exp

val ne_to_exp : coq_PtsSig -> ne -> exp

val nf_eq_dec : coq_PtsSig -> coq_DecidableSig -> nf -> nf -> bool

val ne_eq_dec : coq_PtsSig -> coq_DecidableSig -> ne -> ne -> bool
