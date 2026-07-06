open Signatures
open Syntax

type domain =
| Coq_d_sort of coq_St
| Coq_d_pi of coq_St * coq_St * coq_St * coq_Ru_pi * domain * domain list
   * exp
| Coq_d_fn of coq_St * coq_St * coq_St * coq_Ru_pi * domain list * exp
| Coq_d_nat
| Coq_d_zero
| Coq_d_succ of domain
| Coq_d_neut of domain * domain_ne
and domain_ne =
| Coq_d_var of int
| Coq_d_app of domain_ne * domain_nf
| Coq_d_natrec of domain list * exp * domain * exp * domain_ne
and domain_nf =
| Coq_d_dom of domain * domain

(** val empty_env : coq_PtsSig -> domain list **)

let empty_env _ =
  []

(** val extend_env : coq_PtsSig -> domain list -> domain -> domain list **)

let extend_env _ _UU03c1_ d =
  d :: _UU03c1_

(** val drop_env : coq_PtsSig -> domain list -> domain list **)

let drop_env _ = function
| [] -> []
| _ :: _UU03c1_' -> _UU03c1_'
