open Decidability
open NbE
open Signatures
open Syntax

(** val subtyping_nf_impl :
    coq_PtsSig -> coq_DecidableSig -> nf -> nf -> bool **)

let rec subtyping_nf_impl p dec_P a b =
  match a with
  | Coq_nf_st s ->
    (match b with
     | Coq_nf_st s0 -> dec_P.dec_st_sub s s0
     | x -> nf_eq_dec p dec_P (Coq_nf_st s) x)
  | Coq_nf_pi (s1, s2, s3, r, n, n0) ->
    (match b with
     | Coq_nf_pi (s4, s5, s6, r0, n1, n2) ->
       if dec_P.dec_st s1 s4
       then if dec_P.dec_st s2 s5
            then if dec_P.dec_st s3 s6
                 then if strong_dec_pi p dec_P s1 s4 s2 s5 s3 s6 r r0
                      then if nf_eq_dec p dec_P n n1
                           then subtyping_nf_impl p dec_P n0 n2
                           else false
                      else false
                 else false
            else false
       else false
     | x -> nf_eq_dec p dec_P (Coq_nf_pi (s1, s2, s3, r, n, n0)) x)
  | x -> nf_eq_dec p dec_P x b

(** val subtyping_impl :
    coq_PtsSig -> coq_DecidableSig -> exp list -> exp -> exp -> bool **)

let subtyping_impl p dec_P _UU0393_ a b =
  subtyping_nf_impl p dec_P (nbe_ty_impl p _UU0393_ a)
    (nbe_ty_impl p _UU0393_ b)
