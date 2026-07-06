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

(** val nf_to_exp : coq_PtsSig -> nf -> exp **)

let rec nf_to_exp p = function
| Coq_nf_st s -> Coq_a_st s
| Coq_nf_pi (s1, s2, s3, r, a, b) ->
  Coq_a_pi (s1, s2, s3, r, (nf_to_exp p a), (nf_to_exp p b))
| Coq_nf_fn (s1, s2, s3, r, a, b, m0) ->
  Coq_a_fn (s1, s2, s3, r, (nf_to_exp p a), (nf_to_exp p b), (nf_to_exp p m0))
| Coq_nf_nat -> Coq_a_nat
| Coq_nf_zero -> Coq_a_zero
| Coq_nf_succ m0 -> Coq_a_succ (nf_to_exp p m0)
| Coq_nf_neut m0 -> ne_to_exp p m0

(** val ne_to_exp : coq_PtsSig -> ne -> exp **)

and ne_to_exp p = function
| Coq_ne_app (m0, n) -> Coq_a_app ((ne_to_exp p m0), (nf_to_exp p n))
| Coq_ne_var x -> Coq_a_var x
| Coq_ne_natrec (a, mZ, mS, m0) ->
  Coq_a_natrec ((nf_to_exp p a), (nf_to_exp p mZ), (nf_to_exp p mS),
    (ne_to_exp p m0))

(** val nf_eq_dec : coq_PtsSig -> coq_DecidableSig -> nf -> nf -> bool **)

let rec nf_eq_dec p dec_P m m' =
  match m with
  | Coq_nf_st s ->
    (match m' with
     | Coq_nf_st s0 -> dec_P.dec_st s s0
     | _ -> false)
  | Coq_nf_pi (s1, s2, s3, r, n, n0) ->
    (match m' with
     | Coq_nf_pi (s4, s5, s6, r0, n1, n2) ->
       if dec_P.dec_st s1 s4
       then if dec_P.dec_st s2 s5
            then if dec_P.dec_st s3 s6
                 then if dec_P.dec_ru_pi s4 s5 s6 r r0
                      then if nf_eq_dec p dec_P n n1
                           then nf_eq_dec p dec_P n0 n2
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | Coq_nf_fn (s1, s2, s3, r, n, n0, n1) ->
    (match m' with
     | Coq_nf_fn (s4, s5, s6, r0, n2, n3, n4) ->
       if dec_P.dec_st s1 s4
       then if dec_P.dec_st s2 s5
            then if dec_P.dec_st s3 s6
                 then if dec_P.dec_ru_pi s4 s5 s6 r r0
                      then if nf_eq_dec p dec_P n n2
                           then if nf_eq_dec p dec_P n0 n3
                                then nf_eq_dec p dec_P n1 n4
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | Coq_nf_nat -> (match m' with
                   | Coq_nf_nat -> true
                   | _ -> false)
  | Coq_nf_zero -> (match m' with
                    | Coq_nf_zero -> true
                    | _ -> false)
  | Coq_nf_succ n ->
    (match m' with
     | Coq_nf_succ n0 -> nf_eq_dec p dec_P n n0
     | _ -> false)
  | Coq_nf_neut n ->
    (match m' with
     | Coq_nf_neut n0 -> ne_eq_dec p dec_P n n0
     | _ -> false)

(** val ne_eq_dec : coq_PtsSig -> coq_DecidableSig -> ne -> ne -> bool **)

and ne_eq_dec p dec_P m m' =
  let rec f n x =
    match n with
    | Coq_ne_app (n0, n1) ->
      (match x with
       | Coq_ne_app (n2, n3) ->
         if f n0 n2 then nf_eq_dec p dec_P n1 n3 else false
       | _ -> false)
    | Coq_ne_var n0 -> (match x with
                        | Coq_ne_var n1 -> (=) n0 n1
                        | _ -> false)
    | Coq_ne_natrec (n0, n1, n2, n3) ->
      (match x with
       | Coq_ne_natrec (n4, n5, n6, n7) ->
         if nf_eq_dec p dec_P n0 n4
         then if nf_eq_dec p dec_P n1 n5
              then if nf_eq_dec p dec_P n2 n6 then f n3 n7 else false
              else false
         else false
       | _ -> false)
  in f m m'
