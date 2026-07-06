open Domain
open Evaluation
open Nat
open Signatures
open Syntax

(** val read_nf_impl : coq_PtsSig -> int -> domain_nf -> nf **)

let rec read_nf_impl p i = function
| Coq_d_dom (d0, d1) ->
  (match d0 with
   | Coq_d_sort _ -> read_typ_impl p i d1
   | Coq_d_pi (s1, s2, s3, r, d2, l, e) ->
     let b =
       eval_exp_impl p e (extend_env p l (Coq_d_neut (d2, (Coq_d_var i))))
     in
     Coq_nf_fn (s1, s2, s3, r, (read_typ_impl p i d2),
     (read_typ_impl p (Stdlib.Int.succ i) b),
     (read_nf_impl p (Stdlib.Int.succ i) (Coq_d_dom (b,
       (eval_app_impl p d1 (Coq_d_neut (d2, (Coq_d_var i))))))))
   | Coq_d_nat ->
     (match d1 with
      | Coq_d_zero -> Coq_nf_zero
      | Coq_d_succ d2 ->
        Coq_nf_succ (read_nf_impl p i (Coq_d_dom (Coq_d_nat, d2)))
      | Coq_d_neut (_, d2) -> Coq_nf_neut (read_ne_impl p i d2)
      | _ -> assert false (* absurd case *))
   | Coq_d_neut (_, _) ->
     (match d1 with
      | Coq_d_neut (_, d2) -> Coq_nf_neut (read_ne_impl p i d2)
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val read_ne_impl : coq_PtsSig -> int -> domain_ne -> ne **)

and read_ne_impl p i = function
| Coq_d_var x -> Coq_ne_var (sub (sub i x) (Stdlib.Int.succ 0))
| Coq_d_app (d0, d1) ->
  Coq_ne_app ((read_ne_impl p i d0), (read_nf_impl p i d1))
| Coq_d_natrec (l, e, d0, e0, d1) ->
  let b =
    eval_exp_impl p e (extend_env p l (Coq_d_neut (Coq_d_nat, (Coq_d_var i))))
  in
  Coq_ne_natrec ((read_typ_impl p (Stdlib.Int.succ i) b),
  (read_nf_impl p i (Coq_d_dom
    ((eval_exp_impl p e (extend_env p l Coq_d_zero)), d0))),
  (read_nf_impl p (Stdlib.Int.succ (Stdlib.Int.succ i)) (Coq_d_dom
    ((eval_exp_impl p e
       (extend_env p l (Coq_d_succ (Coq_d_neut (Coq_d_nat, (Coq_d_var i)))))),
    (eval_exp_impl p e0
      (extend_env p (extend_env p l (Coq_d_neut (Coq_d_nat, (Coq_d_var i))))
        (Coq_d_neut (b, (Coq_d_var (Stdlib.Int.succ i))))))))),
  (read_ne_impl p i d1))

(** val read_typ_impl : coq_PtsSig -> int -> domain -> nf **)

and read_typ_impl p i = function
| Coq_d_sort s -> Coq_nf_st s
| Coq_d_pi (s1, s2, s3, r, d0, l, e) ->
  Coq_nf_pi (s1, s2, s3, r, (read_typ_impl p i d0),
    (read_typ_impl p (Stdlib.Int.succ i)
      (eval_exp_impl p e (extend_env p l (Coq_d_neut (d0, (Coq_d_var i)))))))
| Coq_d_nat -> Coq_nf_nat
| Coq_d_neut (_, d0) -> Coq_nf_neut (read_ne_impl p i d0)
| _ -> assert false (* absurd case *)
