open Domain
open Signatures
open Syntax

(** val eval_env_lookup_impl_obligations_obligation_1 :
    coq_PtsSig -> int -> domain **)

let eval_env_lookup_impl_obligations_obligation_1 _ _ =
  assert false (* absurd case *)

(** val eval_env_lookup_impl : coq_PtsSig -> domain list -> int -> domain **)

let rec eval_env_lookup_impl p _UU03c1_ x =
  match _UU03c1_ with
  | [] -> eval_env_lookup_impl_obligations_obligation_1 p x
  | d :: l ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> d)
       (fun n -> eval_env_lookup_impl p l n)
       x)

(** val eval_exp_impl : coq_PtsSig -> exp -> domain list -> domain **)

let rec eval_exp_impl p m _UU03c1_ =
  match m with
  | Coq_a_st s -> Coq_d_sort s
  | Coq_a_pi (s1, s2, s3, r, e, e0) ->
    Coq_d_pi (s1, s2, s3, r, (eval_exp_impl p e _UU03c1_), _UU03c1_, e0)
  | Coq_a_fn (s1, s2, s3, r, _, _, e) -> Coq_d_fn (s1, s2, s3, r, _UU03c1_, e)
  | Coq_a_app (e, e0) ->
    eval_app_impl p (eval_exp_impl p e _UU03c1_) (eval_exp_impl p e0 _UU03c1_)
  | Coq_a_var n -> eval_env_lookup_impl p _UU03c1_ n
  | Coq_a_sub (e, s) -> eval_exp_impl p e (eval_sub_impl p s _UU03c1_)
  | Coq_a_nat -> Coq_d_nat
  | Coq_a_zero -> Coq_d_zero
  | Coq_a_succ e -> Coq_d_succ (eval_exp_impl p e _UU03c1_)
  | Coq_a_natrec (e, e0, e1, e2) ->
    eval_natrec_impl p e e0 e1 (eval_exp_impl p e2 _UU03c1_) _UU03c1_

(** val eval_app_impl : coq_PtsSig -> domain -> domain -> domain **)

and eval_app_impl p m n =
  match m with
  | Coq_d_fn (_, _, _, _, l, e) -> eval_exp_impl p e (extend_env p l n)
  | Coq_d_neut (d, d0) ->
    (match d with
     | Coq_d_pi (_, _, _, _, d1, l, e) ->
       Coq_d_neut ((eval_exp_impl p e (extend_env p l n)), (Coq_d_app (d0,
         (Coq_d_dom (d1, n)))))
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

(** val eval_natrec_impl :
    coq_PtsSig -> exp -> exp -> exp -> domain -> domain list -> domain **)

and eval_natrec_impl p a mZ mS m _UU03c1_ =
  match m with
  | Coq_d_zero -> eval_exp_impl p mZ _UU03c1_
  | Coq_d_succ d ->
    eval_exp_impl p mS
      (extend_env p (extend_env p _UU03c1_ d)
        (eval_natrec_impl p a mZ mS d _UU03c1_))
  | Coq_d_neut (d, d0) ->
    Coq_d_neut
      ((eval_exp_impl p a (extend_env p _UU03c1_ (Coq_d_neut (d, d0)))),
      (Coq_d_natrec (_UU03c1_, a, (eval_exp_impl p mZ _UU03c1_), mS, d0)))
  | _ -> assert false (* absurd case *)

(** val eval_sub_impl : coq_PtsSig -> sub -> domain list -> domain list **)

and eval_sub_impl p s _UU03c1_ =
  match s with
  | Coq_a_id -> _UU03c1_
  | Coq_a_weaken -> drop_env p _UU03c1_
  | Coq_a_compose (s0, s1) -> eval_sub_impl p s0 (eval_sub_impl p s1 _UU03c1_)
  | Coq_a_extend (s0, e) ->
    extend_env p (eval_sub_impl p s0 _UU03c1_) (eval_exp_impl p e _UU03c1_)
