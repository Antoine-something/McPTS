open Datatypes
open Domain
open Evaluation
open Readback
open Signatures
open Syntax

(** val initial_env_impl : coq_PtsSig -> exp list -> domain list **)

let rec initial_env_impl p = function
| [] -> empty_env p
| e :: l ->
  let _UU03c1_ = initial_env_impl p l in
  extend_env p _UU03c1_ (Coq_d_neut ((eval_exp_impl p e _UU03c1_), (Coq_d_var
    (length l))))

(** val nbe_impl : coq_PtsSig -> exp list -> exp -> exp -> nf **)

let rec nbe_impl p _UU0393_ m a =
  let _UU03c1_ = initial_env_impl p _UU0393_ in
  read_nf_impl p (length _UU0393_) (Coq_d_dom ((eval_exp_impl p a _UU03c1_),
    (eval_exp_impl p m _UU03c1_)))

(** val nbe_ty_impl : coq_PtsSig -> exp list -> exp -> nf **)

let rec nbe_ty_impl p _UU0393_ a =
  read_typ_impl p (length _UU0393_)
    (eval_exp_impl p a (initial_env_impl p _UU0393_))
