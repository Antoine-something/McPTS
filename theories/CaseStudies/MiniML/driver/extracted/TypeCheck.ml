open Decidability
open NbE
open Predicativity
open Signatures
open Specif
open Subtyping
open Syntax

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val lookup :
    coq_PtsSig -> coq_DecidableSig -> exp list -> int -> exp option **)

let rec lookup p dec_P _UU0393_ x =
  match _UU0393_ with
  | [] -> None
  | e :: l ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some (Coq_a_sub (e, Coq_a_weaken)))
       (fun n ->
       match lookup p dec_P l n with
       | Some a -> Some (Coq_a_sub (a, Coq_a_weaken))
       | None -> None)
       x)

(** val type_aty_functional :
    (coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> __ -> exp list
    -> exp -> __ -> exp -> __ -> bool) -> (coq_PtsSig -> coq_DecidableSig ->
    coq_PredicativeSig -> __ -> exp list -> __ -> exp -> __ -> bool) ->
    (coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> __ -> exp list
    -> __ -> exp -> __ -> nf option) -> coq_PtsSig -> coq_DecidableSig ->
    coq_PredicativeSig -> exp list -> exp -> bool **)

let type_aty_functional _ _ type_infer0 p dec_P pred_P _UU0393_ = function
| Coq_a_st _ -> true
| x ->
  (match type_infer0 p dec_P pred_P __ _UU0393_ __ x __ with
   | Some a0 -> (match a0 with
                 | Coq_nf_st _ -> true
                 | _ -> false)
   | None -> false)

(** val type_check :
    coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp list -> exp
    -> exp -> bool **)

let rec type_check p dec_P pred_P _UU0393_ a m =
  match type_infer p dec_P pred_P _UU0393_ m with
  | Some a0 -> subtyping_impl p dec_P _UU0393_ (nf_to_exp p a0) a
  | None -> false

(** val type_aty :
    coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp list -> exp
    -> bool **)

and type_aty p dec_P pred_P _UU0393_ a =
  type_aty_functional (fun x x0 x1 _ x2 x3 _ x4 _ ->
    type_check x x0 x1 x2 x3 x4) (fun x x0 x1 _ x2 _ x3 _ ->
    type_aty x x0 x1 x2 x3) (fun x x0 x1 _ x2 _ x3 _ ->
    type_infer x x0 x1 x2 x3) p dec_P pred_P _UU0393_ a

(** val type_infer :
    coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp list -> exp
    -> nf option **)

and type_infer p dec_P pred_P _UU0393_ = function
| Coq_a_st s ->
  (match dec_P.dec_ax_typ s with
   | Some a -> let Coq_existT (s', _) = a in Some (Coq_nf_st s')
   | None -> None)
| Coq_a_pi (s1, s2, s3, _, e, e0) ->
  if type_check p dec_P pred_P _UU0393_ (Coq_a_st s1) e
  then if type_check p dec_P pred_P (e :: _UU0393_) (Coq_a_st s2) e0
       then Some (Coq_nf_st s3)
       else None
  else None
| Coq_a_fn (s1, s2, s3, r, e, e0, e1) ->
  if type_check p dec_P pred_P _UU0393_ (Coq_a_st s1) e
  then if type_check p dec_P pred_P (e :: _UU0393_) (Coq_a_st s2) e0
       then if type_check p dec_P pred_P (e :: _UU0393_) e0 e1
            then Some (Coq_nf_pi (s1, s2, s3, r,
                   (nbe_impl p _UU0393_ e (Coq_a_st s1)),
                   (nbe_impl p (e :: _UU0393_) e0 (Coq_a_st s2))))
            else None
       else None
  else None
| Coq_a_app (e, e0) ->
  (match type_infer p dec_P pred_P _UU0393_ e with
   | Some a ->
     (match a with
      | Coq_nf_pi (_, _, _, _, n, n0) ->
        if type_check p dec_P pred_P _UU0393_ (nf_to_exp p n) e0
        then Some
               (nbe_ty_impl p _UU0393_ (Coq_a_sub ((nf_to_exp p n0),
                 (Coq_a_extend (Coq_a_id, e0)))))
        else None
      | _ -> None)
   | None -> None)
| Coq_a_var n ->
  (match lookup p dec_P _UU0393_ n with
   | Some a -> Some (nbe_ty_impl p _UU0393_ a)
   | None -> None)
| Coq_a_sub (_, _) -> None
| Coq_a_nat ->
  (match dec_P.dec_ru_nat with
   | Some a -> let Coq_existT (s, _) = a in Some (Coq_nf_st s)
   | None -> None)
| Coq_a_zero ->
  (match dec_P.dec_ru_nat with
   | Some _ -> Some Coq_nf_nat
   | None -> None)
| Coq_a_succ e ->
  (match dec_P.dec_ru_nat with
   | Some _ ->
     if type_check p dec_P pred_P _UU0393_ Coq_a_nat e
     then Some Coq_nf_nat
     else None
   | None -> None)
| Coq_a_natrec (e, e0, e1, e2) ->
  (match dec_P.dec_ru_nat with
   | Some _ ->
     if type_aty p dec_P pred_P (Coq_a_nat :: _UU0393_) e
     then if type_check p dec_P pred_P _UU0393_ (Coq_a_sub (e, (Coq_a_extend
               (Coq_a_id, Coq_a_zero)))) e0
          then if type_check p dec_P pred_P (e :: (Coq_a_nat :: _UU0393_))
                    (Coq_a_sub (e, (Coq_a_extend ((Coq_a_compose
                    (Coq_a_weaken, Coq_a_weaken)), (Coq_a_succ (Coq_a_var
                    (Stdlib.Int.succ 0))))))) e1
               then if type_check p dec_P pred_P _UU0393_ Coq_a_nat e2
                    then Some
                           (nbe_ty_impl p _UU0393_ (Coq_a_sub (e,
                             (Coq_a_extend (Coq_a_id, e2)))))
                    else None
               else None
          else None
     else None
   | None -> None)

(** val type_check_closed :
    coq_PtsSig -> coq_DecidableSig -> coq_PredicativeSig -> exp -> exp -> bool **)

let type_check_closed p dec_P pred_P a m =
  if type_aty p dec_P pred_P [] a
  then type_check p dec_P pred_P [] a m
  else false
