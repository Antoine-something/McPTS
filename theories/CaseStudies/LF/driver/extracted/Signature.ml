open Decidability
open Equality
open Predicativity
open Signatures
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_LF_St =
| Coq_s_typ
| Coq_s_knd

type coq_LF_Ru_pi =
| Coq_f_simple
| Coq_f_dep

(** val coq_LF_Sig : coq_PtsSig **)

let coq_LF_Sig =
  Coq_mkPtsSig

(** val coq_P : coq_PtsSig **)

let coq_P =
  coq_LF_Sig

(** val coq_LF_Predicative : coq_PredicativeSig **)

let coq_LF_Predicative =
  Coq_mkPredicativeSig

(** val coq_LF_dec_st : coq_St -> coq_St -> bool **)

let coq_LF_dec_st s s' =
  match Obj.magic s with
  | Coq_s_typ ->
    (match Obj.magic s' with
     | Coq_s_typ -> true
     | Coq_s_knd -> false)
  | Coq_s_knd ->
    (match Obj.magic s' with
     | Coq_s_typ -> false
     | Coq_s_knd -> true)

(** val coq_LF_dec_ru_pi :
    coq_St -> coq_St -> coq_St -> coq_Ru_pi -> coq_Ru_pi -> bool **)

let coq_LF_dec_ru_pi _ _ _ r r' =
  match Obj.magic r with
  | Coq_f_simple ->
    (match Obj.magic r' with
     | Coq_f_simple ->
       simplification_heq (Obj.magic Coq_f_simple) r' (fun _ ->
         solution_right (Obj.magic Coq_f_simple) true r')
     | Coq_f_dep -> assert false (* absurd case *))
  | Coq_f_dep ->
    (match Obj.magic r' with
     | Coq_f_simple -> assert false (* absurd case *)
     | Coq_f_dep ->
       simplification_heq (Obj.magic Coq_f_dep) r' (fun _ ->
         solution_right (Obj.magic Coq_f_dep) true r'))

(** val coq_LF_dec_st_sub : coq_St -> coq_St -> bool **)

let coq_LF_dec_st_sub s s' =
  match Obj.magic s with
  | Coq_s_typ ->
    (match Obj.magic s' with
     | Coq_s_typ -> true
     | Coq_s_knd -> false)
  | Coq_s_knd ->
    (match Obj.magic s' with
     | Coq_s_typ -> false
     | Coq_s_knd -> true)

(** val coq_LF_dec_ru_nat : (coq_St, coq_Ru_nat) sigT option **)

let coq_LF_dec_ru_nat =
  None

(** val coq_LF_dec_ax_typ : coq_St -> (coq_St, __) sigT option **)

let coq_LF_dec_ax_typ s =
  match Obj.magic s with
  | Coq_s_typ -> Some (Coq_existT ((Obj.magic Coq_s_knd), __))
  | Coq_s_knd -> None

(** val coq_LF_Decidable : coq_DecidableSig **)

let coq_LF_Decidable =
  { dec_st = coq_LF_dec_st; dec_ru_pi = coq_LF_dec_ru_pi; dec_st_sub =
    coq_LF_dec_st_sub; dec_ru_nat = coq_LF_dec_ru_nat; dec_ax_typ =
    coq_LF_dec_ax_typ }
