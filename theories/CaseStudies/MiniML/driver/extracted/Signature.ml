open Decidability
open Equality
open Predicativity
open Signatures
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_MiniML_St =
| Coq_s_typ

(** val coq_MiniML_Sig : coq_PtsSig **)

let coq_MiniML_Sig =
  Coq_mkPtsSig

(** val coq_P : coq_PtsSig **)

let coq_P =
  coq_MiniML_Sig

(** val coq_MiniML_Predicative : coq_PredicativeSig **)

let coq_MiniML_Predicative =
  Coq_mkPredicativeSig

(** val coq_MiniML_dec_st : coq_St -> coq_St -> bool **)

let coq_MiniML_dec_st _ _ =
  true

(** val coq_MiniML_dec_ru_pi : coq_St -> coq_St -> coq_St -> bool **)

let coq_MiniML_dec_ru_pi _ _ _ =
  simplification_heq __ __ (fun _ -> solution_right __ true __)

(** val coq_MiniML_dec_st_sub : coq_St -> coq_St -> bool **)

let coq_MiniML_dec_st_sub _ _ =
  true

(** val coq_MiniML_dec_ru_nat : (coq_St, coq_Ru_nat) sigT option **)

let coq_MiniML_dec_ru_nat =
  Some (Coq_existT ((Obj.magic Coq_s_typ), (Obj.magic __)))

(** val coq_MiniML_dec_ax_typ : coq_St -> (coq_St, __) sigT option **)

let coq_MiniML_dec_ax_typ _ =
  None

(** val coq_MiniML_Decidable : coq_DecidableSig **)

let coq_MiniML_Decidable =
  { dec_st = coq_MiniML_dec_st; dec_ru_pi =
    (Obj.magic (fun x x0 x1 _ _ -> coq_MiniML_dec_ru_pi x x0 x1));
    dec_st_sub = coq_MiniML_dec_st_sub; dec_ru_nat = coq_MiniML_dec_ru_nat;
    dec_ax_typ = coq_MiniML_dec_ax_typ }
