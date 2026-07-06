open Decidability
open Equality
open Predicativity
open Signatures
open Specif

type __ = Obj.t

type coq_MiniML_St =
| Coq_s_typ

val coq_MiniML_Sig : coq_PtsSig

val coq_P : coq_PtsSig

val coq_MiniML_Predicative : coq_PredicativeSig

val coq_MiniML_dec_st : coq_St -> coq_St -> bool

val coq_MiniML_dec_ru_pi : coq_St -> coq_St -> coq_St -> bool

val coq_MiniML_dec_st_sub : coq_St -> coq_St -> bool

val coq_MiniML_dec_ru_nat : (coq_St, coq_Ru_nat) sigT option

val coq_MiniML_dec_ax_typ : coq_St -> (coq_St, __) sigT option

val coq_MiniML_Decidable : coq_DecidableSig
