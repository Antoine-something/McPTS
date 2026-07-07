open Decidability
open Equality
open Predicativity
open Signatures
open Specif

type __ = Obj.t

type coq_LF_St =
| Coq_s_typ
| Coq_s_knd

type coq_LF_Ru_pi =
| Coq_f_simple
| Coq_f_dep

val coq_LF_Sig : coq_PtsSig

val coq_P : coq_PtsSig

val coq_LF_Predicative : coq_PredicativeSig

val coq_LF_dec_st : coq_St -> coq_St -> bool

val coq_LF_dec_ru_pi :
  coq_St -> coq_St -> coq_St -> coq_Ru_pi -> coq_Ru_pi -> bool

val coq_LF_dec_st_sub : coq_St -> coq_St -> bool

val coq_LF_dec_ru_nat : (coq_St, coq_Ru_nat) sigT option

val coq_LF_dec_ax_typ : coq_St -> (coq_St, __) sigT option

val coq_LF_Decidable : coq_DecidableSig
