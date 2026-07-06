open Signatures
open Specif

type __ = Obj.t

type coq_DecidableSig = { dec_st : (coq_St -> coq_St -> bool);
                          dec_ru_pi : (coq_St -> coq_St -> coq_St ->
                                      coq_Ru_pi -> coq_Ru_pi -> bool);
                          dec_st_sub : (coq_St -> coq_St -> bool);
                          dec_ru_nat : (coq_St, coq_Ru_nat) sigT option;
                          dec_ax_typ : (coq_St -> (coq_St, __) sigT option) }

val strong_dec_pi :
  coq_PtsSig -> coq_DecidableSig -> coq_St -> coq_St -> coq_St -> coq_St ->
  coq_St -> coq_St -> coq_Ru_pi -> coq_Ru_pi -> bool
