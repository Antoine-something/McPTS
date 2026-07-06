open Signatures
open Specif

type __ = Obj.t

type coq_DecidableSig = { dec_st : (coq_St -> coq_St -> bool);
                          dec_ru_pi : (coq_St -> coq_St -> coq_St ->
                                      coq_Ru_pi -> coq_Ru_pi -> bool);
                          dec_st_sub : (coq_St -> coq_St -> bool);
                          dec_ru_nat : (coq_St, coq_Ru_nat) sigT option;
                          dec_ax_typ : (coq_St -> (coq_St, __) sigT option) }

(** val strong_dec_pi :
    coq_PtsSig -> coq_DecidableSig -> coq_St -> coq_St -> coq_St -> coq_St ->
    coq_St -> coq_St -> coq_Ru_pi -> coq_Ru_pi -> bool **)

let strong_dec_pi _ dec_P s1 s1' s2 s2' s3 s3' r r' =
  if dec_P.dec_st s1 s1'
  then if dec_P.dec_st s2 s2'
       then if dec_P.dec_st s3 s3'
            then dec_P.dec_ru_pi s1' s2' s3' r r'
            else false
       else false
  else false
