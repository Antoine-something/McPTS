From McPTS.PtsSignature Require Import Signatures.

Record FunctionalSig (P : PtsSig) : Prop :=
  mkFunctionalSig {
      Func_ax_typ : forall s1 s2 s2', Ax_typ P s1 s2 -> Ax_typ P s1 s2' -> s2 = s2';
      Func_ru_pi : forall s1 s2 s3 s3', Ru_pi P s1 s2 s3 -> Ru_pi P s1 s2 s3' -> s3 = s3';
      Func_ru_nat : forall s s', Ru_nat P s -> Ru_nat P s' -> s = s';
    }.
