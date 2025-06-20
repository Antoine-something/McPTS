From Coq Require Import Relation_Definitions RelationClasses.
From McPTS.Core.PTSSignature Require Import Signature.

Module Type PredicativeSig (S : PtsSig).
  Import S.

  Axiom predicative : exists (P : relation St),
      order St P
      /\ (forall (s1 : St) (s2 : St), Ax s1 s2 -> P s1 s2)
      /\ (forall (s1 s2 s3 : St), Ru s1 s2 s3 -> (P s1 s3) /\ (P s2 s3)).
End PredicativeSig.
