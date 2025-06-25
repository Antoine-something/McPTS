From Coq Require Import Relation_Definitions RelationClasses.
From McPTS.Core.PTSSignature Require Import Signature.


Record PredicativeSig (S : PtsSig) : Prop :=
  mkPredicativeSig {
      test : exists (P : relation (St S)),
        order (St S) P
        /\ (forall s1 s2 : St S, Ax S s1 s2 -> P s1 s2)
        /\ (forall s1 s2 s3 : St S, Ru S s1 s2 s3 -> (P s1 s3) /\ (P s2 s3))
    }.
