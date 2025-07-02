From Coq Require Import Relation_Definitions RelationClasses.

(* Pure type system signatures consist of sorts, axioms, and rules *)
Record PtsSig : Type :=
  mkPtsSig{
      St : Set;
      Ax : St -> St -> Set;
      Ru : St -> St -> St -> Set;
    }.

(* A signature is predicative if there is a partial order that respects its relations *)
Record PredicativeSig (S : PtsSig) : Prop :=
  mkPredicativeSig {
      test : exists (P : relation (St S)),
        order (St S) P
        /\ (forall s1 s2 : St S, Ax S s1 s2 -> P s1 s2)
        /\ (forall s1 s2 s3 : St S, Ru S s1 s2 s3 -> (P s1 s3) /\ (P s2 s3))
    }.
