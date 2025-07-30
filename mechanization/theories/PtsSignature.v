From Coq Require Import Relation_Definitions RelationClasses.

From Equations Require Import Equations.

Record PtsSig : Type :=
  mkPtsSig{
      St : Set;
      Ax : St -> St -> Set;
      Ru : St -> St -> St -> Set;
    }.

(* It would be nicer to have this in Prop, but Rocq complains *)
Record PredicativeSig (P : PtsSig) : Type :=
  mkPredicativeSig {
      pred_rel : relation (St P);
      ord_rel : order (St P) pred_rel;
      wf_rel : Classes.WellFounded pred_rel;
      ord_ax : forall s1 s2 : St P, Ax P s1 s2 -> pred_rel s1 s2 /\ s1 <> s2;
      ord_ru : forall s1 s2 s3 : St P, Ru P s1 s2 s3 -> (pred_rel s1 s3) /\ (pred_rel s1 s2);
    }.
