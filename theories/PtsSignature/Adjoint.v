From Coq Require Import Relation_Definitions RelationClasses.

From McPTS.PtsSignature Require Import Signatures.
From McPTS.Core Require Import Base.

Record AdjSig : Type :=
  mkAdjPts {
      Modes : Set;
      Mode_preorder : relation Modes;
      Preorder_refl : forall m, Mode_preorder m m;
      Preorder_trans : forall m1 m2 m3, Mode_preorder m1 m2 -> Mode_preorder m2 m3 -> Mode_preorder m1 m3;
      
      Mode_to_PtsSig : Modes -> PtsSig;
      Ru_upshift : forall m1 m2, Mode_preorder m1 m2 -> Mode_to_PtsSig m1 -> Mode_to_PtsSig m2 -> Set;
    }.

Coercion Mode_to_PtsSig : Modes >-> PtsSig.

Notation "m1 ⪯ m2 ∈ P" := (Mode_preorder P m1 m2) (in custom judg at level 80, m1 constr, m2 constr, P constr) : type_scope.
