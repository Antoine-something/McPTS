From Coq Require Import Morphisms_Relations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import LogicalRelation SortCases.
Import Domain_Notations.

Proposition valid_gctx_empty {P} {pred_P : PredicativeSig P} :
  {{ ⟪ pred_P ⟫ ▶ ⋅ }}.
Proof. mauto 2. Qed.
  
