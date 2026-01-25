From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma glu_rel_ctx_empty {P} (pred_P : PredicativeSig P) : {{ ⟪ pred_P ⟫ ⊩ ⋅ }}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_empty : mcpts.

Lemma glu_rel_ctx_extend {P} (pred_P : PredicativeSig P) : forall {Γ A s s'},
    {{ ⟪ pred_P ⟫ ⊩ Γ }} ->
    {{ ⟪ pred_P ⟫ Γ ⊩ A : Sort@s > s' }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A:Sort@s }}.
Proof.
  intros * [Sb].
  intros HA.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 3.
  inversion_clear HA.
  destruct_conjs.
  eexists.
  econstructor; mauto 3; try reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend : mcpts.
