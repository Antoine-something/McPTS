From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Domain_Notations.

Lemma glu_rel_ctx_empty {P} (pred_P : PredicativeSig P) : {{ ⟪ pred_P ⟫ ⊩ ⋅ : nil }}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_empty : mcpts.

Lemma glu_rel_ctx_extend {P} (pred_P : PredicativeSig P) : forall {sts Γ A s},
    {{ ⟪ pred_P ⟫ ⊩ Γ : sts }} ->
    {{ ⟪ pred_P ⟫ Γ : sts ⊩ A : Sort@s }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A : (s :: sts) }}.
Proof.
  intros * [Sb] HA.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 3.
  invert_glu_rel_exp HA.
  eexists.
  econstructor; mauto 3; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend : mcpts.
