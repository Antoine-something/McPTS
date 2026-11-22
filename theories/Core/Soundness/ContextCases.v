From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Soundness Require Import LogicalRelation.
From McPTS.Core.Semantic Require Import Realizability.
Import Domain_Notations.

Lemma glu_rel_ctx_empty {P} (pred_P : PredicativeSig P) : {{ ⟪ pred_P ⟫ ⊩ ⋅ @ nil }}.
Proof.
  do 2 econstructor; reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_empty : mcpts.

Lemma glu_rel_ctx_extend {P} (pred_P : PredicativeSig P) : forall {anns Γ A so},
    {{ ⟪ pred_P ⟫ ⊩ Γ @ anns }} ->
    {{ ⟪ pred_P ⟫ Γ @ anns ⊩ A @ so }} ->
    {{ ⟪ pred_P ⟫ ⊩ Γ, A @ so::anns}}.
Proof.
  intros * [SbΓ] HA.
  assert {{ Γ ⊢ A }} by mauto 3.
  destruct HA as [SbΓ' []].
  handle_functional_glu_ctx_env P.
  eexists;
    econstructor; mauto 3; try reflexivity.
Qed.

#[export]
Hint Resolve glu_rel_ctx_extend : mcpts.
