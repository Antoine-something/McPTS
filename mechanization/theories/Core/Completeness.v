From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Export FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

Theorem completeness {P} {pred_P : PredicativeSig P} : forall {Γ : ctx P} {M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof with mautosolve.
  intros * [env_relΓ]%(@completeness_fundamental_exp_eq P pred_P).
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [p] by (eauto using per_ctx_then_per_env_initial_env).
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ P).
  functional_eval_rewrite_clear.
  destruct_by_head (@rel_exp P).
  unshelve epose proof (per_elem_then_per_top _ _ (length Γ)) as [? []]; shelve_unifiable; mauto.
Qed.

Lemma completeness_ty : forall {Γ i A A'},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    exists W, nbe_ty Γ A W /\ nbe_ty Γ A' W.
Proof.
  intros * [? [?%nbe_type_to_nbe_ty ?%nbe_type_to_nbe_ty]]%completeness.
  mauto 3.
Qed.
