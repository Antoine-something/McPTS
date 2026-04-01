From Coq Require Import RelationClasses.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core Require Export Completeness.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Domain_Notations.

Lemma exp_eq_typ_implies_eq_level {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s1 s2 s3},
    {{ Γ ⊢ Sort@s1 ≈ Sort@s2 : Sort@s3 }} ->
    s1 = s2.
Proof with mautosolve.
  intros * H.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u Sort@s1 ≈ Sort@s2 : Sort@s3 }} as [env_relΓ] by eauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) as [p [? [? []]]] by eauto using per_ctx_then_per_env_initial_env.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_body.
  destruct_by_head (@rel_exp P).
  invert_rel_typ_body.
  destruct_conjs.
  assert (per_typ_elem pred_P (per_sort pred_P s3) d{{{ Sort@s3 }}} d{{{ Sort@s3 }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  unfold per_sort in *.
  destruct_conjs.
  invert_per_sort_elems.
  reflexivity.
Qed.

#[export]
Hint Resolve exp_eq_typ_implies_eq_level : mcpts.

Inductive is_typ_constr {P} : typ P -> Prop :=
| typ_is_typ_constr : forall s, is_typ_constr {{{ Sort@s }}}
| nat_is_typ_constr : is_typ_constr {{{ ℕ }}}
| pi_is_typ_constr : forall s1 s2 s3 (r : Ru P s1 s2 s3) A B, is_typ_constr {{{ Π r A B }}}
| var_is_typ_constr : forall x, is_typ_constr {{{ #x }}}
.

#[export]
Hint Constructors is_typ_constr : mcpts.

Theorem is_typ_constr_and_exp_eq_var_implies_eq_var {P} (pred_P : PredicativeSig P) : forall (Γ : ctx P) A x s,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ #x : Sort@s }} ->
    A = {{{ #x }}}.
Proof.
  intros * Histyp ?.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ #x : Sort@s }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  rename H2 into ρ, H3 into ρ'.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted P).
  invert_rel_typ_body.
  destruct_by_head (@rel_exp P).
  gen_presups.
  assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  unfold per_sort in *.
  destruct_conjs.
  
  assert (exists A' s', {{ #x : A'@s'  ∈ Γ }} /\ {{ Γ ⊢ A' ≈ Sort@s }}) as [A' [s' [? _]]] by mauto 2.
  assert (exists a, {{ #| ρ[x] |↘ ⇑! a (length Γ - x - 1) }}) as [? Heq] by mauto 2.
  destruct Histyp;
    invert_rel_typ_body.
  (* unfold per_bot in H5. *)
  assert (exists A'' s'', {{ #x1 : A''@s''  ∈ Γ }} /\ {{ Γ ⊢ A'' ≈ Sort@s }}) as [A'' [s'' [? _]]] by mauto 2.
  assert (exists a', {{ #| ρ[x1] |↘ ⇑! a' (length Γ - x1 - 1) }}) as [? Heq'] by mauto 2.
  assert (x < length Γ) by mauto 2.
  assert (x1 < length Γ) by mauto 2.  
  f_equal.
  enough (length Γ - x - 1 = length Γ - x1 - 1) by lia.
  match_by_head1 (@per_bot P) ltac:(fun H => destruct (H (length Γ)) as [? []]).  
  match_by_head (@read_ne P) ltac:(fun H => directed dependent destruction H).
  simplify_evals.
  inversion H12.
  lia.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_var_implies_eq_var : mcpts.

Theorem is_typ_constr_and_exp_eq_typ_implies_eq_typ {P} (pred_P : PredicativeSig P) : forall (Γ : ctx P) A s s',
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ Sort@s : Sort@s' }} ->
    A = {{{ Sort@s }}}.
Proof.
  intros * Histyp ?.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ Sort@s : Sort@s' }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head (@rel_typ_unsorted).
  invert_rel_typ_body.
  destruct_by_head @rel_exp.
  assert (per_typ_elem pred_P (per_sort pred_P s') d{{{ Sort@s' }}} d{{{ Sort@s' }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  unfold per_sort in *.
  destruct_conjs.
  destruct Histyp;
    invert_rel_typ_body;
    destruct_conjs;
    invert_per_sort_elems.
  - reflexivity.
  - replace {{{ #x }}} with {{{ Sort@s }}} by mauto 3 using is_typ_constr_and_exp_eq_var_implies_eq_var.
    reflexivity.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_typ_implies_eq_typ : mcpts.

Theorem is_typ_constr_and_exp_eq_nat_implies_eq_nat {P} (pred_P : PredicativeSig P) : forall (Γ : ctx P) A s,
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ ℕ : Sort@s }} ->
    A = {{{ ℕ }}}.
Proof.
  intros * Histyp ?.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ ℕ : Sort@s }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head @rel_typ_unsorted.
  invert_rel_typ_body.
  destruct_by_head @rel_exp.
  assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  unfold per_sort in *.
  destruct_conjs.
  destruct Histyp;
    invert_rel_typ_body;
    destruct_conjs;
    invert_per_sort_elems.
  - reflexivity.
  - replace {{{ #x }}} with (@a_nat P) by mauto 3 using is_typ_constr_and_exp_eq_var_implies_eq_var.
    reflexivity.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_nat_implies_eq_nat : mcpts.

Theorem is_typ_constr_and_exp_eq_pi_implies_eq_pi {P} (pred_P : PredicativeSig P) : forall Γ A B C s1 s2 s3 (r : Ru P s1 s2 s3),
    is_typ_constr A ->
    {{ Γ ⊢ A ≈ Π r B C : Sort@s3 }} ->
    exists B' C', A = {{{ Π r B' C' }}}.
Proof.
  intros * Histyp ?.
  assert {{ ⟪ pred_P ⟫ Γ ⊨u A ≈ Π r B C : Sort@s3 }} as [env_relΓ] by mauto using completeness_fundamental_exp_eq.
  destruct_conjs.
  assert (exists p p', initial_env Γ p /\ initial_env Γ p' /\ {{ Dom p ≈ p' ∈ env_relΓ }}) by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  (on_all_hyp: destruct_rel_by_assumption env_relΓ).
  destruct_by_head @rel_typ_unsorted.
  invert_rel_typ_body.
  destruct_by_head @rel_exp.
  assert (per_typ_elem pred_P (per_sort pred_P s3) d{{{ Sort@s3 }}} d{{{ Sort@s3 }}}) by (econstructor; reflexivity).
  handle_per_typ_elem_irrel.
  unfold per_sort in *.
  destruct_conjs.
  destruct Histyp;
    invert_rel_typ_body;
    destruct_conjs;
    invert_per_sort_elems.
  - do 2 eexists. reflexivity.
  - replace {{{ #x }}} with {{{ Π r B C }}} by mauto 3 using is_typ_constr_and_exp_eq_var_implies_eq_var.
    do 2 eexists. reflexivity.
Qed.

#[export]
Hint Resolve is_typ_constr_and_exp_eq_pi_implies_eq_pi : mcpts.
