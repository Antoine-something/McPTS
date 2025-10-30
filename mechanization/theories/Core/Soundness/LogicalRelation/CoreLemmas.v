From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From McPTS.Core.Soundness.Weakening Require Export Lemmas.
Import Domain_Notations.


#[global]
Ltac simpl_glu_rel :=
  apply_equiv_left;
  repeat invert_glu_rel1;
  apply_equiv_left;
  destruct_all;
  gen_presups.

Lemma glu_sort_elem_sort_lvl {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A : Sort@s }}.
Proof.
  simpl.  
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel; trivial.
Qed.

Lemma glu_sort_elem_typ_resp_exp_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A A',
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A ≈ A' : Sort@s }} ->
      {{ Γ ⊢ A' ® typ_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel; mauto 4.

  split; [trivial |].
  intros.
  transitivity {{{ A[σ] }}}; mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) Γ : (typ_rel Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}} ==> iff as glu_sort_elem_typ_morphism_iff1.
Proof.
  split; intros; eapply glu_sort_elem_typ_resp_exp_eq; mauto 2.
Qed.

Lemma glu_sort_elem_trm_resp_typ_exp_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m A',
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ A ≈ A' : Sort@s }} ->
      {{ Γ ⊢ M : A' ® m ∈ exp_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel; repeat split; intros; mauto 3.
  - firstorder.
  - econstructor; mauto 3.
  - transitivity {{{ A[σ] }}}; mauto 4.
  - assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Sort@s }}; mauto 4.    
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) Γ : (exp_rel Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as glu_sort_elem_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_sort_elem_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_sort_elem_typ_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A Δ,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ ⊢ Γ ≈ Δ }} ->
      {{ Δ ⊢ A ® typ_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel; mauto 2;
    econstructor; mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) : typ_rel
    with signature wf_ctx_eq ==> eq ==> iff as glu_sort_elem_typ_morphism_iff2.
Proof.
  intros. split; intros;
    eapply glu_sort_elem_typ_resp_ctx_eq;
    mauto 2.
Qed.

Lemma glu_sort_elem_trm_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m Δ,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ ⊢ Γ ≈ Δ }} ->
      {{ Δ ⊢ M : A ® m ∈ exp_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel; mauto 2;
    econstructor; mauto 4.

  - split; mauto.
    do 2 eexists.
    split; mauto.
    eapply glu_sort_elem_typ_resp_ctx_eq; mauto.
  - split; mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) : exp_rel
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_sort_elem_trm_morphism_iff2.
Proof.
  intros. split; intros;
    eapply glu_sort_elem_trm_resp_ctx_eq;
    mauto 2.
Qed.


Lemma glu_sort_elem_trm_escape {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M : A }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel; mauto 4.
Qed.

Lemma glu_sort_elem_per_sort {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Dom a ≈ a ∈ per_sort pred_P s }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros; eexists.
  - eapply per_sort_elem_core_sort'; mauto 2.
    reflexivity.
  - try solve [per_sort_elem_econstructor; mauto 3; try reflexivity].
    eassumption.
  - try solve [per_sort_elem_econstructor; mauto 3; try reflexivity].  
Qed.

#[export]
Hint Resolve glu_sort_elem_per_sort : mcpts.

Lemma glu_sort_elem_per_elem {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m R,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} ->
      {{ Dom m ≈ m ∈ R }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros.
  2,3: match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H);
    simpl_glu_rel;
    try fold (per_sort pred_P s' m m);
    mauto 4.
  - assert (per_sort_elem pred_P s (fun a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem pred_P s' ↘ R' }}) d{{{ Sort@s' }}} d{{{ Sort@s' }}}).
    {
      eapply per_sort_elem_core_sort'; mauto.
      unfold per_sort.
      reflexivity.
    }
    handle_per_sort_elem_irrel.
    simpl_glu_rel.
    try fold (per_sort pred_P s' m m).
    mauto 4.

  - intros.
    destruct_rel_mod_app.
    destruct_rel_mod_eval.
    functional_eval_rewrite_clear.
    do_per_sort_elem_irrel_assert.

    econstructor; firstorder eauto.
Qed.

Lemma glu_sort_elem_trm_typ {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ A ® typ_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel;
    mauto 4.

  econstructor; eauto.
  match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
  intros ? ? N n ? ? equiv_n.
  destruct_rel_mod_eval.
  enough (exists mn : domain P, {{ $| m & n |↘ mn }} /\  {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEL n equiv_n }}) as [? []]; eauto 3.
Qed.

Lemma glu_sort_elem_trm_sort_lvl {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros. eapply glu_sort_elem_sort_lvl; [| eapply glu_sort_elem_trm_typ]; eassumption.
Qed.

Lemma glu_sort_elem_trm_resp_exp_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m M',
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M ≈ M' : A }} ->
      {{ Γ ⊢ M' : A ® m ∈ exp_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel;
    repeat split; mauto 3.

  - repeat eexists; try split; eauto.
    eapply glu_sort_elem_typ_resp_exp_eq; mauto.

  - econstructor; eauto.
    match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
    intros.
    destruct_rel_mod_eval.
    assert {{ Δ ⊢ N : IT[σ]}} by eauto using glu_sort_elem_trm_escape.
    assert (exists mn : domain P, {{ $| m & n |↘ mn }} /\  {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEL n equiv_n }}) as [? []] by intuition.
    eexists; split; eauto.
    enough {{ Δ ⊢ M[σ] N ≈ M'[σ] N : OT[σ,,N] }} by eauto.
    assert {{ Γ ⊢ M ≈ M' : Π r0 IT OT }} as Hty by mauto.
    eassert {{ Δ ⊢ IT[σ] : Sort@_ }} by mauto 3.
    eapply wf_exp_eq_sub_cong with (Γ := Δ) in Hty; [| eapply sub_eq_refl; mauto 3].
    autorewrite with mcpts in Hty.
    eapply wf_exp_eq_app_cong with (N := N) (N' := N) in Hty.  (* try pi_sort_level_tac; [|mauto 2]. *)
    autorewrite with mcpts in Hty.
    assert ({{ Δ ⊢ OT[q σ][Id,,N] ≈ OT[σ,,N] }}) by mauto.
    mauto.
    + eassumption.
    + eapply wf_exp_conv with (A := {{{ Sort@s4[q σ] }}}); mauto 4.
    + mauto.
  - intros.
    enough {{ Δ ⊢ M[σ] ≈ M'[σ] : A[σ] }}; mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) Γ T : (exp_rel Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as glu_sort_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_sort_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

(* STOPPED HERE *)
Lemma glu_univ_elem_core_univ' : forall j i typ_rel el_rel,
    j < i ->
    (typ_rel <∙> univ_glu_typ_pred j i) ->
    (el_rel <∙> univ_glu_exp_pred j i) ->
    {{ DG 𝕌@j ∈ glu_univ_elem i ↘ typ_rel ↘ el_rel }}.
Proof.
  intros.
  unshelve basic_glu_univ_elem_econstructor; mautosolve.
Qed.

#[export]
Hint Resolve glu_univ_elem_core_univ' : mcpts.

Ltac glu_univ_elem_econstructor :=
  eapply glu_univ_elem_core_univ' + basic_glu_univ_elem_econstructor.

Lemma glu_univ_elem_univ_simple_constructor : forall {i},
    glu_univ_elem (S i) (univ_glu_typ_pred i (S i)) (univ_glu_exp_pred i (S i)) d{{{ 𝕌@i }}}.
Proof.
  intros.
  glu_univ_elem_econstructor; mauto; reflexivity.
Qed.

#[export]
Hint Resolve glu_univ_elem_univ_simple_constructor : mcpts.

Ltac rewrite_predicate_equivalence_left :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_predicate_equivalence_right :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_predicate_equivalence :=
  repeat match goal with
    | H : ?R1 <∙> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_predicate_equivalence :=
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_right;
  clear_predicate_equivalence;
  rewrite_predicate_equivalence_left;
  clear_predicate_equivalence.

(** *** Simple Morphism instance for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> iff as simple_glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' ? El El'.
  split; intro Horig; [gen El' P' | gen El P];
    induction Horig using glu_univ_elem_ind; unshelve glu_univ_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.

(** *** Morphism instances for [neut_glu_*_pred]s *)
Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> eq ==> eq ==> iff as neut_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition.
Qed.

Add Parametric Morphism i : (neut_glu_typ_pred i)
    with signature per_bot ==> glu_typ_pred_equivalence as neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_typ_pred_morphism_iff; mauto.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> eq ==> eq ==> eq ==> eq ==> iff as neut_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head per_bot ltac:(fun H => specialize (H (length Δ)) as [? []]);
    functional_read_rewrite_clear; intuition;
    match_by_head per_bot ltac:(fun H => rewrite H in *); eassumption.
Qed.

Add Parametric Morphism i : (neut_glu_exp_pred i)
    with signature per_bot ==> glu_exp_pred_equivalence as neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_exp_pred_morphism_iff; mauto.
Qed.

(** *** Morphism instances for [pi_glu_*_pred]s *)
Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_typ_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> glu_typ_pred_equivalence as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i IR : (pi_glu_exp_pred i IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.


(** *** Morphism instances for [eq_glu_*_pred]s *)
Add Parametric Morphism i m n : (eq_glu_typ_pred i m n)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> iff as eq_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism i m n : (eq_glu_typ_pred i m n)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> glu_typ_pred_equivalence as eq_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.


Add Parametric Morphism i m n IR : (eq_glu_exp_pred i m n IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> eq ==> eq ==> eq ==> eq ==> iff as eq_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; destruct_glu_eq; repeat (econstructor; intuition).
Qed.

Add Parametric Morphism i m n IR : (eq_glu_exp_pred i m n IR)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> glu_exp_pred_equivalence as eq_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; destruct_glu_eq; repeat (econstructor; intuition).
Qed.


Lemma functional_glu_univ_elem : forall i a P P' El El',
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P' ↘ El' }} ->
    (P <∙> P') /\ (El <∙> El').
Proof.
  simpl.
  intros * Ha Ha'. gen P' El'.
  induction Ha using glu_univ_elem_ind; intros; basic_invert_glu_univ_elem Ha';
    apply_predicate_equivalence; try solve [split; reflexivity].
  - assert ((IP <∙> IP0) /\ (IEl <∙> IEl0)) as [] by mauto.
    apply_predicate_equivalence.
    handle_per_univ_elem_irrel.
    (on_all_hyp: fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    split; [intros Γ C | intros Γ M C m].
    + split; intros []; econstructor; intuition;
        [rename equiv_m into equiv0_m; assert (equiv_m : in_rel m m) by intuition
        | assert (equiv0_m : in_rel0 m m) by intuition ];
        destruct_rel_mod_eval;
        functional_eval_rewrite_clear;
        assert ((OP m equiv_m <∙> OP0 m equiv0_m) /\ (OEl m equiv_m <∙> OEl0 m equiv0_m)) as [] by mauto 3;
        intuition.
    + split; intros []; econstructor; intuition;
        [rename equiv_n into equiv0_n; assert (equiv_n : in_rel n n) by intuition
        | assert (equiv0_n : in_rel0 n n) by intuition];
        destruct_rel_mod_eval;
        [assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Δ ⊢ M0[σ] N : OT[σ,,N] ® m0n ∈ OEl n equiv_n }}) by intuition
        | assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Δ ⊢ M0[σ] N : OT[σ,,N] ® m0n ∈ OEl0 n equiv0_n }}) by intuition];
        destruct_conjs;
        assert ((OP n equiv_n <∙> OP0 n equiv0_n) /\ (OEl n equiv_n <∙> OEl0 n equiv0_n)) as [] by mauto 3;
        eexists; split; intuition.
  - assert ((P <∙> P0) /\ (El <∙> El0)) as [] by mauto.
    apply_predicate_equivalence.
    handle_per_univ_elem_irrel.
    split; [intros Γ C | intros Γ M C m'].
    + split; intros []; econstructor; intuition.
    + split; intros []; econstructor; intuition;
        destruct_glu_eq;
        econstructor; intros; apply_equiv_right; mauto 4.
Qed.

Ltac apply_functional_glu_univ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_univ_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DG ^?a ∈ glu_univ_elem ?i ↘ ?P1 ↘ ?El1 }},
      H2 : {{ DG ^?a ∈ glu_univ_elem ?i' ↘ ?P2 ↘ ?El2 }} |- _ =>
      unify i i';
      assert_fails (unify P1 P2; unify El1 El2);
      match goal with
      | H : P1 <∙> P2, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P1 <∙> P2, H0 : El2 <∙> El1 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El1 <∙> El2 |- _ => fail 1
      | H : P2 <∙> P1, H0 : El2 <∙> El1 |- _ => fail 1
      | _ => assert ((P1 <∙> P2) /\ (El1 <∙> El2)) as [] by (eapply functional_glu_univ_elem; [apply H1 | apply H2]) || tactic_error P1 P2
      end
  end.

Ltac apply_functional_glu_univ_elem :=
  repeat apply_functional_glu_univ_elem1.

Ltac handle_functional_glu_univ_elem :=
  functional_eval_rewrite_clear;
  fold glu_typ_pred in *;
  fold glu_exp_pred in *;
  apply_functional_glu_univ_elem;
  apply_predicate_equivalence;
  clear_dups.

Lemma glu_univ_elem_pi_clean_inversion1 : forall {i a ρ B in_rel P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
  {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists IP IEl (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred) elem_rel,
      {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} /\
        (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
            {{ DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) /\
        {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
        (P <∙> pi_glu_typ_pred i in_rel IP IEl OP) /\
        (El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_univ_elem Hglu.
  handle_functional_glu_univ_elem.
  handle_per_univ_elem_irrel.
  do 5 eexists.
  repeat split.
  1,3: eassumption.
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ M : A ® m ∈ Elb }}).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain) Pb Elb,
                          {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                          {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                          {{ Γ ⊢ A ® Pb }}).
  2-5: intros []; econstructor; mauto.
  all: intros.
  - assert {{ Dom c ≈ c ∈ in_rel0 }} as equiv0_c by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP c equiv0_c ↘ OEl c equiv0_c }} by mauto 3.
    apply -> simple_glu_univ_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_univ_elem; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_univ_elem |]; intuition.
  - assert {{ Dom m ≈ m ∈ in_rel0 }} as equiv0_m by intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP m equiv0_m ↘ OEl m equiv0_m }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    destruct_rel_mod_eval.
    intuition.
  - assert {{ Dom n ≈ n ∈ in_rel0 }} as equiv0_n by intuition.
    assert (exists mn : domain, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEl n equiv0_n }}) by mauto 3.
    destruct_conjs.
    eexists.
    intuition.
    assert {{ DG b ∈ glu_univ_elem i ↘ OP n equiv0_n ↘ OEl n equiv0_n }} by mauto 3.
    handle_functional_glu_univ_elem.
    intuition.
  - assert (exists mn : domain,
               {{ $| m & n |↘ mn }} /\
                 (forall (b : domain) (Pb : glu_typ_pred) (Elb : glu_exp_pred),
                     {{ ⟦ B ⟧ ρ ↦ n ↘ b }} ->
                     {{ DG b ∈ glu_univ_elem i ↘ Pb ↘ Elb }} ->
                     {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ Elb }})) by intuition.
    destruct_conjs.
    match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H).
    handle_per_univ_elem_irrel.
    destruct_rel_mod_eval.
    destruct_rel_mod_app.
    functional_eval_rewrite_clear.
    eexists.
    intuition.
Qed.

Lemma glu_univ_elem_pi_clean_inversion2 : forall {i a ρ B in_rel IP IEl P El},
  {{ DF a ≈ a ∈ per_univ_elem i ↘ in_rel }} ->
  {{ DG a ∈ glu_univ_elem i ↘ IP ↘ IEl }} ->
  {{ DG Π a ρ B ∈ glu_univ_elem i ↘ P ↘ El }} ->
  exists (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred) elem_rel,
    (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
        {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
        {{ DG b ∈ glu_univ_elem i ↘ OP _ equiv_c ↘ OEl _ equiv_c }}) /\
      {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} /\
      (P <∙> pi_glu_typ_pred i in_rel IP IEl OP) /\
      (El <∙> pi_glu_exp_pred i in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hinglu Hglu.
  unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in Hglu; shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]].
  handle_functional_glu_univ_elem.
  do 3 eexists.
  repeat split; try eassumption;
    intros []; econstructor; mauto.
Qed.

Ltac invert_glu_univ_elem H :=
  (unshelve eapply (glu_univ_elem_pi_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_univ_elem_pi_clean_inversion1 _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_univ_elem H.

Lemma glu_nat_resp_per_nat : forall m n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    forall Γ M,
      glu_nat Γ M m ->
      glu_nat Γ M n.
Proof.
  induction 1; intros; progressive_inversion; mauto.
  econstructor.
  - mauto using (PER_refl2 _ per_bot).
  - intros.
    specialize (H (length Δ)).
    destruct_all.
    functional_read_rewrite_clear.
    mauto.
Qed.

#[local]
 Hint Resolve glu_nat_resp_per_nat : mcpts.

#[local]
  Ltac resp_per_IH :=
  match_by_head1 glu_univ_elem
    ltac:(fun H =>
            match goal with
            | H' : _ |- _ => eapply H' in H
            end);
  eauto; intuition.

Lemma glu_univ_elem_resp_per_univ_elem : forall i a a' R,
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    forall P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P ↘ El }} /\
      (forall Γ M A m m',
          {{ Γ ⊢ M : A ® m ∈ El }} ->
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Γ ⊢ M : A ® m' ∈ El }}).
Proof.
  simpl.
  intros * Hper * Horig.
  pose proof Hper.
  gen P El.

  induction Hper using per_univ_elem_ind; intros; subst;
    saturate_refl_for per_univ_elem;
    invert_glu_univ_elem Horig;
    split;
    try glu_univ_elem_econstructor;
    try eassumption; mauto 3;
    intros;
    handle_per_univ_elem_irrel;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all;
    mauto 3.

  - repeat split; eauto.
    resp_per_IH.
    mauto.
  - resp_per_IH.
  - invert_per_univ_elem H.
    destruct_rel_mod_eval.
    handle_per_univ_elem_irrel.
    pose proof (H9 _ equiv_c _ H4).
    resp_per_IH.
  - reflexivity.
  - simpl_glu_rel.
    invert_per_univ_elem H10.

    econstructor; mauto 3.
    + eapply H17.
      pose proof (proj1 (H17 _ _) H16).
      simpl in *.

      intros.
      saturate_refl_for in_rel.
      pose proof (H18 _ _ equiv_c_c') as [].
      pose proof (H18 _ _ H19) as [].
      pose proof (H10 _ _ equiv_c_c') as [].
      pose proof (H10 _ _ H19) as [].
      simplify_evals.
      econstructor; eauto.
      symmetry.
      etransitivity.
      * symmetry. eassumption.
      * handle_per_univ_elem_irrel.
        eapply H24.
        eassumption.
    + resp_per_IH.
      destruct_rel_mod_eval.
      handle_per_univ_elem_irrel.
      pose proof (H9 _ equiv_n _ H22).
      eapply H28 in H25 as []; eauto.
      destruct (H15 _ _ _ _ H20 H21 equiv_n) as [? []].
      destruct (H16 _ _ equiv_n) as [].
      simplify_evals.
      eauto.
  - resp_per_IH.
  - mauto using (PER_refl2 _ R).
  - mauto using (PER_refl2 _ R).
  - split; intros []; econstructor; intuition.
  - split; intros []; econstructor; intuition;
      destruct_glu_eq;
      econstructor; mauto 3;
      apply_equiv_left.
    + etransitivity; eauto.
      symmetry. trivial.
    + etransitivity; eauto.
    + etransitivity; [| eauto]; eauto.
    + etransitivity; eauto.
      symmetry. trivial.
  - simpl_glu_rel.
    econstructor; eauto.
    destruct_glu_eq; progressive_invert H20; econstructor; mauto 3; intros.
    + etransitivity; mauto.
    + etransitivity; eauto.
      symmetry. eauto.
    + resp_per_IH.
    + specialize (H20 (length Δ)).
      destruct_all.
      functional_read_rewrite_clear.
      mauto.
  - apply neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
    eassumption.
  - apply neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
    eassumption.
  - simpl_glu_rel.
    progressive_invert H9.
    econstructor; unfold neut_glu_typ_pred; mauto 3.

    intros.
    specialize (H9 (length Δ)).
    destruct_all.
    functional_read_rewrite_clear.
    mauto.
Qed.


Lemma glu_univ_elem_resp_per_univ : forall i a a' P El,
    {{ Dom a ≈ a' ∈ per_univ i }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ DG a' ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  intros * [? H] ?.
  eapply glu_univ_elem_resp_per_univ_elem in H; eauto.
  intuition.
Qed.

Lemma glu_univ_elem_resp_per_elem : forall i a a' R P El Γ M A m m',
    {{ DF a ≈ a' ∈ per_univ_elem i ↘ R }} ->
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Γ ⊢ M : A ® m' ∈ El }}.
Proof.
  intros * H ?.
  eapply glu_univ_elem_resp_per_univ_elem in H; eauto.
  intuition.
Qed.


(** *** Morphism instances for [glu_univ_elem] *)
Add Parametric Morphism i : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ i ==> iff as glu_univ_elem_morphism_iff.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; eassumption.
Qed.

Add Parametric Morphism i R : (glu_univ_elem i)
    with signature glu_typ_pred_equivalence ==> glu_exp_pred_equivalence ==> per_univ_elem i R ==> iff as glu_univ_elem_morphism_iff'.
Proof with mautosolve.
  intros P P' HPP' El El' HElEl' **.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_univ_elem_resp_per_univ; mauto.
  symmetry; mauto.
Qed.

Ltac saturate_glu_by_per1 :=
  match goal with
  | H : glu_univ_elem ?i ?P ?El ?a,
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a') by (rewrite <- H1; eassumption);
      fail_if_dup
  | H : glu_univ_elem ?i ?P ?El ?a',
      H1 : per_univ_elem ?i _ ?a ?a' |- _ =>
      assert (glu_univ_elem i P El a) by (rewrite H1; eassumption);
      fail_if_dup
  end.

Ltac saturate_glu_by_per :=
  clear_dups;
  repeat saturate_glu_by_per1.

Lemma per_univ_glu_univ_elem : forall i a,
    {{ Dom a ≈ a ∈ per_univ i }} ->
    exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  simpl.
  intros * [? Hper].
  induction Hper using per_univ_elem_ind; intros;
    try solve [do 2 eexists; unshelve (glu_univ_elem_econstructor; try reflexivity; subst; trivial)].

  - destruct_conjs.
    do 2 eexists.
    glu_univ_elem_econstructor; try (eassumption + reflexivity).
    + saturate_refl; eassumption.
    + instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A M m =>
                          forall b P El,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ M : A ® m ∈ El }}).
      instantiate (1 := fun (c : domain) (equiv_c : in_rel c c) Γ A =>
                          forall b P El,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_univ_elem i P El b ->
                            {{ Γ ⊢ A ® P }}).
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_univ_elem_irrel.
      rewrite simple_glu_univ_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_univ_elem; intuition.
    + enough {{ DF Π a ρ B ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel }} by (etransitivity; [symmetry |]; eassumption).
      per_univ_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
  - destruct_conjs.
    saturate_refl.
    do 2 eexists.
    glu_univ_elem_econstructor; eauto; reflexivity.
  - do 2 eexists.
    glu_univ_elem_econstructor; try reflexivity; mauto.
Qed.

#[export]
Hint Resolve per_univ_glu_univ_elem : mcpts.

Corollary per_univ_elem_glu_univ_elem : forall i a R,
    {{ DF a ≈ a ∈ per_univ_elem i ↘ R }} ->
    exists P El, {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }}.
Proof.
  intros.
  apply per_univ_glu_univ_elem; mauto.
Qed.

#[export]
Hint Resolve per_univ_elem_glu_univ_elem : mcpts.

Ltac saturate_glu_info1 :=
  match goal with
  | H : glu_univ_elem _ ?P _ _,
      H1 : ?P _ _ |- _ =>
      pose proof (glu_univ_elem_univ_lvl _ _ _ _ H _ _ H1);
      fail_if_dup
  | H : glu_univ_elem _ _ ?El _,
      H1 : ?El _ _ _ _ |- _ =>
      pose proof (glu_univ_elem_trm_escape _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_info :=
  clear_dups;
  repeat saturate_glu_info1.

#[local]
Hint Rewrite -> sub_decompose_q using solve [mauto 4] : mcpts.

Lemma glu_univ_elem_mut_monotone : forall i a P El,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    forall Δ σ Γ,
      {{ Δ ⊢w σ : Γ }} ->
      (forall A,
        {{ Γ ⊢ A ® P }} ->
        {{ Δ ⊢ A[σ] ® P }}) /\
    (forall M A m,
      {{ Γ ⊢ M : A ® m ∈ El }} ->
      {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }}).
Proof.
  simpl. induction 1 using glu_univ_elem_ind;
    split; intros;
    saturate_weakening_escape;
    handle_functional_glu_univ_elem;
    simpl in *;
    destruct_all;
    try solve [bulky_rewrite].
  - repeat eexists; mauto 2; bulky_rewrite.
    resp_per_IH.
  - repeat eexists; mauto 2; bulky_rewrite.

  - simpl_glu_rel.
    econstructor; eauto; try solve [bulky_rewrite]; mauto 3.
    + intros.
      eapply IHglu_univ_elem; eauto.
    + intros.
      saturate_weakening_escape.
      saturate_glu_info.
      invert_per_univ_elem H3.
      destruct_rel_mod_eval.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      autorewrite with mcpts in *.
      mauto 3.

  - simpl_glu_rel.
    econstructor; mauto 4;
      intros;
      saturate_weakening_escape.
    + eapply IHglu_univ_elem; eauto.
    + saturate_glu_info.
      invert_per_univ_elem H3.
      apply_equiv_left.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      autorewrite with mcpts in *.
      repeat eexists; eauto.
      assert {{ Δ0 ⊢s σ0,,N : Δ, IT[σ] }}.
      {
        econstructor; mauto 2.
        bulky_rewrite.
      }
      assert {{Δ0 ⊢ M[σ][σ0] N ≈ M[σ∘σ0] N : OT [σ∘σ0,,N]}}.
      {
        rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.
        rewrite <- @exp_eq_sub_compose_typ; mauto 3;
          [eapply wf_exp_eq_app_cong' |];
          mauto 4.
        symmetry.
        bulky_rewrite_in H4.
        assert {{ Δ0 ⊢ Π IT[σ∘σ0] (OT[q (σ∘σ0)]) ≈ (Π IT OT)[σ∘σ0] : Type@_ }} by mauto.
        eapply wf_exp_eq_conv'; mauto 4.
      }

      bulky_rewrite.
      edestruct H11 with (n := n) as [? []];
        simplify_evals; [| | eassumption];
        mauto.

  - simpl_glu_rel.
    econstructor; intros.
    + bulky_rewrite.
    + mauto 3.
    + mauto 3.
    + mauto 3.
    + eapply IHglu_univ_elem; eauto.
    + eapply IHglu_univ_elem; eauto.
    + eapply IHglu_univ_elem; eauto.
  - simpl_glu_rel.
    econstructor; intros.
    + mauto 3.
    + bulky_rewrite.
    + mauto 3.
    + mauto 3.
    + mauto 3.
    + eapply IHglu_univ_elem; eauto.
    + eapply IHglu_univ_elem; eauto.
    + eapply IHglu_univ_elem; eauto.
    + destruct_glu_eq; econstructor; eauto; intros.
      * transitivity {{{(refl B M'')[σ]}}}; [mauto 3 |].
        eapply wf_exp_eq_conv';
          [eapply wf_exp_eq_refl_sub'; gen_presups; eauto |].
        symmetry.
        transitivity {{{(Eq B M N)[σ]}}}; mauto 2.
        eapply exp_eq_sub_cong_typ1; eauto.
        econstructor; mauto.
      * mauto.
      * mauto.
      * eapply IHglu_univ_elem; eauto.
      * assert {{ Δ0 ⊢w σ ∘ σ0 : Γ }} by mauto 4.
        bulky_rewrite.
        etransitivity;
          [| deepexec H14 ltac:(fun H => apply H)].
        mauto 4.
  - destruct_conjs.
    split; [mauto 3 |].
    intros.
    saturate_weakening_escape.
    autorewrite with mcpts.
    mauto 3.
  - simpl_glu_rel.
    econstructor; repeat split; mauto 3;
      intros;
      saturate_weakening_escape.
    + autorewrite with mcpts.
      mauto 3.
    + autorewrite with mcpts.
      etransitivity.
      * symmetry.
        eapply wf_exp_eq_sub_compose;
          mauto 3.
      * mauto 3.
Qed.

Lemma glu_univ_elem_typ_monotone : forall i a P El Δ σ Γ A,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ A ® P }} ->
    {{ Δ ⊢w σ : Γ }} ->
    {{ Δ ⊢ A[σ] ® P }}.
Proof.
  intros * H; intros.
  eapply glu_univ_elem_mut_monotone in H; eauto.
  intuition.
Qed.

Lemma glu_univ_elem_exp_monotone : forall i a P El Δ σ Γ M A m,
    {{ DG a ∈ glu_univ_elem i ↘ P ↘ El }} ->
    {{ Γ ⊢ M : A ® m ∈ El }} ->
    {{ Δ ⊢w σ : Γ }} ->
    {{ Δ ⊢ M[σ] : A[σ] ® m ∈ El }}.
Proof.
  intros * H; intros.
  eapply glu_univ_elem_mut_monotone in H; eauto.
  intuition.
Qed.

Add Parametric Morphism i a : (glu_elem_bot i a)
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4; [rewrite <- HΓΓ' | rewrite -> HΓΓ']; eassumption.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_bot i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_bot i a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Δ ⊢ M[σ] ≈ M'[σ] : A[σ] }} as HMσM'σ by mauto 4;
    [rewrite <- HMσM'σ | rewrite -> HMσM'σ];
    mauto.
Qed.

Add Parametric Morphism i a : (glu_elem_top i a)
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4; [rewrite <- HΓΓ' | rewrite -> HΓΓ']; eassumption.
Qed.

Add Parametric Morphism i a Γ : (glu_elem_top i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3; [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    intros;
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.

Add Parametric Morphism i a Γ A : (glu_elem_top i a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_top_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Δ ⊢ M[σ] ≈ M'[σ] : A[σ] }} as HMσM'σ by mauto 4;
    [rewrite <- HMσM'σ | rewrite -> HMσM'σ];
    mauto.
Qed.

Add Parametric Morphism i a : (glu_typ_top i a)
    with signature wf_ctx_eq ==> eq ==> iff as glu_typ_top_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4.
Qed.

Add Parametric Morphism i a Γ : (glu_typ_top i a Γ)
    with signature wf_exp_eq Γ {{{ Type@i }}} ==> iff as glu_typ_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    try (gen_presup HAA'; eassumption);
    intros;
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] : Type@i }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.

(** *** Simple Morphism instance for [glu_ctx_env] *)
Add Parametric Morphism : glu_ctx_env
    with signature glu_sub_pred_equivalence ==> eq ==> iff as simple_glu_ctx_env_morphism_iff.
Proof.
  intros Sb Sb' HSbSb' a.
  split; intro Horig; [gen Sb' | gen Sb];
    induction Horig; econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.
