From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Import SystemAnnotated.
From McPTS.Core.Soundness.LogicalRelation Require Import CoreTactics Definitions.
From McPTS.Core.Syntactic.Weakening Require Export Lemmas.
Import Domain_Notations.

Lemma glu_nat_per_nat {P} {s} (r : Ru_nat P s) : forall (Γ : ctx P) M a,
    glu_nat r Γ M a ->
    {{ Dom a ≈ a ∈ per_nat }}.
Proof.
  induction 1; mauto.
Qed.

#[local]
Hint Resolve glu_nat_per_nat : mcpts.

Lemma glu_nat_escape {P} {s} (r : Ru_nat P s) : forall (Γ : ctx P) M a,
    glu_nat r Γ M a ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ M : ℕ }}.
Proof.
  induction 1; intros;
    try match goal with
    | H : _ |- _ => solve [gen_presup H; mauto]
    end.
  assert {{ Γ ⊢w Id : Γ }} by mauto.
  match_by_head (per_bot m m) ltac:(fun H => specialize (H (length Γ)) as [M' []]).
  clear_dups.
  assert {{ Γ ⊢ M[Id] ≈ M' : ℕ }} by mauto.
  gen_presups.
  mauto.
Qed.

#[export]
Hint Resolve glu_nat_escape : mcpts.

Lemma glu_nat_resp_ctx_eq {P} {s} (r : Ru_nat P s) : forall (Γ : ctx P) M a Γ',
    glu_nat r Γ M a ->
    {{ ⊢ Γ ≈ Γ' }} ->
    glu_nat r Γ' M a.
Proof.
  induction 1; intros; mauto 4.
  assert {{ ⊢ Γ' ⊆ Γ }} by mauto 3.
  econstructor; mauto 3.
Qed.

#[local]
Hint Resolve glu_nat_resp_ctx_eq : mcpts.

Add Parametric Morphism {P} {s} (r : Ru_nat P s) : (glu_nat r)
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as glu_ctx_env_sub_morphism_iff1.
Proof.
  split; mauto using glu_nat_resp_ctx_eq.
Qed.

Lemma glu_nat_resp_exp_eq {P} {s} (r : Ru_nat P s) : forall (Γ : ctx P) M a,
    glu_nat r Γ M a ->
    forall M',
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    glu_nat r Γ M' a.
Proof.
  induction 1; intros; mauto 4.
  econstructor; trivial.
  intros.
  transitivity {{{ M[σ] }}}; mauto 2.
  symmetry.
  assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
  mauto 3.
Qed.

#[local]
Hint Resolve glu_nat_resp_exp_eq : mcpts.

Add Parametric Morphism {P} {s} (r : Ru_nat P s) Γ : (glu_nat r Γ)
    with signature wf_exp_eq Γ {{{ ℕ }}} ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; mauto using glu_nat_resp_exp_eq.
Qed.

Lemma glu_nat_readback {P} {s} (r : Ru_nat P s) : forall Γ M a,
    glu_nat r Γ M a ->
    forall Γ' σ M',
      {{ Γ' ⊢w σ : Γ }} ->
      {{ Rnf ⇓ ℕ a in length Γ' ↘ M' }} ->
      {{ Γ' ⊢ M[σ] ≈ M' : ℕ }}.
Proof.
  induction 1; intros; progressive_inversion; gen_presups.
  - transitivity {{{ zero[σ] }}}; mauto 3.
  - assert {{ Γ' ⊢ M'[σ] ≈ M0 : ℕ }} by mauto 4.
    transitivity {{{ (succ M')[σ] }}}; mauto 3.
    transitivity {{{ succ M'[σ] }}}; mauto 4.
  - mauto 4.
Qed.

Lemma glu_nat_rule_irrelevance {P} {s} (r : Ru_nat P s) : forall Γ M a,
    glu_nat r Γ M a ->
    forall s' (r' : Ru_nat P s'), glu_nat r' Γ M a.
Proof.
  intros.
  induction H; mauto 2.
Qed.

#[local]
Hint Resolve glu_nat_rule_irrelevance : mcpts.

Lemma glu_nat_resp_per_nat {P} {s} (r : Ru_nat P s) : forall m n,
    {{ Dom m ≈ n ∈ per_nat }} ->
    forall Γ M,
      glu_nat r Γ M m ->
      glu_nat r Γ M n.
Proof.
  induction 1; intros; progressive_inversion; mauto 3.
  econstructor; mauto 3.
  intros.
  specialize (H (length Γ')).
  destruct_all.
  functional_read_rewrite_clear.
  mauto.
Qed.

#[local]
Hint Resolve glu_nat_resp_per_nat : mcpts.


(* #[global] *)
(* Ltac simpl_glu_rel := *)
(*   apply_equiv_left; *)
(*   repeat invert_glu_rel1; *)
(*   apply_equiv_left; *)
(*   destruct_all; *)
(*   gen_presups. *)


Lemma glu_sort_elem_sort_lvl {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A : Sort@s }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind;
    intros; simpl_glu_rel; mauto 3.  
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
    
  split; [eassumption | ].
  intros.
  transitivity {{{ A[σ] }}}; mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) Γ : (typ_rel Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}}  ==> iff as glu_sort_elem_typ_morphism_iff1.
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
  - assert {{ Γ' ⊢ M[σ] ≈ M' : A[σ] }} by mauto 2.
    eapply wf_exp_eq_conv_exp_eq'; mauto 3.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) Γ : (exp_rel Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}}  ==> eq ==> eq ==> iff as glu_sort_elem_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_sort_elem_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_sort_elem_typ_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A Γ',
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ ⊢ Γ ≈ Γ' }} ->
      {{ Γ' ⊢ A ® typ_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    assert {{ ⊢ Γ' ⊆ Γ }} by mauto 3;
    simpl_glu_rel; mauto 3;
    econstructor; mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) : typ_rel
    with signature wf_ctx_eq ==> eq ==> iff as glu_sort_elem_typ_morphism_iff2.
Proof.
  intros. split; intros;
    eapply glu_sort_elem_typ_resp_ctx_eq;
    mauto 2.
Qed.


Lemma glu_sort_elem_trm_resp_ctx_eq_pi_helper {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 s} (r : Ru_pi P s1 s2 s3) (sub_s3_s : st_subtyp s3 s) IR IP IEL elem_rel OEL Γ M A m Γ',
  {{ Γ ⊢ M : A ® m ∈ pi_glu_exp_pred r sub_s3_s IR IP IEL elem_rel OEL }} ->
  {{ ⊢ Γ ≈ Γ' }} ->
  {{ Γ' ⊢ M : A ® m ∈ pi_glu_exp_pred r sub_s3_s IR IP IEL elem_rel OEL }}.
Proof.
  intros.
  assert {{ ⊢ Γ' ⊆ Γ }} by mauto 3.  
  inversion_clear H.
  econstructor; mauto 4.
Qed.


Lemma glu_sort_elem_trm_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m Γ',
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ ⊢ Γ ≈ Γ' }} ->
      {{ Γ' ⊢ M : A ® m ∈ exp_rel }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    assert {{ ⊢ Γ' ⊆ Γ }} by mauto 3;
    simpl_glu_rel; mauto 2.
  - repeat split; mauto 3.
    do 2 eexists; split; mauto 4.
    eapply glu_sort_elem_typ_resp_ctx_eq; mauto 2.

  - eapply glu_sort_elem_trm_resp_ctx_eq_pi_helper; mauto.
  - econstructor; mauto 2 using glu_nat_resp_ctx_eq.
  - econstructor; mauto 4.
    repeat split; mauto 2; intros.
    mauto 4.
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

Lemma glu_sort_elem_typ_escape {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros;
    simpl_glu_rel; mauto 3.
Qed.

Lemma glu_sort_elem_per_sort {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Dom a ≈ a ∈ per_sort pred_P s }}.
Proof.
  simpl.
  induction 1 using glu_sort_elem_ind; intros; eexists;    
    only 1: (eapply per_sort_elem_core_sort'; mauto 2; reflexivity);
    try solve [per_sort_elem_econstructor; mauto 3; try reflexivity; econstructor]; try eassumption.  
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
  2-4: match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H);
    simpl_glu_rel;
    try fold (per_sort pred_P s' m m);
    mauto 4.
  - assert (per_sort_elem pred_P s (per_sort pred_P s'') d{{{ Sort@s'' }}} d{{{ Sort@s'' }}}) by (eapply per_sort_elem_core_sort'; mauto; reflexivity).
    handle_per_sort_elem_irrel.
    simpl_glu_rel.
    mauto 4.

  - intros.
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    assert (in_rel0 n n') as equiv0_n_n' by intuition.
    destruct_rel_mod_app.
    destruct_rel_mod_eval.
    functional_eval_rewrite_clear.
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    econstructor; mauto 2.
    intuition.
Qed.


Lemma glu_sort_elem_per_typ_elem {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m R,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
      {{ Dom m ≈ m ∈ R }}.
Proof.
  simpl.
  intros * Hglu.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s }} as [] by mauto.
  intros.
  eapply glu_sort_elem_per_elem; mauto.
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
    mauto 3.

  econstructor; eauto.
  match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
  intros ? ? N n ? ? equiv_n.
  clear_pi_sort_eq_and_pred_rel.
  handle_per_sort_elem_irrel.
  assert (in_rel0 n n) by intuition.
  destruct_rel_mod_eval.
  enough (exists mn : domain P, {{ $| m & n |↘ mn }} /\  {{ Γ' ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEL n equiv_n }}) as [? []]; eauto 3.
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
    destruct_conjs.
    match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
    intros.
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    assert (in_rel0 n n) by intuition.
    destruct_rel_mod_eval.
    assert {{ Γ' ⊢ N : IT[σ]}} by eauto using glu_sort_elem_trm_escape.
    assert (exists mn : domain P, {{ $| m & n |↘ mn }} /\  {{ Γ' ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEL n equiv_n }}) as [? []] by intuition.
    eexists; split; eauto.
    enough {{ Γ' ⊢ M[σ] N ≈ M'[σ] N : OT[σ,,N] }} by eauto.
    assert {{ Γ ⊢ M ≈ M' : Π r IT OT }} as Hty by mauto.
    assert {{ Γ' ⊢ IT[σ] : Sort@s1 }} by mauto 3.
    assert {{ Γ', IT[σ] ⊢ OT[q σ] : Sort@s2 }} by mauto 4.
    eapply wf_exp_eq_sub_cong with (Γ := Γ') in Hty; mauto 3.
    autorewrite with mcpts in Hty.
    eapply wf_exp_eq_app_cong with (N := N) (N' := N) in Hty; mauto 2.
    assert ({{ Γ' ⊢ OT[q σ][Id,,N] ≈ OT[σ,,N] }}) by mauto 4.
    mauto.

  - intros.
    enough {{ Γ' ⊢ M[σ] ≈ M'[σ] : A[σ] }}; mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_sort_elem pred_P s typ_rel exp_rel a) Γ T : (exp_rel Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as glu_sort_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_sort_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

Lemma glu_sort_elem_core_sort' {P} (pred_P : PredicativeSig P) : forall s'' s' s typ_rel exp_rel,
    Ax_typ P s'' s' ->
    st_subtyp s' s ->
    (typ_rel <∙> sort_glu_typ_pred pred_P s'' s) ->
    (exp_rel <∙> sort_glu_exp_pred pred_P s'' s) ->
    {{ DG Sort@s'' ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}.
Proof.
  intros.
  unshelve basic_glu_sort_elem_econstructor; [| eassumption | | |]; mautosolve.
Qed.

#[export]
Hint Resolve glu_sort_elem_core_sort' : mcpts.

Ltac glu_sort_elem_econstructor :=
  eapply glu_sort_elem_core_sort' + basic_glu_sort_elem_econstructor.

Lemma glu_sort_elem_sort_simple_constructor {P} (pred_P : PredicativeSig P) : forall {s'' s' s},
    Ax_typ P s'' s' ->
    st_subtyp s' s ->
    glu_sort_elem pred_P s (sort_glu_typ_pred pred_P s'' s) (sort_glu_exp_pred pred_P s'' s) d{{{ Sort@s'' }}}.
Proof.
  intros.
  glu_sort_elem_econstructor; mauto; reflexivity.
Qed.

#[export]
Hint Resolve glu_sort_elem_sort_simple_constructor : mcpts.

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

Lemma glu_typ_elem_sort_lvl {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A : Sort@s }}.
Proof.
  simpl.
  intros.
  inversion H; subst.
  eapply glu_sort_elem_sort_lvl; mauto 2.
Qed.

Lemma glu_typ_elem_wf_typ {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A }}.
Proof.
  simpl.
  intros.
  inversion H; subst; apply_predicate_equivalence;
    unfold top_sort_glu_typ_pred in *;
    gen_presups; [eassumption|].
  mauto 3 using glu_sort_elem_sort_lvl.
Qed.

Lemma glu_typ_elem_none_typ_resp_typ_eq {P} (pred_P : PredicativeSig P) : forall typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so_None ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A A',
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A ≈ A' }} ->
      {{ Γ ⊢ A' ® typ_rel }}.
Proof.
  simpl.
  inversion_clear 1.
  intros.
  simpl_glu_rel.
  transitivity A; mauto 3.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) typ_rel exp_rel a (H : glu_typ_elem pred_P so_None typ_rel exp_rel a) Γ : (typ_rel Γ)
    with signature wf_typ_eq Γ  ==> iff as glu_typ_elem_typ_morphism_iff1.
Proof.
  split; intros;
    eapply glu_typ_elem_none_typ_resp_typ_eq;
    mauto 2.
Qed.

Lemma glu_typ_elem_some_typ_resp_exp_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A A',
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A ≈ A' : Sort@s }} ->
      {{ Γ ⊢ A' ® typ_rel }}.
Proof.
  simpl.
  intros.
  inversion_clear H.
  eapply glu_sort_elem_typ_resp_exp_eq; mauto 2.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_typ_elem pred_P (so_Some s) typ_rel exp_rel a) Γ : (typ_rel Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}}  ==> iff as glu_typ_elem_some_typ_morphism_iff1.
Proof.
  split; intros; eapply glu_typ_elem_some_typ_resp_exp_eq; mauto 2.
Qed.

Lemma glu_typ_elem_none_trm_resp_typ_eq {P} (pred_P : PredicativeSig P) : forall typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so_None ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m A',
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ A ≈ A' }} ->
      {{ Γ ⊢ M : A' ® m ∈ exp_rel }}.
Proof.
  simpl.
  intros.
  inversion_clear H.
  apply_predicate_equivalence.
  unfold top_sort_glu_exp_pred in *.
  destruct_conjs.
  split; mauto.
Qed.
Add Parametric Morphism {P} (pred_P : PredicativeSig P) typ_rel exp_rel a (H : glu_typ_elem pred_P so_None typ_rel exp_rel a) Γ : (exp_rel Γ)
    with signature wf_typ_eq Γ  ==> eq ==> eq ==> iff as glu_typ_elem_none_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_typ_elem_none_trm_resp_typ_eq;
    mauto 2.
Qed.

Lemma glu_typ_elem_some_trm_resp_typ_exp_eq {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m A',
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ A ≈ A' : Sort@s }} ->
      {{ Γ ⊢ M : A' ® m ∈ exp_rel }}.
Proof.
  simpl.
  intros.
  inversion_clear H.
  eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2.
Qed.
Add Parametric Morphism {P} (pred_P : PredicativeSig P) s typ_rel exp_rel a (H : glu_typ_elem pred_P (so_Some s) typ_rel exp_rel a) Γ : (exp_rel Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}}  ==> eq ==> eq ==> iff as glu_typ_elem_some_trm_morphism_iff1.
Proof.
  split; intros;
    eapply glu_typ_elem_some_trm_resp_typ_exp_eq;
    mauto 2.
Qed.

Lemma glu_typ_elem_typ_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A Γ',
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ ⊢ Γ ≈ Γ' }} ->
      {{ Γ' ⊢ A ® typ_rel }}.
Proof.
  simpl.
  induction 1 using glu_typ_elem_ind; intros;
    assert {{ ⊢ Γ' ⊆ Γ }} by mauto 3;
    simpl_glu_rel; mauto 2;
    eapply glu_sort_elem_typ_resp_ctx_eq; mauto 2.
Qed.
Add Parametric Morphism {P} (pred_P : PredicativeSig P) so typ_rel exp_rel a (H : glu_typ_elem pred_P so typ_rel exp_rel a) : typ_rel
    with signature wf_ctx_eq ==> eq ==> iff as glu_typ_elem_typ_morphism_iff2.
Proof.
  intros. split; intros;
    eapply glu_typ_elem_typ_resp_ctx_eq;
    mauto 2.
Qed.

Lemma glu_typ_elem_trm_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m Γ',
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ ⊢ Γ ≈ Γ' }} ->
      {{ Γ' ⊢ M : A ® m ∈ exp_rel }}.
Proof.
  simpl.
  induction 1 using glu_typ_elem_ind; intros;
    assert {{ ⊢ Γ' ⊆ Γ }} by mauto 3;
    simpl_glu_rel; mauto 2.
  - repeat split; mauto 3.
    do 2 eexists; split; mauto 4.
    eapply glu_sort_elem_typ_resp_ctx_eq; mauto 2.
  - eapply glu_sort_elem_trm_resp_ctx_eq; mauto 2.
Qed.
Add Parametric Morphism {P} (pred_P : PredicativeSig P) so typ_rel exp_rel a (H : glu_typ_elem pred_P so typ_rel exp_rel a) : exp_rel
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_typ_elem_trm_morphism_iff2.
Proof.
  intros. split; intros;
    eapply glu_typ_elem_trm_resp_ctx_eq;
    mauto 2.
Qed.

Lemma glu_typ_elem_trm_escape {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M : A }}.
Proof.
  simpl.
  intros.
  inversion_clear H.
  - apply_predicate_equivalence.
    unfold top_sort_glu_exp_pred in *.
    destruct_conjs.
    assert {{ Γ ⊢ M : Sort@s }} by (eapply glu_sort_elem_sort_lvl; mauto 2).
    mauto 3.
  - eapply glu_sort_elem_trm_escape; mauto 2.
Qed.

(* Duplicate of earlier 'glu_typ_elem_wf_typ' *)
Lemma glu_typ_elem_typ_escape {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A }}.
Proof.
  simpl.
  induction 1 using glu_typ_elem_ind; intros;
    simpl_glu_rel; mauto 4 using glu_sort_elem_typ_escape.
Qed.

Lemma glu_typ_elem_trm_typ {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ A ® typ_rel }}.
Proof.
  simpl.
  induction 1 using glu_typ_elem_ind; intros;
    simpl_glu_rel;
    mauto 4.
  eapply glu_sort_elem_trm_typ; mauto 2.
Qed.

Lemma glu_typ_elem_trm_sort_lvl {P} (pred_P : PredicativeSig P) : forall s typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P (so_Some s) ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros.
  inversion_clear H.
  eapply glu_sort_elem_trm_sort_lvl; mauto 2.
Qed.

Lemma glu_typ_elem_trm_resp_exp_eq {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m M',
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M ≈ M' : A }} ->
      {{ Γ ⊢ M' : A ® m ∈ exp_rel }}.
Proof.
  simpl.
  inversion_clear 1; intros; [| eapply glu_sort_elem_trm_resp_exp_eq; mauto 2];
    simpl_glu_rel;
    repeat split; mauto 3.
  repeat eexists; mauto 2.
  eapply glu_sort_elem_typ_resp_exp_eq; mauto 2.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) so typ_rel exp_rel a (H : glu_typ_elem pred_P so typ_rel exp_rel a) Γ T : (exp_rel Γ T)
    with signature wf_exp_eq Γ T ==> eq ==> iff as glu_typ_elem_trm_morphism_iff3.
Proof.
  split; intros;
    eapply glu_typ_elem_trm_resp_exp_eq;
    mauto 2.
Qed.

(** *** Simple Morphism instance for [glu_sort_elem] *)
Add Parametric Morphism {P} (pred_P : PredicativeSig P) s : (glu_sort_elem pred_P s)
    with signature glu_typ_pred_equivalence P ==> glu_exp_pred_equivalence P ==> eq ==> iff as simple_glu_sort_elem_morphism_iff.
Proof with mautosolve.
  intros typ_rel typ_rel' ? exp_rel exp_rel'.
  split; intro Horig; [gen exp_rel' typ_rel' | gen exp_rel typ_rel];
    induction Horig using glu_sort_elem_ind.
  1,5:
    intros;
    eapply glu_sort_elem_core_sort'; mauto 3;
    etransitivity; try eassumption; symmetry; eassumption.
  
  all:
    unshelve glu_sort_elem_econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto;
    split; intros; subst; mauto.
Qed.

(** *** Morphism instances for [neut_glu_*_pred]s *)
Add Parametric Morphism {P : PtsSig} (s : P) : (neut_glu_typ_pred s)
    with signature per_bot ==> eq ==> eq ==> iff as neut_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head (@per_bot P) ltac:(fun H => specialize (H (length Γ')) as [? []]);
    functional_read_rewrite_clear; intuition.
Qed.

Add Parametric Morphism {P : PtsSig} (s : P) : (neut_glu_typ_pred s)
    with signature per_bot ==> glu_typ_pred_equivalence P as neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_typ_pred_morphism_iff; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (s : P) : (neut_glu_exp_pred s)
    with signature per_bot ==> eq ==> eq ==> eq ==> eq ==> iff as neut_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition;
    match_by_head (@per_bot P) ltac:(fun H => specialize (H (length Γ')) as [? []]);
    functional_read_rewrite_clear; intuition;
    match_by_head (@per_bot P) ltac:(fun H => rewrite H in *); eassumption.
Qed.

Add Parametric Morphism {P : PtsSig} (s : P) : (neut_glu_exp_pred s)
    with signature per_bot ==> glu_exp_pred_equivalence P as neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; apply neut_glu_exp_pred_morphism_iff; mauto.
Qed.

(** *** Morphism instances for [pi_glu_*_pred]s *)
Add Parametric Morphism {P : PtsSig} {s1 s2 s3 s} (r : Ru_pi P s1 s2 s3) (sub_s3_s : st_subtyp s3 s) IR : (pi_glu_typ_pred r sub_s3_s IR)
    with signature glu_typ_pred_equivalence P ==> glu_exp_pred_equivalence P ==> eq ==> eq ==> eq ==> iff as pi_glu_typ_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism {P : PtsSig} {s1 s2 s3 s} (r : Ru_pi P s1 s2 s3) (sub_s3_s : st_subtyp s3 s) IR : (pi_glu_typ_pred r sub_s3_s IR)
    with signature glu_typ_pred_equivalence P ==> glu_exp_pred_equivalence P ==> eq ==> glu_typ_pred_equivalence P as pi_glu_typ_pred_morphism_glu_typ_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism {P : PtsSig} {s1 s2 s3 s} (r : Ru_pi P s1 s2 s3) (sub_s3_s : st_subtyp s3 s) IR : (pi_glu_exp_pred r sub_s3_s IR)
    with signature glu_typ_pred_equivalence P ==> glu_exp_pred_equivalence P ==> relation_equivalence ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff as pi_glu_exp_pred_morphism_iff.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.

Add Parametric Morphism {P : PtsSig} {s1 s2 s3 s} (r : Ru_pi P s1 s2 s3) (sub_s3_s : st_subtyp s3 s) IR : (pi_glu_exp_pred r sub_s3_s IR)
    with signature glu_typ_pred_equivalence P ==> glu_exp_pred_equivalence P ==> relation_equivalence ==> eq ==> glu_exp_pred_equivalence P as pi_glu_exp_pred_morphism_glu_exp_pred_equivalence.
Proof with mautosolve.
  split; intros []; econstructor; intuition.
Qed.


Lemma functional_glu_sort_elem {P} (pred_P : PredicativeSig P) : forall s a typ_rel typ_rel' exp_rel exp_rel',
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  simpl.
  intros * Ha Ha'. gen typ_rel' exp_rel'.
  induction Ha using glu_sort_elem_ind; intros; basic_invert_glu_sort_elem Ha';
    apply_predicate_equivalence; try solve [split; reflexivity].

  - clear_pi_sort_eq_and_pred_rel.
    assert ((IP <∙> IP0) /\ (IEL <∙> IEL0)) as [] by mauto 2.
    apply_predicate_equivalence.
    handle_per_sort_elem_irrel.
    (on_all_hyp: fun H => directed invert_per_sort_elem H).
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    
    split; [intros Γ C | intros Γ M C m].
    + split; intros []; econstructor; intuition;
        [rename equiv_m into equiv0_m; assert (equiv_m : in_rel m m) by intuition
        | assert (equiv0_m : in_rel0 m m) by intuition ];
        assert (equiv1_m : in_rel1 m m) by intuition;
        destruct_rel_mod_eval;
        functional_eval_rewrite_clear;
        specialize (H7 _ ltac:(eassumption) _ ltac:(eassumption));
        clear_pi_sort_eq_and_pred_rel;
        assert ((OP m equiv_m <∙> OP0 m equiv0_m) /\ (OEL m equiv_m <∙> OEL0 m equiv0_m)) as [] by mauto 3;
        intuition.
      
    + split; intros []; econstructor; intuition;
        [rename equiv_n into equiv0_n; assert (equiv_n : in_rel n n) by intuition
        | assert (equiv0_n : in_rel0 n n) by intuition];
        assert (equiv1_n : in_rel1 n n) by intuition;
        destruct_rel_mod_eval;
        [assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Γ' ⊢ M0[σ] N : OT[σ,,N] ® m0n ∈ OEL n equiv_n }}) by intuition
        | assert (exists m0n, {{ $| m0 & n |↘ m0n }} /\ {{ Γ' ⊢ M0[σ] N : OT[σ,,N] ® m0n ∈ OEL0 n equiv0_n }}) by intuition];
        destruct_conjs;
        functional_eval_rewrite_clear;
        specialize (H7 _ ltac:(eassumption) _ ltac:(eassumption));
        clear_pi_sort_eq_and_pred_rel;
        assert ((OP n equiv_n <∙> OP0 n equiv0_n) /\ (OEL n equiv_n <∙> OEL0 n equiv0_n)) as [] by mauto 3;
        eexists; split; intuition.

  - split; [solve_refl |].
    split; intros []; econstructor; mauto 2.
Qed.


Ltac apply_functional_glu_sort_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_sort_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DG ^?a ∈ glu_sort_elem ?pred_P ?s ↘ ?typ_rel1 ↘ ?exp_rel1 }},
      H2 : {{ DG ^?a ∈ glu_sort_elem ?pred_P ?s' ↘ ?typ_rel2 ↘ ?exp_rel2 }} |- _ =>
      match goal with
      | H : typ_rel1 <∙> typ_rel2, H0 : exp_rel1 <∙> exp_rel2 |- _ => fail 1
      | H : typ_rel1 <∙> typ_rel2, H0 : exp_rel2 <∙> exp_rel1 |- _ => fail 1
      | H : typ_rel2 <∙> typ_rel1, H0 : exp_rel1 <∙> exp_rel2 |- _ => fail 1
      | H : typ_rel2 <∙> typ_rel1, H0 : exp_rel2 <∙> exp_rel1 |- _ => fail 1
      | _ => assert ((typ_rel1 <∙> typ_rel2) /\ (exp_rel1 <∙> exp_rel2)) as [] by (eapply functional_glu_sort_elem; [apply H1 | apply H2]) || tactic_error typ_rel1 typ_rel2
      end
  end.

Ltac apply_functional_glu_sort_elem :=
  repeat apply_functional_glu_sort_elem1.

Ltac handle_functional_glu_sort_elem P :=
  functional_eval_rewrite_clear;
  fold (glu_typ_pred P) in *;
  fold (glu_exp_pred P) in *;
  apply_functional_glu_sort_elem;
  apply_predicate_equivalence;
  clear_dups.


Lemma functional_glu_typ_elem {P} (pred_P : PredicativeSig P) : forall so a typ_rel typ_rel' exp_rel exp_rel',
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  simpl.
  intros * Ha Ha'.
  inversion Ha; subst;
    inversion_clear Ha'; [ | eapply functional_glu_sort_elem; mauto 2].
  split; etransitivity; try eassumption;
    symmetry; eassumption.
Qed.

Ltac apply_functional_glu_typ_elem1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_sort_elem biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ DG ^?a ∈ glu_typ_elem ?pred_P ?so ↘ ?typ_rel1 ↘ ?exp_rel1 }},
      H2 : {{ DG ^?a ∈ glu_typ_elem ?pred_P ?so ↘ ?typ_rel2 ↘ ?exp_rel2 }} |- _ =>
      match goal with
      | H : typ_rel1 <∙> typ_rel2, H0 : exp_rel1 <∙> exp_rel2 |- _ => fail 1
      | H : typ_rel1 <∙> typ_rel2, H0 : exp_rel2 <∙> exp_rel1 |- _ => fail 1
      | H : typ_rel2 <∙> typ_rel1, H0 : exp_rel1 <∙> exp_rel2 |- _ => fail 1
      | H : typ_rel2 <∙> typ_rel1, H0 : exp_rel2 <∙> exp_rel1 |- _ => fail 1
      | _ => assert ((typ_rel1 <∙> typ_rel2) /\ (exp_rel1 <∙> exp_rel2)) as [] by (eapply functional_glu_typ_elem; [apply H1 | apply H2]) || tactic_error typ_rel1 typ_rel2
      end
  end.

Ltac apply_functional_glu_typ_elem :=
  repeat apply_functional_glu_typ_elem1.

Ltac handle_functional_glu_typ_elem P :=
  functional_eval_rewrite_clear;
  fold (glu_typ_pred P) in *;
  fold (glu_exp_pred P) in *;
  apply_functional_glu_typ_elem;
  apply_predicate_equivalence;
  clear_dups.



Lemma glu_sort_elem_pi_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 s a ρ B in_rel typ_rel exp_rel} {r : Ru_pi P s1 s2 s3} (sub_s3_s : st_subtyp s3 s),
  {{ DF a ≈ a ∈ per_sort_elem pred_P s1 ↘ in_rel }} ->
  {{ DG Π r a ρ B ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
  exists IP IEl (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred P)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred P) elem_rel,
      {{ DG a ∈ glu_sort_elem pred_P s1 ↘ IP ↘ IEl }} /\
        (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
            {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP c equiv_c ↘ OEl c equiv_c }}) /\
        {{ DF Π r a ρ B ≈ Π r a ρ B ∈ per_sort_elem pred_P s ↘ elem_rel }} /\
        (typ_rel <∙> pi_glu_typ_pred r sub_s3_s in_rel IP IEl OP) /\
        (exp_rel <∙> pi_glu_exp_pred r sub_s3_s in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hglu.
  basic_invert_glu_sort_elem Hglu.
  handle_per_sort_elem_irrel.
  handle_functional_glu_sort_elem P.
  clear_pi_sort_eq_and_pred_rel.
  do 5 eexists; repeat split; try eassumption.
  1: instantiate (1 := fun c equiv_c Γ A M m => forall (b : domain P) Pb Elb,
                           {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                           {{ DG b ∈ glu_sort_elem pred_P s2 ↘ Pb ↘ Elb }} ->
                           {{ Γ ⊢ M : A ® m ∈ Elb }}).
  1: instantiate (1 := fun c equiv_c Γ A => forall (b : domain P) Pb Elb,
                           {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
                           {{ DG b ∈ glu_sort_elem pred_P s2 ↘ Pb ↘ Elb }} ->
                           {{ Γ ⊢ A ® Pb }}).
  2-5: intros []; econstructor; mauto.
  all: intros.  
  - assert {{ Dom c ≈ c ∈ in_rel0 }} as equiv0_c by intuition.
    pose proof (H0 _ equiv0_c _ ltac:(eassumption)).
    clear_pi_sort_eq_and_pred_rel.
    assert {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP c equiv0_c ↘ OEL c equiv0_c }} by mauto 2.
    apply -> simple_glu_sort_elem_morphism_iff; [| reflexivity | |]; [eauto | |].
    + intros ? ? ? ?.
      split; intros; handle_functional_glu_sort_elem P; intuition.
    + intros ? ?.
      split; [intros; handle_functional_glu_sort_elem P |]; intuition.
  - assert {{ Dom m ≈ m ∈ in_rel0 }} as equiv0_m by intuition.
    pose proof (H0 _ equiv0_m _ ltac:(eassumption)).
    clear_pi_sort_eq_and_pred_rel.
    assert {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP m equiv0_m ↘ OEL m equiv0_m }} by mauto 2.
    handle_functional_glu_sort_elem P.
    intuition.
  - match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    rename equiv_m into equiv0_m.
    assert (equiv1_m : in_rel1 m m) by intuition.
    destruct_rel_mod_eval.
    functional_eval_rewrite_clear.
    pose proof (H0 _ ltac:(eassumption) _ ltac:(eassumption)).
    clear_pi_sort_eq_and_pred_rel.
    assert (glu_sort_elem pred_P s2 (OP m equiv0_m) (OEL m equiv0_m) a0) by mauto 2.
    intuition.

  - assert {{ Dom n ≈ n ∈ in_rel0 }} as equiv0_n by intuition.
    assert (exists mn : domain P, {{ $| m & n |↘ mn }} /\ {{ Γ' ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEL n equiv0_n }}) by mauto 3.
    destruct_conjs.
    eexists.
    split; mauto 2.
    intros.
    pose proof (H0 _ ltac:(eassumption) _ ltac:(eassumption)).
    clear_pi_sort_eq_and_pred_rel.
    assert (glu_sort_elem pred_P s2 (OP n equiv0_n) (OEL n equiv0_n) b) by mauto 2.
    handle_functional_glu_sort_elem P.
    eassumption.

  - assert (exists mn : domain P,
               {{ $| m & n |↘ mn }} /\
                 (forall (b : domain P) (Pb : glu_typ_pred P) (Elb : glu_exp_pred P),
                     {{ ⟦ B ⟧ ρ ↦ n ↘ b }} ->
                     {{ DG b ∈ glu_sort_elem pred_P s2 ↘ Pb ↘ Elb }} ->
                     {{ Γ' ⊢ M[σ] N : OT[σ,,N] ® mn ∈ Elb }})) by intuition.
    destruct_conjs.
    match_by_head (@per_sort_elem P) ltac:(fun H => directed invert_per_sort_elem H).
    handle_per_sort_elem_irrel.
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    assert (equiv1_n : in_rel1 n n) by intuition.    
    destruct_rel_mod_eval.
    functional_eval_rewrite_clear.
    pose proof (H0 _ equiv_n _ ltac:(eassumption)).
    clear_pi_sort_eq_and_pred_rel.
    assert (glu_sort_elem pred_P s2 (OP n equiv_n) (OEL n equiv_n) a0) by mauto 2.
    eexists; intuition.
Qed.


Lemma glu_sort_elem_pi_clean_inversion2 {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 s a ρ B in_rel IP IEl typ_rel exp_rel} {r : Ru_pi P s1 s2 s3} (sub_s3_s : st_subtyp s3 s),
  {{ DF a ≈ a ∈ per_sort_elem pred_P s1 ↘ in_rel }} ->
  {{ DG a ∈ glu_sort_elem pred_P s1 ↘ IP ↘ IEl }} ->
  {{ DG Π r a ρ B ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
  exists (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred P)
     (OEl : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred P) elem_rel,
    (forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
        {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
        {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP c equiv_c ↘ OEl c equiv_c }}) /\
      {{ DF Π r a ρ B ≈ Π r a ρ B ∈ per_sort_elem pred_P s ↘ elem_rel }} /\
      (typ_rel <∙> pi_glu_typ_pred r sub_s3_s in_rel IP IEl OP) /\
      (exp_rel <∙> pi_glu_exp_pred r sub_s3_s in_rel IP IEl elem_rel OEl).
Proof.
  intros *.
  simpl.
  intros Hinper Hinglu Hglu.
  unshelve eapply (glu_sort_elem_pi_clean_inversion1 pred_P sub_s3_s _) in Hglu;
    shelve_unifiable; [eassumption |];
    destruct Hglu as [? [? [? [? [? [? [? [? []]]]]]]]].
  handle_functional_glu_sort_elem P.
  do 3 eexists.
  repeat split; try eassumption;
    intros []; econstructor; mauto.
Qed.

Ltac invert_glu_sort_elem H :=
  (unshelve eapply (glu_sort_elem_pi_clean_inversion2 _ _ _ _) in H; shelve_unifiable; [eassumption | eassumption |];
   destruct H as [? [? [? [? [? []]]]]])
  + (unshelve eapply (glu_sort_elem_pi_clean_inversion1 _ _ _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? [? [? [? [? [? [? []]]]]]]]])
  + basic_invert_glu_sort_elem H.


#[local]
Ltac resp_per_IH :=
  match_by_head1 glu_sort_elem
    ltac:(fun H =>
            match goal with
            | H' : _ |- _ => eapply H' in H
            end);
  eauto; intuition.


Lemma glu_sort_elem_resp_per_sort_elem {P} (pred_P : PredicativeSig P) : forall s a a' R,
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    forall typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} /\
      (forall Γ M A m m',
          {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
          {{ Dom m ≈ m' ∈ R }} ->
          {{ Γ ⊢ M : A ® m' ∈ exp_rel }}).
Proof.
  simpl.
  intros * Hper * Horig.
  pose proof Hper.
  gen typ_rel exp_rel.

  induction Hper using per_sort_elem_ind; intros; subst;
    saturate_refl_for (@per_sort_elem P);
    (unshelve invert_glu_sort_elem Horig; try eassumption; shelve_unifiable);
    split;
    try glu_sort_elem_econstructor;
    try eassumption; mauto 3;
    intros;
    handle_per_sort_elem_irrel;
    handle_functional_glu_sort_elem P;
    simpl in *;
    destruct_all;
    mauto 3.
  
  
  - repeat split; eauto.
    unfold glu_sort_typ_rec in *.
    destruct_conjs.
    do 2 eexists; split; mauto.
    resp_per_IH.
  - rename x into IP, x0 into IEL.
    destruct_conjs.
    clear_pi_sort_eq_and_pred_rel.
    resp_per_IH.
    subst.
    mauto.
  - invert_per_sort_elem H.
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    assert (equiv0_c : in_rel0 c c) by intuition.
    destruct_rel_mod_eval.
    handle_per_sort_elem_irrel.
    rename x into IP, x0 into IEL, x1 into OP, x2 into OEL.
    enough (glu_sort_elem pred_P s_out (OP c equiv_c) (OEL c equiv_c) b) by (split; intros; subst; eassumption).
    clear_pi_sort_eq_and_pred_rel.
    assert (glu_sort_elem pred_P s_out (OP c equiv_c) (OEL c equiv_c) a0) by mauto 2.
    resp_per_IH.
    
  - reflexivity. 
  - simpl_glu_rel.
    invert_per_sort_elem H10.
    econstructor; mauto 3.
    + intros.
      assert (in_rel n n) by (transitivity n'; [| symmetry]; eassumption).
      assert (in_rel n' n') by (transitivity n; [symmetry |]; eassumption).
      assert (in_rel n' n) by intuition.

      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.

      handle_per_sort_elem_irrel.
      apply_relation_equivalence.
      
      econstructor; mauto 2.
      
      transitivity fa1.
      * symmetry; eassumption.
      * eapply H37; eassumption.
        
    + resp_per_IH.
      destruct_rel_mod_eval.
      handle_per_sort_elem_irrel.
      pose proof (H9 _ equiv_n _ H25).
      eapply H28 in H27 as []; eauto.
      
      
      destruct (H17 _ _ _ _ H23 H24 equiv_n) as [? []].
      destruct (H18 _ _ equiv_n) as [].
      simplify_evals.
      eauto.

  - apply neut_glu_typ_pred_morphism_glu_typ_pred_equivalence.
    eassumption.
  - apply neut_glu_exp_pred_morphism_glu_exp_pred_equivalence.
    eassumption.
  - simpl_glu_rel.
    progressive_invert H9.
    econstructor; unfold neut_glu_typ_pred; mauto 3.
    intros.
    specialize (H9 (length Γ')).
    destruct_all.
    functional_read_rewrite_clear.
    mauto.
Qed.


Lemma glu_sort_elem_resp_per_sort {P} (pred_P : PredicativeSig P) : forall s a a' typ_rel exp_rel,
    {{ Dom a ≈ a' ∈ per_sort pred_P s }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}.
Proof.
  intros * [? H] ?.
  eapply glu_sort_elem_resp_per_sort_elem in H; eauto.
  intuition.
Qed.

Lemma glu_sort_elem_resp_per_elem {P} (pred_P : PredicativeSig P) : forall s a a' R typ_rel exp_rel Γ M A m m',
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Dom m ≈ m' ∈ R }} ->
    {{ Γ ⊢ M : A ® m' ∈ exp_rel }}.
Proof.
  intros * H ?.
  eapply glu_sort_elem_resp_per_sort_elem in H; eauto.
  intuition.
Qed.


(** *** Morphism instances for [glu_sort_elem] *)
Add Parametric Morphism {P} (pred_P : PredicativeSig P) s : (glu_sort_elem pred_P s)
    with signature glu_typ_pred_equivalence P ==> glu_exp_pred_equivalence P ==> per_sort pred_P s ==> iff as glu_sort_elem_morphism_iff.
Proof with mautosolve.
  intros typ_rel typ_rel' HPP' exp_rel exp_rel' HElEl' a a' Haa'.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_sort_elem_resp_per_sort; mauto.
  symmetry; eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s R : (glu_sort_elem pred_P s)
    with signature glu_typ_pred_equivalence P ==> glu_exp_pred_equivalence P ==> per_sort_elem pred_P s R ==> iff as glu_sort_elem_morphism_iff'.
Proof with mautosolve.
  intros typ_rel typ_rel' HPP' exp_rel exp_rel' HElEl' **.
  rewrite HPP', HElEl'.
  split; intros; eapply glu_sort_elem_resp_per_sort; mauto.
  symmetry; mauto.
Qed.

Ltac saturate_glu_by_per1 :=
  match goal with
  | H : glu_sort_elem ?pred_P ?s ?typ_rel ?exp_rel ?a,
      H1 : per_sort_elem ?pred_P ?s _ ?a ?a' |- _ =>
      assert (glu_sort_elem pred_P s typ_rel exp_rel a') by (rewrite <- H1; eassumption);
      fail_if_dup
  | H : glu_sort_elem ?pred_P ?s ?typ_rel ?exp_rel ?a',
      H1 : per_sort_elem ?pred_P ?s _ ?a ?a' |- _ =>
      assert (glu_sort_elem pred_P s typ_rel exp_rel a) by (rewrite H1; eassumption);
      fail_if_dup
  end.

Ltac saturate_glu_by_per :=
  clear_dups;
  repeat saturate_glu_by_per1.

Lemma per_sort_glu_sort_elem {P} (pred_P : PredicativeSig P) : forall s a,
    {{ Dom a ≈ a ∈ per_sort pred_P s }} ->
    exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}.
Proof.
  simpl.
  intros * [? Hper].
  induction Hper using per_sort_elem_ind; intros;
    try solve [do 2 eexists; unshelve (glu_sort_elem_econstructor; try reflexivity; subst; trivial)].

  - destruct_conjs.
    do 2 eexists.
    subst.
    glu_sort_elem_econstructor; try (eassumption + reflexivity).
  
  - destruct_conjs.
    do 2 eexists.
    unshelve glu_sort_elem_econstructor; only 1: eassumption; shelve_unifiable; try (eassumption + reflexivity).
    + saturate_refl; split; intros; subst; eassumption.
    + transitivity a; [symmetry|]; eassumption.
    + instantiate (1 := fun (c : domain P) (equiv_c : in_rel c c) Γ A M m =>
                          forall b OP OEL,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_sort_elem pred_P s_out OP OEL b ->
                            {{ Γ ⊢ M : A ® m ∈ OEL }}).
      instantiate (1 := fun (c : domain P) (equiv_c : in_rel c c) Γ A =>
                          forall b OP OEL,
                            {{ ⟦ B' ⟧ ρ' ↦ c ↘ b }} ->
                            glu_sort_elem pred_P s_out OP OEL b ->
                            {{ Γ ⊢ A ® OP }}).

      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      handle_per_sort_elem_irrel.
      split; intros; subst;
        rewrite simple_glu_sort_elem_morphism_iff; try (eassumption + reflexivity);
        split; intros; handle_functional_glu_sort_elem P; intuition.

    + enough {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s_elem ↘ elem_rel }} by (etransitivity; [symmetry |]; eassumption).
      per_sort_elem_econstructor; mauto.
      intros.
      (on_all_hyp: destruct_rel_by_assumption in_rel).
      econstructor; mauto.
    
  - saturate_refl.
    do 2 eexists.
    unshelve glu_sort_elem_econstructor; [| eassumption | | |]; eauto; reflexivity.

  - saturate_refl.
    do 2 eexists.
    glu_sort_elem_econstructor; eauto; reflexivity.
Qed.

#[export]
Hint Resolve per_sort_glu_sort_elem : mcpts.

Corollary per_sort_elem_glu_sort_elem {P} (pred_P : PredicativeSig P) : forall s a R,
    {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} ->
    exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}.
Proof.
  intros.
  apply per_sort_glu_sort_elem; mauto.
Qed.

#[export]
Hint Resolve per_sort_elem_glu_sort_elem : mcpts.

Ltac saturate_glu_info1 :=
  match goal with
  | H : glu_sort_elem _ _ ?typ_rel _ _,
      H1 : ?typ_rel _ _ |- _ =>
      pose proof (glu_sort_elem_sort_lvl _ _ _ _ _ H _ _ H1);
      fail_if_dup
  | H : glu_sort_elem _ _ _ ?exp_rel _,
      H1 : ?exp_rel _ _ _ _ |- _ =>
      pose proof (glu_sort_elem_trm_escape _ _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  | H : glu_typ_elem _ (so_Some ?s) ?typ_rel _ _,
      H1 : ?typ_rel _ _ |- _ =>
      pose proof (glu_typ_elem_sort_lvl _ _ _ _ _ H _ _ H1);
      fail_if_dup
  | H : glu_typ_elem _ so_None ?typ_rel _ _,
      H1 : ?typ_rel _ _ |- _ =>
      pose proof (glu_typ_elem_wf_typ _ _ _ _ _ H _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_info :=
  clear_dups;
  repeat saturate_glu_info1.

#[local]
Hint Rewrite -> @sub_decompose_q using solve [mauto 4] : mcpts.

Lemma glu_nat_monotone {P} {s} (r : Ru_nat P s) : forall Γ M m,
    {{ ⊢ Γ }} ->
    glu_nat r Γ M m ->
    forall Γ' σ,
      {{ Γ' ⊢w σ : Γ }} ->
      glu_nat r Γ' {{{ M[σ] }}} m.
Proof.
  intros * HΓ Hglu.
  assert {{ Γ ⊢ M : ℕ }} by mauto 2.
  induction Hglu; intros; econstructor; mauto 2.
  - transitivity {{{ zero[σ] }}}; mauto 3.
  - transitivity {{{ (succ M')[σ] }}}; mauto 3.
    econstructor; mauto 3.
  - eapply IHHglu; mauto 3.
  - intros.
    assert {{ Γ'0 ⊢w σ∘σ0 : Γ }} by mauto.
    assert {{ Γ'0 ⊢ M[σ∘σ0] ≈ M' : ℕ }} by mauto 3.
    transitivity {{{ M[σ∘σ0] }}}; mauto 3.
    eapply (@wf_exp_eq_sub_compose_nat _ _ _ _ M σ σ0 s r); mauto 3.
Qed.

Lemma glu_sort_elem_mut_monotone {P} (pred_P : PredicativeSig P) : forall s a typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ' σ Γ,
      {{ Γ' ⊢w σ : Γ }} ->
      (forall A,
        {{ Γ ⊢ A ® typ_rel }} ->
        {{ Γ' ⊢ A[σ] ® typ_rel }}) /\
    (forall M A m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ' ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}).
Proof.
  simpl. induction 1 using glu_sort_elem_ind;
    split; intros;
    saturate_weakening_escape;
    handle_functional_glu_sort_elem P;
    simpl in *;
    destruct_all;
    try solve [bulky_rewrite].

  - assert {{ ⊢ Γ' }} by mauto 2.
    assert {{ Γ' ⊢ Sort@s' ⊆ Sort@s }} by mauto 2.
    assert {{ Γ' ⊢ Sort@s'' : Sort@s }} by mauto 3.
    assert {{ ⊢ Γ }} by mauto 2.
    assert {{ Γ ⊢ Sort@s' ⊆ Sort@s }} by mauto 2.
    assert {{ Γ ⊢ Sort@s'' : Sort@s }} by mauto 3.
    transitivity {{{ Sort@s''[σ] }}}; mauto 3.
    
  - gen_presups; repeat eexists; mauto 2; bulky_rewrite.
    + assert {{ ⊢ Γ' }} by mauto 2.
      assert {{ Γ' ⊢ Sort@s' ⊆ Sort@s }} by mauto 2.
      assert {{ Γ' ⊢ Sort@s'' : Sort@s }} by mauto 3.
      mauto 3.
    + assert {{ ⊢ Γ' }} by mauto 2.
      assert {{ Γ' ⊢ Sort@s' ⊆ Sort@s }} by mauto 2.
      mauto 3.
    + resp_per_IH.
  - destruct H7.
    simpl_glu_rel.
    econstructor; eauto; try solve [bulky_rewrite]; mauto 3.
    + transitivity {{{ (Π r IT OT)[σ] }}}; mauto 3.
      eapply wf_exp_eq_conv with (A := {{{ Sort@s3 }}}); mauto 3.
    + intros.
      eapply IHglu_sort_elem; eauto.
    + intros.
      saturate_weakening_escape.
      saturate_glu_info.
      invert_per_sort_elem H3.
      assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto).
      handle_per_sort_elem_irrel.
      assert (in_rel0 m m) by intuition.
      destruct_rel_mod_eval.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      assert {{ Γ'0 ⊢s (q σ)∘(σ0,,M) ≈ σ∘σ0,,M : Γ, IT }} by mauto.
      assert {{ Γ', IT[σ] ⊢s q σ : Γ, IT }} by mauto 3.
      assert {{ Γ'0 ⊢s σ0,,M : Γ', IT[σ] }} by mauto 4.
      assert {{ Γ'0 ⊢ OT[q σ][σ0,,M] ≈ OT[(q σ)∘(σ0,,M)] : Sort@s2 }} by mauto.
      assert {{ Γ'0 ⊢ OT[q σ][σ0,,M] ≈ OT[σ∘σ0,,M] : Sort@s2 }} by mauto.
      enough (OP m equiv_m Γ'0 {{{ OT[σ∘σ0,,M] }}}) by (eapply glu_sort_elem_typ_resp_exp_eq; mauto 2).
      eapply H11; mauto.
      assert {{ Γ'0 ⊢ IT[σ∘σ0] ≈ IT[σ][σ0] : Sort@s1 }} by mauto 4.
      enough (IEL Γ'0 {{{ IT[σ][σ0] }}} M m) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto).
      eassumption.

  - destruct H7.
    simpl_glu_rel.
    econstructor; mauto 4;
      intros;
      saturate_weakening_escape.
    + transitivity {{{ (Π r IT OT)[σ] }}}; mauto 3.
      eapply wf_exp_eq_conv with (A := {{{ Sort@s3 }}}); mauto 3.
    + eapply IHglu_sort_elem; eauto.
    + saturate_glu_info.
      invert_per_sort_elem H3.
      apply_equiv_left.
      assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto).
      handle_per_sort_elem_irrel.
      assert (in_rel0 n n) by intuition.
      destruct_rel_mod_eval.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      autorewrite with mcpts in *.
      repeat eexists; eauto.
      assert {{ Γ'0 ⊢s σ0,,N : Γ', IT[σ] }} by mauto 4.
      assert {{ Γ ⊢ M : Π r IT OT }} by mauto.
      assert {{ Γ' ⊢ M[σ] : (Π r IT OT)[σ] }} by mauto 3.
      assert {{ Γ'0 ⊢ M[σ][σ0] : (Π r IT OT)[σ][σ0] }} by mauto 4.
      assert {{ Γ'0 ⊢ (Π r IT OT)[σ][σ0] ≈ (Π r IT OT)[σ∘σ0] }} by (symmetry; mauto 3).
      assert {{ Γ'0 ⊢ M[σ][σ0] ≈ M[σ∘σ0] : (Π r IT OT)[σ][σ0] }} by mauto.
      assert {{ Γ'0 ⊢ (Π r IT OT)[σ∘σ0] ≈ Π r IT[σ∘σ0] OT[q (σ∘σ0)] }} by mauto 4.
      assert {{ Γ'0 ⊢ M[σ][σ0] ≈ M[σ∘σ0] : Π r IT[σ∘σ0] OT[q (σ∘σ0)] }} by mauto.
      assert {{ Γ'0 ⊢ IT[σ∘σ0] : Sort@s1 }} by mauto 4.
      assert {{ Γ'0 ⊢ IT[σ∘σ0] ≈ IT[σ][σ0] : Sort@s1 }} by mauto.
      assert {{ Γ'0, IT[σ∘σ0] ⊢ #0 : IT[(σ∘σ0)][Wk] }} by (eapply wf_exp_vlookup; econstructor; mauto 2).
      assert {{ Γ'0, IT[σ∘σ0] ⊢ IT[(σ∘σ0)∘Wk] ≈ IT[σ∘σ0][Wk] : Sort@s1[(σ∘σ0)∘Wk] }} by (eapply wf_exp_eq_sub_compose; mauto 3).
      gen_presup H39.
      assert {{ Γ'0, IT[σ∘σ0] ⊢s (σ∘σ0)∘Wk : Γ }} by mauto 4.
      assert {{ Γ'0, IT[σ∘σ0] ⊢ Sort@s1[(σ∘σ0)∘Wk] ≈ Sort@s1 }} by mauto 4.
      assert {{ Γ'0, IT[σ∘σ0] ⊢ IT[(σ∘σ0)∘Wk] ≈ IT[σ∘σ0][Wk] : Sort@s1 }} by mauto 3.  
      assert {{ Γ'0, IT[σ∘σ0] ⊢ #0 : IT[(σ∘σ0)∘Wk] }} by mauto 3.
      assert {{ Γ'0, IT[σ∘σ0] ⊢ OT[q (σ∘σ0)] : Sort@s2 }} by mauto 4.
      assert {{ Γ'0 ⊢ M[σ][σ0] N ≈ M[σ∘σ0] N : OT[q (σ∘σ0)][Id,,N] }} by (eapply wf_exp_eq_app_cong; mauto 4).
      assert {{ Γ'0 ⊢ OT[(q (σ∘σ0))∘(Id,,N)] ≈ OT[q (σ∘σ0)][Id,,N] : Sort@s2[(q (σ∘σ0))∘(Id,,N)] }} by (eapply wf_exp_eq_sub_compose; mauto 4).
      assert {{ Γ'0 ⊢s Id,,N : Γ'0, IT[σ∘σ0] }} by mauto 4.
      assert {{ Γ'0 ⊢ Sort@s2[(q (σ∘σ0))∘(Id,,N)] ≈ Sort@s2 }} by mauto 5.
      assert {{ Γ'0 ⊢ OT[(q (σ∘σ0))∘(Id,,N)] ≈ OT[q (σ∘σ0)][Id,,N] : Sort@s2 }} by mauto 3. 
      assert {{ Γ'0 ⊢s (q (σ∘σ0))∘(Id,,N) ≈ σ∘σ0,,N : Γ, IT }} by (eapply wf_sub_eq_q_sigma_id_extend; mauto 3).
      assert {{ Γ, IT ⊢ OT ≈ OT : Sort@s2 }} by mauto 3.
      assert {{ Γ'0 ⊢ OT[(q (σ∘σ0))∘(Id,,N)] ≈ OT[σ∘σ0,,N] : Sort@s2 }} by mauto 3.
      assert {{ Γ'0 ⊢ OT[q (σ∘σ0)][Id,,N] ≈ OT[σ∘σ0,,N] : Sort@s2 }} by mauto.
      assert {{ Γ'0 ⊢ M[σ][σ0] N ≈ M[σ∘σ0] N : OT[σ∘σ0,,N] }} by mauto.
      assert {{ Γ'0 ⊢s (q σ)∘(σ0,,N) ≈ (σ∘σ0),,N : Γ, IT }} by mauto 3.
      assert {{ Γ'0 ⊢ OT[(q σ)∘(σ0,,N)] ≈ OT[q σ][σ0,,N] : Sort@s2 }} by mauto.
      assert {{ Γ'0 ⊢ OT[(q σ)∘(σ0,,N)] ≈ OT[σ∘σ0,,N] : Sort@s2 }} by mauto 4.
      assert {{ Γ'0 ⊢ OT[q σ][σ0,,N] ≈ OT[σ∘σ0,,N] : Sort@s2 }} by mauto.
      enough (OEL n equiv_n Γ'0 {{{ OT[σ∘σ0,,N] }}} {{{ M[σ][σ0] N }}} fa) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3).
      enough (OEL n equiv_n Γ'0 {{{ OT[σ∘σ0,,N] }}} {{{ M[σ∘σ0] N }}} fa) by (eapply glu_sort_elem_trm_resp_exp_eq; mauto 3).
      assert (IEL Γ'0 {{{ IT[σ∘σ0] }}} N n) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3).
      assert (exists mn : domain P, {{ $| m & n |↘ mn }} /\ OEL n equiv_n Γ'0 {{{ OT[σ∘σ0,,N] }}} {{{ M[σ∘σ0] N }}} mn) by mauto 3.
      destruct_conjs.
      simplify_evals.
      eassumption.

  - transitivity {{{ ℕ[σ] }}}; mauto 3.
    eapply wf_exp_eq_conv; mauto 3.
  - split.
    + transitivity {{{ ℕ[σ] }}}; mauto 3.
      eapply wf_exp_eq_conv; mauto 3.
    + gen_presup H3.
      eapply glu_nat_monotone; mauto 2.

  - destruct_conjs.
    split; [mauto 3 |].
    intros.
    saturate_weakening_escape.
    transitivity {{{ A[σ∘σ0] }}}.
    + symmetry.
      mauto.
    + eapply H1; mauto.

  - simpl_glu_rel.
    econstructor; repeat split; mauto 3;
      intros;
      saturate_weakening_escape.
    + transitivity {{{ A[σ∘σ0] }}}.
      * symmetry.
        mauto.
      * eapply H1; mauto.
    + transitivity {{{ M[σ∘σ0] }}}.
      * symmetry; mauto 4.
      * enough {{ Γ'0 ⊢ M[σ∘σ0] ≈ M' : A[σ∘σ0] }} by mauto.
        eapply H5; mauto.
Qed.


Lemma glu_sort_elem_typ_monotone {P} (pred_P : PredicativeSig P) : forall s a typ_rel exp_rel Γ' σ Γ A,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ' ⊢w σ : Γ }} ->
    {{ Γ' ⊢ A[σ] ® typ_rel }}.
Proof.
  intros * H; intros.
  eapply glu_sort_elem_mut_monotone in H; eauto.
  intuition.
Qed.

Lemma glu_sort_elem_exp_monotone {P} (pred_P : PredicativeSig P) : forall s a typ_rel exp_rel Γ' σ Γ M A m,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ' ⊢w σ : Γ }} ->
    {{ Γ' ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}.
Proof.
  intros * H; intros.
  eapply glu_sort_elem_mut_monotone in H; eauto.
  intuition.
Qed.

Lemma glu_typ_elem_typ_monotone {P} (pred_P : PredicativeSig P) : forall so a typ_rel exp_rel Γ' σ Γ A,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ' ⊢w σ : Γ }} ->
    {{ Γ' ⊢ A[σ] ® typ_rel }}.
Proof.
  intros * H; intros.
  inversion H; subst.
  - apply_predicate_equivalence.
    unfold top_sort_glu_typ_pred in *.
    gen_presups.
    assert {{ Γ' ⊢ Sort@s[σ] ≈ Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[σ] ≈ Sort@s[σ] }} by mauto 3.
    mautosolve 3.
  - eapply glu_sort_elem_typ_monotone; mauto 3.
Qed.

Lemma glu_typ_elem_exp_monotone {P} (pred_P : PredicativeSig P) : forall so a typ_rel exp_rel Γ' σ Γ M A m,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ' ⊢w σ : Γ }} ->
    {{ Γ' ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}.
Proof.
  intros * H; intros.
  inversion H; subst.
  - apply_predicate_equivalence.
    unfold top_sort_glu_exp_pred in *.
    destruct_conjs.
    assert {{ Γ' ⊢ Sort@s[σ] ≈ Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[σ] ≈ Sort@s[σ] }} by mauto 3.
    split; mauto 3.
    repeat eexists; mauto 3.
    eapply glu_sort_elem_typ_monotone; mauto 3.
  - eapply glu_sort_elem_exp_monotone; mauto 3.
Qed.


(* Lemma wf_typ_eq_implies_wf_exp_eq {P} (pred_P : PredicativeSig P) *)


Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a : (glu_elem_bot pred_P so a)
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4; [rewrite <- HΓΓ' | | rewrite -> HΓΓ']; try eassumption.

  intros.
  eapply H3; mauto 2.
  eapply weakening_conv; mauto 3.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ : (glu_elem_bot pred_P (so_Some s) a Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2_sorted.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    try split; intros;
    try assert {{ Γ' ⊢ A[σ] ≈ A'[σ] : Sort@s }} as HAσA'σ by mauto 4;
    try eapply wf_exp_eq_conv';
    mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) a Γ : (glu_elem_bot pred_P so_None a Γ)
    with signature wf_typ_eq Γ ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2_unsorted.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    [rewrite <- HAA' | | rewrite -> HAA' |];
    try eassumption;
    try split; intros;
    try assert {{ Γ' ⊢ A[σ] ≈ A'[σ] }} as HAσA'σ by mauto 4;
    try eapply wf_exp_eq_conv';
    mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a Γ A : (glu_elem_bot pred_P so a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3.
Proof.
  intros M M' HMM' *.

  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Γ ⊢ A }} by (eapply glu_typ_elem_typ_escape; mauto 2);
    saturate_weakening_escape;
    assert {{ Γ' ⊢ M[σ] ≈ M'[σ] : A[σ] }} as HMσM'σ by mauto 4;
    [rewrite <- HMσM'σ | rewrite -> HMσM'σ ];
    mauto 3.
Qed.


(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a : (glu_elem_bot pred_P s a) *)
(*     with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff1. *)
(* Proof. *)
(*   intros Γ Γ' HΓΓ' *. *)
(*   split; intros []; econstructor; mauto 4; [rewrite <- HΓΓ' | | rewrite -> HΓΓ']; try eassumption. *)

(*   intros. *)
(*   eapply H3; mauto 2. *)
(*   eapply weakening_conv; mauto 3. *)
(* Qed. *)

(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ : (glu_elem_bot pred_P s a Γ) *)
(*     with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as glu_elem_bot_morphism_iff2. *)
(* Proof. *)
(*   intros A A' HAA' *. *)
(*   split; intros []; econstructor; mauto 3; *)
(*     [rewrite <- HAA' | | rewrite -> HAA' |]; *)
(*     try eassumption; *)
(*     try split; intros; *)
(*     try assert {{ Γ' ⊢ A[σ] ≈ A'[σ] : Sort@s }} as HAσA'σ by mauto 4; *)
(*     try eapply wf_exp_eq_conv'; *)
(*     mauto 4. *)
(* Qed. *)

(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ A : (glu_elem_bot pred_P s a Γ A) *)
(*     with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_bot_morphism_iff3. *)
(* Proof. *)
(*   intros M M' HMM' *. *)
(*   split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption); *)
(*     intros; *)
(*     assert {{ Γ ⊢ A : Sort@s }} by (eapply glu_sort_elem_sort_lvl; mauto 2); *)
(*     assert {{ Γ' ⊢ M[σ] ≈ M'[σ] : A[σ] }} as HMσM'σ by mauto 5; *)
(*     [rewrite <- HMσM'σ | rewrite -> HMσM'σ ]; *)
(*     mauto 3. *)
(* Qed. *)

(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) a Γ : (glu_elem_bot_unsorted pred_P so_None a Γ) *)
(*     with signature wf_typ_eq Γ  ==> eq ==> eq ==> iff as glu_elem_bot_unsorted_morphism_iff2. *)
(* Proof. *)
(*   intros A A' HAA' *.   *)
(*   split; intros Hglu; dependent destruction Hglu; econstructor; mauto 3. *)
(*   - rewrite <- HAA'. *)
(*     eassumption. *)
(*   - intros. *)
(*     assert {{ Γ' ⊢ M[σ] ≈ M' : A[σ] }} by mauto 3. *)
(*     mauto 4. *)
(*   - rewrite HAA'. *)
(*     eassumption. *)
(*   - intros. *)
(*     assert {{ Γ' ⊢ M[σ] ≈ M' : A'[σ] }} by mauto 3. *)
(*     mauto. *)
(* Qed. *)

(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a Γ A : (glu_elem_bot_unsorted pred_P so a Γ A) *)
(*     with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_bot_unsorted_morphism_iff3. *)
(* Proof. *)
(*   intros M M' HMM' *. *)
(*   split; intros Hglu; dependent destruction Hglu; econstructor; mauto 3; try (gen_presup HMM'; eassumption); intros. *)
(*   - assert {{ Γ' ⊢ M[σ] ≈ M'0 : A[σ] }} by mauto 3. *)
(*     assert {{ Γ' ⊢s σ ≈ σ : Γ }} by mauto 3. *)
(*     gen_presup HMM'. *)
(*     assert {{ Γ' ⊢ M[σ] ≈ M'[σ] : A[σ] }} by mauto 3. *)
(*     mauto 3. *)
(*   - assert {{ Γ' ⊢ M[σ] ≈ M'0 : A[σ] }} by mauto 3. *)
(*     assert {{ Γ' ⊢s σ ≈ σ : Γ }} by mauto 3. *)
(*     gen_presup HMM'. *)
(*     assert {{ Γ' ⊢ M[σ] ≈ M'[σ] : A[σ] }} by mauto 3. *)
(*     mauto 3. *)
(*   - assert {{ Γ' ⊢ M0[σ] ≈ M' : A[σ] }} by mauto 3. *)
(*     assert {{ Γ' ⊢s σ ≈ σ : Γ }} by mauto 3. *)
(*     gen_presup HMM'. *)
(*     assert {{ Γ' ⊢ M[σ] ≈ M0[σ] : A[σ] }} by mauto 3. *)
(*     mauto 3. *)
(*   - assert {{ Γ' ⊢ M0[σ] ≈ M' : A[σ] }} by mauto 3. *)
(*     assert {{ Γ' ⊢s σ ≈ σ : Γ }} by mauto 3. *)
(*     gen_presup HMM'. *)
(*     assert {{ Γ' ⊢ M[σ] ≈ M0[σ] : A[σ] }} by mauto 3. *)
(*     mauto 3. *)
(* Qed. *)


Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a : (glu_elem_top pred_P so a)
    with signature wf_ctx_eq ==> eq ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4; [rewrite <- HΓΓ' | | rewrite -> HΓΓ']; try eassumption.

  intros.
  eapply H3; mauto 2.
  eapply weakening_conv; mauto 3.  
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ : (glu_elem_top pred_P (so_Some s) a Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2_sorted.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    [rewrite <- HAA' | | rewrite -> HAA' | ];
    try eassumption;
    intros;
    assert {{ Γ' ⊢ A[σ] ≈ A'[σ] : Sort@s }} as HAσA'σ by mauto 5;
    eapply wf_exp_eq_conv';
    mauto 4.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) a Γ : (glu_elem_top pred_P so_None a Γ)
    with signature wf_typ_eq Γ ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2_unsorted.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    [rewrite <- HAA' | | rewrite -> HAA' | ];
    try eassumption;
    intros;
    assert {{ Γ' ⊢ A[σ] ≈ A'[σ] }} as HAσA'σ by mauto 5;
    eapply wf_exp_eq_conv';
    mauto 4.
Qed.


(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ : (glu_elem_top pred_P s a Γ) *)
(*     with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as glu_elem_top_morphism_iff2. *)
(* Proof. *)
(*   intros A A' HAA' *. *)
(*   split; intros []; econstructor; mauto 3; *)
(*     [rewrite <- HAA' | | rewrite -> HAA' | ]; *)
(*     try eassumption; *)
(*     intros; *)
(*     assert {{ Γ' ⊢ A[σ] ≈ A'[σ] : Sort@s }} as HAσA'σ by mauto 5; *)
(*     eapply wf_exp_eq_conv'; *)
(*     mauto 4. *)
(* Qed. *)

Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a Γ A : (glu_elem_top pred_P so a Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as glu_elem_top_morphism_iff3.
Proof.
  intros M M' HMM' *.
  split; intros []; econstructor; mauto 3; try (gen_presup HMM'; eassumption);
    intros;
    assert {{ Γ ⊢ A }} by (eapply glu_typ_elem_typ_escape; mauto 2);
    saturate_weakening_escape;
    assert {{ Γ' ⊢ M[σ] ≈ M'[σ] : A[σ] }} as HMσM'σ by mauto 4;
    [rewrite <- HMσM'σ | rewrite -> HMσM'σ];
    mauto.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a : (glu_typ_top_of_sort pred_P s a)
    with signature wf_ctx_eq ==> eq ==> iff as glu_typ_top_of_sort_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4.

  intros.
  eapply H1; mauto 3.
  eapply weakening_conv; mauto 3.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ : (glu_typ_top_of_sort pred_P s a Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}} ==> iff as glu_typ_top_of_sort_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    try (gen_presup HAA'; eassumption);
    intros;
    assert {{ Γ' ⊢ A[σ] ≈ A'[σ] : Sort@s }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.


Add Parametric Morphism {P} (pred_P : PredicativeSig P) a : (glu_typ_top pred_P a)
    with signature wf_ctx_eq ==> eq ==> iff as glu_typ_top_morphism_iff1.
Proof.
  intros Γ Γ' HΓΓ' *.
  split; intros []; econstructor; mauto 4.

  intros.
  eapply H1; mauto 3.
  eapply weakening_conv; mauto 3.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) a Γ : (glu_typ_top pred_P a Γ)
    with signature wf_typ_eq Γ ==> iff as glu_typ_top_morphism_iff2.
Proof.
  intros A A' HAA' *.
  split; intros []; econstructor; mauto 3;
    try (gen_presup HAA'; eassumption);
    intros;
    assert {{ Γ' ⊢ A[σ] ≈ A'[σ] }} as HAσA'σ by mauto 4;
    [rewrite <- HAσA'σ | rewrite -> HAσA'σ];
    mauto.
Qed.

Lemma glu_typ_top_of_sort_implies_glu_typ_top {P} (pred_P : PredicativeSig P) : forall {Γ : ctx P} {s a A},
    {{ Γ ⊢ A ® glu_typ_top_of_sort pred_P s a }} ->
    {{ Γ ⊢ A ® glu_typ_top pred_P a }}.
Proof.
  intros * [].
  econstructor; mauto 3.
Qed.  

(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a : (glu_typ_top pred_P s a) *)
(*     with signature wf_ctx_eq ==> eq ==> iff as glu_typ_top_morphism_iff1. *)
(* Proof. *)
(*   intros Γ Γ' HΓΓ' *. *)
(*   split; intros []; econstructor; mauto 4. *)

(*   intros. *)
(*   eapply H1; mauto 3. *)
(*   eapply weakening_conv; mauto 3. *)
(* Qed. *)

(* Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ : (glu_typ_top pred_P s a Γ) *)
(*     with signature wf_exp_eq Γ {{{ Sort@s }}} ==> iff as glu_typ_top_morphism_iff2. *)
(* Proof. *)
(*   intros A A' HAA' *. *)
(*   split; intros []; econstructor; mauto 3; *)
(*     try (gen_presup HAA'; eassumption); *)
(*     intros; *)
(*     assert {{ Γ' ⊢ A[σ] ≈ A'[σ] : Sort@s }} as HAσA'σ by mauto 4; *)
(*     [rewrite <- HAσA'σ | rewrite -> HAσA'σ]; *)
(*     mauto. *)
(* Qed. *)

(** *** Simple Morphism instance for [glu_ctx_env] *)
Add Parametric Morphism {P} (pred_P : PredicativeSig P) (anns : ctx_anns P) : (glu_ctx_env pred_P anns)
    with signature glu_sub_pred_equivalence P ==> eq ==> iff as simple_glu_ctx_env_morphism_iff.
Proof.
  intros Sb Sb' HSbSb' a.
  split; intro Horig; [gen Sb' | gen Sb];
    induction Horig; econstructor;
    try (etransitivity; [symmetry + idtac|]; eassumption); eauto.
Qed.



(** Lemmas for unsorted gluing model *)
Lemma glu_typ_elem_per_typ {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Dom a ≈ a ∈ per_typ pred_P }}.
Proof.
  inversion_clear 1.
  - eexists; econstructor; reflexivity.
  - enough (per_sort pred_P s a a); mauto 3.
    destruct H as [R].
    eexists.
    mauto 2.
Qed.

#[export]
Hint Resolve glu_sort_elem_per_sort : mcpts.

Lemma glu_typ_elem_per_elem {P} (pred_P : PredicativeSig P) : forall so typ_rel exp_rel a,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ M A m R,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
      {{ Dom m ≈ m ∈ R }}.
Proof.
  inversion_clear 1.
  - intros.
    assert (per_typ_elem pred_P (per_sort pred_P s) d{{{ Sort@s }}} d{{{ Sort@s }}}) by (econstructor; reflexivity).
    handle_per_typ_elem_irrel.
    simpl_glu_rel.
    eapply glu_sort_elem_per_sort; mauto 3.
  - intros.
    eapply glu_sort_elem_per_typ_elem; mauto 3.
Qed.
