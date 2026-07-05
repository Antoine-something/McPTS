From Coq Require Import Equivalence Morphisms Morphisms_Prop Morphisms_Relations Relation_Definitions RelationClasses.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Completeness Require Import FundamentalTheorem.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness Require Export Realizability.
Import Domain_Notations.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ A M : (glu_elem_bot pred_P s a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) s a Γ A M R (H : per_sort_elem pred_P s R a a) : (glu_elem_top pred_P s a Γ A M)
    with signature R ==> iff as glu_elem_top_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; intros []; econstructor; mauto 3;
    pose proof (per_elem_then_per_top H Hmm') as Hmm'';
    try (etransitivity; mauto 4);
    intros;
    specialize (Hmm'' (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto.
Qed.

Lemma glu_sort_elem_typ_unique_upto_exp_eq {P} (pred_P : PredicativeSig P) : forall {s a typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A ® glu_typ_top pred_P s a }} as [] by mauto 3.
  assert {{ Γ ⊢ A' ® glu_typ_top pred_P s a }} as [] by mauto 3.
  match_by_head (@per_top_typ P) ltac:(fun H => destruct (H (length Γ)) as [V []]).
  clear_dups.
  functional_read_rewrite_clear.
  assert {{ Γ ⊢ A[Id] ≈ V : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ A ≈ A[Id] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A ≈ V : Sort@s }} by (etransitivity; mauto 3).
  assert {{ Γ ⊢ A'[Id] ≈ V : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ A' ≈ A'[Id] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ A' ≈ V : Sort@s }} by (etransitivity; mauto 3).
  etransitivity; mauto 3.
Qed.

#[export]
Hint Resolve glu_sort_elem_typ_unique_upto_exp_eq : mcpts.


Lemma glu_sort_elem_per_sort_elem_typ_escape {P} (pred_P : PredicativeSig P) : forall {s a a' elem_rel typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof with mautosolve 4.
  simpl in *.
  intros * Hper Hglu Hglu' HA HA'.
  assert {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} by (setoid_rewrite Hper; eassumption).
  (handle_functional_glu_sort_elem P)...
Qed.

#[export]
Hint Resolve glu_sort_elem_per_sort_elem_typ_escape : mcpts.


Lemma glu_sort_elem_per_sort_typ_escape {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ Dom a ≈ a' ∈ per_sort pred_P s }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }}.
Proof.
  intros * [] **...
  mauto 4.
Qed.

#[export]
Hint Resolve glu_sort_elem_per_sort_typ_escape : mcpts.



Lemma glu_sort_elem_exp_unique_upto_exp_eq {P} (pred_P : PredicativeSig P) : forall {s a typ_rel typ_rel' exp_rel exp_rel' Γ A A' M M' m},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel' }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof.
  intros.
  assert {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P s a }} as [] by mauto 3.
  assert {{ Γ ⊢ M' : A' ® m ∈ glu_elem_top pred_P s a }} as [] by mauto 3.
  assert {{ Γ ⊢ A ≈ A' : Sort@s }} by mauto 3.
  match_by_head (@per_top P) ltac:(fun H => destruct (H (length Γ)) as [W []]).
  clear_dups.
  assert {{ Γ ⊢ M[Id] ≈ W : A[Id] }} by mauto 4.
  assert {{ Γ ⊢ M[Id] ≈ W : A }} by (gen_presups; mauto 4).
  assert {{ Γ ⊢ M : A }} by mauto 4.
  assert {{ Γ ⊢ M'[Id] ≈ W : A'[Id] }} by mauto 4.
  assert {{ Γ ⊢ M'[Id] ≈ W : A' }} by (gen_presups; mauto 4).
  assert {{ Γ ⊢ M'[Id] ≈ W : A }} by (gen_presups; mauto 4).
  assert {{ Γ ⊢ M' : A }} by mauto 4.
  transitivity {{{M[Id]}}}; [mauto 3 |].
  transitivity W; [mauto 3 |].
  mauto 4.
Qed.

#[export]
Hint Resolve glu_sort_elem_exp_unique_upto_exp_eq : mcpts.

Lemma glu_sort_elem_exp_unique_upto_exp_eq' {P} (pred_P : PredicativeSig P) : forall {s a typ_rel exp_rel Γ A A' M M' m},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof. mautosolve 4. Qed.

#[export]
Hint Resolve glu_sort_elem_exp_unique_upto_exp_eq' : mcpts.


Lemma glu_sort_elem_per_sort_typ_iff {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel'},
    {{ Dom a ≈ a' ∈ per_sort pred_P s }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  intros * Hper **.
  eapply functional_glu_sort_elem;
    [eassumption | rewrite Hper];
    eassumption.
Qed.


Lemma glu_sort_elem_per_typ_iff {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel'},
    {{ Dom a ≈ a' ∈ per_typ pred_P }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  intros * Hper **.
  assert (per_sort pred_P s a a) by mauto 2.
  unfold per_sort in H1.
  unfold per_typ in Hper.
  destruct_conjs.
  assert (per_sort_elem pred_P s Hper a a') by mauto 2.
  assert (per_sort pred_P s a a') by mauto 3.
  eapply glu_sort_elem_per_sort_typ_iff; mauto 2.
Qed.

Corollary glu_sort_elem_cumu {P} (pred_P : PredicativeSig P) : forall {s1 s2 a typ_rel exp_rel},
    st_subtyp s1 s2 ->
    {{ DG a ∈ glu_sort_elem pred_P s1 ↘ typ_rel ↘ exp_rel }} ->
    exists typ_rel' exp_rel', {{ DG a ∈ glu_sort_elem pred_P s2 ↘ typ_rel' ↘ exp_rel' }}.
Proof.
  intros.
  assert {{ Dom a ≈ a ∈ per_sort pred_P s1 }} as [R] by mauto.
  assert {{ DF a ≈ a ∈ per_sort_elem pred_P s2 ↘ R }} by mauto.
  mauto.
Qed.


Section glu_sort_elem_cumulativity.
  Lemma glu_sort_elem_pi_sub_irrel {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 s} {r : Ru_pi P s1 s2 s3} {sub_s3_s sub_s3_s' : st_subtyp s3 s} {in_rel elem_rel IP IEL OP OEL},
      (pi_glu_typ_pred r sub_s3_s in_rel IP IEL OP <∙> pi_glu_typ_pred r sub_s3_s' in_rel IP IEL OP) /\
        (pi_glu_exp_pred r sub_s3_s in_rel IP IEL elem_rel OEL <∙> pi_glu_exp_pred r sub_s3_s' in_rel IP IEL elem_rel OEL).
  Proof.
    intros.
    repeat split; intros []; econstructor; mauto 3.
  Qed.
  
  (* This lemma should go in the PER lemmas, but I didn't want to recompile *)
  Lemma per_sort_elem_pi_lowering {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 s} {r : Ru_pi P s1 s2 s3} {elem_rel a ρ B a' ρ' B'},
      {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
      {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s3 ↘ elem_rel }}.
  Proof.
    intros.
    invert_per_sort_elem H.
    per_sort_elem_econstructor; mauto 3.
    - destruct_conjs.
      pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2.
    - intros.
      destruct_rel_mod_eval.
      econstructor; mauto 3.
      pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2.
  Qed.

  Lemma glu_sort_elem_pi_lowering {P} (pred_P : PredicativeSig P) : forall {s1 s2 s3 s} {r : Ru_pi P s1 s2 s3} {a ρ B typ_rel exp_rel},
      {{ DG Π r a ρ B ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
      exists typ_rel' exp_rel',
        {{ DG Π r a ρ B ∈ glu_sort_elem pred_P s3 ↘ typ_rel' ↘ exp_rel' }}.
  Proof.
    simpl.
    intros.
    assert (per_sort pred_P s d{{{ Π r a ρ B }}} d{{{ Π r a ρ B }}}) as [elem_rel ?] by mauto 3.
    eapply per_sort_elem_pi_lowering in H0.
    invert_glu_sort_elem H.
    pose proof ord_ru_pi_sub pred_P r sub_s3_s as [ord_dom ord_im].
    repeat eexists.
    
    unshelve glu_sort_elem_econstructor; try reflexivity; shelve_unifiable; mauto 2.
    - destruct_conjs.
      assert (glu_sort_elem pred_P s1 IP IEL a) by (destruct ord_dom; subst; mauto 2).
      split; intros; subst; mauto 2.
    - intros.
      specialize (H0 _ equiv_c _ H5) as [].
      assert (glu_sort_elem pred_P s2 (OP c equiv_c) (OEL c equiv_c) b) by (destruct ord_im; subst; mauto 2).
      split; intros; subst; mauto 2.
  Qed.
    
        
  #[local]
  Lemma glu_sort_elem_cumulativity {P} (pred_P : PredicativeSig P) : forall {s s' a typ_rel typ_rel' exp_rel exp_rel'},
      st_subtyp s s' ->
      {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
      {{ DG a ∈ glu_sort_elem pred_P s' ↘ typ_rel' ↘ exp_rel' }} ->
      (forall Γ A, {{ Γ ⊢ A ® typ_rel }} -> {{ Γ ⊢ A ® typ_rel' }}) /\
        (forall Γ A M m, {{ Γ ⊢ M : A ® m ∈ exp_rel }} -> {{ Γ ⊢ M : A ® m ∈ exp_rel' }}) /\
        (forall Γ A M m, {{ Γ ⊢ A ® typ_rel }} -> {{ Γ ⊢ M : A ® m ∈ exp_rel' }} -> {{ Γ ⊢ M : A ® m ∈ exp_rel }}).
  Proof with mautosolve 4.
    simpl.
    intros * Hsub Hglu Hglu'. gen exp_rel' typ_rel' s'.
    induction Hglu using glu_sort_elem_ind; repeat split; intros;
      try assert {{ DF a ≈ a ∈ per_sort_elem pred_P s' ↘ in_rel }} by mauto 2;
      try assert {{ DF a ≈ a ∈ per_sort_elem pred_P s' ↘ fst_rel }} by mauto 2;
      unshelve invert_glu_sort_elem Hglu'; try (etransitivity; eassumption); shelve_unifiable;
      handle_functional_glu_sort_elem P;
      simpl in *;
      try solve [repeat split; intros; destruct_conjs; mauto 2 | intuition mauto 3 using glu_bot_typ_cumu_ge].
    
    - eapply wf_exp_eq_conv; mauto 3.
    - destruct_conjs.
      repeat split; mauto 3.
      + eapply wf_exp_eq_conv; mauto 3.
      + repeat eexists; mauto 2.

    - destruct_by_head (@pi_glu_typ_pred P).
      econstructor; intros; mauto 4.
      + eapply wf_exp_eq_conv; mauto 3.
      + match_by_head (per_sort_elem pred_P) ltac:(fun H => directed invert_per_sort_elem H).
        assert (per_sort_elem pred_P s1 in_rel1 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub0 as [[] ?]; subst; mauto 2).
        assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub_s3_s as [[] ?]; subst; mauto 2).
        handle_per_sort_elem_irrel.

        assert (in_rel0 m m) by intuition.
        assert (in_rel1 m m) by intuition.
        destruct_rel_mod_eval.
        simplify_evals. rename a0 into b.
        
        assert (per_sort_elem pred_P s2 (out_rel m m H0) b b) by (pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2).
        assert (per_sort_elem pred_P s2 (out_rel0 m m H3) b b) by (pose proof ord_ru_pi_sub pred_P r sub0 as [? []]; subst; mauto 2).
        handle_per_sort_elem_irrel.

        assert (glu_sort_elem pred_P s2 (x m equiv_m) (x0 m equiv_m) b) by mauto 2.
        assert (glu_sort_elem pred_P s2 (OP m equiv_m) (OEL m equiv_m) b) by mauto 2.
        handle_functional_glu_sort_elem P.
        eapply H31.
        mauto 3.

    - handle_per_sort_elem_irrel.
      destruct_by_head (pi_glu_exp_pred r sub_s3_s).
      econstructor; intros; mauto 4.
      + eapply wf_exp_eq_conv; mauto 3.      
      + match_by_head (per_sort_elem pred_P) ltac:(fun H => directed invert_per_sort_elem H).
        assert (per_sort_elem pred_P s1 in_rel1 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub0 as [[] ?]; subst; mauto 2).
        assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub_s3_s as [[] ?]; subst; mauto 2).
        handle_per_sort_elem_irrel.        
        
        assert (in_rel0 n n) by intuition.
        assert (in_rel1 n n) by intuition.
        destruct_rel_mod_eval.
        simplify_evals. rename a0 into b.

        assert (per_sort_elem pred_P s2 (out_rel n n H0) b b) by (pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2).
        assert (per_sort_elem pred_P s2 (out_rel0 n n H3) b b) by (pose proof ord_ru_pi_sub pred_P r sub0 as [? []]; subst; mauto 2).
        handle_per_sort_elem_irrel.

        assert (glu_sort_elem pred_P s2 (x n equiv_n) (x0 n equiv_n) b) by mauto 2.
        assert (glu_sort_elem pred_P s2 (OP n equiv_n) (OEL n equiv_n) b) by mauto 2.
        handle_functional_glu_sort_elem P.

        specialize (H12 _ _ _ _ H17 H18 equiv_n) as [mn []].
        eexists; split; mauto 2.
        eapply H35; eassumption.

    - handle_per_sort_elem_irrel.
      simpl_glu_rel.

      assert (sub_s3_s3 : st_subtyp s3 s3) by reflexivity.
      assert (glu_sort_elem pred_P s3 (pi_glu_typ_pred r sub_s3_s3 in_rel IP IEL OP) (pi_glu_exp_pred r sub_s3_s3 in_rel IP IEL elem_rel OEL) d{{{ Π r a ρ B }}}).
      {
        glu_sort_elem_econstructor; mauto 2; try reflexivity.
        - split; intros; subst; mauto 2.
        - intros.
          specialize (H1 _ equiv_c _ H18).
          split; intros; subst; mauto 2.
        - eapply per_sort_elem_pi_lowering; mauto 2.
      }

      invert_per_sort_elem H17.
      assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2).
      handle_per_sort_elem_irrel.      
      
      econstructor; intros; mauto 3.
      assert (in_rel0 n n) by intuition.
      destruct_rel_mod_eval.
      simplify_evals.
      rename a0 into b.
      assert (glu_sort_elem pred_P s2 (x n equiv_n) (x0 n equiv_n) b) by mauto 2.
      assert (glu_sort_elem pred_P s2 (OP n equiv_n) (OEL n equiv_n) b) by mauto 2.
      handle_functional_glu_sort_elem P.

      assert (IP Δ {{{ IT0[σ] }}}) by mauto 2.
      assert (IP Δ {{{ IT[σ] }}}) by mauto 2.
      assert {{ Δ ⊢ IT[σ] ≈ IT0[σ] : Sort@s1 }} by mauto 2.
      assert (IEL Δ {{{ IT0[σ] }}} N n) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3).

      
      assert (OP n equiv_n Δ {{{ OT[σ,,N] }}}) by mauto 2.
      assert (exists mn, {{ $| m & n |↘ mn }} /\ x0 n equiv_n Δ {{{ OT0[σ,,N] }}} {{{ M[σ] N }}} mn) as [mn []] by mauto 2.
      assert (OP n equiv_n Δ {{{ OT0[σ,,N] }}}).
     {
        eapply H31.
        eapply glu_sort_elem_trm_typ; mauto 2.
      }
      
      eexists; split; mauto 2.
      assert {{ Δ ⊢ OT[σ,,N] ≈ OT0[σ,,N] : Sort@s2 }} as -> by mauto 2.
      eapply H32.
      eassumption.
      
    - eapply wf_exp_eq_conv; mauto 3.
    - destruct_conjs; split.
      + eapply wf_exp_eq_conv; mauto 3.
      + eapply glu_nat_rule_irrelevance; mauto 2.
    - destruct_conjs; split; mauto 2.
      eapply glu_nat_rule_irrelevance; mauto 2.

    - destruct_conjs; split.
      + eapply wf_exp_conv; mauto 3.
      + intros.
        eapply wf_exp_eq_conv; mauto 4.
    - simpl_glu_rel.
      econstructor; mauto 3.
      econstructor; mauto 3.
      intros.
      eapply wf_exp_eq_conv; mauto 4.
    - simpl_glu_rel.
      econstructor; mauto 3.
      econstructor; mauto 3.
  Qed.
End glu_sort_elem_cumulativity.

Corollary glu_sort_elem_typ_cumu {P} (pred_P : PredicativeSig P) : forall {s s' a typ_rel typ_rel' exp_rel exp_rel' Γ A},
    st_subtyp s s' ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s' ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A ® typ_rel' }}.
Proof.
  intros * sub_s_s' Hglu Hglu' ?.
  pose proof glu_sort_elem_cumulativity pred_P sub_s_s' Hglu Hglu' as [? []].
  mauto 2.
Qed.

Corollary glu_sort_elem_exp_cumu {P} (pred_P : PredicativeSig P) : forall {s s' a typ_rel typ_rel' exp_rel exp_rel' Γ M A m},
    st_subtyp s s' ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s' ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel' }}.
Proof.
  intros * sub_s_s' Hglu Hglu' ?.
  pose proof glu_sort_elem_cumulativity pred_P sub_s_s' Hglu Hglu' as [? []].
  mauto 2.
Qed.

Corollary glu_sort_elem_exp_lower {P} (pred_P : PredicativeSig P) : forall {s s' a typ_rel typ_rel' exp_rel exp_rel' Γ A M m},
    st_subtyp s s' ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_sort_elem pred_P s' ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }}.
Proof.
  intros * sub_s_s' Hglu Hglu' ? ?.
  pose proof glu_sort_elem_cumulativity pred_P sub_s_s' Hglu Hglu' as [? []].
  mauto 2.
Qed.


Lemma glu_sort_elem_exp_conv {P} (pred_P : PredicativeSig P) : forall {saa' sa sa' a a' typ_rel typ_rel' exp_rel exp_rel' Γ A M m},
    {{ Dom a ≈ a' ∈ per_sort pred_P saa' }} ->
    {{ DG a ∈ glu_sort_elem pred_P sa ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P sa' ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel' }}.
Proof.
  intros * [] ? ? ? ?.

  assert (per_typ_elem pred_P x a a') by mauto 2.
  assert (per_sort_elem pred_P sa x a a') by (assert (per_sort pred_P sa a a) as [R2 ?]; mauto 3).
  assert (per_sort_elem pred_P sa' x a' a) by (assert (per_sort pred_P sa' a' a') as [R3 ?]; symmetry in H4; mauto 3).
  assert (glu_sort_elem pred_P sa typ_rel exp_rel a') by (eapply glu_sort_elem_resp_per_sort; mauto 3).
  assert (glu_sort_elem pred_P sa' typ_rel' exp_rel' a) by (eapply glu_sort_elem_resp_per_sort; mauto 3).

  pose proof H0.
  invert_glu_sort_elem H0.
  - invert_glu_sort_elem H9.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    apply_predicate_equivalence.
    destruct_conjs.
    repeat eexists; mauto 2.

  - pose proof H12.
    assert (st_subtyp s3 sa').
    {
      match_by_head (per_sort_elem pred_P sa') ltac:(fun H => directed invert_per_sort_elem H).
      eassumption.
    }
    unshelve invert_glu_sort_elem H12; try eassumption; shelve_unifiable.
    
    assert (glu_sort_elem pred_P s1 IP IEL a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub_s3_s as [[] ?]; subst; mauto 2).
    handle_functional_glu_sort_elem P.
    rename x0 into IP, x1 into IEL.
        
    assert (exists typ_rel exp_rel, glu_sort_elem pred_P s3 typ_rel exp_rel d{{{ Π r a ρ B }}}) as [typ_rel [exp_rel ?]] by (eapply glu_sort_elem_pi_lowering; mauto 2).
    pose proof H3.
    unshelve invert_glu_sort_elem H3; try reflexivity; shelve_unifiable.
    
    simpl_glu_rel.
    handle_per_sort_elem_irrel.
    econstructor; mauto 2.

    intros.
    invert_per_sort_elem H28.
    assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r ltac:(reflexivity) as [[] ?]; subst; mauto 2).
    handle_per_sort_elem_irrel.
    assert (in_rel0 n n) by intuition.
    destruct_rel_mod_eval.
    simplify_evals.
    rename a0 into b.
    assert (glu_sort_elem pred_P s2 (x2 n equiv_n) (x3 n equiv_n) b) by mauto 2.
    assert (glu_sort_elem pred_P s2 (x0 n equiv_n) (x1 n equiv_n) b) by mauto 2.
    specialize (H1 n equiv_n b ltac:(eassumption)) as [].
    assert (glu_sort_elem pred_P s2 (OP n equiv_n) (OEL n equiv_n) b) by (pose proof ord_ru_pi_sub pred_P r sub_s3_s as [? []]; subst; mauto 2).
    handle_functional_glu_sort_elem P.

    assert (x2 n equiv_n Δ {{{ OT0[σ,,N] }}}) by mauto 2.
    assert (IP Δ {{{ IT[σ] }}}) by mauto 2.
    assert (IP Δ {{{ IT0[σ] }}}) by mauto 2.
    assert {{ Δ ⊢ IT[σ] ≈ IT0[σ] : Sort@s1 }} by mauto 2.
    assert (IEL Δ {{{ IT[σ] }}} N n) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2).
    assert (exists mn : domain P, {{ $| m & n |↘ mn }} /\ OEL n equiv_n Δ {{{ OT[σ,,N] }}} {{{ M[σ] N }}} mn) as [mn []] by mauto 2.
    eexists; split; mauto 2.
    eapply H52.
    eapply H51 in H33.
    assert (OP n equiv_n Δ {{{ OT[σ,,N] }}}) by (eapply glu_sort_elem_trm_typ; mauto 2).
    assert {{ Δ ⊢ OT[σ,,N] ≈ OT0[σ,,N] : Sort@s2 }} as <- by mauto 2.
    eassumption.

  - invert_glu_sort_elem H9.
    simpl_glu_rel.
    split; mauto 2.
    eapply glu_nat_rule_irrelevance; mauto 2.

  - invert_glu_sort_elem H10.
    simpl_glu_rel.
    econstructor; mauto 2.
    econstructor; mauto 2.
Qed.

Ltac do_sort_elem_lower_for_assert sort_elem s :=
  match goal with
  | [ r : Ru_pi ?P s ?s2 ?s3,
        sub : st_subtyp ?s3 ?s',
          H1 : pred_rel ?pred_P s ?s' -> sort_elem ?pred_P s ?a ?b ?c,
            H2 : s = ?s' -> sort_elem ?pred_P ?s' ?a ?b ?c |- _ ] =>
      
      assert (sort_elem pred_P s a b c) by (pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2);
      clear H1 H2
  | [ r : Ru_pi ?P ?s1 s ?s3,
        sub : st_subtyp ?s3 ?s',
          H1 : pred_rel ?pred_P s ?s' -> sort_elem ?pred_P s ?a ?b ?c,
            H2 : s = ?s' -> sort_elem ?pred_P ?s' ?a ?b ?c |- _ ] =>
      
      assert (sort_elem pred_P s a b c) by (pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2);
      clear H1 H2
  end.

Ltac handle_per_sort_elem_lower_for s :=
  try match goal with
  | P : PtsSig |- _ => repeat do_sort_elem_lower_for_assert (@per_sort_elem P) s
  end.

Ltac handle_glu_sort_elem_lower_for s :=
  try match goal with
  | P : PtsSig |- _ => repeat do_sort_elem_lower_for_assert (@glu_sort_elem P) s
  end.

Ltac handle_per_sort_elem_lower :=
  match goal with
  | [ r : Ru_pi ?P ?s1 ?s2 ?s3 |- _ ] =>
      handle_per_sort_elem_lower_for s1;
      handle_per_sort_elem_lower_for s2;
      clear_dups
  | _ => idtac
  end.
 
Ltac handle_glu_sort_elem_lower :=
  match goal with
  | [ r : Ru_pi ?P ?s1 ?s2 ?s3 |- _ ] =>
      handle_glu_sort_elem_lower_for s1;
      handle_glu_sort_elem_lower_for s2;
      clear_dups
  | _ => idtac
  end.    

Lemma glu_sort_elem_per_subtyp_typ_sorted_escape {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ ⟪ pred_P ⟫ Subs a <: a' at s }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ⊆ A' }}.
Proof.
  handle_per_sort_elem_irrel.
  intros * Hsubtyp Hglu Hglu' HA HA'.
  gen A' A Γ. gen exp_rel' exp_rel typ_rel' typ_rel.
  induction Hsubtyp (* using per_subtyp_ind *); intros; subst;
    saturate_refl_for (per_sort_elem pred_P);
    try solve [simpl in *; bulky_rewrite; mauto 3];
    unshelve invert_glu_sort_elem Hglu; try eassumption; shelve_unifiable;
    handle_functional_glu_sort_elem P;
    handle_per_sort_elem_irrel;
    destruct_by_head (@pi_glu_typ_pred P);
    saturate_glu_by_per;
    unshelve invert_glu_sort_elem Hglu'; try eassumption; shelve_unifiable;
    handle_functional_glu_sort_elem P.
  
  - unfold sort_glu_typ_pred in *.
    assert {{ Γ ⊢ A ⊆ Sort@s1 }} by mauto 3.
    assert {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto 3.
    assert {{ Γ ⊢ Sort@s2 ⊆ A' }} by mauto 4.
    bulky_rewrite.

  - unfold nat_glu_typ_pred in *.
    assert {{ Γ ⊢ A ⊆ ℕ }} by mauto 3.
    assert {{ Γ ⊢ ℕ ⊆ A' }} by mauto 4.
    etransitivity; mauto 2.
    
  - destruct_by_head (@pi_glu_typ_pred P).

    rename A0 into A'. rename IT0 into IT'. rename OT0 into OT'.
    rename x into IP, x0 into IEL, x1 into OP, x2 into OEL, x3 into OP', x4 into OEL'.

    assert {{ Γ ⊢ A ⊆ Π r IT OT }} by mauto 3.
    transitivity {{{ Π r IT OT }}}; mauto 2.
    assert {{ Γ ⊢ Π r IT' OT' ⊆ A' }} by mauto 4.
    transitivity {{{ Π r IT' OT' }}}; mauto 2.
    
    assert {{ Γ ⊢w Id : Γ }} by mauto 3.
    assert (IP Γ {{{ IT[Id] }}}) by mauto 2.
    assert (IP Γ {{{ IT'[Id] }}}) by mauto 2.
    assert {{ Γ ⊢ IT[Id] ≈ IT : Sort@s1 }} by mauto 3.
    assert (IP Γ IT) by (rewrite -> H26 in H24; eassumption).
    assert {{ Γ ⊢ IT'[Id] ≈ IT' : Sort@s1 }} by mauto 3.
    assert (IP Γ IT') by (rewrite -> H28 in H25; eassumption).
    assert {{ Γ ⊢ IT ≈ IT' : Sort@s1 }} by mauto 2.
    
    assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv0_len_len' by (eapply per_bot_then_per_elem; mauto 4).
    assert {{ Dom ⇑! a (length Γ) ≈ ⇑! a (length Γ) ∈ in_rel }} as equiv0_len_len by (eapply per_bot_then_per_elem; mauto 4).
    assert {{ Dom ⇑! a' (length Γ) ≈ ⇑! a' (length Γ) ∈ in_rel }} as equiv0_len'_len' by (eapply per_bot_then_per_elem; mauto 4).
    handle_per_sort_elem_irrel.

    match_by_head (per_sort_elem pred_P) ltac:(fun H => directed invert_per_sort_elem H).
    destruct_conjs.

    handle_per_sort_elem_lower.
    handle_per_sort_elem_irrel.
    
    assert (in_rel d{{{ ⇑! a (length Γ) }}} d{{{ ⇑! a' (length Γ) }}}) as equiv_len_len' by intuition.
    assert (in_rel d{{{ ⇑! a (length Γ) }}} d{{{ ⇑! a (length Γ) }}}) as equiv_len_len by intuition.
    assert (in_rel d{{{ ⇑! a' (length Γ) }}} d{{{ ⇑! a' (length Γ) }}}) as equiv_len'_len' by intuition.
    assert (in_rel1 d{{{ ⇑! a (length Γ) }}} d{{{ ⇑! a' (length Γ) }}}) as equiv1_len_len' by intuition.
    assert (in_rel1 d{{{ ⇑! a (length Γ) }}} d{{{ ⇑! a (length Γ) }}}) as equiv1_len_len by intuition.
    assert (in_rel1 d{{{ ⇑! a' (length Γ) }}} d{{{ ⇑! a' (length Γ) }}}) as equiv1_len'_len' by intuition.
    destruct_rel_mod_eval.    
    functional_eval_rewrite_clear.
    rename a0 into b'ρ'a', a1 into b'ρ'a, a3 into bρa', a4 into bρa.

    handle_per_sort_elem_lower.
    handle_per_sort_elem_irrel.
    
    assert {{ ⟪ pred_P ⟫ Subs bρa <: b'ρ'a' at s2 }} by mauto 2.
    assert (glu_sort_elem pred_P s2 (OP _ equiv_len_len) (OEL _ equiv_len_len) bρa) by mauto 2.
    assert (glu_sort_elem pred_P s2 (OP _ equiv_len'_len') (OEL _ equiv_len'_len') bρa') by mauto 2.
    assert (glu_sort_elem pred_P s2 (OP' _ equiv_len_len) (OEL' _ equiv_len_len) b'ρ'a) by mauto 2.
    assert (glu_sort_elem pred_P s2 (OP' _ equiv_len'_len') (OEL' _ equiv_len'_len') b'ρ'a') by mauto 2.

    assert (per_sort pred_P s2 bρa bρa') by mauto 3.
    assert (per_sort pred_P s2 b'ρ'a b'ρ'a') by mauto 3.

    assert (glu_sort_elem pred_P s2 (OP _ equiv_len_len) (OEL _ equiv_len_len) bρa') by (eapply glu_sort_elem_resp_per_sort; mauto 3).
    assert (glu_sort_elem pred_P s2 (OP' _ equiv_len_len) (OEL' _ equiv_len_len) b'ρ'a') by (eapply glu_sort_elem_resp_per_sort; mauto 3).
    handle_functional_glu_sort_elem P.
    clear_dups.

    assert {{ Γ, IT ⊢ #0 : IT[Wk] ® ⇑! a' (length Γ) ∈ IEL }} by (eapply realize_glu_elem_bot; [| eapply var_glu_elem_bot]; mauto 3).
    assert {{ Γ, IT' ⊢ #0 : IT'[Wk] ® ⇑! a' (length Γ) ∈ IEL }} by (eapply realize_glu_elem_bot; [| eapply var_glu_elem_bot]; mauto 3).
    simpl in H48, H51.
    
    assert {{ Γ, IT ⊢w Wk : Γ }} by mauto 3.
    assert (OP d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' {{{ Γ, IT }}} {{{ OT[Wk,,#0] }}}) by mauto 2.
    assert {{ Γ, IT' ⊢w Wk : Γ }} by mauto 3.
    assert (OP' d{{{ ⇑! a' (length Γ) }}} equiv_len'_len' {{{ Γ, IT' }}} {{{ OT'[Wk,,#0] }}}) by mauto 2.
    
    
    eapply wf_subtyp_pi; mauto 3.

    assert {{ ⊢ Γ, IT ≈ Γ, IT' }} by mauto 5.
    assert {{ Γ, IT' ⊢s Wk,,#0 ≈ Id : Γ, IT' }} by mauto 3.
    assert {{ Γ, IT' ⊢ OT[Wk,,#0] ≈ OT : Sort@s2 }} by (transitivity {{{ OT[Id] }}}; mauto 3).
    assert {{ Γ, IT' ⊢ OT'[Wk,,#0] ≈ OT' : Sort@s2 }} by (transitivity {{{ OT'[Id] }}}; mauto 3).

    assert (OP d{{{ ⇑! a (length Γ) }}} equiv_len_len {{{ Γ, IT' }}} {{{ OT[Wk,,#0] }}}) by (eapply H58; eapply glu_sort_elem_typ_resp_ctx_eq; mauto 3).    
    assert (OP d{{{ ⇑! a (length Γ) }}} equiv_len_len {{{ Γ, IT' }}} OT) by (eapply glu_sort_elem_typ_resp_exp_eq; mauto 2).

    assert (OP' d{{{ ⇑! a (length Γ) }}} equiv_len_len {{{ Γ, IT' }}} OT').
    {
      eapply H56.
      eapply glu_sort_elem_typ_resp_exp_eq; mauto 2.
    }
    eapply H1; mauto 3.

  - match_by_head (per_bot e e') ltac:(fun H => specialize (H (length Γ)) as [V []]).
    simpl in *.
    destruct_conjs.
    assert {{ Γ ⊢ A[Id] ≈ A : Sort@s }} by mauto 4.
    assert {{ Γ ⊢ A'[Id] ≈ A' : Sort@s }} by mauto 3.
    assert {{ Γ ⊢w Id : Γ }} by mauto 3.
    assert {{ Γ ⊢ A[Id] ≈ V : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ A'[Id] ≈ V : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ A ≈ V : Sort@s }} by (etransitivity; mauto 3).
    assert {{ Γ ⊢ A' ≈ V : Sort@s }} by (etransitivity; mauto 3).
    assert {{ Γ ⊢ A ≈ A' : Sort@s }} by (etransitivity; mauto 3).
    mauto 3.
Qed.

Lemma glu_sort_elem_per_subtyp_typ_escape {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A'},
    {{ ⟪ pred_P ⟫ Sub a <: a' }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ A ⊆ A' }}.
Proof.
  intros.
  assert {{ ⟪ pred_P ⟫ Subs a <: a' at s }} by (eapply per_subtyp_implies_per_subtyp_sorted; mauto 2).
  eapply glu_sort_elem_per_subtyp_typ_sorted_escape; mauto 2.
Qed.

Lemma glu_sort_elem_per_subtyp_trm_sorted_conv {P} (pred_P : PredicativeSig P) : forall {s s' s0 a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A' M m},
    {{ ⟪ pred_P ⟫ Subs a <: a' at s0 }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s' ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A' ® m ∈ exp_rel' }}.
Proof.
  intros * H.
  gen typ_rel typ_rel' exp_rel exp_rel'. gen A A' M m. gen s s' Γ.
  induction H; intros.
  - invert_glu_sort_elem H4.
    invert_glu_sort_elem H3.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.
    
    simpl_glu_rel.
    handle_functional_glu_sort_elem P.
    
    epose proof glu_sort_elem_cumu pred_P H H10 as [? []].
    epose proof glu_sort_elem_typ_cumu pred_P H H10 H3 H11.
    simpl_glu_rel.
    
    split; [|split]; mauto 4.
  - invert_glu_sort_elem H2.
    invert_glu_sort_elem H1.
    unfold nat_glu_typ_pred in *.
    unfold nat_glu_exp_pred in *.
    simpl_glu_rel.
    handle_functional_glu_sort_elem P.
    split; mauto 3 using glu_nat_rule_irrelevance.
  - intros.
    invert_glu_sort_elem H5.
    invert_glu_sort_elem H10.
    invert_per_sort_elems.
    destruct_conjs.
    handle_glu_sort_elem_lower.
    handle_per_sort_elem_lower.
    handle_per_sort_elem_irrel.
    simpl_glu_rel.
    econstructor; mauto 4.
    intros.

    assert (in_rel0 n n') as equiv_n_n'0 by intuition.
    assert (in_rel1 n n') as equiv_n_n'1 by intuition.
    assert (in_rel2 n n') as equiv_n_n'2 by intuition.
    assert (in_rel3 n n') as equiv_n_n'3 by intuition.
    assert (in_rel4 n n') as equiv_n_n'4 by intuition.
    rename equiv_n_n' into equiv_n_n'5.

    destruct_rel_mod_eval.
    simplify_evals.

    rename a1 into bn.
    rename a'1 into bn'.
    rename a0 into b'n.
    rename a'0 into b'n'.
    
    handle_per_sort_elem_lower.
    destruct_rel_mod_app.
    econstructor; mauto.
    + assert {{ ⟪ pred_P ⟫ Subs bn <: b'n' at s2 }} by mauto 2.
      saturate_refl_for @per_sort_elem.
      eapply per_elem_subtyping_sorted; mauto.
      handle_per_sort_elem_irrel.
      apply H55; mauto.

    + intros.
      assert (in_rel0 n n) as equiv_n0 by intuition.
      assert (in_rel1 n n) as equiv_n1 by intuition.
      assert (in_rel2 n n) as equiv_n2 by intuition.
      assert (in_rel3 n n) as equiv_n3 by intuition.
      assert (in_rel5 n n) as equiv_n5 by intuition.
      rename equiv_n into equiv_n4.
      
      assert (per_sort pred_P s1 a a') by mauto 3.
      assert (glu_sort_elem pred_P s1 IP IEL a') by (eapply glu_sort_elem_resp_per_sort; mauto 3).
      handle_functional_glu_sort_elem P.

      assert (IP Δ {{{ IT[σ] }}}) by mauto 2.
      assert (IP0 Δ {{{ IT0[σ] }}}) by mauto 2.
      eapply H34 in H15.

      assert {{ Δ ⊢ IT[σ] ≈ IT0[σ] : Sort@s1 }} by mauto 2.
      assert (IEL Δ {{{ IT[σ] }}} N n) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2).
      assert (exists mn : domain P, {{ $| m & n |↘ mn }} /\ OEL n equiv_n2 Δ {{{ OT[σ,,N] }}} {{{ M[σ] N }}} mn) as [mn []] by mauto 3.
      eexists; split; mauto 4.

      destruct_rel_mod_eval.
      simplify_evals.
      rename a1 into b.
      rename a0 into b'.

      handle_per_sort_elem_lower.
      assert {{ ⟪ pred_P ⟫ Subs b <: b' at s2 }} by mauto 2.
      handle_per_sort_elem_irrel.

      assert ((s2 = s0 -> glu_sort_elem pred_P s0 (OP _ equiv_n2) (OEL _ equiv_n2) b) /\
                (pred_rel pred_P s2 s0 -> glu_sort_elem pred_P s2 (OP _ equiv_n2) (OEL _ equiv_n2) b))
        as [] by mauto 3.
      assert ((s2 = s' -> glu_sort_elem pred_P s' (OP0 _ equiv_n4) (OEL0 _ equiv_n4) b') /\
                (pred_rel pred_P s2 s' -> glu_sort_elem pred_P s2 (OP0 _ equiv_n4) (OEL0 _ equiv_n4) b'))
        as [] by mauto 3.

      handle_glu_sort_elem_lower.
      eapply H1; mauto 4.
      eapply glu_sort_elem_per_subtyp_typ_sorted_escape; mauto.
      eapply glu_sort_elem_trm_typ; mauto 4.

      eapply H25; mauto.
      eapply H35.
      rewrite <- H21.
      eassumption.

      eapply H25; mauto.
      eapply H35.
      rewrite <- H21.
      eassumption.
  - invert_glu_sort_elem H2.
    invert_glu_sort_elem H1.
    match_by_head (per_bot e e') ltac:(fun H => specialize (H (length Γ)) as [V []]).
    simpl in *.

    unfold neut_glu_typ_pred in *.
    simpl_glu_rel.
    handle_functional_glu_sort_elem P.
    econstructor; mauto 4.
    econstructor; mauto 4.
    intros; mauto 4.

    saturate_weakening_escape.
    assert {{ Γ ⊢w Id : Γ }} by mauto 3.
    assert {{ Γ ⊢ A[Id] ≈ V }} by mauto 3.
    assert {{ Γ ⊢ A'[Id] ≈ V }} by mauto 3.
    assert {{ Γ ⊢ A ≈ V }} by (transitivity {{{ A[Id] }}}; mauto 3).
    assert {{ Γ ⊢ A' ≈ V }} by (transitivity {{{ A'[Id] }}}; mauto 3).
    assert {{ Γ ⊢ A ≈ A' }} by mauto 3.
    assert {{ Δ ⊢ A[σ] ≈ A'[σ] }} by mauto 3.
    mauto 3.
Qed.

Lemma glu_sort_elem_per_subtyp_trm_conv {P} (pred_P : PredicativeSig P) : forall {s s' a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A' M m},   {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⟪ pred_P ⟫ Sub a <: a' }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s' ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A' ® m ∈ exp_rel' }}.
Proof.
  intros * Hsubtyp Hsubtyp' Hglu Hglu' HA HA'.
  gen A' A Γ. gen exp_rel' exp_rel typ_rel' typ_rel.
  induction Hsubtyp' (* using per_subtyp_ind *); intros; subst.
  -     

    invert_glu_sort_elem  Hglu.
    invert_glu_sort_elem  Hglu'.
    unfold sort_glu_exp_pred' in *.
    unfold glu_sort_typ_rec in *.

    simpl_glu_rel.
    handle_functional_glu_sort_elem P.

    epose proof glu_sort_elem_cumu pred_P H H6 as [? []].
    epose proof glu_sort_elem_typ_cumu pred_P H H6 H0 H7.
    simpl_glu_rel.
    split; [|split]; mauto 3.
    do 2 eexists; split; mauto 4.
  - eapply glu_sort_elem_per_subtyp_trm_sorted_conv; mauto. 
Qed.

Lemma glu_sort_elem_per_subtyp_trm_if {P} (pred_P : PredicativeSig P) : forall {s a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A' M m},
    {{ ⟪ pred_P ⟫ Sub a <: a' }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A' ® m ∈ exp_rel' }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ® typ_rel }} by (eapply glu_sort_elem_trm_typ; mauto 2).
  assert {{ Γ ⊢ A ⊆ A' }} by (eapply glu_sort_elem_per_subtyp_typ_escape; mauto 2).
  eapply glu_sort_elem_per_subtyp_trm_conv; mauto 2.
Qed.


Lemma mk_glu_rel_typ_with_sub' {P} (pred_P : PredicativeSig P) : forall {s Δ A σ ρ a},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ.
Proof.
  intros * ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_typ_with_sub' : mcpts.

Lemma mk_glu_rel_typ_with_sub'' {P} (pred_P : PredicativeSig P) : forall {s Δ A σ ρ a},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ Dom a ≈ a ∈ per_sort pred_P s }} ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ A[σ] ® typ_rel }}) ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ.
Proof.
  intros * ? [] ?.
  assert (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) as [? []] by mauto.
  eapply mk_glu_rel_typ_with_sub'; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_typ_with_sub'' : mcpts.


Lemma mk_glu_rel_exp_with_sub' {P} (pred_P : PredicativeSig P) : forall {s Δ A M σ ρ a m},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}) ->
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ.
Proof.
  intros * ? ? [? []] HEl.
  econstructor; mauto.
  eapply HEl; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_exp_with_sub' : mcpts.

Lemma mk_glu_rel_exp_with_sub'' {P} (pred_P : PredicativeSig P) : forall {s Δ A M σ ρ a m},
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    {{ Dom a ≈ a ∈ per_sort pred_P s }} ->
    (forall typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> {{ Δ ⊢ M[σ] : A[σ] ® m ∈ exp_rel }}) ->
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ.
Proof.
  intros * ? ? [] ?.
  assert (exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }}) as [? []] by mauto.
  eapply mk_glu_rel_exp_with_sub'; mauto.
Qed.

#[export]
Hint Resolve mk_glu_rel_exp_with_sub'' : mcpts.


Lemma glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ {P} (pred_P : PredicativeSig P) : forall {s s' Δ A M σ Γ ρ},
    Ax_typ P s s' ->
    {{ Δ ⊢s σ : Γ }} ->
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ ->
    glu_rel_exp_with_sub pred_P s' Δ A {{{ Sort@s }}} σ ρ.
Proof.
  intros * ? ? [].
  econstructor; mauto.
  assert {{ Δ ⊢ A[σ] : Sort@s }} by mauto 3 using glu_sort_elem_trm_sort_lvl.
  assert {{ Δ ⊢ Sort@s : Sort@s' }} by mauto 3.
  assert {{ Γ ⊢ Sort@s : Sort@s' }} by mauto 3.
  assert {{ Δ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s' }} by mauto 2.
  repeat split; try do 2 eexists; mauto 3.
  split; mauto 4.
  eapply glu_sort_elem_trm_typ; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_exp_sub_with_typ : mcpts.


Lemma glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub {P} (pred_P : PredicativeSig P) : forall {s Δ A s' σ ρ},
  glu_rel_exp_with_sub pred_P s Δ A {{{ Sort@s' }}} σ ρ ->
  glu_rel_typ_with_sub pred_P s' Δ A σ ρ.
Proof.
  intros * [].
  simplify_evals.
  match_by_head1 (@glu_sort_elem P) invert_glu_sort_elem.
  apply_predicate_equivalence.
  unfold sort_glu_exp_pred' in *.
  unfold glu_sort_typ_rec in *.
  destruct_conjs.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_implies_glu_rel_typ_with_sub : mcpts.


Lemma glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub {P} (pred_P : PredicativeSig P) : forall {Δ A s s' σ Γ ρ},
    Ax_typ P s s' ->
    {{ Δ ⊢s σ : Γ }} ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ ->
    glu_rel_exp_with_sub pred_P s' Δ A {{{ Sort@s }}} σ ρ.
Proof.
  intros * ? ? [].
  simplify_evals.
  econstructor; mauto.
  assert {{ Δ ⊢ A[σ] : Sort@s }} by mauto 4 using glu_sort_elem_sort_lvl.
  repeat split; try do 2 eexists; mauto 3.
  assert {{ Γ ⊢ Sort@s : Sort@s' }} by mauto 3.
  assert {{ Δ ⊢ Sort@s : Sort@s' }} by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_typ_with_sub_implies_glu_rel_exp_with_sub : mcpts.

(** *** Lemmas for [glu_ctx_env] *)

Lemma glu_ctx_env_sub_resp_ctx_eq {P} (pred_P : PredicativeSig P) : forall {so Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P so ↘ Sb }} ->
    forall {Δ Δ' σ ρ},
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ ⊢ Δ ≈ Δ' }} ->
      {{ Δ' ⊢s σ ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hctxeq;
    apply_predicate_equivalence;
    simpl in *;
    mauto 4; destruct_by_head (@cons_glu_sub_pred P);
    econstructor; mauto 5;
    rewrite <- Hctxeq; eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) anns Sb Γ (H : glu_ctx_env pred_P anns Sb Γ) : Sb
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as glu_ctx_env_sub_morphism_iff1.
Proof.
  intros.
  split; intros; eapply glu_ctx_env_sub_resp_ctx_eq; mauto.
Qed.


Lemma glu_ctx_env_sub_resp_sub_eq {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    forall {Δ σ σ' ρ},
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ Δ ⊢s σ ≈ σ' : Γ }} ->
      {{ Δ ⊢s σ' ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hsubeq;
    apply_predicate_equivalence;
    simpl in *;
    gen_presup Hsubeq;
    try eassumption.

  - destruct_by_head (@cons_glu_sub_pred P).

    econstructor; mauto 4.
    inversion_clear H4.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] : Sort@s }} as <- by mauto 5.
    assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <- by mauto 5.
    eassumption.
  - destruct_by_head (@cons_glu_sub_pred P).

    econstructor; mauto 4.
    (* inversion H4. *)
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] }} as <- by mauto 5.
    assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <- by mauto 5.
    eassumption.
Qed.    

Add Parametric Morphism {P} (pred_P : PredicativeSig P) anns Sb Γ (H : glu_ctx_env pred_P anns Sb Γ) Δ : (Sb Δ)
    with signature wf_sub_eq Δ Γ ==> eq ==> iff as glu_ctx_env_sub_morphism_iff2.
Proof.
  split; intros; eapply glu_ctx_env_sub_resp_sub_eq; mauto.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq {P} (pred_P : PredicativeSig P) : forall {anns Γ A Sb Δ σ σ' ρ},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ Γ ⊢ A }} ->
    {{ Δ ⊢s σ ≈ σ' : Γ, A }} ->
    {{ Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred pred_P None Γ A Sb }} ->
    {{ Δ ⊢s σ' ® ρ ∈ cons_glu_sub_pred pred_P None Γ A Sb }}.
Proof.
  simpl.
  intros * Hglu HA Heq Hσ.
  dependent destruction Hσ.
  gen_presup Heq.
  assert {{ Δ ⊢s Wk∘σ : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ' : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ ≈ Wk∘σ' : Γ }} as HWkσσ' by mauto 3.
  econstructor; mauto 3.
  - assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] }} as <- by mauto 5.
    assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <- by mauto 4.
    eassumption.
  - rewrite <- HWkσσ'.
    eassumption.
Qed.

Add Parametric Morphism {P} (pred_P : PredicativeSig P) anns Γ A Sb Δ (Hglu : {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }}) (HA : {{ Γ ⊢ A }}) : (cons_glu_sub_pred pred_P None Γ A Sb Δ)
    with signature wf_sub_eq Δ {{{ Γ, A }}} ==> eq ==> iff as cons_glu_sub_pred_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq.
Qed.

Lemma cons_glu_sub_pred_resp_wf_sub_eq_sorted {P} (pred_P : PredicativeSig P) : forall {s anns Γ A Sb Δ σ σ' ρ},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ ≈ σ' : Γ, A }} ->
    {{ Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred pred_P (Some s) Γ A Sb }} ->
    {{ Δ ⊢s σ' ® ρ ∈ cons_glu_sub_pred pred_P (Some s) Γ A Sb }}.
Proof.
  simpl.
  intros * Hglu HA Heq Hσ.
  dependent destruction Hσ.
  gen_presup Heq.
  assert {{ Δ ⊢s Wk∘σ : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ' : Γ }} by mauto 3.
  assert {{ Δ ⊢s Wk∘σ ≈ Wk∘σ' : Γ }} as HWkσσ' by mauto 3.
  econstructor; mauto 3.
  - inversion_clear H1.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ ⊢ A[Wk][σ] ≈ A[Wk][σ'] : Sort@s }} as <- by mauto 5.
    assert {{ Δ ⊢ #0[σ] ≈ #0[σ'] : A[Wk][σ] }} as <- by mauto 4.
    eassumption.
  - rewrite <- HWkσσ'.
    eassumption.
Qed.


Add Parametric Morphism {P} (pred_P : PredicativeSig P) s anns Γ A Sb Δ (Hglu : {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }}) (HA : {{ Γ ⊢ A : Sort@s }}) : (cons_glu_sub_pred pred_P (Some s) Γ A Sb Δ)
    with signature wf_sub_eq Δ {{{ Γ, A }}} ==> eq ==> iff as cons_glu_sub_pred_unsorted_morphism_iff.
Proof.
  split; mauto using cons_glu_sub_pred_resp_wf_sub_eq_sorted.
Qed.


Lemma glu_ctx_env_per_env {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb env_rel Δ σ ρ},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Dom ρ ≈ ρ ∈ env_rel }}.
Proof.
  intros * Hglu Hper.
  gen ρ σ Δ env_rel.
  induction Hglu; intros;
    invert_per_ctx_env Hper;
    apply_predicate_equivalence;
    handle_per_ctx_env_irrel;
    mauto 3.

  - inversion_clear_by_head (@cons_glu_sub_pred P).
    assert {{ Dom ρ ↯ ≈ ρ ↯ ∈ tail_rel }} by intuition.
    destruct_rel_typ_unsorted.
    handle_per_typ_elem_irrel.
    assert (exists typ_rel' exp_rel', {{ DG a ∈ glu_typ_elem pred_P (Some s) ↘ typ_rel' ↘ exp_rel' }}) as [? []] by mauto 3.

    eexists; eauto.
    handle_functional_glu_typ_elem P.
    eapply glu_typ_elem_per_elem; mauto.
  - inversion_clear_by_head (@cons_glu_sub_pred P).
    assert {{ Dom ρ ↯ ≈ ρ ↯ ∈ tail_rel }} by intuition.
    destruct_rel_typ_unsorted.
    handle_per_typ_elem_irrel.
    assert (exists typ_rel' exp_rel', {{ DG a ∈ glu_typ_elem pred_P None ↘ typ_rel' ↘ exp_rel' }}) as [? []] by mauto 3.

    eexists; eauto.
    handle_functional_glu_typ_elem P.
    eapply glu_typ_elem_per_elem; mauto.
Qed.

Lemma glu_ctx_env_wf_ctx {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ ⊢ Γ }}.
Proof.
  induction 1; intros; mauto 3.
Qed.

Lemma glu_ctx_env_sub_escape {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    forall Δ σ ρ,
      {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
      {{ Δ ⊢s σ : Γ }}.
Proof.
  induction 1; intros;
    handle_functional_glu_sort_elem P;
    destruct_by_head (@cons_glu_sub_pred P);
    eassumption.
Qed.

#[export]
Hint Resolve glu_ctx_env_wf_ctx glu_ctx_env_sub_escape : mcpts.

Lemma glu_ctx_env_per_ctx_env {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}.
Proof.
  intros.
  enough {{ ⟪ pred_P ⟫ ⊨ Γ }} by eassumption.
  mauto 3 using completeness_fundamental_ctx.
Qed.

#[export]
Hint Resolve glu_ctx_env_per_ctx_env : mcpts.


(* Lemma glu_sort_elem_resp_per_subtyp_sorted {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel, *)
(*     {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} -> *)
(*     forall a', *)
(*       {{ ⟪ pred_P ⟫ Subs a <: a' at s }} -> *)
(*       exists typ_rel' exp_rel', *)
(*         {{ DG a' ∈ glu_sort_elem pred_P s ↘ typ_rel' ↘ exp_rel' }}. *)
(* Proof. *)
(*   simpl. *)
(*   induction 1 using glu_sort_elem_ind; *)
(*     intros * Hsub; dependent destruction Hsub; subst. *)
(*   - match_by_head (per_sort pred_P) ltac:(fun H => destruct H as []). *)
(*     invert_per_sort_elem H4. *)
(*     repeat eexists; glu_sort_elem_econstructor; mauto 2; reflexivity. *)
(*   - (* Pi case will require a helper lemma *) *)
(*     admit.  *)
(*     (* assert (glu_sort_elem pred_P s1 IP IEL a') by (eapply glu_sort_elem_resp_per_sort; mauto 3). *) *)
(*     (* handle_per_sort_elem_irrel. *) *)
(*     (* assert (per_sort_elem pred_P s1 in_rel a' a') by (etransitivity; [symmetry|]; eassumption). *) *)

(*     (* invert_per_sort_elems. *) *)
(*     (* assert (per_sort_elem pred_P s1 in_rel0 a a). *) *)
(*     (* { *) *)
(*     (*   destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub_s3_s as [[] ?]; subst; mauto 2. *) *)
(*     (* } *) *)
(*     (* assert (per_sort_elem pred_P s1 in_rel1 a' a'). *) *)
(*     (* { *) *)
(*     (*   destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub_s3_s as [[] ?]; subst; mauto 2. *) *)
(*     (* } *) *)
(*     (* handle_per_sort_elem_irrel. *) *)

(*     (* Pi case will need a helper lemma *) *)

(*     (* repeat eexists; glu_sort_elem_econstructor. *) *)
(*     (* + split; intros; subst; eassumption. *) *)
(*     (* + eassumption. *) *)
(*     (* + intros c equiv_c_c1. *) *)
(*     (*   assert (in_rel c c) as equiv_c_c by intuition. *) *)
(*     (*   assert (in_rel0 c c) as equiv_c_c0 by intuition. *) *)
(*     (*   destruct (H8 c c equiv_c_c0). *) *)
(*     (*   destruct H9. *) *)
(*     (*   intros. *) *)
(*     (*   simplify_evals. *) *)
(*     (*   rename b into b', a0 into b. *) *)
(*     (*   assert {{ ⟪ pred_P ⟫ Subs b <: b' at s2 }} by mauto 2. *) *)
(*     (*   assert (exists OP' OEL',  glu_sort_elem pred_P s2 OP' OEL' b') as [OP' [OEL']] by mauto 2. *) *)
      
(*     (*   split; intros; subst; mauto 2. *) *)
(*   - repeat eexists; glu_sort_elem_econstructor; mauto 2. *)
(*   - assert (per_bot e' e') by (etransitivity; [symmetry|]; eassumption). *)
(*     repeat eexists; glu_sort_elem_econstructor; mauto 2; try reflexivity. *)
(* Abort. *)

Lemma glu_sort_elem_resp_per_subtyp {P} (pred_P : PredicativeSig P) : forall a a' s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ ⟪ pred_P ⟫ Sub a <: a' }} ->
    exists so' typ_rel' exp_rel',
      {{ DG a' ∈ glu_typ_elem pred_P so' ↘ typ_rel' ↘ exp_rel' }}.
Proof.
  simpl.
  intros * Hglu Hsub.
  inversion Hsub; subst.
  - repeat eexists; econstructor; mauto 2; reflexivity.
  - assert (per_sort pred_P s0 a' a') as [R].
    {
      pose proof per_subtyp_sorted_to_sort_elem _ _ _ H as [? [? []]].
      eexists; eassumption.
    }
    pose proof per_sort_elem_glu_sort_elem pred_P _ _ _ H0 as [typ_rel' [exp_rel' ]].
    repeat eexists; econstructor; mauto 2.
Qed.

Lemma glu_typ_elem_resp_per_subtyp {P} (pred_P : PredicativeSig P) : forall a a' so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ ⟪ pred_P ⟫ Sub a <: a' }} ->
    exists so' typ_rel' exp_rel',
      {{ DG a' ∈ glu_typ_elem pred_P so' ↘ typ_rel' ↘ exp_rel' }}.
Proof.
  induction 1 using glu_typ_elem_ind; intros Hsub.
  - inversion Hsub; subst.
    + repeat eexists; mauto 2.
      econstructor; mauto 2; reflexivity.
    + inversion H1; subst.
      repeat eexists; mauto 2.
      econstructor; mauto 2; reflexivity.
  - eapply glu_sort_elem_resp_per_subtyp; mauto 2.
Qed.


Lemma glu_typ_elem_per_subtyp_trm_if {P} (pred_P : PredicativeSig P) : forall {so a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A' M m},
    {{ ⟪ pred_P ⟫ Sub a <: a' }} ->
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_typ_elem pred_P so ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A' ® m ∈ exp_rel' }}.
Proof.
  intros.
  dependent destruction H0.
  - inversion H2; subst.
    simpl_glu_rel.
    assert (st_subtyp s s0).
    {
      inversion H; try eassumption.
      inversion H9; eassumption.
    }
    pose proof glu_sort_elem_cumu pred_P H9 H7 as [typ_rel1 [exp_rel1]].
    repeat eexists; mauto 2.
    eapply glu_sort_elem_typ_cumu; mauto 2.
  - inversion H1; subst.
    eapply glu_sort_elem_per_subtyp_trm_if; mauto 2.
Qed.

(* This should be moves to CoreLemmas.v *)
Lemma glu_typ_elem_per_subtyp_trm_if' {P} (pred_P : PredicativeSig P) : forall {so so' a a' typ_rel typ_rel' exp_rel exp_rel' Γ A A' M m},
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⟪ pred_P ⟫ Sub a <: a' }} ->
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_typ_elem pred_P so' ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ A' ® typ_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M : A' ® m ∈ exp_rel' }}.
Proof.
  intros.
  destruct so; destruct so'.
  - eapply glu_typ_elem_per_subtyp_trm_if; mauto 4.
  - inversion H1; subst.
    inversion H2; subst.
    epose proof per_subtyp_sort_inv_left pred_P H0 as [s' []]; subst.
    apply_predicate_equivalence.
    destruct H4.
    destruct_conjs.
    invert_glu_sort_elem H8.
    apply_predicate_equivalence.
    unfold top_sort_glu_typ_pred in *.
    unfold top_sort_glu_exp_pred in *.
    unfold sort_glu_exp_pred' in *.
    unfold sort_glu_typ_pred in *.
    unfold glu_sort_typ_rec in *.
    simpl_glu_rel.
    assert {{ Γ ⊢ M : Sort@s0 }} by (eapply glu_sort_elem_sort_lvl; mauto 2).
    assert {{ Γ ⊢ Sort@s0 ⊆ Sort@s' }} by mauto 2.
    assert {{ Γ ⊢ M : Sort@s' }} by mauto 2.
    assert {{ Γ ⊢ M : A' }} by mauto 3.
    epose proof glu_sort_elem_cumu pred_P H13 H11.
    destruct_conjs.
    repeat eexists; mauto 4.
    eapply glu_sort_elem_typ_cumu; mauto 4.
  - inversion H1; subst.
    inversion H2; subst.
    epose proof per_subtyp_sort_inv_right pred_P H0 as [s' []]; subst.
    invert_glu_sort_elem H6; subst.
    apply_predicate_equivalence.
    unfold top_sort_glu_typ_pred in *.
    unfold sort_glu_exp_pred' in *.
    destruct_conjs.
    unfold glu_sort_typ_rec in *.
    destruct_conjs.
    
    simpl_glu_rel.
    econstructor; mauto 4.
    epose proof glu_sort_elem_cumu pred_P H9 H13.
    destruct_conjs.
    repeat eexists; mauto 4.
    eapply glu_sort_elem_typ_cumu; mauto 4.
  - inversion H1; subst.
    inversion H2; subst.
    eapply glu_sort_elem_per_subtyp_trm_conv; mauto 4.
Qed.

Lemma glu_ctx_env_resp_per_ctx_helper {P} (pred_P : PredicativeSig P) : forall {anns anns' Γ Γ' Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P anns' ↘ Sb' }} ->
    {{ ⊢ Γ ⊆ Γ' }} ->
    (Sb -∙> Sb').
Proof.
  intros * Hglu Hglu' HΓΓ'.
  gen anns' Sb' Γ'.
  dependent induction Hglu; intros;
    epose proof completeness_fundamental_ctx_sub _ pred_P _ _ HΓΓ' as Hsub;
    dependent destruction Hsub;
    apply_predicate_equivalence;
    handle_per_sort_elem_irrel;
    handle_per_typ_elem_irrel;
    dependent destruction Hglu';
    apply_predicate_equivalence;
    try firstorder.

  - invert_per_ctx_envs.
    handle_per_ctx_env_irrel.
    
    rename Γ'0 into Γ'.
    rename TSb0 into TSb'.
    rename tail_rel0 into tail_rel'.
    
    inversion HΓΓ' as [|? ? l ? l']; subst.

    assert (TSb -∙> TSb') by intuition.
    intros Δ σ ρ [].
    saturate_refl_for (@per_ctx_env P).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel' }} by (eapply glu_ctx_env_per_env; [| | eapply H10]; eassumption).
    assert {{ Δ0 ⊢s Wk∘σ0 ® ρ0 ↯ ∈ TSb' }} by intuition.
    
    assert (glu_rel_typ_with_sub_unsorted pred_P (Some s0) Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ0 ↯ }}}) by mautosolve 3.
    inversion H22; subst.
    assert {{ ⟪ pred_P ⟫ Sub a <: a0 }} by mauto 3.

    destruct_rel_typ_unsorted.
    handle_functional_glu_sort_elem P.
    handle_functional_glu_typ_elem P.
    simplify_evals.
    rename a0 into a'.
    rename exp_rel0 into exp_rel'.
    rename typ_rel0 into typ_rel'.
    assert (glu_typ_elem pred_P (Some s0) typ_rel' exp_rel' a') by (econstructor; mauto 2).
    
    econstructor; mauto 4.
    inversion H15; subst.
    inversion H16; subst.
    handle_functional_glu_sort_elem P.
    assert {{ Γ, A ⊢ A[Wk] ⊆ A'[Wk] }} by mauto 4.
    eapply glu_sort_elem_per_subtyp_trm_conv; mauto 3.
    assert {{ Δ0 ⊢s σ0 : Γ, A }} by mauto 3.
    assert {{ Δ0 ⊢ A'[Wk][σ0] ≈ A'[Wk∘σ0] : Sort@s0 }} as -> by (eapply exp_eq_sub_compose_typ_sorted; mauto 3).
    eassumption.
  - invert_per_ctx_envs.
    handle_per_ctx_env_irrel.
    
    rename Γ'0 into Γ'.
    rename TSb0 into TSb'.
    rename tail_rel0 into tail_rel'.
    
    inversion HΓΓ' as [|? ? l ? l']; subst.
    assert (TSb -∙> TSb') by intuition.
    intros Δ σ ρ [].
    saturate_refl_for (@per_ctx_env P).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel' }} by (eapply glu_ctx_env_per_env; [| | eapply H10]; eassumption).
    assert {{ Δ0 ⊢s Wk∘σ0 ® ρ0 ↯ ∈ TSb' }} by intuition.
    
    assert (glu_rel_typ_with_sub_unsorted pred_P None Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ0 ↯ }}}) by mautosolve 3.
    inversion H22; subst.
    inversion H15; subst.
    assert {{ ⟪ pred_P ⟫ Sub a <: Sort@s0 }} by mauto 3.
    
    destruct_rel_typ_unsorted.
    handle_functional_glu_sort_elem P.
    handle_functional_glu_typ_elem P.
    simplify_evals.
    rename exp_rel0 into exp_rel'.
    rename typ_rel0 into typ_rel'.
    
    econstructor; mauto 4.
    assert {{ Δ0 ⊢s σ0 : Γ, A }} by mauto 3.
    assert {{ Δ0 ⊢ A'[Wk][σ0] ≈ A'[Wk∘σ0] }} as -> by (eapply typ_eq_sub_compose_typ; mauto 3).
    eapply glu_typ_elem_per_subtyp_trm_if'; mauto 4.
    assert {{ Δ0 ⊢s σ0 : Γ, A }} by mauto 3.
    assert {{ Δ0 ⊢ A[Wk][σ0] ≈ A[Wk∘σ0] : Sort@s }} as <- by (eapply exp_eq_sub_compose_typ_sorted; mauto 3).
    eassumption.
  - invert_per_ctx_envs.
    handle_per_ctx_env_irrel.
    
    rename Γ'0 into Γ'.
    rename TSb0 into TSb'.
    rename tail_rel0 into tail_rel'.
    
    inversion HΓΓ' as [|? ? l ? l']; subst.

    assert (TSb -∙> TSb') by intuition.
    intros Δ σ ρ [].
    saturate_refl_for (@per_ctx_env P).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel' }} by (eapply glu_ctx_env_per_env; [| | eapply H10]; eassumption).
    assert {{ Δ0 ⊢s Wk∘σ0 ® ρ0 ↯ ∈ TSb' }} by intuition.
    
    assert (glu_rel_typ_with_sub_unsorted pred_P (Some s) Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ0 ↯ }}}) by mautosolve 3.
    inversion H22; subst.
    assert {{ ⟪ pred_P ⟫ Sub a <: a0 }} by mauto 3.

    destruct_rel_typ_unsorted.
    handle_functional_glu_sort_elem P.
    handle_functional_glu_typ_elem P.
    simplify_evals.
    rename a0 into a'.
    rename exp_rel0 into exp_rel'.
    rename typ_rel0 into typ_rel'.
    assert (glu_typ_elem pred_P (Some s) typ_rel' exp_rel' a') by (econstructor; mauto 2).

    econstructor; mauto 4.
    inversion H15; subst.
    inversion H; subst.
    handle_functional_glu_sort_elem P.

    assert {{ Γ, A ⊢ A[Wk] ⊆ A'[Wk] }} by mauto 4.
    eapply glu_typ_elem_per_subtyp_trm_if'; mauto 4.
    assert {{ Δ0 ⊢s σ0 : Γ, A }} by mauto 3.
    assert {{ Δ0 ⊢ A'[Wk][σ0] ≈ A'[Wk∘σ0] : Sort@s }} as -> by (eapply exp_eq_sub_compose_typ_sorted; mauto 3).
    eassumption.
    apply_predicate_equivalence.
    eassumption.
    
  - invert_per_ctx_envs.
    handle_per_ctx_env_irrel.
    
    rename Γ'0 into Γ'.
    rename TSb0 into TSb'.
    rename tail_rel0 into tail_rel'.
    
    inversion HΓΓ' as [|? ? l ? l']; subst.
    assert (TSb -∙> TSb') by intuition.
    intros Δ σ ρ [].
    saturate_refl_for (@per_ctx_env P).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel }} by (eapply glu_ctx_env_per_env; revgoals; eassumption).
    assert {{ Dom ρ0 ↯ ≈ ρ0 ↯ ∈ tail_rel' }} by (eapply glu_ctx_env_per_env; [| | eapply H10]; eassumption).
    assert {{ Δ0 ⊢s Wk∘σ0 ® ρ0 ↯ ∈ TSb' }} by intuition.
    
    assert (glu_rel_typ_with_sub_unsorted pred_P None Δ0 A' {{{ Wk∘σ0 }}} d{{{ ρ0 ↯ }}}) by mautosolve 3.
    inversion H22; subst.
    inversion H15; subst.
    assert {{ ⟪ pred_P ⟫ Sub Sort@s0 <: Sort@s }} by mauto 3.
    
    destruct_rel_typ_unsorted.
    handle_functional_glu_sort_elem P.
    simplify_evals.
    rename exp_rel0 into exp_rel'.
    rename typ_rel0 into typ_rel'.
    
    econstructor; mauto 4.
    assert {{ Δ0 ⊢s σ0 : Γ, A }} by mauto 3.
    assert {{ Δ0 ⊢ A'[Wk][σ0] ≈ A'[Wk∘σ0] }} as -> by (eapply typ_eq_sub_compose_typ; mauto 3).
    eapply glu_typ_elem_per_subtyp_trm_if'; mauto 4.
    assert {{ Δ0 ⊢s σ0 : Γ, A }} by mauto 3.
    assert {{ Δ0 ⊢ A[Wk][σ0] ≈ A[Wk∘σ0]  }} as <- by mauto 4.
    apply_predicate_equivalence.
    eassumption.
Qed.


Corollary functional_glu_ctx_env {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb' }} ->
    (Sb <∙> Sb').
Proof.
  intros.
  assert {{ ⊢ Γ ≈ Γ }} by mauto using glu_ctx_env_wf_ctx.
  split; eapply glu_ctx_env_resp_per_ctx_helper; mauto 3. 
Qed.


Ltac apply_functional_glu_ctx_env1 :=
  let tactic_error o1 o2 := fail 2 "functional_glu_ctx_env biconditional between" o1 "and" o2 "cannot be solved" in
  match goal with
  | H1 : {{ EG ^?Γ ∈ glu_ctx_env ?pred_P ?anns ↘ ?Sb1 }},
      H2 : {{ EG ^?Γ ∈ glu_ctx_env ?pred_P ?anns ↘ ?Sb2 }} |- _ =>
      assert_fails (unify Sb1 Sb2);
      match goal with
      | H : Sb1 <∙> Sb2 |- _ => fail 1
      | _ => assert (Sb1 <∙> Sb2) by (eapply functional_glu_ctx_env; [apply H1 | apply H2]) || tactic_error Sb1 Sb2
      end
  end.

Ltac apply_functional_glu_ctx_env :=
  repeat apply_functional_glu_ctx_env1.

Ltac handle_functional_glu_ctx_env P :=
  functional_eval_rewrite_clear;
  fold (glu_typ_pred P) in *;
  fold (glu_exp_pred P) in *;
  apply_functional_glu_ctx_env;
  apply_predicate_equivalence;
  clear_dups.

Lemma glu_ctx_env_cons_sorted_clean_inversion {P} (pred_P : PredicativeSig P) : forall {anns s Γ TSb A Sb},
  {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ TSb }} ->
  {{ EG Γ, A ∈ glu_ctx_env pred_P ((Some s) :: anns ) ↘ Sb }} ->
  {{ Γ ⊢ A : Sort@s }} /\
      (forall Δ σ ρ,
          {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
          glu_rel_typ_with_sub_unsorted pred_P (Some s) Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred pred_P (Some s) Γ A TSb).
Proof.
  intros.
  simpl in *.
  match_by_head (@glu_ctx_env P) progressive_invert.
  apply_functional_glu_ctx_env.

  intuition.
  rewrite -> H3.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Lemma glu_ctx_env_cons_unsorted_clean_inversion {P} (pred_P : PredicativeSig P) : forall {anns Γ TSb A Sb},
  {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ TSb }} ->
  {{ EG Γ, A ∈ glu_ctx_env pred_P (None :: anns) ↘ Sb }} ->
  {{ Γ ⊢ A }} /\
      (forall Δ σ ρ,
          {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
          glu_rel_typ_with_sub_unsorted pred_P None Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred pred_P None Γ A TSb).
Proof.
  intros.
  simpl in *.
  match_by_head (@glu_ctx_env P) progressive_invert.
  apply_functional_glu_ctx_env.

  intuition.
  rewrite -> H3.
  intros Δ σ ρ.
  split; intros [];
    econstructor; intuition.
Qed.

Lemma glu_ctx_env_cons_clean_inversion {P} (pred_P : PredicativeSig P) : forall {anns so Γ TSb A Sb},
  {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ TSb }} ->
  {{ EG Γ, A ∈ glu_ctx_env pred_P (so :: anns) ↘ Sb }} ->
  ((so = None /\ {{ Γ ⊢ A }}) \/ (exists s, so = Some s /\ {{ Γ ⊢ A : Sort@s }})) /\
      (forall Δ σ ρ,
          {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
          glu_rel_typ_with_sub_unsorted pred_P so Δ A σ ρ) /\
      (Sb <∙> cons_glu_sub_pred pred_P so Γ A TSb).
Proof.
  simpl.
  intros.
  destruct so.
  - pose proof glu_ctx_env_cons_unsorted_clean_inversion pred_P H H0.
    destruct_conjs.
    split; mauto 2.
    left; split; mauto 2.
  - pose proof glu_ctx_env_cons_sorted_clean_inversion pred_P H H0.
    destruct_conjs.
    split; mauto 2.
    right; eexists; split; mauto 2.
Qed.

Ltac invert_glu_ctx_env H :=
  (unshelve eapply (glu_ctx_env_cons_clean_inversion _ _ _ _) in H; shelve_unifiable; [eassumption |];
   destruct H as [? [? []]])
  + dependent destruction H.


Lemma glu_ctx_env_eqtyp_sub_if {P} (pred_P : PredicativeSig P) : forall anns Γ Γ' Sb Sb' Δ σ ρ,
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P anns ↘ Sb' }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb' }}.
Proof.
  intros * HΓΓ' HgluΓ HgluΓ'.
  assert (Sb -∙> Sb') by (eapply glu_ctx_env_resp_per_ctx_helper; mauto 2).
  intros.
  eapply H.
  eassumption.
Qed.


Lemma glu_ctx_env_sub_monotone {P} (pred_P : PredicativeSig P) : forall anns Γ Sb,
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    forall Δ' σ Δ τ ρ,
      {{ Δ ⊢s τ ® ρ ∈ Sb }} ->
      {{ Δ' ⊢w σ : Δ }} ->
      {{ Δ' ⊢s τ ∘ σ ® ρ ∈ Sb }}.
Proof.
  induction 1; intros * HSb Hσ;
    apply_predicate_equivalence;
    simpl in *;
    mauto 3;
    destruct_by_head (@cons_glu_sub_pred P).
  
  - econstructor; mauto 3.
    + assert {{ Δ' ⊢ #0[σ0][σ] : A[Wk][σ0][σ] ® m ∈ exp_rel }} by (eapply glu_typ_elem_exp_monotone; mauto 3).
      assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
      assert {{ Δ' ⊢ #0[σ0∘σ] ≈ #0[σ0][σ] : A[Wk][σ0∘σ] }} as -> by mauto 5.
      assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
      assert {{ Δ' ⊢ A[Wk][σ0][σ] ≈ A[Wk][σ0∘σ] : Sort@s }} as <- by mauto 4.
      eassumption.
    + assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
      assert {{ Δ' ⊢s (Wk ∘ σ0) ∘ σ ≈ Wk ∘ (σ0 ∘ σ) : Γ }} as <- by mauto 3.
      mauto 3.
  - econstructor; mauto 3.
    + assert {{ Δ' ⊢ #0[σ0][σ] : A[Wk][σ0][σ] ® m ∈ exp_rel }} by (eapply glu_typ_elem_exp_monotone; mauto 3).
      assert {{ Γ, A ⊢ #0 : A[Wk] }} by mauto 3.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
      assert {{ Δ' ⊢ #0[σ0∘σ] ≈ #0[σ0][σ] : A[Wk][σ0∘σ] }} as -> by mauto 5.
      assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
      assert {{ Δ' ⊢ A[Wk][σ0][σ] ≈ A[Wk][σ0∘σ] }} as <- by mauto 4.
      eassumption.
    + assert {{ Δ' ⊢s σ : Δ }} by mauto 3.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
      assert {{ Δ' ⊢s (Wk ∘ σ0) ∘ σ ≈ Wk ∘ (σ0 ∘ σ) : Γ }} as <- by mauto 3.
      mauto 3.
Qed.

Lemma cons_glu_sub_pred_helper_sorted {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb Δ σ ρ A a s typ_rel exp_rel M c},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_typ_elem pred_P (Some s) ↘ typ_rel ↘ exp_rel }} ->
    {{ Δ ⊢ M : A[σ] ® c ∈ exp_rel }} ->
    {{ Δ ⊢s σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred pred_P (Some s) Γ A Sb }}.
Proof.
  intros.
  inversion H3; subst.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ M : A[σ] }} by mauto 2 using glu_sort_elem_trm_escape.
  assert {{ Δ ⊢s σ,,M : Γ, A }} by mauto 3.
  econstructor; mauto 4;
    autorewrite with mcpts; mauto 4.


  assert {{ Δ ⊢ #0[σ,,M] ≈ M : A[σ] }}; mauto 3.
  assert {{ Δ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }} by mauto 4.
  enough (exp_rel Δ {{{ A[σ] }}} {{{ #0[σ,,M] }}} c) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto ).
  enough (exp_rel Δ {{{ A[σ] }}} M c) by (eapply glu_sort_elem_trm_resp_exp_eq; mauto 4).
  mauto.
Qed.

#[export]
  Hint Resolve cons_glu_sub_pred_helper_sorted : mcpts.

Lemma cons_glu_sub_pred_helper_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb Δ σ ρ A a typ_rel exp_rel M c},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    {{ Γ ⊢ A }} ->
    {{ ⟦ A ⟧ ρ ↘ a }} ->
    {{ DG a ∈ glu_typ_elem pred_P None ↘ typ_rel ↘ exp_rel }} ->
    {{ Δ ⊢ M : A[σ] ® c ∈ exp_rel }} ->
    {{ Δ ⊢s σ,,M ® ρ ↦ c ∈ cons_glu_sub_pred pred_P None Γ A Sb }}.
Proof.
  intros.
  assert {{ Δ ⊢s σ : Γ }} by mauto 2.
  assert {{ Δ ⊢ M : A[σ] }} by mauto 2 using glu_typ_elem_trm_escape.
  assert {{ Δ ⊢s σ,,M : Γ, A }} by mauto 3.
  econstructor; mauto 4;
    autorewrite with mcpts; mauto 4.

  assert {{ Δ ⊢ #0[σ,,M] ≈ M : A[σ] }}; mauto 3.
  assert {{ Δ ⊢ A[Wk][σ,,M] ≈ A[σ] }} by mauto 4.
  enough (exp_rel Δ {{{ A[σ] }}} {{{ #0[σ,,M] }}} c) by (eapply glu_typ_elem_none_trm_resp_typ_eq; mauto ).
  enough (exp_rel Δ {{{ A[σ] }}} M c) by (eapply glu_typ_elem_trm_resp_exp_eq; mauto 4).
  mauto.
Qed.

#[export]
  Hint Resolve cons_glu_sub_pred_helper_unsorted : mcpts.

Lemma initial_env_glu_rel_exp {P} (pred_P : PredicativeSig P) : forall {anns Γ ρ Sb},
    initial_env Γ ρ ->
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ Γ ⊢s Id ® ρ ∈ Sb }}.
Proof.
  intros * Hinit HΓ.
  gen ρ.
  induction HΓ; intros * Hinit;
    dependent destruction Hinit;
    apply_predicate_equivalence;
    try solve [econstructor; mauto].
  - rename ρ0 into ρ.
    assert (glu_rel_typ_with_sub_unsorted pred_P (Some s) Γ A {{{ Id }}} ρ) by mauto.
    inversion H1; subst.
    functional_eval_rewrite_clear.
    
    econstructor; mauto.
    + econstructor; mauto.
    + match goal with
      | H: typ_rel Γ {{{ A[Id] }}} |- _ =>
          bulky_rewrite_in H
      end.
      eapply realize_glu_elem_bot; mauto.
      assert {{ ⊢ Γ }} by mauto 3.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
      assert {{ Γ, A ⊢ A[Wk] : Sort@s }} by mauto 4.
      assert {{ Γ, A ⊢ A[Wk] ≈ A[Wk][Id] : Sort@s }} as <- by mauto 3.
      assert {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }} as <- by mauto.
      eapply var_glu_elem_bot; mauto.
    + gen_presup H.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
      assert {{ Γ, A ⊢s Wk∘Id : Γ }} by mauto 4.
      assert {{ Γ, A ⊢s Id∘Wk ≈ Wk∘Id : Γ }} as <- by (transitivity (@a_weaken P); mauto 3).
      eapply glu_ctx_env_sub_monotone; mauto 4.
  - rename ρ0 into ρ.
    assert (glu_rel_typ_with_sub_unsorted pred_P None Γ A {{{ Id }}} ρ) by mauto.    
    inversion H1; subst.
    functional_eval_rewrite_clear.
    econstructor; mauto.
    + eapply realize_glu_elem_bot_unsorted; mauto.
      assert {{ ⊢ Γ }} by mauto 3.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
      assert {{ Γ, A ⊢ A[Wk] }} by mauto 4.
      assert {{ Γ, A ⊢ A[Wk] ≈ A[Wk][Id] }} as <- by mauto 3.
      assert {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }} as <- by mauto.
      eapply var_glu_elem_bot_unsorted; mauto.
      assert {{ Γ ⊢ A[Id] ≈ A }} as <- by mauto 3.
      eassumption.
    + gen_presup H.
      assert {{ Γ, A ⊢s Wk : Γ }} by mauto 4.
      assert {{ Γ, A ⊢s Wk∘Id : Γ }} by mauto 4.
      assert {{ Γ, A ⊢s Id∘Wk ≈ Wk∘Id : Γ }} as <- by (transitivity (@a_weaken P); mauto 3).
      eapply glu_ctx_env_sub_monotone; mauto 4.
Qed.


(** *** Tactics for [glu_rel_*] *)

Ltac destruct_glu_rel_by_assumption sub_glu_rel H :=
  repeat
    match goal with
    | H' : {{ ^?Δ ⊢s ^?σ ® ^?ρ ∈ ?sub_glu_rel0 }} |- _ =>
        unify sub_glu_rel0 sub_glu_rel;
        destruct (H _ _ _ H') as [];
        destruct_conjs;
        mark_with H' 1
    end;
  unmark_all_with 1.

Ltac destruct_glu_rel_exp_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_exp_with_sub _ _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_exp_with_sub _ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

Ltac destruct_glu_rel_sub_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_sub_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_sub_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.

Ltac destruct_glu_rel_typ_with_sub :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_typ_with_sub _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_typ_with_sub _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


(** *** Lemmas about [glu_rel_exp] *)

Lemma glu_rel_exp_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {anns s Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s }} ->
    glu_rel_exp_resp_sub_env pred_P s Sb M A.
Proof.
  intros * ? [].
  destruct_conjs.
  intros ? **.
  handle_functional_glu_ctx_env P.
  mauto.
Qed.

#[global]
Ltac invert_glu_rel_exp H :=
 (unshelve eapply (glu_rel_exp_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption |];
  unfold glu_rel_exp_resp_sub_env in H)
  + (inversion H as [? [? [? ?]]]; subst).

Lemma glu_rel_exp_to_wf_exp {P} (pred_P : PredicativeSig P) : forall {anns s Γ A M},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  enough {{ Γ ⊢ M[Id] : A[Id] }} as HId; mauto 3 using glu_sort_elem_trm_escape.
Qed.

#[export]
Hint Resolve glu_rel_exp_to_wf_exp : mcpts.

(** *** Lemmas about [glu_rel_sub] *)

Lemma glu_rel_sub_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {anns anns' Γ Sb τ Γ'},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s τ : Γ' with anns'}} ->
    exists Sb' : glu_sub_pred P,
      glu_ctx_env pred_P anns' Sb' Γ' /\ (forall (Δ : ctx P) (σ : sub P) (ρ : env P), Sb Δ σ ρ -> glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ).
Proof.
  intros * ? [? []].
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 3.
  intros.
  rewrite_predicate_equivalence_left.
  mauto 3.
Qed.

Lemma glu_rel_sub_clean_inversion2 {P} (pred_P : PredicativeSig P) : forall {anns anns' Γ τ Γ' Sb'},
    {{ EG Γ' ∈ glu_ctx_env pred_P anns' ↘ Sb' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s τ : Γ' with anns' }} ->
    exists Sb : glu_sub_pred P,
      glu_ctx_env pred_P anns Sb Γ /\ (forall (Δ : ctx P) (σ : sub P) (ρ : env P), Sb Δ σ ρ -> glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ).
Proof.
  intros * ? [? [Sb'0]].
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  eexists; split; mauto 3.
  intros.
  assert (glu_rel_sub_with_sub pred_P Δ τ Sb'0 σ ρ) as [] by mauto 3.
  econstructor; mauto 3.
  rewrite_predicate_equivalence_left.
  mauto 3.
Qed.

Lemma glu_rel_sub_clean_inversion3 {P} (pred_P : PredicativeSig P) : forall {anns anns' Γ Sb τ Γ' Sb'},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ EG Γ' ∈ glu_ctx_env pred_P anns' ↘ Sb' }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s τ : Γ' with anns' }} ->
    glu_rel_sub_resp_sub_env pred_P Sb Sb' τ.
Proof.
  simpl. intros * ? ? Hglu.
  eapply glu_rel_sub_clean_inversion2 in Hglu; [| eassumption].
  destruct_conjs.
  handle_functional_glu_ctx_env P.
  intros.
  rewrite_predicate_equivalence_right.
  mauto 3.
Qed.

Ltac invert_glu_rel_sub H :=
  (unshelve eapply (glu_rel_sub_clean_inversion3 _ _ _) in H; shelve_unifiable; [eassumption | eassumption |])
  + (unshelve eapply (glu_rel_sub_clean_inversion2 _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (unshelve eapply (glu_rel_sub_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption |];
     destruct H as [? []])
  + (inversion H; subst).

Lemma glu_rel_sub_wf_sub {P} (pred_P : PredicativeSig P) : forall {anns anns' Γ σ Δ},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩s σ : Δ with anns'}} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  intros * [SbΓ [SbΔ]].
  destruct_conjs.
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ] by mauto 3 using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ SbΓ }} by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_sub_with_sub.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_sub_wf_sub : mcpts.


Ltac saturate_glu_typ_from_el1 :=
  match goal with
  | H : glu_sort_elem _ _ _ ?exp_rel _, H1 : ?exp_rel _ _ _ _ |- _ =>
      pose proof (glu_sort_elem_trm_typ _ _ _ _ _ H _ _ _ _ H1);
      fail_if_dup
  end.

Ltac saturate_glu_typ_from_el :=
  fail_if_dup;
  repeat saturate_glu_typ_from_el1.

Ltac apply_glu_rel_judge P :=
  destruct_glu_rel_typ_with_sub;
  destruct_glu_rel_exp_with_sub;
  destruct_glu_rel_sub_with_sub;
  simplify_evals;
  match_by_head (@glu_sort_elem P) ltac:(fun H => directed invert_glu_sort_elem H);
  handle_functional_glu_sort_elem P;
  unfold sort_glu_exp_pred' in *;
  destruct_conjs;
  clear_dups.


Lemma glu_rel_exp_preserves_lvl {P} (pred_P : PredicativeSig P) : forall {anns Γ Sb M A s},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    (forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_exp_with_sub pred_P s Δ M A σ ρ) ->
    {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros.
  assert (exists env_relΓ, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_relΓ }}) as [env_relΓ] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_relΓ }}) as [ρ] by mauto 3 using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  assert (glu_rel_exp_with_sub pred_P s Γ M A {{{ Id }}} ρ) by mauto 2.
  dependent destruction H4.
  saturate_glu_typ_from_el.
  saturate_glu_info.
  mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_preserves_lvl : mcpts.



Ltac saturate_syn_judge1 :=
  match goal with
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ with ?anns ⊩ ^?M : ^?A @ ^?s }} |- _ =>
      assert {{ Γ ⊢ M : A }} by mauto; fail_if_dup
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ with ?anns ⊩s ^?τ : ^?Γ' with ?anns' }} |- _ =>
      assert {{ Γ ⊢s τ : Γ' }} by mauto; fail_if_dup
  end.

#[global]
Ltac saturate_syn_judge :=
  repeat saturate_syn_judge1.

Ltac invert_sem_judge1 :=
  match goal with
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ with ?anns ⊩ ^?M : ^?A @ ^?s }} |- _ =>
      invert_glu_rel_exp H
  | H : {{ ⟪ ?pred_P ⟫ ^?Γ with ?anns ⊩s ^?τ : ^?Γ' with ?anns'}} |- _ =>
      invert_glu_rel_sub H
  end.

#[global]
Ltac invert_sem_judge :=
  repeat invert_sem_judge1.


Lemma glu_rel_exp_typ_well_sorted {P} (pred_P : PredicativeSig P) : forall {anns Γ M A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s }} ->
    {{ Γ ⊢ A : Sort@s }}.
Proof.
  intros.
  destruct H as [Sb []].
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ [ρ' []]] by mauto using per_ctx_then_per_env_initial_env.
  assert (Sb Γ {{{ Id }}} ρ) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  mauto 2.
Qed.


Lemma glu_rel_exp_typ_implies_glu_rel_typ {P} {pred_P : PredicativeSig P} : forall {s s' Γ A σ ρ},
    glu_rel_exp_with_sub pred_P s' Γ A {{{ Sort@s }}} σ ρ ->
    glu_rel_typ_with_sub pred_P s Γ A σ ρ.
Proof.
  intros.
  inversion_clear H.
  simplify_evals.
  invert_glu_sort_elem H2.
  unfold sort_glu_exp_pred' in H0.
  unfold glu_sort_typ_rec in H0.
  apply H0 in H3.
  destruct_conjs.
  econstructor; mauto 2.
Qed.


(* Lemma glu_rel_typ_implies_glu_rel_exp_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : forall {s Γ A σ ρ}, *)
(*     glu_rel_typ_with_sub pred_P s Γ A σ ρ -> *)
(*     exists s', glu_rel_exp_with_sub pred_P s' Γ A {{{ Sort@s }}} σ ρ. *)
(* Proof. *)
(*   intros. *)
(*   assert (exists s', Ax P s s') as [s'] by (eapply full_P). *)
(*   destruct H. *)
(*   eexists; econstructor; mauto 3. *)
(*   assert {{ Γ ⊢ A[σ] : Sort@s }} by (eapply glu_sort_elem_sort_lvl; mauto 3). *)
(*   gen_presup H3. *)
(*   assert (exists Δ K s', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ A : K }} /\ *)
(*                       (({{ Γ ⊢ K[σ] ≈ Sort@s }} /\ {{ Δ ⊢ K : Sort@s' }}) \/ ({{ Γ ⊢ K ≈ Sort@s }} /\ {{ Δ ⊢ K ≈ Sort@s' }}))) as [Δ [K [s'']]] by mauto 2. *)
(*   destruct_conjs. *)
(*   repeat split; mauto 3. *)
(*   repeat eexists; mauto 3. *)
(* Qed. *)


Lemma glu_rel_exp_sort_implies_ax {P} (pred_P : PredicativeSig P) : forall {anns Γ A s s'},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ A: Sort@s @ s' }} ->
    exists s'', Ax_typ P s s'' /\ st_subtyp s'' s'.
Proof.
  intros.
  destruct H as [SbΓ []].
  assert {{ ⊢ Γ }} by mauto 2.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ [ρ' []]] by mauto using per_ctx_then_per_env_initial_env.
  assert (SbΓ Γ {{{ Id }}} ρ) by (eapply initial_env_glu_rel_exp; mauto 3).
  destruct_glu_rel_exp_with_sub.
  simplify_evals.
  invert_glu_sort_elem H8.
  eexists; split; eassumption.
Qed.



(** Lemmas for unsorted logical relations *)
Lemma glu_rel_exp_implies_glu_rel_exp_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ M A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ ^(Some s) }}.
Proof.
  intros * [SbΓ []].
  eexists; split; [eassumption |].
  intros.
  destruct (H0 Δ σ ρ H1).
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_implies_glu_rel_exp_unsorted : mcpts.

Lemma glu_rel_exp_unsorted_implies_glu_rel_exp {P} (pred_P : PredicativeSig P) : forall {anns Γ M A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ M : A @ s }}.
Proof.
  intros * [SbΓ []].
  eexists; split; [eassumption |].
  intros.
  pose proof (H0 Δ σ ρ H1).
  inversion_clear H2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_exp_unsorted_implies_glu_rel_exp : mcpts.


Lemma glu_rel_typ_implies_glu_rel_typ_unsorted {P} (pred_P : PredicativeSig P) : forall {anns Γ A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ A @ s }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^(Some s) }}.
Proof.
  intros *[SbΓ []].
  eexists; split; [eassumption|].
  intros.
  destruct (H0 Δ σ ρ H1).
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_implies_glu_rel_typ_unsorted : mcpts.

Lemma glu_rel_typ_unsorted_implies_glu_rel_typ {P} (pred_P : PredicativeSig P) : forall {anns Γ A s},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ ^(Some s) }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩ A @ s }}.
Proof.
  intros *[SbΓ []].
  eexists; split; [eassumption|].
  intros.
  pose proof (H0 Δ σ ρ H1).
  inversion_clear H2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve glu_rel_typ_unsorted_implies_glu_rel_typ : mcpts.


(** Lemmas for unsorted relations *)
Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a Γ A M : (glu_elem_bot_unsorted pred_P so a Γ A M)
    with signature per_bot ==> iff as glu_elem_bot_unsorted_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; inversion_clear 1;
    econstructor; mauto 3;
    intros;
    specialize (Hmm' (length Δ)) as [? []];
    specialize (H3 (length Δ)) as [? []];
    functional_read_rewrite_clear;
    mauto 3.
Qed.


Add Parametric Morphism {P} (pred_P : PredicativeSig P) so a Γ A M R (H : per_typ_elem pred_P R a a) : (glu_elem_top_unsorted pred_P so a Γ A M)
    with signature R ==> iff as glu_elem_top_unsorted_morphism_iff4.
Proof.
  intros m m' Hmm' *.
  split; inversion_clear 1.
  all: (econstructor; mauto 3;
        pose proof (per_typ_elem_then_per_top H Hmm') as Hmm'';
        [try (etransitivity; mauto 3) |];
        intros;
        specialize (Hmm'' (length Δ)) as [? []];
        functional_read_rewrite_clear;
        mauto 3).
Qed.


Lemma glu_typ_elem_exp_unique_upto_exp_eq {P} (pred_P : PredicativeSig P) : forall {so a typ_rel typ_rel' exp_rel exp_rel' Γ A A' M M' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel' ↘ exp_rel' }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel' }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof.
  inversion_clear 1; inversion_clear 1; intros.
  - simpl_glu_rel.
    subst.
    mauto 4.
  - mauto 3.
Qed.

#[export]
Hint Resolve glu_typ_elem_exp_unique_upto_exp_eq : mcpts.

Lemma glu_typ_elem_exp_unique_upto_exp_eq' {P} (pred_P : PredicativeSig P) : forall {so a typ_rel exp_rel Γ A A' M M' m},
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M' : A' ® m ∈ exp_rel }} ->
    {{ Γ ⊢ M ≈ M' : A }}.
Proof. mautosolve 4. Qed.

#[export]
Hint Resolve glu_typ_elem_exp_unique_upto_exp_eq' : mcpts.


Lemma glu_typ_elem_per_typ_iff {P} (pred_P : PredicativeSig P) : forall {so a a' typ_rel typ_rel' exp_rel exp_rel'},
    {{ Dom a ≈ a' ∈ per_typ pred_P }} ->
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    {{ DG a' ∈ glu_typ_elem pred_P so ↘ typ_rel' ↘ exp_rel' }} ->
    (typ_rel <∙> typ_rel') /\ (exp_rel <∙> exp_rel').
Proof.
  inversion 2; subst.
  - destruct H as [R].
    pose proof (per_typ_elem_then_per_top_typ H) as Haa'.
    specialize (Haa' 0) as [? []].
    inversion H3; subst.
    inversion H4; subst.
    inversion_clear 1.
    split; etransitivity; [| symmetry | | symmetry]; mauto 2.
  - inversion_clear 1.
    eapply glu_sort_elem_per_typ_iff; mauto 2.
Qed.


Lemma glu_rel_exp_unsorted_clean_inversion1 {P} (pred_P : PredicativeSig P) : forall {anns so Γ Sb M A},
    {{ EG Γ ∈ glu_ctx_env pred_P anns ↘ Sb }} ->
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so }} ->
    glu_rel_exp_resp_sub_env_unsorted pred_P so Sb M A.
Proof.
  intros * ? [].
  destruct_conjs.
  intros ? **.
  handle_functional_glu_ctx_env P.
  mauto.
Qed.

#[global]
Ltac invert_glu_rel_exp_unsorted H :=
  (unshelve eapply (glu_rel_exp_unsorted_clean_inversion1 _ _) in H; shelve_unifiable; [eassumption |];
   unfold glu_rel_exp_resp_sub_env_unsorted in H)
  + (inversion H as [? [? [? ?]]]; subst).

Ltac destruct_glu_rel_exp_unsorted_by_assumption sub_glu_rel H :=
  repeat
    match goal with
    | H' : {{ ^?Δ ⊢s ^?σ ® ^?ρ ∈ ?sub_glu_rel0 }} |- _ =>
        unify sub_glu_rel0 sub_glu_rel;
        let H'' := fresh "H''" in
        assert (glu_rel_exp_with_sub_unsorted _ _ _ _ _ _ _) as H'' by (eapply (H _ _ _ H'); mauto 3);
        inversion_clear H'' as [];
        subst;
        destruct_conjs;
        mark_with H' 1
    end;
  unmark_all_with 1.

Ltac destruct_glu_rel_exp_with_sub_unsorted :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_exp_with_sub_unsorted _ _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_exp_unsorted_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_exp_with_sub_unsorted _ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


Ltac destruct_glu_rel_typ_with_sub_unsorted :=
  repeat
    match goal with
    | H : (forall Δ σ ρ, {{ Δ ⊢s σ ® ρ ∈ ?sub_glu_rel }} -> glu_rel_typ_with_sub_unsorted _ _ _ _ _ _) |- _ =>
        destruct_glu_rel_by_assumption sub_glu_rel H; fail_if_dup; mark H
    | H : glu_rel_typ_with_sub_unsorted _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


Lemma glu_rel_exp_unsorted_to_wf_exp {P} (pred_P : PredicativeSig P) : forall {anns so Γ A M},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u M : A @ so }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  assert (glu_rel_exp_with_sub_unsorted pred_P so Γ M A {{{ Id }}} ρ) by mauto 3.
  dependent destruction H4.
  - inversion_clear H8.
    
    simpl_glu_rel.
    assert {{ Γ ⊢ A }} by mauto 2.
    assert {{ Γ ⊢ A ≈ Sort@s }} by mauto 4.
    assert {{ Γ ⊢ M[Id] : Sort@s }} by (eapply glu_sort_elem_sort_lvl; mauto 3).    
    mauto 4.
  - enough {{ Γ ⊢ M[Id] : A[Id] }} as HId; mauto 3 using glu_sort_elem_trm_escape.
Qed.

#[export]
  Hint Resolve glu_rel_exp_unsorted_to_wf_exp : mcpts.

Lemma glu_rel_typ_unsorted_to_wf_typ {P} (pred_P : PredicativeSig P) : forall {anns so Γ A},
    {{ ⟪ pred_P ⟫ Γ with anns ⊩u A @ so }} ->
    {{ Γ ⊢ A }}.
Proof.
  intros * [Sb].
  destruct_conjs.
  assert (exists env_rel, {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ env_rel }}) as [env_rel] by mauto 3.
  assert (exists ρ ρ', initial_env Γ ρ /\ initial_env Γ ρ' /\ {{ Dom ρ ≈ ρ' ∈ env_rel }}) as [ρ] by mauto using per_ctx_then_per_env_initial_env.
  destruct_conjs.
  functional_initial_env_rewrite_clear.
  assert {{ Γ ⊢s Id ® ρ ∈ Sb }} by (eapply initial_env_glu_rel_exp; mauto 3).
  assert (glu_rel_typ_with_sub_unsorted pred_P so Γ A {{{ Id }}} ρ) by mauto 3.
  dependent destruction H4.
  - inversion_clear H7.
    simpl_glu_rel.
    mauto 2.
  - enough {{ Γ ⊢ A[Id] }} as HId; mauto 3 using glu_sort_elem_typ_escape.
Qed.

#[export]
Hint Resolve glu_rel_typ_unsorted_to_wf_typ : mcpts.



Lemma glu_rel_exp_with_sub_unsorted_typ_implies_glu_rel_typ_with_sub {P} (pred_P : PredicativeSig P) : forall {so s Δ A σ ρ},
    glu_rel_exp_with_sub_unsorted pred_P so Δ A {{{ Sort@s }}} σ ρ ->
    glu_rel_typ_with_sub pred_P s Δ A σ ρ.
Proof.
  intros * H.
  dependent destruction H.
  - inversion H2; subst.
    simpl_glu_rel.
    inversion H; subst.
    econstructor; mauto 4.
  - simplify_evals.
    invert_glu_sort_elem H1.
    unfold sort_glu_exp_pred' in H1.
    unfold glu_sort_typ_rec in H1.
    simpl_glu_rel.
    econstructor; mauto 2.
Qed.

#[export]
Hint Resolve glu_rel_exp_with_sub_unsorted_typ_implies_glu_rel_typ_with_sub : mcpts.
