From Coq Require Import Nat.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations.

Open Scope list_scope.

Lemma wf_ctx_sub_ctx_lookup {P} : forall n (A : typ P) s Γ,
    {{ #n : A@s ∈ Γ }} ->
    forall Δ,
      {{ ⊢ Δ ≈ Γ }} ->
      exists Δ1 A0 Δ2 A',
        Δ = Δ1 ++ (A0, s) :: Δ2 /\
          n = length Δ1 /\
          A' = iter (S n) (fun A => {{{ A[Wk] }}}) A0 /\
          {{ #n : A'@s ∈ Δ }} /\
          {{ Δ ⊢ A' ≈ A : Sort@s }}.
Proof.
  induction 1; intros; progressive_inversion.
  - exists nil.
    repeat eexists; mauto 4.
  - edestruct IHctx_lookup as [Δ1 [? [? [? [? [? [? []]]]]]]]; mauto.
    exists ((A0, s') :: Δ1). subst.
    repeat eexists; mauto 4.
Qed.

Lemma var_arith {P} : forall (Γ1 Γ2 : ctx P) (A : typ P) s,
    length (Γ1 ++ (A, s) :: Γ2) - length Γ2 - 1 = length Γ1.
Proof.
  intros.
  rewrite List.app_length. simpl.
  lia.
Qed.

Lemma var_weaken_gen {P} : forall (Δ : ctx P) (σ : sub P) (Γ : ctx P),
    {{ Δ ⊢w σ : Γ }} ->
    forall Γ1 Γ2 A0 s0,
      Γ = Γ1 ++ (A0, s0) :: Γ2 ->
      {{ Δ ⊢ #(length Γ1)[σ] ≈ #(length Δ - length Γ2 - 1) : ^(iter (S (length Γ1)) (fun A => {{{ A[Wk] }}}) A0)[σ] }}.
Proof.
  induction 1; intros; subst; gen_presups.
  - pose proof (app_ctx_vlookup _ _ _ _ _ ltac:(eassumption) eq_refl) as Hvar.
    
    (* gen_presup Hvar. *)
    pose proof (app_ctx_lookup Γ1 A0 Γ2 (length Γ1) s0 ltac:(reflexivity)).
    assert {{ ⊢ ^ (app Γ1 {{{ Γ2, A0@s0 }}}) }} by mauto.
    pose proof (presup_ctx_lookup_typ H1 H0).
    assert {{ ^(app Γ1 {{{ Γ2, A0@s0 }}}) ⊢ ^(iter (S (length Γ1)) (fun T : exp P => {{{ T[Wk] }}}) A0) }} by (eapply presup_exp_typ; mauto).   
    clear_dups.
    apply wf_sub_id_inversion in Hτ.
    pose proof (wf_ctx_sub_length _ _ Hτ).
    transitivity {{{ #(length Γ1)[^(@a_id P)] }}}; mauto 3.
    replace (length Γ) with (length (Γ1 ++ {{{ Γ2, A0@s0 }}})) by lia.
    rewrite var_arith.
    eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_id; mauto 3 |].
    transitivity {{{ ^(iter (S (length Γ1)) (fun T : exp P => {{{ T[Wk] }}}) A0)[Id] }}}; mauto.

  - pose proof (app_ctx_vlookup _ _ _ _ _ HΔ0 eq_refl) as Hvar.
    pose proof (app_ctx_lookup Γ1 A0 Γ2 _ s0 eq_refl).

    (* gen_presup Hvar. *)
    clear_dups.
    assert {{ ⊢ Δ', A@s }} by mauto 3.
    assert {{ Δ', A@s ⊢s Wk : ^(Γ1 ++ {{{ Γ2, A0@s0 }}}) }} by mauto 3.
    transitivity {{{ #(length Γ1)[Wk∘τ] }}}; [mauto 4 |].
    eapply wf_exp_eq_conv' with (A := {{{ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[Wk∘τ] }}}); mauto 4.
    
    etransitivity; [eapply wf_exp_eq_sub_compose_typ; mauto 3 |].
    pose proof (wf_ctx_sub_length _ _ H0).

    eapply wf_exp_eq_conv' with (A := {{{ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[Wk][τ] }}}); mauto 4.

    deepexec (@wf_ctx_sub_ctx_lookup P) ltac:(fun H => destruct H as [Γ1' [? [Γ2' [? [-> [? [-> []]]]]]]]).
    repeat rewrite List.app_length in *.

    etransitivity.
    + assert {{ ⊢ ^ (app Γ1' {{{ Γ2',x@s0 }}}) }} by mauto 3.
      eapply wf_exp_eq_sub_cong_typ; [| eapply wf_exp_eq_conv' |mauto 3].      
      * eapply wf_exp_sub_sort; mauto 2.
      * eapply wf_exp_eq_var_weaken; [mauto 3|]; eauto.
      * mauto 4.
    + replace (length Γ1) with (length Γ1') in * by lia.
      clear_refl_eqs.
      replace (length Γ2) with (length Γ2') by (simpl in *; lia).
      eapply wf_exp_eq_conv'.
      * eapply IHweakening with (Γ1 := (A, s) :: _).
        reflexivity.
      * eapply wf_exp_eq_sub_cong_sort; mauto 3.
Qed.

Lemma var_glu_elem_bot {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel Γ A,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} -> 
    {{ Γ, A@s ⊢ #0 : A[Wk] ® !(length Γ) ∈ glu_elem_bot pred_P s a }}.
Proof.
  intros. saturate_glu_info.
  econstructor; mauto 4.
  - eapply glu_sort_elem_typ_monotone; eauto.
    assert {{ ⊢ Γ, A@s }} by mauto 3.
    eapply weakening_wk; mauto 3.
  - intros. progressive_inversion.
    exact (var_weaken_gen _ _ _ H2 nil _ _ _ eq_refl).
Qed.

#[local]
Hint Rewrite -> @wf_sub_eq_extend_compose using mauto 4 : mcpts.


Theorem realize_glu_sort_elem_gen {P} {pred_P : PredicativeSig P} : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    (forall Γ A R,
        {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} ->
        {{ Γ ⊢ A ® typ_rel }} ->
        {{ Γ ⊢ A ® glu_typ_top pred_P s a }}) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_bot pred_P s a }} ->
          {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
          {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} ->
          {{ Dom m ≈ m ∈ R }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P s a }}).
Proof.
  simpl. induction 1 using glu_sort_elem_ind.
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 (@per_sort_elem P) ltac:(fun H => pose proof (per_sort_then_per_top_typ H));
    match_by_head (@glu_elem_bot P) ltac:(fun H => destruct H as []);
    destruct_all.
  - econstructor; eauto; intros.
    progressive_inversion.
    transitivity {{{ Sort@s'[σ] }}}; mauto 3.
  - handle_functional_glu_sort_elem P.
    match_by_head (@glu_sort_elem P) invert_glu_sort_elem.
    clear_dups.
    apply_equiv_left.
    repeat split; eauto.
    repeat eexists.
    + glu_sort_elem_econstructor; eauto; reflexivity.
    + simpl. repeat split.
      * rewrite <- H5. trivial.
      * intros.
        saturate_weakening_escape.
        rewrite <- wf_exp_eq_typ_sub; try eassumption.
        rewrite <- H5.
        firstorder.
  - deepexec (@glu_sort_elem_per_sort P) ltac:(fun H => pose proof H).
    unfold per_sort in H10. deex.
    firstorder.
    specialize (H _ _ _ H8) as [? []].
    econstructor; mauto 3.
    + apply_equiv_left. trivial.
    + intros.
      saturate_weakening_escape.
      deepexec H ltac:(fun H => destruct H).
      progressive_invert H14.
      deepexec H18 ltac:(fun H => pose proof H).
      functional_read_rewrite_clear.
      bulky_rewrite.

  - match_by_head (@pi_glu_typ_pred P) progressive_invert.
    handle_per_sort_elem_irrel.
    invert_per_sort_elem H6.
    econstructor; eauto; intros.
    + gen_presups. trivial.
    + saturate_weakening_escape.
      assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      assert {{ Δ ⊢ IT[σ] ® IP }} by mauto 3.
      assert (IP Γ {{{ IT[Id] }}}) as HITId by mauto 3.
      bulky_rewrite_in HITId.
      assert {{ Γ ⊢ IT[Id] ≈ IT : Sort@s1 }} by mauto 3.
      dependent destruction H17.
      assert {{ Γ ⊢ IT ® glu_typ_top pred_P s1 a }} as [] by mauto 3.
      bulky_rewrite.
      simpl. apply wf_exp_eq_pi_cong'; [firstorder |].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      assert (IEL {{{ Δ, IT[σ]@s1 }}} {{{ IT[σ][Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}) by mauto 3 using var_glu_elem_bot.
      assert {{ Δ, IT[σ]@s1 ⊢ IT[σ][Wk] ≈ IT[σ∘Wk] : Sort@s1 }}.
      {
        symmetry.
        eapply exp_eq_sub_compose_typ_sort; mauto.
      }
      assert (IEL {{{ Δ,IT[σ]@s1 }}} {{{ IT[σ∘Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2).
      specialize (H14 {{{ Δ, IT[σ]@s1 }}} {{{ σ∘Wk }}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)).
      specialize (H8 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      etransitivity; [| eapply H33]; mauto 3.
  - handle_functional_glu_sort_elem P.
    apply_equiv_left.
    invert_glu_rel1.
    econstructor; try eapply per_bot_then_per_elem; eauto.

    intros.
    saturate_weakening_escape.
    saturate_glu_info.
    match_by_head1 (@per_sort_elem P) invert_per_sort_elem.
    destruct_rel_mod_eval.
    simplify_evals.
    eexists; repeat split; mauto 3.
    eapply H2; eauto.
    assert (HAs3: {{ Γ ⊢ A : Sort@s3 }}) by (gen_presup H4; mauto 2).
    assert {{ Δ ⊢ M[σ] : A[σ] }} by mauto 3.
    bulky_rewrite_in H23.
    unshelve (econstructor; eauto).
    + trivial.
    + eassert {{ Δ ⊢ M[σ] N : ^_ }} by (eapply wf_app'; eassumption).
      assert {{ Δ ⊢ M[σ] N : OT[σ,,N] }} by mauto 4.
      trivial.
    + mauto using domain_app_per.
    + intros.
      saturate_weakening_escape.
      progressive_invert H26.
      destruct (H15 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) equiv_n).
      handle_functional_glu_sort_elem P.
      
      assert {{ Δ0 ⊢ OT[σ∘σ0,,N[σ0]] ≈ OT[σ,,N][σ0] : Sort@s2 }} by (transitivity {{{ OT[(σ,,N)∘σ0] }}}; mauto 4).
      enough {{ Δ0 ⊢ (M[σ] N)[σ0] ≈ ^ n{{{ M0 N0 }}} : OT[σ∘σ0,,N[σ0]] }} by mauto.

      etransitivity.
      * assert {{ Δ0 ⊢ OT[σ∘σ0,,N[σ0]] ≈ OT[q σ][σ0,,N[σ0]] : Sort@s2 }} by (eapply sub_decompose_q_typ; mauto 3).
        eapply wf_exp_eq_conv' with (A:= {{{ OT[q σ][σ0,,N[σ0]] }}}); mauto 3.
      * simpl.
        rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.
        assert {{ Δ0 ⊢ OT[q (σ∘σ0)][(Id,,N[σ0])] ≈ OT[q (σ∘σ0)∘(Id,,N[σ0])] : Sort@s2 }}.
        {
          symmetry.
          assert {{ Δ0 ⊢ IT[σ][σ0][Id] ≈ IT[σ][σ0] : Sort@s1 }} by mauto 4.
          assert {{ Δ0 ⊢ N[σ0] : IT[σ][σ0] }} by mauto 3.
          assert {{ Δ0 ⊢ N[σ0] : IT[σ][σ0][Id] }} by mauto 3.
          assert {{ Δ0 ⊢s Id,,N[σ0] : Δ0, IT[σ][σ0]@s1 }} by mauto 4.
          assert {{ Δ0 ⊢s σ∘σ0 : Γ }} by mauto 2.
          assert {{ Δ0, IT[σ∘σ0]@s1 ⊢s q (σ∘σ0) : Γ, IT@s1 }} by mauto 4.
          assert {{ Δ0 ⊢ IT[σ∘σ0] ≈ IT[σ][σ0] : Sort@s1 }} by mauto 3.
          assert {{ ⊢ Δ0 }} by mauto 2.
          assert {{ ⊢ Δ0, IT[σ][σ0]@s1 ≈ Δ0, IT[σ∘σ0]@s1 }} by mauto 4.
          assert {{ Δ0 ⊢s Id,,N[σ0] : Δ0, IT[σ∘σ0]@s1 }} by mauto 4.
          eapply wf_exp_eq_sub_compose_sort; mauto 2.
        }
        
        eapply wf_exp_eq_conv' with (A:= {{{ OT[q (σ∘σ0)][(Id,,N[σ0])] }}}); mauto 3.
        eapply wf_exp_eq_app_cong'.
        -- specialize (H12 _ {{{σ ∘ σ0}}} _ ltac:(mauto 3) ltac:(eassumption)).
           rewrite wf_exp_eq_sub_compose_typ with (M := M) in H12; mauto 3.
           bulky_rewrite_in H12.
        -- assert (wf_typ_eq Δ0 {{{ IT[σ][σ0] }}} {{{ IT[σ∘σ0] }}}) by mauto.
           eapply wf_exp_eq_conv'; mauto 3.
        -- assert (wf_typ Δ0 {{{ IT[σ∘σ0] }}}) by mauto.
           assert (wf_typ Δ0 {{{ IT[σ][σ0] }}}) by mauto 4.
           econstructor; mauto 3.
           
  - handle_functional_glu_sort_elem P.
    handle_per_sort_elem_irrel.
    pose proof H8.
    invert_per_sort_elem H8.
    econstructor; mauto 3.
    + invert_glu_rel1. trivial.
    + eapply glu_sort_elem_trm_typ; eauto.
    + intros.
      saturate_weakening_escape.
      invert_glu_rel1. clear_dups.
      progressive_invert H20.
      assert (weakening Γ (@a_id P) Γ) by mauto 3.
      pose proof (H10 _ _ H24).
      specialize (H10 _ _ H19).
      assert (wf_exp_eq Γ {{{ Sort@s1 }}} {{{ IT[Id] }}} {{{ IT }}}) by mauto 3.
      bulky_rewrite_in H25.
      destruct (H11 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H29 _ _ _ H19 H9).
      rewrite H5 in *.
      autorewrite with mcpts.
      eassert (wf_exp Δ _ {{{ M[σ] }}}) by mauto 3.
      autorewrite with mcpts in H30.
      rewrite @wf_exp_eq_pi_eta' with (M := {{{ M[σ] }}}); [| trivial].
      cbn [nf_to_exp].
      eapply wf_exp_eq_fn_cong'; eauto; [| mauto 4].
      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      specialize (H12 _ _ _ _ ltac:(trivial) (var_glu_elem_bot _ _ _ _ _ _ _ H H10)).
      assert (IEL {{{ Δ,IT[σ]@s1 }}} {{{ IT[σ∘Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}).
      {
        eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3.
        symmetry.
        eapply exp_eq_sub_compose_typ_sort; mauto 4.
      }
      specialize (H14 {{{Δ, IT[σ]@s1 }}} {{{σ ∘ Wk}}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)) as [? []].
      apply_equiv_left.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      specialize (H33 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H41 _ {{{Id}}} _ ltac:(mauto 3) ltac:(eassumption)).
      do 2 (rewrite wf_exp_eq_sub_id in H41; mauto 4).
      etransitivity; [|eassumption].
      simpl.
      assert (wf_exp {{{ Δ, IT[σ]@s1 }}} {{{ IT[σ∘Wk] }}} (@a_var P 0)).
      {
        eapply wf_conv' with (A := {{{ IT[σ][Wk] }}}); mauto 3.
        symmetry; eapply wf_exp_eq_sub_compose_sort; mauto 3.
      }
      rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.
      assert (wf_exp {{{ Γ, IT@s1 }}} {{{ Sort@s2 }}} OT ) by mauto 3.
      assert (wf_sub Δ Γ σ) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ]@s1 }}} Δ {{{ Wk }}}) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ]@s1 }}} Γ {{{ σ ∘ Wk }}}) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ]@s1, IT[σ∘Wk]@s1 }}} {{{ Γ, IT@s1 }}} {{{ q (σ∘Wk ) }}}) by mauto 3.
      assert (wf_exp {{{ Δ, IT[σ]@s1 }}} {{{ IT[σ∘Wk] }}} {{{ #0 }}}) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ]@s1 }}} {{{ Δ, IT[σ]@s1, IT[σ∘Wk]@s1 }}} {{{ Id,,#0 }}}) by mauto 4.
      assert (wf_exp_eq {{{ Δ, IT[σ]@s1 }}} {{{ Sort@s2 }}} {{{ OT[q (σ∘Wk)∘(Id,,#0)] }}} {{{ OT[q (σ∘Wk)][Id,,#0] }}}) by (symmetry; mauto 3).
      eapply wf_exp_eq_conv' with (A := {{{ OT[q (σ∘Wk)][Id,,#0] }}}); mauto 2.
      eapply wf_exp_eq_app_cong'; [| mauto 3].
      symmetry.
      rewrite <- wf_exp_eq_pi_sub; mauto 4.      
      
  - econstructor; eauto.
    intros.
    progressive_inversion.
    firstorder.
  - handle_functional_glu_sort_elem P.
    apply_equiv_left.
    econstructor; eauto.
  - handle_functional_glu_sort_elem P.
    invert_glu_rel1.
    econstructor; eauto.
    + intros i. destruct (H3 i) as [? []].
      mauto.
    + intros.
      progressive_inversion.
      specialize (H3 (length Δ)) as [? []].
      firstorder.
Qed.


Corollary realize_glu_typ_top {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A ® glu_typ_top pred_P s a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_sort_elem_per_sort in H.
  simpl in *. destruct_all.
  eapply realize_glu_sort_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_bot {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ glu_elem_bot pred_P s a }} ->
      {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}.
Proof.
  intros.
  eapply realize_glu_sort_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P s a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_sort_elem_per_sort in H.
  simpl in *. destruct_all.
  eapply realize_glu_sort_elem_gen; eauto.
  eapply glu_sort_elem_per_elem; eauto.
Qed.

#[export]
Hint Resolve realize_glu_typ_top realize_glu_elem_top : mcpts.

Corollary var0_glu_elem {P} (pred_P : PredicativeSig P) : forall {s a typ_rel exp_rel Γ A},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ, A@s ⊢ #0 : A[Wk] ® ⇑! a (length Γ) ∈ exp_rel }}.
Proof.
  intros.
  eapply realize_glu_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.


(** Realizability for unsorted gluing model *)
Theorem realize_glu_typ_elem_gen {P} {pred_P : PredicativeSig P} : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    (forall Γ A R,
        {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
        {{ Γ ⊢ A ® typ_rel }} ->
        {{ Γ ⊢ A ® glu_typ_top_unsorted pred_P so a }}) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_bot_unsorted pred_P so a }} ->
          {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
          {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
          {{ Dom m ≈ m ∈ R }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_top_unsorted pred_P so a }}).
Proof.
  destruct 1; subst.
  - repeat split; intros.
    + simpl_glu_rel; econstructor; mauto 3.
    + inversion_clear H3.
      inversion_clear H6.
      handle_functional_glu_sort_elem P.
      simpl in H7.
      simpl.
      split; mauto 2.
      do 2 eexists; split.
      * glu_sort_elem_econstructor; mauto 2; reflexivity.
      * simpl.
        split; [subst; mauto 2|].
        intros.
        subst.
        eapply H9; mauto 3.
    + simpl_glu_rel.
      assert {{ Γ ⊢ M ® glu_typ_top pred_P s m }} by mauto 3.
      destruct H8.
      subst.
      econstructor; mauto 2.
      * inversion_clear H2.
        simpl_glu_rel.
        reflexivity.
      * intros.
        inversion_clear H11.
        eapply H10; mauto 2.        

  - assert (glu_sort_elem pred_P s typ_rel exp_rel a) by eassumption. 
    eapply realize_glu_sort_elem_gen in H0.
    destruct_conjs.
    repeat split; intros.
    + enough (glu_typ_top pred_P s a Γ A).
      {
        destruct H5.
        econstructor; mauto 3.
      }
      eapply H0; mauto 3.
      assert (per_sort pred_P s a a) as [] by mauto 2.
      assert (per_sort_elem pred_P s R a a) by mauto 3. 
      eassumption.
    + eapply H1; mauto 3.
      inversion_clear H4.
      econstructor; mauto 3.
    + enough (glu_elem_top pred_P s a Γ A M m).
      {
        destruct H7.
        econstructor; mauto 3.
      }
      eapply H2; mauto 3.
      assert (per_sort pred_P s a a) as [] by mauto 2.
      assert (per_sort_elem pred_P s R a a) by mauto 3. 
      eassumption.
Qed.


Corollary realize_glu_typ_top_unsorted {P} (pred_P : PredicativeSig P) : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A ® glu_typ_top_unsorted pred_P so a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_typ_elem_per_typ in H.
  simpl in *. destruct_all.
  eapply realize_glu_typ_elem_gen; eauto.
Qed.

Corollary realize_glu_elem_bot_unsorted {P} (pred_P : PredicativeSig P) : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ glu_elem_bot_unsorted pred_P so a }} ->
      {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}.
Proof.
  intros.
  eapply realize_glu_typ_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top_unsorted {P} (pred_P : PredicativeSig P) : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M : A ® m ∈ glu_elem_top_unsorted pred_P so a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_typ_elem_per_typ in H.
  simpl in *. destruct_all.
  eapply realize_glu_typ_elem_gen; eauto.
  eapply glu_typ_elem_per_elem; eauto.
Qed.

#[export]
Hint Resolve realize_glu_typ_top_unsorted realize_glu_elem_top_unsorted : mcpts.
