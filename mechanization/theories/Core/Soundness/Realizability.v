From Coq Require Import Nat.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations.

Open Scope list_scope.

Lemma wf_ctx_sub_ctx_lookup {P} : forall n (A : typ P) Γ,
    {{ #n : A ∈ Γ }} ->
    forall Δ,
      {{ ⊢ Δ ≈ Γ }} ->
      exists Δ1 A0 Δ2 A',
        Δ = Δ1 ++ A0 :: Δ2 /\
          n = length Δ1 /\
          A' = iter (S n) (fun A => {{{ A[Wk] }}}) A0 /\
          {{ #n : A' ∈ Δ }} /\
          {{ Δ ⊢ A' ≈ A }}.
Proof.
  induction 1; intros; progressive_inversion.
  - exists nil.
    repeat eexists; mauto 4.
  - edestruct IHctx_lookup as [Δ1 [? [? [? [? [? [? []]]]]]]]; mauto.
    exists (A0 :: Δ1). subst.
    repeat eexists; mauto 4.
Qed.

Lemma var_arith {P} : forall (Γ1 Γ2 : ctx P) (A : typ P),
    length (Γ1 ++ A :: Γ2) - length Γ2 - 1 = length Γ1.
Proof.
  intros.
  rewrite List.length_app. simpl.
  lia.
Qed.

Lemma var_weaken_gen {P} : forall (Δ : ctx P) (σ : sub P) (Γ : ctx P),
    {{ Δ ⊢w σ : Γ }} ->
    forall Γ1 Γ2 A0,
      Γ = Γ1 ++ A0 :: Γ2 ->
      {{ Δ ⊢ #(length Γ1)[σ] ≈ #(length Δ - length Γ2 - 1) : ^(iter (S (length Γ1)) (fun A => {{{ A[Wk] }}}) A0)[σ] }}.
Proof.  
  induction 1; intros; subst; gen_presups.
  - pose proof (app_ctx_vlookup _ _ _ _ ltac:(eassumption) eq_refl) as Hvar.

    (* gen_presup Hvar. *)
    assert {{ ⊢ ^ (app Γ1 {{{ Γ2, A0 }}}) }} by mauto.
    assert {{ ^(app Γ1 {{{ Γ2, A0 }}}) ⊢ ^(iter (S (length Γ1)) (fun T : exp P => {{{ T[Wk] }}}) A0) }} by (eapply presup_exp_typ; mauto).   
    clear_dups.
    apply wf_sub_id_inversion in Hτ.
    pose proof (wf_ctx_sub_length _ _ Hτ).
    transitivity {{{ #(length Γ1)[^(@a_id P)] }}}; [mauto 3 |].
    replace (length Γ) with (length (Γ1 ++ {{{ Γ2, A0 }}})) by lia.
    rewrite var_arith.
    eapply wf_exp_eq_conv; [eapply wf_exp_eq_sub_id; mauto | mauto |].
    transitivity {{{ ^(iter (S (length Γ1)) (fun T : exp P => {{{ T[Wk] }}}) A0)[Id] }}}; mauto.

  - pose proof (app_ctx_vlookup _ _ _ _ HΔ0 eq_refl) as Hvar.
    pose proof (app_ctx_lookup Γ1 A0 Γ2 _ eq_refl).

    gen_presup Hvar.
    clear_dups.
    assert {{ ⊢ Δ', A }} by mauto 3.
    assert {{ Δ', A ⊢s Wk : ^(Γ1 ++ {{{ Γ2, A0 }}}) }} by mauto 3.
    transitivity {{{ #(length Γ1)[Wk∘τ] }}}; [mauto 3 |].
    eapply wf_exp_eq_conv' with (A := {{{ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[Wk∘τ] }}}); mauto 3.
    
    etransitivity; [eapply wf_exp_eq_sub_compose; mauto 3 |].
    pose proof (wf_ctx_sub_length _ _ H0).

    eapply wf_exp_eq_conv' with {{{ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[Wk][τ] }}}; mauto 3.

    deepexec (@wf_ctx_sub_ctx_lookup P) ltac:(fun H => destruct H as [Γ1' [? [Γ2' [? [-> [? [-> []]]]]]]]).
    repeat rewrite List.length_app in *.
    replace (length Γ1) with (length Γ1') in * by lia.
    clear_refl_eqs.
    replace (length Γ2) with (length Γ2') by (simpl in *; lia).

    etransitivity.
    + eapply wf_exp_eq_sub_cong; [ |mauto 3].
      eapply wf_exp_eq_conv'.
      * eapply wf_exp_eq_var_weaken; [mauto 3|]; eauto.
      * mauto 4.
    + eapply wf_exp_eq_conv'.
      * eapply IHweakening with (Γ1 := A :: _).
        reflexivity.
      * eapply wf_subtyp_subst; [ |mauto 3].
        simpl. eapply wf_subtyp_subst; mauto 3.
Qed.

Lemma var_glu_elem_bot {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel Γ A,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    typ_rel Γ A ->
    (* {{ Γ ⊢ A ® P }} -> *)
    glu_elem_bot pred_P s a {{{ Γ, A }}} {{{ A[Wk] }}} {{{ #0 }}} (d_var (length Γ) ).
    (* {{ Γ, A ⊢ #0 : A[Wk] ® !(length Γ) ∈ glu_elem_bot pred_P s a }}. *)
Proof.
  intros. saturate_glu_info.
  econstructor; mauto 4.
  - eapply glu_sort_elem_typ_monotone; eauto.
    assert {{ ⊢ Γ, A }} by mauto 3.
    eapply weakening_wk; mauto 3.
  - intros. progressive_inversion.
    exact (var_weaken_gen _ _ _ H2 nil _ _ eq_refl).
Qed.

#[local]
Hint Rewrite -> @wf_sub_eq_extend_compose using mauto 4 : mcpts.

      
Theorem realize_glu_sort_elem_gen {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    (forall Γ A R,
        {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} ->
        {{ Γ ⊢ A ® typ_rel }} ->
        {{ Γ ⊢ A ® glu_typ_top_unsorted pred_P a }}) /\
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
    try match_by_head1 per_sort_elem ltac:(fun H => pose proof (per_sort_then_per_top_typ H));
    match_by_head (@glu_elem_bot P) ltac:(fun H => destruct H as []);
    destruct_all.
  - econstructor; eauto; intros.
    + intros; eexists; split; mauto 2.
    + inversion_clear H5.
      transitivity {{{ Sort@s'[σ] }}}; mauto 4.
      (* eapply H4; mauto 3. *)
      
    (* assert (wf_exp Γ {{{ Sort@s }}} A). *)
    (* { *)
    (*   gen_presup H3. *)
    (*   assert (wf_exp Γ {{{ Sort@s }}} {{{ Sort@s' }}}) by mauto 2. *)
    (*   assert (wf_exp_eq Γ {{{ Sort@s }}} {{{ A[Id] }}} {{{ Sort@s' }}}) by (eapply H4; mauto 3). *)
    (*   gen_presup H6. *)
    (*   mauto 2. *)
    (* } *)
    (* econstructor; eauto; intros. *)
    (* progressive_inversion. *)
    (* + intros; eexists; split; mauto. *)
    (* + inversion_clear H7. *)
    (*   transitivity {{{ Sort@s'[σ] }}}; mauto 4. *)
    (*   eapply H4; mauto 3. *)
  - handle_functional_glu_sort_elem P.
    match_by_head (@glu_sort_elem P) invert_glu_sort_elem.
    clear_dups.
    apply_equiv_left.
    unfold sort_glu_typ_pred in H5.
    destruct_conjs.
    repeat split; mauto 3; intros.
    (* + assert (wf_exp Δ K {{{ A[σ] }}} -> wf_exp_eq Δ K {{{ A[σ] }}} A') by (eapply H4; mauto 3). *)
    (*   mauto 2. *)
    (* + eapply H4; mauto 3. *)
    + repeat eexists.
      * glu_sort_elem_econstructor; eauto; reflexivity.
      * simpl.
        assert {{ Γ ⊢ M : Sort@s' }} by mauto 2.
        assert {{ Γ ⊢ M }} by mauto 2.
        repeat split; mauto 2.
        intros.
        specialize (H6 (length Δ)); destruct H6 as [M' []].
        assert {{ Δ ⊢ M[σ] ≈ A' : A[σ] }} by mauto 2.
        assert {{ Δ ⊢ Sort@s' ≈ A[σ] }} by (transitivity {{{ Sort@s'[σ] }}}; mauto 4).
        assert {{ Δ ⊢ M[σ] ≈ A' : Sort@s' }} by mauto 3.
        mauto 2.
        (* assert (wf_exp_eq Δ {{{ A[σ] }}} {{{ M[σ] }}} A') by mauto 2. *)
        (* assert (wf_typ_eq Δ {{{ Sort@s' }}} {{{ A[σ] }}}) by (transitivity {{{ Sort@s'[σ] }}}; mauto 4). *)
        (* assert (wf_exp_eq Δ {{{ Sort@s' }}} {{{ M[σ] }}} A') by mauto 4. *)
        (* mauto 2. *)
           


        
        (* assert (glu_sort_typ pred_P s' d{{{ ⇑ Sort@s' m }}} Γ M). *)
        (* { *)
        (*   do 2 eexists; split. *)
        (*   - glu_sort_elem_econstructor; [mauto 2 | |]; reflexivity. *)
        (*   - econstructor; mauto 3. *)
        (*     repeat split; intros. *)
        (*     + *)
        (* } *)
        (* repeat split; mauto 3; intros. *)
        (* -- repeat split; mauto 3; intros. *)
        (*   specialize (H6 (length Δ)); destruct H6 as [M' []]. *)
        (*    assert (wf_exp_eq Δ {{{ A[σ] }}} {{{ M[σ] }}} M') by mauto 2. *)
           
        (*    admit. *)
        (* -- admit. *)
        (* -- specialize (H6 (length Δ)); destruct H6 as [M' []]. *)
        (*    assert (wf_exp_eq Δ {{{ A[σ] }}} {{{ M[σ] }}} A') by mauto 2. *)
        (*    assert (wf_typ_eq Δ {{{ Sort@s' }}} {{{ A[σ] }}}) by (transitivity {{{ Sort@s'[σ] }}}; mauto 4). *)
        (*    assert (wf_exp_eq Δ {{{ Sort@s' }}} {{{ M[σ] }}} A') by mauto 4. *)
        (*    mauto 2. *)
  - deepexec (@glu_sort_elem_per_sort P) ltac:(fun H => pose proof H).
    unfold per_sort in H9. deex.
    firstorder.
    specialize (H _ _ _ H7) as [? []].
    econstructor; mauto 3.
    + apply_equiv_left. repeat split; mauto 3; intros.
      (* * assert (wf_exp Δ K {{{ A[σ] }}} -> wf_exp_eq Δ K {{{ A[σ] }}} A') by (eapply H7; mauto 3). *)
      (*   mauto 2. *)
      (* * eapply H7; mauto 3. *)
    + intros.
      saturate_weakening_escape.
      deepexec H ltac:(fun H => destruct H).
      progressive_invert H13.
      deepexec H17 ltac:(fun H => pose proof H).
      (* assert {{ Δ ⊢ A[σ] ≈ Sort@s' }} by mauto 4. *)
      (* eapply wf_exp_eq_conv'; mauto 2. *)
      admit.
      
  - match_by_head (@pi_glu_typ_pred P) progressive_invert.
    assert ({{ Γ ⊢ IT : Sort@s1 }} /\ {{ Γ, IT ⊢ OT : Sort@s2 }}) by (gen_presup H7; mauto 3).
    destruct_conjs.
    handle_per_sort_elem_irrel.
    invert_per_sort_elem H6.
    econstructor; eauto; intros.
    + gen_presups; eassumption.
    + eapply per_sort_then_per_top_typ; mauto.
    + saturate_weakening_escape.
      assert {{ Γ ⊢w Id : Γ }} by mauto 3.
      assert {{ Δ ⊢ IT[σ] ® IP }} by mauto 3.
      assert (IP Γ {{{ IT[Id] }}}) as HITId by mauto 3.
      bulky_rewrite_in HITId.
      assert {{ Γ ⊢ IT[Id] ≈ IT : Sort@s1 }} by mauto 3.
      dependent destruction H18.
      assert {{ Γ ⊢ IT ® glu_typ_top_unsorted pred_P a }} as [] by mauto 3.
      assert {{ Δ ⊢ A[σ] ≈ Π r IT[σ] OT[q σ] }} by (transitivity {{{ (Π r IT OT)[σ] }}}; mauto 3).
      bulky_rewrite.
      simpl.
      
      enough {{ Δ ⊢ Π r IT[σ] OT[σ∘Wk,,#0] ≈ Π r A0 B' : Sort@s3 }} by mauto 3.
      apply wf_exp_eq_pi_cong'.
      * 

        admit.
      * pose proof (var_per_elem (length Δ) H0).
        destruct_rel_mod_eval.
        simplify_evals.
        destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
        assert (IEL {{{ Δ, IT[σ] }}} {{{ IT[σ][Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}) by mauto 3 using var_glu_elem_bot.
        assert {{ ⊢ Δ, IT[σ] }} by mauto 3.
        autorewrite with mcpts in H31.
        assert {{ Δ, IT[σ] ⊢w σ∘Wk : Γ }} by mauto 3.
        specialize (H14 {{{ Δ, IT[σ] }}} {{{ σ∘Wk }}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)).
        specialize (H11 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
        etransitivity; [| eapply H35]; mauto 3.
      
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
    assert (wf_exp Δ {{{ A[σ] }}} {{{ M[σ] }}}) by mauto 3.
    (* assert {{ Δ ⊢ M[σ] : A[σ] }} by mauto 3. *)
    bulky_rewrite_in H23.
    unshelve (econstructor; eauto).
    + trivial.
    + eassert (wf_exp Δ _ {{{ M[σ] N }}}) by (eapply wf_app'; eassumption).
      (* eassert {{ Δ ⊢ M[σ] N : ^_ }} by (eapply wf_app'; eassumption). *)
      assert (wf_typ_eq Δ {{{ OT[q σ][Id,,N] }}} {{{ OT[σ,,N] }}}) by mauto.
      assert (wf_exp Δ {{{ OT[σ,,N] }}} {{{ M[σ] N }}}) by mauto.
      (* autorewrite with mcpts in H24. *)
      trivial.
    + mauto using domain_app_per.
    + intros.
      saturate_weakening_escape.
      progressive_invert H26.
      destruct (H14 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) equiv_n).
      handle_functional_glu_sort_elem P.
      assert (wf_typ_eq Δ0 {{{ OT[σ∘σ0,,N[σ0]] }}} {{{ OT[(σ,,N)][σ0] }}}).
      {
        gen_presups.
        assert (wf_sub Δ {{{ Γ, IT }}} {{{ σ,,N }}}) by mauto 3.
        assert (wf_typ_eq Δ0 {{{ OT[(σ,,N)∘σ0] }}} {{{ OT[σ,,N][σ0] }}}) by mauto 3.
        assert (wf_typ_eq Δ0 {{{ OT[(σ,,N)∘σ0] }}} {{{ OT[σ∘σ0,,N[σ0]] }}}) by mauto 5.
        etransitivity; mauto 2.
      }
      enough (wf_exp_eq Δ0 {{{ OT[σ∘σ0,,N[σ0]] }}} {{{ (M[σ] N)[σ0] }}} {{{ M0 N0 }}}) by mauto.

      etransitivity.
      * assert (wf_typ_eq Δ0 {{{ OT[σ∘σ0,,N[σ0]] }}} {{{ OT[q σ][σ0,,N[σ0]] }}}) by (eapply sub_decompose_q_typ; mauto 3).
        eapply wf_exp_eq_conv' with (A:= {{{ OT[q σ][σ0,,N[σ0]] }}}); mauto 3.
      * simpl.
        rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.
        assert (wf_typ_eq Δ0 {{{ OT[q (σ∘σ0)][(Id,,N[σ0])] }}} {{{ OT[q (σ∘σ0)∘(Id,,N[σ0])] }}}).
        {
          eapply exp_eq_sub_compose_typ; mauto 4.
          assert (wf_sub Δ0 Δ0 (@a_id P)) by mauto 3.
          assert (wf_exp Δ0 {{{ IT[σ][σ0] }}} {{{ N[σ0] }}}) by mauto 3.
          assert (wf_typ_eq Δ0 {{{ IT[σ][σ0] }}} {{{ IT[σ∘σ0] }}}) by mauto 3.
          gen_presup H35.
          econstructor; mauto 3.
        }
        eapply wf_exp_eq_conv' with (A:= {{{ OT[q (σ∘σ0)][(Id,,N[σ0])] }}}); mauto 3.
        eapply wf_exp_eq_app_cong'.
        (* rewrite <- @exp_eq_sub_compose_typ; mauto 3; *)
        (*   [eapply wf_exp_eq_app_cong' |]. *)
        -- specialize (H16 _ {{{σ ∘ σ0}}} _ ltac:(mauto 3) ltac:(eassumption)).
           rewrite wf_exp_eq_sub_compose with (M := M) in H16; mauto 3.
           bulky_rewrite_in H16.
        -- assert (wf_typ_eq Δ0 {{{ IT[σ][σ0] }}} {{{ IT[σ∘σ0] }}}) by mauto.
           eapply wf_exp_eq_conv'; mauto 3.
          (* rewrite <- @exp_eq_sub_compose_typ; mauto 3. *)
        -- assert (wf_typ Δ0 {{{ IT[σ∘σ0] }}}) by mauto 4.
           assert (wf_typ Δ0 {{{ IT[σ][σ0] }}}) by mauto 4.
           econstructor; mauto 3.
           transitivity {{{ IT[σ][σ0] }}}; mauto 3.
           (* autorewrite with mcpts. *)
           (* rewrite <- @exp_eq_sub_compose_typ; mauto 3. *)

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
      (* assert {{ Γ ⊢w Id : Γ }} by mauto 4. *)
      pose proof (H14 _ _ H24).
      specialize (H14 _ _ H19).
      assert (wf_exp_eq Γ {{{ Sort@s1 }}} {{{ IT[Id] }}} {{{ IT }}}) by mauto 3.
      (* assert {{ Γ ⊢ IT[Id] ≈ IT : Type@i }} by mauto 3. *)
      bulky_rewrite_in H25.
      destruct (H10 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H29 _ _ _ H19 H9).
      rewrite H5 in *.
      autorewrite with mcpts.
      eassert (wf_exp Δ _ {{{ M[σ] }}}) by mauto 2.
      (* eassert {{ Δ ⊢ M[σ] : ^_ }} by (mauto 2). *)
      autorewrite with mcpts in H30.
      rewrite @wf_exp_eq_pi_eta' with (M := {{{ M[σ] }}}); [| trivial].
      cbn [nf_to_exp].

      eapply wf_exp_eq_fn_cong'; eauto; [| mauto 4].

      pose proof (var_per_elem (length Δ) H0).
      destruct_rel_mod_eval.
      simplify_evals.
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      specialize (H11 _ _ _ _ ltac:(trivial) (var_glu_elem_bot _ _ _ _ _ _ _ H H14)).
      assert (IEL {{{ Δ,IT[σ] }}} {{{ IT[σ∘Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Δ) }}}).
      {
        eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 3.
        symmetry.
        eapply exp_eq_sub_compose_typ_sort; mauto 4.
      }
      (* autorewrite with mcpts in H11. *)
      specialize (H15 {{{Δ, IT[σ]}}} {{{σ ∘ Wk}}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)) as [? []].
      apply_equiv_left.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).
      specialize (H33 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H41 _ {{{Id}}} _ ltac:(mauto 3) ltac:(eassumption)).
      do 2 (rewrite wf_exp_eq_sub_id in H41; mauto 4).
      etransitivity; [|eassumption].
      simpl.
      assert (wf_exp {{{ Δ, IT[σ] }}} {{{ IT[σ∘Wk] }}} (@a_var P 0)).
      {
        eapply wf_conv' with (A := {{{ IT[σ][Wk] }}}); mauto 3.
        symmetry; eapply wf_typ_eq_sub_compose; mauto 3.
      }
      (* assert {{ Δ, IT[σ] ⊢ #0 : IT[σ∘Wk] }} by (rewrite <- @exp_eq_sub_compose_typ; mauto 3). *)
      rewrite <- @sub_eq_q_sigma_id_extend; mauto 4.

      (* rewrite <- (@exp_eq_sub_compose_typ_sort); mauto 2. *)
      assert (wf_typ {{{ Γ, IT }}} OT ) by mauto 3.
      assert (wf_sub Δ Γ σ) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ] }}} Δ {{{ Wk }}}) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ] }}} Γ {{{ σ ∘ Wk }}}) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ], IT[σ∘Wk] }}} {{{ Γ, IT }}} {{{ q (σ ∘ Wk ) }}}) by mauto 3.
      assert (wf_exp {{{ Δ, IT[σ] }}} {{{ IT[σ∘Wk] }}} {{{ #0 }}}) by mauto 3.
      assert (wf_sub {{{ Δ, IT[σ] }}} {{{ Δ, IT[σ], IT[σ∘Wk] }}} {{{ Id,,#0 }}}) by mauto 4.
      assert (wf_typ_eq {{{ Δ, IT[σ] }}} {{{ OT[q (σ∘Wk)∘(Id,,#0)] }}} {{{ OT[q (σ∘Wk)][Id,,#0] }}}) by (symmetry; mauto 3).
      eapply wf_exp_eq_conv' with (A := {{{ OT[q (σ∘Wk)][Id,,#0] }}}); mauto 2.
      
      eapply wf_exp_eq_app_cong'; [| mauto 3].
      symmetry.
      rewrite <- wf_exp_eq_pi_sub; mauto 4.

  - assert (per_top_typ d{{{ ⇑ Sort@s b }}} d{{{ ⇑ Sort@s b }}}) by mauto.
    econstructor; eauto.
    intros.
    progressive_inversion.
    assert (wf_typ_eq Δ {{{ A[σ] }}} B) by mauto 2.
    assert (wf_exp Δ {{{ Sort@s }}} {{{ A[σ] }}}) by mauto 3.
    assert (wf_exp Δ {{{ Sort@s }}} {{{ A[σ] }}} -> wf_exp_eq Δ {{{ Sort@s }}} {{{ A[σ] }}} B) by (eapply H4; mauto 3).
    mauto 2.
  - handle_functional_glu_sort_elem P.
    apply_equiv_left.
    econstructor; eauto.
  - handle_functional_glu_sort_elem P.
    invert_glu_rel1.
    econstructor; eauto.
    + mauto.
    + intros.
      progressive_inversion.
      specialize (H3 (length Δ)) as [? []].
      firstorder.
Qed.


Corollary realize_glu_typ_top {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      (typ_rel Γ A) ->
      (glu_typ_top pred_P s a Γ A).
      (* {{ Γ ⊢ A ® P }} -> *)
      (* {{ Γ ⊢ A ® glu_typ_top i a }}. *)
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
      (glu_elem_bot pred_P s a Γ A M m) ->
      (exp_rel Γ A M d{{{ ⇑ a m }}}).
      (* {{ Γ ⊢ M : A ® m ∈ glu_elem_bot i a }} -> *)
      (* {{ Γ ⊢ M : A ® ⇑ a m ∈ El }}. *)
Proof.
  intros.
  eapply realize_glu_sort_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      (exp_rel Γ A M m) ->
      (glu_elem_top pred_P s a Γ A M m).
      (* {{ Γ ⊢ M : A ® m ∈ El }} -> *)
      (* {{ Γ ⊢ M : A ® m ∈ glu_elem_top i a }}. *)
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
    (typ_rel Γ A) ->
    (exp_rel {{{ Γ, A }}} {{{ A[Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Γ) }}}).
    (* {{ Γ ⊢ A ® P }} -> *)
    (* {{ Γ, A ⊢ #0 : A[Wk] ® ⇑! a (length Γ) ∈ El }}. *)
Proof.
  intros.
  eapply realize_glu_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.



(** Realizability for unsorted gluing model *)
Theorem realize_glu_typ_unsorted_elem_gen {P} (pred_P : PredicativeSig P) : forall a typ_rel exp_rel,
    {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
    (forall Γ A R,
        {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
        (typ_rel Γ A) ->
        (* {{ Γ ⊢ A ® P }} -> *)
        (* {{ Γ ⊢ A ® glu_typ_top i a }} *)
          (glu_typ_top_unsorted pred_P a Γ A)) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
          (glu_elem_bot_unsorted pred_P a Γ A M m) ->
          (* {{ Γ ⊢ M : A ® m ∈ glu_elem_bot i a }} -> *)
          (* {{ Γ ⊢ M : A ® ⇑ a m ∈ El }} *)
          (exp_rel Γ A M d{{{ ⇑ a m }}})) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
          (exp_rel Γ A M m) ->
          (* {{ Γ ⊢ M : A ® m ∈ El }} -> *)
          {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
          {{ Dom m ≈ m ∈ R }} ->
          (* {{ Γ ⊢ M : A ® m ∈ glu_elem_top i a }} *)
          (glu_elem_top_unsorted pred_P a Γ A M m)).
Proof.
  intros * Hglu.
  inversion Hglu; subst.
  - repeat split.
    + rewrite H in H2.
      unfold unsorted_glu_typ_pred in H2.
      gen_presup H2.
      eassumption.
    + mauto.
    + intros.
      rewrite H in H2.
      unfold unsorted_glu_typ_pred in H2.
      inversion_clear H4.
      transitivity {{{ Sort@s[σ] }}}; mauto 3.
    + intros.
      inversion H2.
      handle_functional_glu_typ_unsorted_elem P.
      unfold unsorted_glu_exp_pred.
      unfold unsorted_glu_typ_pred in H5.
      repeat split; mauto 2.
      unfold glu_sort_typ.
      do 2 eexists; split.
      * glu_sort_elem_econstructor; mauto 2; reflexivity.
      * econstructor; mauto 2.
        intros.
        eapply wf_exp_eq_conv' with (A:= {{{ A[σ] }}}); mauto 2.
        transitivity {{{ Sort@s[σ] }}}; mauto 3.
    + intros.
      rewrite H0 in H2.
      unfold unsorted_glu_exp_pred in H2.
      unfold glu_sort_typ in H2.
      destruct_conjs.
      assert (per_sort pred_P s m m) by mauto.
      unfold per_sort in H10; destruct_conjs.
      assert (glu_typ_top pred_P s m Γ M) by mauto 2.
      inversion_clear H12.
      assert (glu_typ_unsorted_elem pred_P H6 H7 m) by (econstructor; mauto 2).
      handle_functional_glu_typ_unsorted_elem P.
      econstructor; mauto 2.
      intros.
      inversion_clear H0.
      eapply wf_exp_eq_conv' with (A := {{{ Sort@s }}}); mauto 3.
      symmetry.
      transitivity {{{ Sort@s[σ] }}}; mauto 3.

  - repeat split.
    + assert (glu_typ_top pred_P s a Γ A) by mauto 2.
      inversion_clear H2.
      econstructor; mauto 2.
    + mauto 2.
    + assert (glu_typ_top pred_P s a Γ A) by mauto 2.
      inversion_clear H2.
      intros.
      econstructor; mauto 2.
    + intros.
      assert (glu_elem_bot pred_P s a Γ A M m).
      {
        inversion_clear H1.
        handle_functional_glu_typ_unsorted_elem P.
        econstructor; mauto 2.        
      }
      eapply realize_glu_elem_bot; mauto 2.
    + intros.
      assert (glu_elem_top pred_P s a Γ A M m) by (eapply realize_glu_elem_top; mauto 2).
      inversion_clear H4.
      handle_functional_glu_sort_elem P.
      econstructor; mauto 2.
Qed.


Corollary realize_glu_typ_top_unsorted {P} (pred_P : PredicativeSig P) : forall a typ_rel exp_rel,
    {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      (typ_rel Γ A) ->
      (glu_typ_top_unsorted pred_P a Γ A).
      (* {{ Γ ⊢ A ® P }} -> *)
      (* {{ Γ ⊢ A ® glu_typ_top i a }}. *)
Proof.
  intros.
  pose proof H.
  eapply glu_typ_unsorted_elem_per_typ in H.
  simpl in *. destruct_all.
  eapply realize_glu_typ_unsorted_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_bot_unsorted {P} (pred_P : PredicativeSig P) : forall a typ_rel exp_rel,
    {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      (glu_elem_bot_unsorted pred_P a Γ A M m) ->
      (exp_rel Γ A M d{{{ ⇑ a m }}}).
      (* {{ Γ ⊢ M : A ® m ∈ glu_elem_bot i a }} -> *)
      (* {{ Γ ⊢ M : A ® ⇑ a m ∈ El }}. *)
Proof.
  intros.
  eapply realize_glu_typ_unsorted_elem_gen; eauto.
Qed.

Theorem realize_glu_elem_top_unsorted {P} (pred_P : PredicativeSig P) : forall a typ_rel exp_rel,
    {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      (exp_rel Γ A M m) ->
      (glu_elem_top_unsorted pred_P a Γ A M m).
      (* {{ Γ ⊢ M : A ® m ∈ El }} -> *)
      (* {{ Γ ⊢ M : A ® m ∈ glu_elem_top i a }}. *)
Proof.
  intros.
  pose proof H.
  eapply glu_typ_unsorted_elem_per_typ in H.
  simpl in *. destruct_all.
  eapply realize_glu_typ_unsorted_elem_gen; eauto.
  eapply glu_typ_unsorted_elem_per_typ_elem; eauto.
Qed.

#[export]
Hint Resolve realize_glu_typ_top_unsorted realize_glu_elem_top_unsorted : mcpts.

Lemma var_glu_elem_bot_unsorted {P} (pred_P : PredicativeSig P) : forall a typ_rel exp_rel Γ A,
    {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
    typ_rel Γ A ->
    (* {{ Γ ⊢ A ® P }} -> *)
    glu_elem_bot_unsorted pred_P a {{{ Γ, A }}} {{{ A[Wk] }}} {{{ #0 }}} (d_var (length Γ) ).
    (* {{ Γ, A ⊢ #0 : A[Wk] ® !(length Γ) ∈ glu_elem_bot pred_P s a }}. *)
Proof.
  intros. saturate_glu_unsorted_info.
  econstructor; mauto 4.
  - assert (wf_typ Γ A) by (eapply glu_typ_unsorted_elem_sort_lvl; mauto 2).
    econstructor; mauto 3.
    
  - eapply glu_typ_unsorted_elem_typ_monotone; eauto.
    assert (wf_typ Γ A) by (eapply glu_typ_unsorted_elem_sort_lvl; mauto 2).
    assert {{ ⊢ Γ, A }} by mauto 3.
    eapply weakening_wk; mauto 3.
  - intros. progressive_inversion.
    exact (var_weaken_gen _ _ _ H1 nil _ _ eq_refl).
Qed.

Corollary var0_glu_elem_unsorted {P} (pred_P : PredicativeSig P) : forall {a typ_rel exp_rel Γ A},
    {{ DG a ∈ glu_typ_unsorted_elem pred_P ↘ typ_rel ↘ exp_rel }} ->
    (typ_rel Γ A) ->
    (exp_rel {{{ Γ, A }}} {{{ A[Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Γ) }}}).
    (* {{ Γ ⊢ A ® P }} -> *)
    (* {{ Γ, A ⊢ #0 : A[Wk] ® ⇑! a (length Γ) ∈ El }}. *)
Proof.
  intros.
  eapply realize_glu_elem_bot_unsorted; mauto 4.
  eauto using var_glu_elem_bot_unsorted.
Qed.
