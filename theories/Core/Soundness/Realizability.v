From Coq Require Import Nat.

From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Semantic Require Import Realizability.
From McPTS.Core.Soundness.LogicalRelation Require Export Core.
Import Domain_Notations.

Open Scope list_scope.

Lemma wf_ctx_sub_ctx_lookup {P} : forall n (A : typ P) Γ,
    {{ #n : A ∈ Γ }} ->
    forall Γ',
      {{ ⊢ Γ' ⊆ Γ }} ->
      exists Γ'1 A0 Γ'2 A',
        Γ' = Γ'1 ++ A0 :: Γ'2 /\
          n = length Γ'1 /\
          A' = iter (S n) (fun A => {{{ A[Wk] }}}) A0 /\
          {{ #n : A' ∈ Γ' }} /\
          {{ Γ' ⊢ A' ⊆ A }}.
Proof.
  induction 1; intros; progressive_inversion.
  - exists nil.
    repeat eexists; mauto 4.    
  - edestruct IHctx_lookup as [Γ'1 [? [? [? [? [? [? []]]]]]]]; mauto.
    exists (A0 :: Γ'1). subst.
    repeat eexists; mauto 4.
Qed.

Lemma var_arith {P} : forall (Γ1 Γ2 : ctx P) (A : typ P),
    length (Γ1 ++ A :: Γ2) - length Γ2 - 1 = length Γ1.
Proof.
  intros.
  rewrite List.length_app.
  simpl.
  lia.
Qed.

Lemma var_weaken_gen {P} : forall (Γ' : ctx P) (σ : sub P) (Γ : ctx P),
    {{ Γ' ⊢w σ : Γ }} ->
    forall Γ1 Γ2 A0,
      Γ = Γ1 ++ A0 :: Γ2 ->
      {{ Γ' ⊢ #(length Γ1)[σ] ≈ #(length Γ' - length Γ2 - 1) : ^(iter (S (length Γ1)) (fun A => {{{ A[Wk] }}}) A0)[σ] }}.
Proof.
  induction 1; intros; subst; gen_presups.
  - pose proof (app_ctx_vlookup _ _ _ _ ltac:(eassumption) eq_refl) as Hvar.

    (* gen_presup Hvar. *)
    pose proof (app_ctx_lookup Γ1 A0 Γ2 (length Γ1) ltac:(reflexivity)).
    assert {{ ⊢ ^ (app Γ1 {{{ Γ2, A0 }}}) }} by mauto.
    pose proof (presup_ctx_lookup_typ H1 H0).
    assert {{ ^(app Γ1 {{{ Γ2, A0 }}}) ⊢ ^(iter (S (length Γ1)) (fun T : exp P => {{{ T[Wk] }}}) A0) }} by (eapply presup_wf_exp; mauto).
    clear_dups.
    apply wf_sub_id_inversion in Hτ.
    pose proof (wf_ctx_subtyp_length Hτ).
    transitivity {{{ #(length Γ1)[^(@a_id P)] }}}; mauto 3.
    replace (length Γ) with (length (Γ1 ++ {{{ Γ2, A0 }}})) by lia.
    rewrite var_arith.
    eapply wf_exp_eq_conv'; [eapply wf_exp_eq_sub_id; mauto 3 |].
    transitivity {{{ ^(iter (S (length Γ1)) (fun T : exp P => {{{ T[Wk] }}}) A0)[Id] }}}; mauto.

  - pose proof (app_ctx_vlookup _ _ _ _ HΓ'0 eq_refl) as Hvar.
    pose proof (app_ctx_lookup Γ1 A0 Γ2 _ eq_refl).
    clear_dups.
    assert {{ ⊢ Γ', A }} by mauto 3.
    assert {{ Γ', A ⊢s Wk : ^(Γ1 ++ {{{ Γ2, A0 }}}) }} by mauto 3.
    transitivity {{{ #(length Γ1)[Wk∘τ] }}}; [mauto 5 |].
    assert {{ Γ ⊢ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[Wk∘τ] ≈ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[σ] }} by mauto 5.
    eapply wf_exp_eq_conv'; mauto 2.

    etransitivity; [eapply wf_exp_eq_sub_compose; mauto 3 |].
    pose proof (wf_ctx_subtyp_length H0).
    assert {{ Γ ⊢ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[Wk][τ] ≈ ^ (iter (S (length Γ1)) (fun A1 : exp P => {{{ A1[Wk] }}}) A0)[Wk∘τ] }} by mauto 5.
    eapply wf_exp_eq_conv'; mauto 2.

    deepexec (@wf_ctx_sub_ctx_lookup P) ltac:(fun H => destruct H as [Γ1' [? [Γ2' [? [-> [? [-> []]]]]]]]).
    repeat rewrite List.length_app in *.

    etransitivity.
    + assert {{ ⊢ ^ (app Γ1' {{{ Γ2',x }}}) }} by mauto 3.
      eapply wf_exp_eq_sub_cong; [| eapply wf_exp_eq_conv |mauto 3];
        mauto 3.
        
    + replace (length Γ1) with (length Γ1') in * by lia.
      clear_refl_eqs.
      replace (length Γ2) with (length Γ2') by (simpl in *; lia).
      eapply wf_exp_eq_conv.
      * eapply IHweakening with (Γ1 := A :: _).
        reflexivity.
      * assert {{ ^(app Γ1' {{{ Γ2', x }}}), A ⊢s Wk : ^(app Γ1' {{{ Γ2', x }}}) }} by mauto 3.
        mauto 4.
      * eapply wf_typ_subtyp_sub; mauto 3.
        eapply wf_typ_subtyp_sub; mauto 3.
Qed.

Lemma var_glu_elem_bot {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel Γ A,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ, A ⊢ #0 : A[Wk] ® !(length Γ) ∈ glu_elem_bot pred_P (so_Some s) a }}.
Proof.
  intros. saturate_glu_info.
  econstructor; mauto 3.
  - econstructor; mauto 2.
    econstructor; mauto 2.
  - econstructor; try eassumption; try reflexivity.
  - eapply glu_sort_elem_typ_monotone; mauto 3.
    assert {{ ⊢ Γ, A }} by (econstructor; mauto 2).
    eapply weakening_wk; mauto 3.
  - intros.
    progressive_inversion.
    exact (var_weaken_gen _ _ _ H2 nil _ _ eq_refl).
Qed.

#[local]
Hint Rewrite -> @wf_sub_eq_extend_compose using mauto 4 : mcpts.

Ltac raise_sorted_to_typ1 H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?A : Sort@?s }} =>
      assert {{ Γ ⊢ A }} by mauto 2
  | {{ ^?Γ ⊢ ^?A ≈ ^?B : Sort@?s }} =>
      assert {{ Γ ⊢ A ≈ B }} by mauto 2
  end.

Ltac raise_sorted_to_typ :=
  (on_all_hyp: raise_sorted_to_typ1).

Theorem realize_glu_sort_elem_gen {P} {pred_P : PredicativeSig P} : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    (forall Γ A R,
        {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} ->
        {{ Γ ⊢ A ® typ_rel }} ->
        {{ Γ ⊢ A ® glu_typ_top_of_sort pred_P s a }}) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_bot pred_P (so_Some s) a }} ->
          {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
          {{ DF a ≈ a ∈ per_sort_elem pred_P s ↘ R }} ->
          {{ Dom m ≈ m ∈ R }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P (so_Some s) a }}).
Proof.
  simpl. induction 1 using glu_sort_elem_ind.
  all:split; [| split]; intros;
    apply_equiv_left;
    gen_presups;
    try match_by_head1 (@per_sort_elem P) ltac:(fun H => pose proof (per_sort_then_per_top_typ H));
    match_by_head (@glu_elem_bot P) ltac:(fun H => destruct H as []);
    destruct_all.
  - econstructor; eauto; intros.
    raise_sorted_to_typ.
    progressive_inversion; mauto 2.
    transitivity {{{ Sort@s''[σ] }}}; mauto 4.
    enough {{ Γ' ⊢ Sort@s'' : Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ Sort@s' ⊆ Sort@s }} by mauto 4.
    eapply wf_exp_conv'; mauto 3.
    (* econstructor; mauto 3. *)
  - match_by_head (glu_typ_elem pred_P) ltac:(fun H => inversion H; subst).
    handle_functional_glu_sort_elem P.    
    match_by_head (@glu_sort_elem P) invert_glu_sort_elem.
    unfold sort_glu_typ_pred in *.    
    (* clear_dups. *)
    (* apply_equiv_left. *)
    repeat split; eauto.
    repeat eexists.
    + glu_sort_elem_econstructor; eauto; reflexivity.
    + simpl. repeat split.
      * rewrite <- H5. (* H5 is equality {{ Γ ⊢ A ≈ Sort@s'' : Sort@s }} *)
        trivial.
      * intros.
        saturate_weakening_escape.
        assert {{ Γ' ⊢ A[σ] ≈ Sort@s'' }} by (etransitivity; mauto 3).
        enough {{ Γ' ⊢ M[σ] ≈ A' : A[σ] }} by mauto 3.
        firstorder.

  - deepexec (@glu_sort_elem_per_sort P) ltac:(fun H => pose proof H).
    unfold per_sort in *. deex.
    (* firstorder. *)
    specialize (H _ _ _ H8) as [? []].
    econstructor; mauto 3.
    + econstructor; mauto 2.
    + apply_equiv_left; trivial.
    + intros.
      saturate_weakening_escape.
      deepexec H ltac:(fun H => destruct H).
      progressive_invert H14.
      deepexec H18 ltac:(fun H => pose proof H).
      (* functional_read_rewrite_clear. *)
      bulky_rewrite.
      
  - match_by_head (@pi_glu_typ_pred P) progressive_invert.
    handle_per_sort_elem_irrel.
    invert_per_sort_elem H6.
    econstructor; eauto; intros.
    + gen_presups. mauto 2.
    + saturate_weakening_escape.
      assert {{ Γ ⊢w Id : Γ }} by mauto 4.
      assert {{ Γ' ⊢ IT[σ] ® IP }} by mauto 3.
      assert (IP Γ {{{ IT[Id] }}}) as HITId by mauto 3.
      bulky_rewrite_in HITId.
      assert {{ Γ ⊢ IT[Id] ≈ IT : Sort@s1 }} by mauto 3.
      dependent destruction H18.
      assert {{ Γ ⊢ IT ® glu_typ_top_of_sort pred_P s1 a }} as [] by mauto 3.
      bulky_rewrite.
      simpl.
      assert {{ Γ' ⊢ Sort@s3 ⊆ Sort@s }} by mauto 4.
      assert {{ Γ' ⊢ A[σ] ≈ (Π r IT OT)[σ] : Sort@s }} by mauto 3.
      transitivity {{{ (Π r IT OT)[σ] }}}; mauto 3.
      assert {{ Γ' ⊢ (Π r IT OT)[σ] ≈ Π r IT[σ] OT[q σ] : Sort@s3 }} by mauto 3.
      assert {{ Γ' ⊢ (Π r IT OT)[σ] ≈ Π r IT[σ] OT[q σ] : Sort@s }} by (eapply wf_exp_eq_conv; mauto 3).
      transitivity {{{ Π r IT[σ] OT[q σ] }}}; mauto 3.
      enough {{ Γ' ⊢ Π r IT[σ] OT[q σ] ≈ Π r A0 B' : Sort@s3 }} by mauto 3.
      apply wf_exp_eq_pi_cong'; [firstorder |].
      pose proof (var_per_elem (length Γ') H0).

      clear_pi_sort_eq_and_pred_rel.
      handle_per_sort_elem_irrel.
      destruct_rel_mod_eval.
      simplify_evals.
      clear_pi_sort_eq_and_pred_rel.      
      assert (IEL {{{ Γ', IT[σ] }}} {{{ IT[σ][Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Γ') }}}) by mauto 3 using var_glu_elem_bot.
      assert {{ Γ', IT[σ] ⊢ IT[σ][Wk] ≈ IT[σ∘Wk] : Sort@s1 }} by (eapply wf_exp_eq_sub_compose_sorted2; mauto).
      assert (IEL {{{ Γ',IT[σ] }}} {{{ IT[σ∘Wk] }}} {{{ #0 }}} d{{{ ⇑! a (length Γ') }}}) by (eapply glu_sort_elem_trm_resp_typ_exp_eq; mauto 2).
      assert {{ Γ', IT[σ] ⊢w σ∘Wk : Γ }} by mauto 4.

      assert (in_rel d{{{ ⇑! a (length Γ') }}} d{{{ ⇑! a (length Γ') }}}) by intuition.
      specialize (H1 d{{{ ⇑! a (length Γ') }}} ltac:(eassumption) b ltac:(eassumption)).
      specialize (H2 d{{{ ⇑! a (length Γ') }}} ltac:(eassumption) b ltac:(eassumption)) as [? []].
      
      specialize (H15 {{{ Γ', IT[σ] }}} {{{ σ∘Wk }}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(intuition)).

      specialize (H2 _ _ _ H0 H15) as [].
      etransitivity; [| eapply H38]; mauto 3.
      
  - match_by_head (@glu_typ_elem) ltac:(fun H => directed inversion H; subst).
    handle_functional_glu_sort_elem P.
    apply_equiv_left.
    invert_glu_rel1.
    econstructor; try eapply per_bot_then_per_elem; eauto.

    intros.
    saturate_weakening_escape.
    saturate_glu_info.
    match_by_head1 (@per_sort_elem P) invert_per_sort_elem.
    clear_pi_sort_eq_and_pred_rel.
    handle_per_sort_elem_irrel.
    assert (in_rel0 n n) by intuition.
    destruct_rel_mod_eval.
    simplify_evals.
    rename a0 into b.
    clear_pi_sort_eq_and_pred_rel.
    eexists; repeat split; mauto 3.
    eapply H2; eauto.
    assert (HAs3: {{ Γ ⊢ A : Sort@s }}) by (gen_presup H10; mauto 2).
    assert {{ Γ' ⊢ M[σ] : A[σ] }} by mauto 3.
    bulky_rewrite_in H28. (* H28 : {{ Γ' ⊢ M[σ] : A[σ] }} *)
    unshelve (invert_glu_sort_elem H21); try eassumption.
    assert (glu_sort_elem pred_P s2 (OP n equiv_n) (OEL n equiv_n) b) by mauto 2.
    assert (glu_sort_elem pred_P s2 (x n H0) (x0 n H0) b) by mauto 2.
    handle_functional_glu_sort_elem P.
    unshelve (econstructor; mauto 3); shelve_unifiable.
    + assert {{ Γ ⊢ M : Π r IT OT }} by mauto 3.
      assert {{ Γ' ⊢ M[σ] : (Π r IT OT)[σ] }} by mauto 4.
      assert {{ Γ' ⊢ M[σ] : Π r IT[σ] OT[q σ] }} by mauto 3.
      assert {{ Γ' ⊢ M[σ] N : OT[q σ][Id,,N] }} by mauto 3.
      assert {{ Γ' ⊢ M[σ] N : OT[σ,,N] }} by mauto 3.
      trivial.
    + econstructor; mauto 2.
    + eapply H35; mauto 2.
    + mauto using domain_app_per.
    + intros.
      saturate_weakening_escape.
      progressive_invert H37. (* H37 : {{ Rne m ⇓ a n in length Γ'0 ↘ M' }} *)
      
      destruct (H15 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) H0).
      handle_functional_glu_sort_elem P. 

      assert {{ Γ'0 ⊢ OT[σ∘σ0,,N[σ0]] ≈ OT[σ,,N][σ0] : Sort@s2 }} by (transitivity {{{ OT[(σ,,N)∘σ0] }}}; mauto 5).
      enough {{ Γ'0 ⊢ (M[σ] N)[σ0] ≈ ^ n{{{ M0 N0 }}} : OT[σ∘σ0,,N[σ0]] }} by mauto.

      etransitivity.
      * assert {{ Γ'0 ⊢ OT[σ∘σ0,,N[σ0]] ≈ OT[q σ][σ0,,N[σ0]] }} as -> by (eapply sub_decompose_q_typ; mauto 4).       
        eapply wf_exp_eq_app_sub with (A := {{{ IT[σ] }}}) ; mauto 3.
        (* assert {{ Γ' ⊢ (Π r IT OT)[σ] ≈ Π r IT[σ] OT[q σ] : Sort@s3 }} as <- by mauto 3. *)
        (* mauto 3. *)
      * simpl.
        assert {{ Γ'0 ⊢ N[σ0] : IT[σ∘σ0] }}.
        {
          assert {{ Γ'0 ⊢ IT[σ∘σ0] ≈ IT[σ][σ0] }} as ->; mauto 3.
          econstructor; mauto 3.
        }
        
        rewrite <- @wf_sub_eq_q_sigma_id_extend; mauto 4.
        assert {{ Γ'0 ⊢ OT[q (σ∘σ0)][(Id,,N[σ0])] ≈ OT[q (σ∘σ0)∘(Id,,N[σ0])] : Sort@s2 }}.
        {
          symmetry.
          assert {{ Γ'0 ⊢ IT[σ][σ0][Id] ≈ IT[σ][σ0] : Sort@s1 }} by mauto 4.
          assert {{ Γ'0 ⊢ N[σ0] : IT[σ][σ0] }} by mauto 4.
          assert {{ Γ'0 ⊢ N[σ0] : IT[σ][σ0][Id] }} by mauto 3.
          assert {{ Γ'0 ⊢s Id,,N[σ0] : Γ'0, IT[σ][σ0] }} by mauto 5.
          assert {{ Γ'0 ⊢s σ∘σ0 : Γ }} by mauto 2.
          assert {{ Γ'0, IT[σ∘σ0] ⊢s q (σ∘σ0) : Γ, IT }} by mauto 4.
          assert {{ Γ'0 ⊢ IT[σ∘σ0] ≈ IT[σ][σ0] : Sort@s1 }} by mauto 3.
          assert {{ ⊢ Γ'0 }} by mauto 2.
          assert {{ ⊢ Γ'0, IT[σ][σ0] ≈ Γ'0, IT[σ∘σ0] }} by mauto 5.
          assert {{ Γ'0 ⊢s Id,,N[σ0] : Γ'0, IT[σ∘σ0] }} by mauto 4.
          eapply wf_exp_eq_sub_compose_sorted1; mauto 2.
        }

        eapply wf_exp_eq_conv'; mauto 3.
        eapply wf_exp_eq_app_cong'.
        -- specialize (H19 _ {{{σ ∘ σ0}}} _ ltac:(mauto 3) ltac:(eassumption)).
           bulky_rewrite_in H19.
           transitivity {{{ M[σ∘σ0] }}}; mauto 3.
           assert {{ Γ'0 ⊢ (Π r IT OT)[σ∘σ0] ≈ Π r IT[σ∘σ0] OT[q (σ∘σ0)] : Sort@s3 }} as <- by mauto 3.
           symmetry.
           eapply wf_exp_eq_sub_compose; mauto 3.
        -- assert (wf_typ_eq Γ'0 {{{ IT[σ][σ0] }}} {{{ IT[σ∘σ0] }}}) by mauto.
           eapply wf_exp_eq_conv'; mauto 3.

        
    (* unshelve (econstructor; eauto); shelve_unifiable. *)
    (* + trivial. *)
    (* + assert {{ Γ ⊢ M : Π r IT OT }} by mauto 3. *)
    (*   assert {{ Γ' ⊢ M[σ] : (Π r IT OT)[σ] }} by mauto 4. *)
    (*   assert {{ Γ' ⊢ M[σ] : Π r IT[σ] OT[q σ] }} by mauto 3. *)
    (*   assert {{ Γ' ⊢ M[σ] N : OT[q σ][Id,,N] }} by mauto 3. *)
    (*   assert {{ Γ' ⊢ M[σ] N : OT[σ,,N] }} by mauto 3. *)
    (*   trivial. *)
    (* + mauto using domain_app_per. *)
    (* + intros. *)
    (*   saturate_weakening_escape. *)
    (*   progressive_invert H28. *)
      
    (*   destruct (H15 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) H0). *)
    (*   handle_functional_glu_sort_elem P. *)
      
    (*   assert {{ Γ'0 ⊢ OT[σ∘σ0,,N[σ0]] ≈ OT[σ,,N][σ0] : Sort@s2 }} by (transitivity {{{ OT[(σ,,N)∘σ0] }}}; mauto 5). *)
    (*   enough {{ Γ'0 ⊢ (M[σ] N)[σ0] ≈ ^ n{{{ M0 N0 }}} : OT[σ∘σ0,,N[σ0]] }} by mauto. *)

    (*   etransitivity. *)
    (*   * assert {{ Γ'0 ⊢ OT[σ∘σ0,,N[σ0]] ≈ OT[q σ][σ0,,N[σ0]] }} as -> by (eapply sub_decompose_q_typ; mauto 4).        *)
    (*     eapply wf_exp_eq_app_sub with (A := {{{ IT[σ] }}}) ; mauto 3. *)
    (*     assert {{ Γ' ⊢ (Π r IT OT)[σ] ≈ Π r IT[σ] OT[q σ] : Sort@s3 }} as <- by mauto 3. *)
    (*     mauto 3. *)
    (*   * simpl. *)
    (*     assert {{ Γ'0 ⊢ N[σ0] : IT[σ∘σ0] }}. *)
    (*     { *)
    (*       assert {{ Γ'0 ⊢ IT[σ∘σ0] ≈ IT[σ][σ0] }} as ->; mauto 3. *)
    (*       econstructor; mauto 3. *)
    (*     } *)
        
    (*     rewrite <- @wf_sub_eq_q_sigma_id_extend; mauto 4. *)
    (*     assert {{ Γ'0 ⊢ OT[q (σ∘σ0)][(Id,,N[σ0])] ≈ OT[q (σ∘σ0)∘(Id,,N[σ0])] : Sort@s2 }}. *)
    (*     { *)
    (*       symmetry. *)
    (*       assert {{ Γ'0 ⊢ IT[σ][σ0][Id] ≈ IT[σ][σ0] : Sort@s1 }} by mauto 4. *)
    (*       assert {{ Γ'0 ⊢ N[σ0] : IT[σ][σ0] }} by mauto 4. *)
    (*       assert {{ Γ'0 ⊢ N[σ0] : IT[σ][σ0][Id] }} by mauto 3. *)
    (*       assert {{ Γ'0 ⊢s Id,,N[σ0] : Γ'0, IT[σ][σ0] }} by mauto 5. *)
    (*       assert {{ Γ'0 ⊢s σ∘σ0 : Γ }} by mauto 2. *)
    (*       assert {{ Γ'0, IT[σ∘σ0] ⊢s q (σ∘σ0) : Γ, IT }} by mauto 4. *)
    (*       assert {{ Γ'0 ⊢ IT[σ∘σ0] ≈ IT[σ][σ0] : Sort@s1 }} by mauto 3. *)
    (*       assert {{ ⊢ Γ'0 }} by mauto 2. *)
    (*       assert {{ ⊢ Γ'0, IT[σ][σ0] ≈ Γ'0, IT[σ∘σ0] }} by mauto 5. *)
    (*       assert {{ Γ'0 ⊢s Id,,N[σ0] : Γ'0, IT[σ∘σ0] }} by mauto 4. *)
    (*       eapply wf_exp_eq_sub_compose_sorted1; mauto 2. *)
    (*     } *)

    (*     eapply wf_exp_eq_conv'; mauto 3. *)
    (*     eapply wf_exp_eq_app_cong'. *)
    (*     -- specialize (H17 _ {{{σ ∘ σ0}}} _ ltac:(mauto 3) ltac:(eassumption)). *)
    (*        rewrite wf_exp_eq_sub_compose with (M := M) in H17; mauto 3. *)
    (*        bulky_rewrite_in H17. *)
    (*     -- assert (wf_typ_eq Γ'0 {{{ IT[σ][σ0] }}} {{{ IT[σ∘σ0] }}}) by mauto. *)
    (*        eapply wf_exp_eq_conv'; mauto 3. *)

  - handle_functional_glu_sort_elem P.
    handle_per_sort_elem_irrel.
    pose proof H8.
    invert_per_sort_elem H8.
    
    econstructor; mauto 3.
    + invert_glu_rel1. trivial.
    + econstructor; mauto 2.
    + eapply glu_sort_elem_trm_typ; eauto.
    + intros.
      saturate_weakening_escape.
      assert {{ Γ' ⊢s σ : Γ }} by mauto 2.
      invert_glu_rel1. clear_dups.
      progressive_invert H21.

      assert {{ Γ ⊢w Id : Γ }} by mauto 3.
      assert (IP Γ {{{ IT[Id] }}}) by mauto 3.
      assert {{ Γ ⊢ IT[Id] ≈ IT : Sort@s1 }} by mauto 3.
      bulky_rewrite_in H27.
      
      destruct (H11 _ _ _ ltac:(eassumption) ltac:(eassumption)) as [].
      assert {{ Γ' ⊢ IT[σ] ® IP }} by mauto 3.
      specialize (H31 _ _ _ H20 H9).
      autorewrite with mcpts in H31.
      assert {{ Γ' ⊢ A[σ] ≈ (Π r IT OT)[σ] : Sort@s }} as -> by mauto 3.
      rewrite -> H10 in *.      
      assert {{ Γ, IT ⊢ OT : Sort@s2 }} by mauto 3.
      
      assert {{ Γ' ⊢ (Π r IT OT)[σ] ≈ Π r IT[σ] OT[q σ] : Sort@s }} by (econstructor; mauto 3).
      assert {{ Γ' ⊢ M[σ] : (Π r IT OT)[σ] }} by mauto 4.
      autorewrite with mcpts in H35.
      rewrite -> H34.
      rewrite @wf_exp_eq_pi_eta' with (M := {{{ M[σ] }}}); [| trivial].
      cbn [nf_to_exp].

      pose proof (var_per_elem (length Γ') H0).
      assert (per_sort_elem pred_P s1 in_rel0 a a) by (destruct_conjs; pose proof ord_ru_pi_sub pred_P r sub_s3_s as [[] ?]; subst; mauto 2).
      handle_per_sort_elem_irrel.
      assert (in_rel d{{{ ⇑! a (length Γ') }}} d{{{ ⇑! a (length Γ') }}}) by intuition.
      destruct_rel_mod_eval.
      simplify_evals.
      
      destruct (H2 _ ltac:(eassumption) _ ltac:(eassumption)) as [? []].
      specialize (H12 _ _ _ _ ltac:(trivial) (var_glu_elem_bot _ _ _ _ _ _ _ H H32)).
      assert {{ Γ', IT[σ] ⊢ IT[σ∘Wk] ≈ IT[σ][Wk] : Sort@s1 }} by (eapply wf_exp_eq_sub_compose_sorted1; mauto 4).
      rewrite <- H43 in H12.
      
      specialize (H17 {{{ Γ', IT[σ] }}} {{{ σ∘Wk }}} _ _ ltac:(mauto) ltac:(eassumption) ltac:(eassumption)) as [? []].
      apply_equiv_left.
      destruct_rel_mod_app.
      simplify_evals.
      deepexec H1 ltac:(fun H => pose proof H).

      assert (per_sort_elem pred_P s2 (out_rel d{{{ ⇑! a (length Γ') }}} d{{{ ⇑! a (length Γ') }}} H36) b b) by (pose proof ord_ru_pi_sub pred_P r sub_s3_s as [? []]; subst; mauto 2).
      specialize (H42 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)) as [].
      specialize (H50 _ {{{Id}}} _ ltac:(mauto 3) ltac:(eassumption)).
      do 2 (rewrite wf_exp_eq_sub_id in H50; mauto 3).
      eapply wf_exp_eq_fn_cong'; mauto 3.
      * etransitivity; [|eassumption].
        simpl.
        assert {{ Γ', IT[σ] ⊢s σ∘Wk : Γ }} by mauto 4.
        assert {{ Γ', IT[σ] ⊢ #0 : IT[σ∘Wk] }} by (rewrite -> @wf_exp_eq_sub_compose_sorted1; mauto 3).
        rewrite <- @wf_sub_eq_q_sigma_id_extend; mauto 4.
        assert {{ Γ', IT[σ] ⊢ OT[q (σ∘Wk)∘(Id,,#0)] ≈ OT[q (σ∘Wk)][Id,,#0] : Sort@s2 }} as -> by (eapply wf_exp_eq_sub_compose_sorted1; mauto 3).
        eapply wf_exp_eq_app_cong'; [| mauto 3].
        symmetry.
        rewrite <- wf_exp_eq_pi_sub; mauto 4.
        eapply wf_exp_eq_sub_compose; mauto 3.
             
      * match_by_head (@glu_typ_elem) ltac:(fun H => directed inversion H; subst).
        handle_functional_glu_sort_elem P.
        assert {{ Γ', IT[σ] ⊢w Id : Γ', IT[σ] }} by mauto 3.
        assert {{ Γ', IT[σ] ⊢ OT[σ∘Wk,,#0] ® glu_typ_top_of_sort pred_P s2 b }}  as [] by mauto 3.
        assert ({{ Γ', IT[σ] ⊢ OT[σ∘Wk,,#0][Id] ≈ B' : Sort@s2 }}) by mauto 4.
        mauto 4.
      
  - econstructor; eauto; intros.
    progressive_inversion.
    transitivity {{{ ℕ[σ] }}}; mauto 3.
    assert {{ ⊢ Γ' }} by mauto 3.
    assert {{ Γ' ⊢ Sort@s' ⊆ Sort@s }} by mauto 3.
    enough {{ Γ' ⊢ ℕ[σ] ≈ ℕ : Sort@s' }} by (eapply wf_exp_eq_conv; mauto 3).
    mauto 3.
    
  - match_by_head (@glu_typ_elem) ltac:(fun H => directed inversion H; subst).
    handle_functional_glu_sort_elem P.
    match_by_head (@glu_sort_elem P) invert_glu_sort_elem.
    apply_equiv_left.
    repeat split; eauto.
    econstructor; trivial.

    intros.
    saturate_weakening_escape.
    assert {{ Γ' ⊢ A[σ] ≈ ℕ[σ] : Sort@s }} by mauto 3.
    assert {{ Γ' ⊢ A[σ] ≈ ℕ[σ] }} by mauto 2.
    rewrite <- wf_exp_eq_nat_sub; try eassumption.
    mauto 3.

  - econstructor; mauto 3.
    + bulky_rewrite. mauto 3.
    + econstructor; mauto 2.
    + apply_equiv_left. trivial.
    + intros.
      saturate_weakening_escape.
      bulky_rewrite.
      mauto using glu_nat_readback.

  - econstructor; eauto.
    intros.
    progressive_inversion.
    firstorder.
    
  - match_by_head (@glu_typ_elem) ltac:(fun H => directed inversion H; subst).
    handle_functional_glu_sort_elem P.
    apply_equiv_left.
    econstructor; eauto.
  - handle_functional_glu_sort_elem P.
    invert_glu_rel1.
    econstructor; eauto.
    + econstructor; mauto 2.
    + intros i. destruct (H3 i) as [? []].
      mauto.
    + intros.
      progressive_inversion.
      specialize (H3 (length Γ')) as [? []].
      firstorder.
Qed.

Corollary realize_glu_sort_typ_top {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A ® glu_typ_top_of_sort pred_P s a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_sort_elem_per_sort in H.
  simpl in *. destruct_all.
  eapply realize_glu_sort_elem_gen; eauto.
Qed.

Theorem realize_glu_sort_elem_bot {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ glu_elem_bot pred_P (so_Some s) a }} ->
      {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}.
Proof.
  intros.
  eapply realize_glu_sort_elem_gen; eauto.
Qed.

Theorem realize_glu_sort_elem_top {P} (pred_P : PredicativeSig P) : forall a s typ_rel exp_rel,
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P (so_Some s) a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_sort_elem_per_sort in H.
  simpl in *. destruct_all.
  eapply realize_glu_sort_elem_gen; eauto.
  eapply glu_sort_elem_per_elem; eauto.
Qed.

#[export]
Hint Resolve realize_glu_sort_typ_top realize_glu_sort_elem_top : mcpts.

Corollary var0_glu_elem {P} (pred_P : PredicativeSig P) : forall {s a typ_rel exp_rel Γ A},
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ, A ⊢ #0 : A[Wk] ® ⇑! a (length Γ) ∈ exp_rel }}.
Proof.
  intros.
  eapply realize_glu_sort_elem_bot; mauto 4.
  eauto using var_glu_elem_bot.
Qed.


(** Realizability for unsorted gluing model *)
Theorem realize_glu_typ_elem_gen {P} {pred_P : PredicativeSig P} : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    (forall Γ A R,
        {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
        {{ Γ ⊢ A ® typ_rel }} ->
        {{ Γ ⊢ A ® glu_typ_top pred_P a }}) /\
      (forall Γ M A m,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_bot pred_P so a }} ->
          {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}) /\
      (forall Γ M A m R,
          (** We repeat this to get the relation between [a] and [P]
              more easily after applying [induction 1.] *)
          {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
          {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
          {{ DF a ≈ a ∈ per_typ_elem pred_P ↘ R }} ->
          {{ Dom m ≈ m ∈ R }} ->
          {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P so a }}).
Proof.
  inversion 1; subst.
  - repeat split; intros.
    + simpl_glu_rel; eassumption.
    + econstructor; mauto 2.
    + simpl_glu_rel.
      inversion_clear H5.
      transitivity {{{ Sort@s[σ] }}}; mauto 3.
    + inversion_clear H.
      inversion_clear H2.
      inversion_clear H3.
      inversion_clear H7.
      handle_functional_glu_sort_elem P.
      simpl in H8.
      simpl.
      split; mauto 2.
      do 2 eexists; split.
      * glu_sort_elem_econstructor; mauto 2; reflexivity.
      * simpl.
        split; [subst; mauto 2|].
        intros.
        assert {{ Γ' ⊢ A[σ] ≈ Sort@s[σ] }} by mauto 3.
        assert {{ Γ' ⊢ A[σ] ≈ Sort@s }} by mauto 4.
        enough {{ Γ' ⊢ M[σ] ≈ A' : A[σ] }}; mauto 2.
    + inversion_clear H.
      inversion_clear H2.
      simpl_glu_rel.
      assert {{ Γ ⊢ M ® glu_typ_top_of_sort pred_P s m }} as [] by mauto 3.
      econstructor.
      * mauto 3.
      * econstructor; mauto 2.
      * simpl_glu_rel.
        eassumption.
      * mauto 2.
      * intros.
        inversion_clear H10. (* H10 : {{ Rnf ⇓ Sort @ s m in length Γ' ↘ W }} *)
        assert {{ Γ' ⊢ A[σ] ≈ Sort@s[σ] }} by mauto 3.
        assert {{ Γ' ⊢ A[σ] ≈ Sort@s }} as -> by mauto 4.
        mauto 3.

  - assert (glu_sort_elem pred_P s typ_rel exp_rel a) by eassumption.
    eapply realize_glu_sort_elem_gen in H0.
    destruct_conjs.
    repeat split; intros; mauto 3.
    + enough (glu_typ_top pred_P a Γ A) as HA by (destruct HA; eassumption).
      enough (glu_typ_top_of_sort pred_P s a Γ A) by (eapply glu_typ_top_of_sort_implies_glu_typ_top; mauto 2).
      eapply H0; mauto 3.
      assert (per_sort pred_P s a a) as [] by mauto 2.
      mauto 3.
    + enough (glu_typ_top pred_P a Γ A) as HA by (destruct HA; mauto 2).
      enough (glu_typ_top_of_sort pred_P s a Γ A) by (eapply glu_typ_top_of_sort_implies_glu_typ_top; mauto 2).
      mauto 2.
Qed.


Corollary realize_glu_typ_typ_top {P} (pred_P : PredicativeSig P) : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A,
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Γ ⊢ A ® glu_typ_top pred_P a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_typ_elem_per_typ in H.
  simpl in *. destruct_all.
  eapply realize_glu_typ_elem_gen; eauto.
Qed.

Corollary realize_glu_typ_elem_bot {P} (pred_P : PredicativeSig P) : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ glu_elem_bot pred_P so a }} ->
      {{ Γ ⊢ M : A ® ⇑ a m ∈ exp_rel }}.
Proof.
  intros.
  eapply realize_glu_typ_elem_gen; eauto.
Qed.

Theorem realize_glu_typ_elem_top {P} (pred_P : PredicativeSig P) : forall a so typ_rel exp_rel,
    {{ DG a ∈ glu_typ_elem pred_P so ↘ typ_rel ↘ exp_rel }} ->
    forall Γ A M m,
      {{ Γ ⊢ M : A ® m ∈ exp_rel }} ->
      {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P so a }}.
Proof.
  intros.
  pose proof H.
  eapply glu_typ_elem_per_typ in H.
  simpl in *. destruct_all.
  eapply realize_glu_typ_elem_gen; eauto.
  eapply glu_typ_elem_per_elem; eauto.
Qed.

#[export]
Hint Resolve realize_glu_typ_typ_top realize_glu_typ_elem_top : mcpts.

Lemma var_glu_typ_elem_bot {P} (pred_P : PredicativeSig P) : forall a typ_rel exp_rel Γ A,
    {{ DG a ∈ glu_typ_elem pred_P so_None ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ, A ⊢ #0 : A[Wk] ® !(length Γ) ∈ glu_elem_bot pred_P so_None a }}.
Proof.
  intros.
  saturate_glu_info.
  econstructor; mauto 4.
  - eapply glu_typ_elem_typ_monotone; mauto 3.
    assert {{ ⊢ Γ, A }} by mauto 4.
    eapply weakening_wk; mauto 3.
  - intros.
    progressive_inversion.
    exact (var_weaken_gen _ _ _ H2 nil _ _ eq_refl).
Qed.

Corollary var0_glu_typ_elem {P} (pred_P : PredicativeSig P) : forall {a typ_rel exp_rel Γ A},
    {{ DG a ∈ glu_typ_elem pred_P so_None ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Γ, A ⊢ #0 : A[Wk] ® ⇑! a (length Γ) ∈ exp_rel }}.
Proof.
  intros.
  eapply realize_glu_typ_elem_bot; mauto 4.
  eauto using var_glu_typ_elem_bot.
Qed.
