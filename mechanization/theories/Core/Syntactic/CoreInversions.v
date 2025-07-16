From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.

Lemma wf_pi_inversion {P : PtsSig} : forall {Γ : Ctx P} {A B C s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B : C }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    destruct_conjs; gen_core_presups; eexists; (try split); mauto 2.
  econstructor; mauto 2.
  eapply IHwf_exp; mauto 2.
  eapply IHwf_exp; mauto 2.
  transitivity {{{ A0 }}}; mauto 2.
  eapply IHwf_exp; mauto 2.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mcpts.

Corollary wf_pi_inversion' {P : PtsSig} : forall {Γ : Ctx P} {A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B : Sort@s3 }} ->
    {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }}.
Proof with mautosolve 4.
  intros.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ Sort@s3 }}) by (eapply wf_pi_inversion; mauto 2).
  destruct_conjs.
  split; assumption.
Qed.

Corollary wf_typ_pi_inversion {P : PtsSig} : forall {Γ : Ctx P} {A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ Π r A B }} ->
    {{ Γ ⊢ Π r A B : Sort@s3 }}.
Proof.
  intros.
  inversion_clear H.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ Sort@s }}).
  eapply wf_pi_inversion; mauto 2.
  destruct_conjs.
  econstructor; mauto 2.
Qed. 

#[export]
Hint Resolve wf_pi_inversion' wf_typ_pi_inversion : mcpts.

Corollary wf_fn_inversion {P : PtsSig} : forall {Γ : Ctx P} {A M C s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ λ r A M : C }} ->
    exists B, {{ Γ, A::Sort@s1 ⊢ M : B }} /\ {{ Γ ⊢ Π r A B ≈ C }}.
Proof with solve [mauto].
  (* There is something wrong here because the IH does not make sense *)
  intros * H.
  dependent induction H;
    try specialize (IHwf_exp1 _ _ eq_refl);
    try specialize (IHwf_exp2 _ _ eq_refl);
    try specialize (IHwf_exp3 _ _ eq_refl);
    destruct_conjs; gen_core_presups;
    eexists; split; mauto 2.
    
  - assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto.
    eapply eq_typ_refl; mauto.

    (* I don't understand why I can't use the IH for these cases *)
  - admit.
  - admit.

Admitted.  

#[export]
Hint Resolve wf_fn_inversion : mcpts.

Lemma wf_app_inversion {P : PtsSig} : forall {Γ : Ctx P} {M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B s1 s2 s3 (r : Ru P s1 s2 s3), {{ Γ ⊢ M : Π r A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ [Id,,N]B ≈ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H.
  - destruct_conjs; 
      do 6 eexists; repeat split; eauto.
    (* reflexivity. *)
    eapply eq_typ_refl.
    assert {{ Γ ⊢ Π r A B : Sort@s3 }} by mauto.
    assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }}).
    {
      eapply wf_pi_inversion'; mauto 2.
    }
    destruct_conjs.
    econstructor; mauto 2.
  - specialize (IHwf_exp _ _ eq_refl); 
      destruct_conjs;
      do 6 eexists; repeat split; eauto.
    transitivity {{{ A }}}; mauto 2.
Qed.

#[export]
Hint Resolve wf_app_inversion : mcpts.

Lemma wf_vlookup_inversion {P : PtsSig} : forall {Γ : Ctx P} {x A},
    {{ Γ ⊢ #x : A }} ->
    exists A' s, {{ #x : A' :: Sort@s ∈ Γ }} /\ {{ Γ ⊢ A' ≈ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H.
  - exists A; exists s.
    split; mauto 2.
    eapply eq_typ_refl.
    econstructor; mauto 2.
  - specialize (IHwf_exp _ eq_refl).
    destruct IHwf_exp as [A' HA'].
    destruct HA' as [s [HA'1 HA'2]].
    exists A'; exists s.
    split; mauto 2.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mcpts.

Lemma wf_exp_sub_inversion {P : PtsSig} : forall {Γ : Ctx P} {M σ A},
    {{ Γ ⊢ [σ]M : A }} ->
    exists Δ A', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\ {{ Γ ⊢ [σ]A' ≈ A }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H.
  - exists Δ; exists A.
    split; mauto 2.
    split; mauto 2.
    eapply eq_typ_refl; mauto 2.
    econstructor; mauto 2.
    eapply presup_exp_typ; mauto 2.
  - specialize (IHwf_exp _ _ eq_refl).
    destruct IHwf_exp as [Δ [A' [Hσ [HM HA]]]].
    exists Δ; exists A'; split; mauto 2.
    split; mauto 2.
Qed.


#[export]
Hint Resolve wf_exp_sub_inversion : mcpts.

(** We omit [wf_conv] and [wf_cumu] as they do not give useful inversions *)

Lemma wf_sub_id_inversion {P : PtsSig} : forall (Γ Δ : Ctx P),
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ≈ Δ }}.
Proof.
  intros * H.
  dependent induction H; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcpts.

Lemma wf_sub_weaken_inversion {P : PtsSig} : forall {Γ Δ : Ctx P},
    {{ Γ ⊢s Wk : Δ }} ->
    exists Γ' A s, {{ ⊢ Γ ≈ Γ', A::Sort@s }} /\ {{ ⊢ Γ' ≈ Δ }}.
Proof.
  intros * H.
  dependent induction H;
    firstorder;
    progressive_inversion;
    repeat eexists; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_weaken_inversion : mcpts.

Lemma wf_sub_compose_inversion {P : PtsSig} : forall {Γ1 : Ctx P} {σ1 σ2 Γ3},
    {{ Γ1 ⊢s σ2 ∘ σ1 : Γ3 }} ->
    exists Γ2, {{ Γ1 ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Γ3 }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H; mauto 3.  
  specialize (IHwf_sub _ _ eq_refl).
  destruct_conjs.
  eexists.
  repeat split...
Qed.

#[export]
Hint Resolve wf_sub_compose_inversion : mcpts.

Lemma wf_sub_extend_inversion {P : PtsSig} : forall {Γ : Ctx P} {σ M Δ},
    {{ Γ ⊢s σ,,M : Δ }} ->
    exists Δ' A' s, {{ ⊢ Δ', A'::Sort@s ≈ Δ }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : [σ]A' }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    try specialize (IHwf_sub _ _ eq_refl);
    destruct_conjs;
    repeat eexists...
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcpts.
