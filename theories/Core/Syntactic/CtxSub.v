From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System.
Import Syntax_Notations.

Lemma ctx_sub_refl {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ⊆ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_sub_refl : mcpts.

Lemma wf_subtyp_sub {P} : forall {Δ : ctx P} {A A'},
    (* {{ Δ ⊢ A : Sort@s }} -> *)
    (* {{ Δ ⊢ A' : Sort@s }} -> *)
    {{ Δ ⊢ A ⊆ A' }} ->
    forall Γ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  induction 1; intros; mauto 4.
  - admit.
  - admit.
  - transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; [econstructor; mauto |].
    transitivity {{{ Π r (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4].
    eapply wf_subtyp_pi; mauto 4.
    
    transitivity {{{ Sort@s }}}; [econstructor; mauto 4 |].
    transitivity {{{ Type@j }}}; [| econstructor; mauto 4].
    mauto 3.
  - transitivity {{{ Π (A[σ]) (B[q σ]) }}}; [econstructor; mauto |].
    transitivity {{{ Π (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4].
    eapply wf_subtyp_pi with (i := i); mauto 4.


Lemma ctx_sub_ctx_lookup {P} : forall {Γ Δ : ctx P},
    {{ ⊢ Δ ⊆ Γ }} ->
    forall {A x s},
      {{ #x : A@s ∈ Γ }} ->
      exists B,
        {{ #x : B@s ∈ Δ }} /\
          {{ Δ ⊢ B ⊆ A }}.
Proof with (do 2 eexists; repeat split; mautosolve).
  induction 1; intros * Hx; progressive_inversion.
  dependent destruction Hx.
  - eexists; split; mauto 3.
    dependent destruction H2.
    + enough {{ Γ, Sort@s0 @ s ⊢ Sort@s0[Wk] ≈ Sort@s0[Wk] : Sort@s }} by (econstructor; mauto 3).
      enough {{ Γ, Sort@s0 @ s ⊢ Sort@s0[Wk] : Sort@s }} by mauto 2.
      mauto 3.
    + assert {{ ⊢ Γ, A@s }} by mauto 3.
      assert {{ Γ, A@s ⊢s Wk : Γ }} by mauto 3.
      assert {{ Γ, A@s ⊢ A[Wk] ≈ A'[Wk] : Sort@s0 }} by mauto 3.
      mauto 3.
    + admit.
    + 
    idtac...
  - edestruct IHwf_ctx_sub as [? []]; try eassumption...
Qed.

Module ctxsub_judg.
  #[local]
  Ltac gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M : ^?A }} => pose proof ctxsub_exp_helper _ _ _ _ H
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} => pose proof ctxsub_exp_eq_helper _ _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} => pose proof ctxsub_sub_helper _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} => pose proof ctxsub_sub_eq_helper _ _ _ _ _ H
  | {{ ^?Γ ⊢ ^?M ⊆ ^?M' }} => pose proof ctxsub_subtyp_helper _ _ _ _ H
  end.

  #[local]
  Lemma ctxsub_exp_helper {P} : forall {Γ : ctx P} {M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M : A }}
  with
  ctxsub_exp_eq_helper {P} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ≈ M' : A }}
  with
  ctxsub_sub_helper {P} : forall {Γ Γ' : ctx P} {σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ : Γ' }}
  with
  ctxsub_sub_eq_helper {P} : forall {Γ Γ' : ctx P} {σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}
  with
  ctxsub_subtyp_helper {P} : forall {Γ : ctx P} {M M'}, {{ Γ ⊢ M ⊆ M' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ⊆ M' }}.
  Proof with mautosolve.
    all: inversion_clear 1;
      (on_all_hyp: gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper);
      clear ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper;
      intros * HΓΔ; destruct (presup_ctx_sub HΓΔ); mauto 4;
      try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
    
    
    1-3: assert {{ Δ ⊢ B : Sort@s1 }} by eauto; assert {{ ⊢ Δ, B@s1 ⊆ Γ, B@s1 }} by mauto;
    econstructor...

    1:{
      assert {{ Δ ⊢ A : Sort@s }} by eauto.
      econstructor.
    }
    
    

    (** ctxsub_exp_helper & ctxsub_exp_eq_helper recursion cases *)
    1,12-14: assert {{ ⊢ Δ, ℕ ⊆ Γ, ℕ }} by (econstructor; mautosolve);
    assert {{ Δ, ℕ ⊢ B : Type@i }} by eauto; econstructor...
    (** ctxsub_exp_helper & ctxsub_exp_eq_helper function cases *)
    1-3,11-15: assert {{ Δ ⊢ B : Type@i }} by eauto; assert {{ ⊢ Δ, B ⊆ Γ, B }} by mauto;
    try econstructor...
    (** equality type case *)
    6,15:idtac...

    (** ctxsub_exp_helper & ctxsub_exp_eq_helper variable cases *)
    5,16: assert (exists B, {{ #x : B ∈ Δ }} /\ {{ Δ ⊢ B ⊆ A }}); destruct_conjs; mautosolve 4.
    (** ctxsub_sub_helper & ctxsub_sub_eq_helper weakening cases *)
    16,17: inversion_clear HΓΔ; econstructor; mautosolve 4.

    (** eqrec related cases *)
    5,12-14: assert {{ ⊢ Δ, B ⊆ Γ, B }} by mauto;
      assert {{ Γ, B ⊢s Wk : Γ }} by mauto 3;
      assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Γ, B, B[Wk] ⊢s Wk : Γ, B }} by mauto 4;
      assert {{ Γ, B, B[Wk] ⊢s Wk∘Wk : Γ }} by mauto 3;
      assert {{ Δ, B ⊢s Wk : Δ }} by mauto 3;
      assert {{ Δ, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢s Wk : Δ, B }} by mauto 4;
      assert {{ Δ, B, B[Wk] ⊢s Wk∘Wk : Δ }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ ⊢ Δ, B, B[Wk] ⊆ Γ, B, B[Wk] }} by (econstructor; mauto 4);
      assert {{ Γ, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ Δ, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ ⊢ Δ, B, B[Wk], Eq B[Wk∘Wk] #1 #0 ⊆ Γ, B, B[Wk], Eq B[Wk∘Wk] #1 #0 }} by mauto 3;
      econstructor; mauto 2.

    (* sigma type case *)
    1-10:
      match goal with
      | _ : context [ {{{ ^?Γ , ^?A }}} ] , _ : {{ ⊢ ^?Δ ⊆ ^?Γ }} |- _ =>
        assert {{ ⊢ Δ, A ⊆ Γ, A }} by (econstructor; mautosolve 3)
      end; econstructor; mauto 3.

    - (** ctxsub_exp_eq_helper variable case *)
      inversion_clear HΓΔ as [|Δ0 ? ? C'].
      assert (exists D, {{ #x : D ∈ Δ0 }} /\ {{ Δ0 ⊢ D ⊆ B }}) as [D [i0 ?]] by mauto.
      destruct_conjs.
      assert {{ ⊢ Δ0, C' }} by mauto.
      assert {{ Δ0, C' ⊢ D[Wk] ⊆ B[Wk] }}...
    - eapply wf_subtyp_pi with (i := i); firstorder mauto 4.
    - eapply wf_subtyp_sigma with (i := i); firstorder mauto 4.
  Qed.

  Corollary ctxsub_exp : forall {Γ Δ M A}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ M : A }} -> {{ Δ ⊢ M : A }}.
  Proof.
    eauto using ctxsub_exp_helper.
  Qed.

  Corollary ctxsub_exp_eq : forall {Γ Δ M M' A}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ M ≈ M' : A }} -> {{ Δ ⊢ M ≈ M' : A }}.
  Proof.
    eauto using ctxsub_exp_eq_helper.
  Qed.

  Corollary ctxsub_sub : forall {Γ Δ σ Γ'}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢s σ : Γ' }} -> {{ Δ ⊢s σ : Γ' }}.
  Proof.
    eauto using ctxsub_sub_helper.
  Qed.

  Corollary ctxsub_sub_eq : forall {Γ Δ σ σ' Γ'}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}.
  Proof.
    eauto using ctxsub_sub_eq_helper.
  Qed.

  Corollary ctxsub_subtyp : forall {Γ Δ A B}, {{ ⊢ Δ ⊆ Γ }} -> {{ Γ ⊢ A ⊆ B }} -> {{ Δ ⊢ A ⊆ B }}.
  Proof.
    eauto using ctxsub_subtyp_helper.
  Qed.

  #[export]
  Hint Resolve ctxsub_exp ctxsub_exp_eq ctxsub_sub ctxsub_sub_eq ctxsub_subtyp : mcpts.
End ctxsub_judg.

Export ctxsub_judg.

Lemma wf_ctx_sub_trans : forall Γ0 Γ1,
    {{ ⊢ Γ0 ⊆ Γ1 }} ->
    forall  Γ2,
    {{ ⊢ Γ1 ⊆ Γ2 }} ->
    {{ ⊢ Γ0 ⊆ Γ2 }}.
Proof.
  induction 1; intros; progressive_inversion; [constructor |].
  eapply wf_ctx_sub_extend with (i := max i i0);
    mauto 3 using lift_exp_max_left, lift_exp_max_right.
Qed.

#[export]
 Hint Resolve wf_ctx_sub_trans : mcpts.

#[export]
Instance wf_ctx_sub_trans_ins : Transitive wf_ctx_sub.
Proof. eauto using wf_ctx_sub_trans. Qed.

Add Parametric Morphism : wf_exp
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_exp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_exp_eq
  with signature wf_ctx_sub --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_exp_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_sub
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_sub_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_sub_eq
  with signature wf_ctx_sub --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_sub_eq_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.

Add Parametric Morphism : wf_subtyp
  with signature wf_ctx_sub --> eq ==> eq ==> Basics.impl as ctxsub_subtyp_morphism.
Proof.
  cbv. intros. mauto 3.
Qed.
