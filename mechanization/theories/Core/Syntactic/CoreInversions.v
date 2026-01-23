From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CtxEq.
Import Syntax_Notations.


Lemma wf_pi_inversion {P : PtsSig} : forall {Γ : ctx P} {A B C},
    {{ Γ ⊢ Π A B : C }} ->
    exists s1 s2 s3,
      Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ C }}.
Proof with mautosolve 4.  
  intros * H.
  dependent induction H;
    gen_core_presups; mauto.
  - do 3 eexists; repeat split; mauto 3.
  - specialize (IHwf_exp A B A0).
    assert (exists s1 s2 s3 : P,
               Ru P s1 s2 s3 /\
                 {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ,A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ A0 }}) by mauto 2.
    destruct_conjs.
    do 3 eexists; repeat split; mauto 2.
Qed.

#[export]
Hint Resolve wf_pi_inversion : mcpts.

(* I am not sure this is really relevant in our setting *)
Corollary wf_pi_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B C},
    {{ Γ ⊢ Π A B : C }} ->
    exists s1 s2 s3,
      Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof with mautosolve 4.
  intros.
  assert (exists s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ C }}) by (eapply wf_pi_inversion; mauto 2).
  destruct_conjs; repeat eexists; mauto 2.
Qed.

Corollary wf_pi_inversion_typ {P} : forall {Γ : ctx P} {A B C},
    {{ Γ ⊢ Π A B : C }} ->
    exists s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ Sort@s3 ≈ C }}.
Proof.
  intros.
  assert (exists s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ C }}) by (eapply wf_pi_inversion; mauto 2).
  destruct_conjs; repeat eexists; mauto 2.  
Qed.


#[export]
Hint Resolve wf_pi_inversion' wf_pi_inversion_typ : mcpts.

Corollary wf_typ_pi_inversion {P : PtsSig} : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ Π A B }} ->
    exists s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Π A B : Sort@s3 }}.
Proof.
  intros * H.
  inversion_clear H.
  assert (exists s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ≈ Sort@s }}) as [s1 [s2 [s3]]] by mauto 2.
  destruct_conjs.
  repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion : mcpts.

Corollary wf_typ_pi_inversion' {P : PtsSig} : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ Π A B }} ->
    exists s1 s2 s3,
      Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}.
Proof.
  intros.
  assert (exists s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Π A B : Sort@s3 }}) by mauto 2.
  destruct_conjs; repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion' : mcpts.

Corollary wf_typ_pi_inversion_typ {P} : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ Π A B }} ->
    exists s1 s2 s3,
      Ru P s1 s2 s3 /\ {{ Γ ⊢ Π A B : Sort@s3 }}.
Proof.
  intros.
  assert (exists s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Π A B : Sort@s3 }}) by mauto 2.
  destruct_conjs; repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_pi_inversion_typ : mcpts.


Corollary wf_fn_inversion {P : PtsSig} : forall {Γ : ctx P} {A M C},
    {{ Γ ⊢ λ A M : C }} ->
    exists s1 s2 s3 B, Ru P s1 s2 s3 /\ {{ Γ, A ⊢ M : B }} /\ {{ Γ ⊢ Π A B ≈ C }}.
Proof with solve [mauto].
  intros * H.
  dependent induction H;
    gen_core_presups.
  - repeat eexists; mauto.
  - specialize (IHwf_exp A M A0).
    assert (exists s1 s2 s3 B, Ru P s1 s2 s3 /\ {{ Γ, A ⊢ M : B }} /\ {{ Γ ⊢ Π A B ≈ A0 }}) by mauto 2.
  destruct_conjs.
  repeat eexists; mauto.
Qed.

#[export]
Hint Resolve wf_fn_inversion : mcpts.

Lemma wf_app_inversion {P : PtsSig} : forall {Γ : ctx P} {M N C},
    {{ Γ ⊢ M N : C }} ->
    exists A B s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ M : Π A B }} /\ {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ B[Id,,N] ≈ C }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 6 eexists; repeat split; eauto.
    eapply wf_typ_eq_refl.
    assert {{ Γ ⊢ Π A B : Sort@s3 }} by mauto.
    assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}) by mauto.
    destruct_conjs.
    econstructor; mauto 3.
  - 
    assert (exists A0 B s1 s2 s3, Ru P s1 s2 s3 /\ {{ Γ ⊢ M : Π A0 B }} /\ {{ Γ ⊢ N : A0 }} /\ {{ Γ ⊢ B[Id,,N] ≈ A }}) by (eapply IHwf_exp; mauto).
    destruct_conjs.
    do 6 eexists; repeat split; mauto.  
Qed.

#[export]
Hint Resolve wf_app_inversion : mcpts.

Lemma wf_vlookup_inversion {P : PtsSig} : forall {Γ : ctx P} {x A},
    {{ Γ ⊢ #x : A }} ->
    exists A', {{ #x : A' ∈ Γ }} /\ {{ Γ ⊢ A' ≈ A }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - eexists; split; mauto.
  - assert (exists A', {{ #x : A' ∈ Γ }} /\ {{ Γ ⊢ A' ≈ A0 }}) by (eapply IHwf_exp; mauto).
    destruct_conjs.
    eexists; split; mauto.
Qed.

#[export]
Hint Resolve wf_vlookup_inversion : mcpts.

(* Lemma wf_nat_inversion {P} : forall {Γ : ctx P} {A}, *)
(*     {{ Γ ⊢ ℕ : A }} -> *)
(*     exists s (r : Ru_nat P s), *)
(*       {{ Γ ⊢ Sort@s ≈ A }}. *)
(* Proof with mautosolve. *)
(*   intros * H. *)
(*   dependent induction H. *)
(*   - eexists. mauto. *)
(*   - specialize (IHwf_exp A0 ltac:(reflexivity) ltac:(reflexivity)). *)
(*     destruct_conjs. *)
(*     do 2 eexists. apply H2. *)
(*     etransitivity; mauto. *)
(* Qed. *)

(* #[export] *)
(*   Hint Resolve wf_nat_inversion : mcpts. *)

(* Corollary wf_zero_inversion {P} : forall {Γ : ctx P} {A}, *)
(*     {{ Γ ⊢ zero : A }} -> *)
(*     exists s (r : Ru_nat P s), *)
(*       {{ Γ ⊢ ℕ ≈ A }}. *)
(* Proof with mautosolve. *)
(*   intros * H. *)
(*   dependent induction H. *)
(*   - eexists. mauto. *)
(*   - specialize (IHwf_exp A0 ltac:(reflexivity) ltac:(reflexivity)). *)
(*     destruct_conjs. *)
(*     do 2 eexists. apply H2. *)
(*     etransitivity; mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_zero_inversion : mcpts. *)

(* Corollary wf_succ_inversion {P} : forall {Γ : ctx P} {A M}, *)
(*     {{ Γ ⊢ succ M : A }} -> *)
(*     {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ ℕ ≈ A }}. *)
(* Proof with mautosolve. *)
(*   intros * H. *)
(*   dependent induction H. *)
(*   - eexists; mautosolve. *)
(*   - specialize (IHwf_exp A0 M ltac:(reflexivity) ltac:(reflexivity)). *)
(*     destruct_conjs. *)
(*     eexists. apply H2. *)
(*     etransitivity; mauto. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_succ_inversion : mcpts. *)

(* Lemma wf_natrec_inversion {P} : forall {Γ : ctx P} {A M A' MZ MS}, *)
(*     {{ Γ ⊢ rec M return A' | zero -> MZ | succ -> MS end : A }} -> *)
(*     {{ Γ ⊢ MZ : A'[Id,,zero] }} /\ {{ Γ, ℕ, A' ⊢ MS : A'[Wk∘Wk,,succ(#1)] }} /\ {{ Γ ⊢ M : ℕ }} /\ {{ Γ ⊢ A'[Id,,M] ≈ A }}. *)
(* Proof with mautosolve. *)
(*   intros * H. *)
(*   dependent induction H. *)
(*   - do 3 (eexists; mauto). *)
(*     eapply wf_typ_eq_refl. *)
(*     assert {{ Γ, ℕ ⊢ A' }}; mauto 2. *)
(*     assert {{ Γ ⊢s Id,,M : Γ, ℕ }} by mauto 4. *)
(*     mauto 2. *)
(*   - specialize (IHwf_exp A0 M A' MZ MS ltac:(reflexivity) ltac:(reflexivity)). *)
(*     destruct_conjs. *)
(*     repeat split; mauto. *)
(* Qed. *)
    
(* #[export] *)
(* Hint Resolve wf_natrec_inversion : mcpts. *)

Lemma wf_exp_sub_inversion {P : PtsSig} : forall {Γ : ctx P} {M σ A},
    {{ Γ ⊢ M[σ] : A }} ->
    exists Δ A', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\ {{ Γ ⊢ A'[σ] ≈ A }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - do 2 eexists; repeat split; mauto.
  - assert (exists Δ A', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ M : A' }} /\ {{ Γ ⊢ A'[σ] ≈ A0 }}) by (eapply IHwf_exp; mauto).
    destruct_conjs.
    do 2 eexists; repeat split; mauto.  
Qed.

#[export]
Hint Resolve wf_exp_sub_inversion : mcpts.  
  
(** We omit [wf_conv] and [wf_cumu] as they do not give useful inversions *)

Lemma wf_sub_id_inversion {P : PtsSig} : forall (Γ : ctx P) Δ,
    {{ Γ ⊢s Id : Δ }} ->
    {{ ⊢ Γ ≈ Δ }}.
Proof.
  intros * H.
  dependent induction H; mautosolve 3.
Qed.

#[export]
Hint Resolve wf_sub_id_inversion : mcpts.

Lemma wf_sub_weaken_inversion {P : PtsSig} : forall {Γ : ctx P} {Δ},
    {{ Γ ⊢s Wk : Δ }} ->
    exists Γ' A, {{ ⊢ Γ ≈ Γ', A }} /\ {{ ⊢ Γ' ≈ Δ }}.
Proof.
  intros * H.
  
  dependent induction H;
    firstorder;
    progressive_inversion.  
  - repeat eexists; mauto 2.
  - assert (exists Γ' A, {{ ⊢ Γ ≈ Γ', A }} /\ {{ ⊢ Γ' ≈ Δ0 }}) by (eapply IHwf_sub; mauto).
    destruct_conjs.
    repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_weaken_inversion : mcpts.

Lemma wf_sub_compose_inversion {P : PtsSig} : forall {Γ1 : ctx P} {σ1 σ2 Γ3},
    {{ Γ1 ⊢s σ1 ∘ σ2 : Γ3 }} ->
    exists Γ2, {{ Γ1 ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Γ3 }}.
Proof with mautosolve 3.
  intros * H.
  dependent induction H; mauto 3.
  assert (exists Γ2, {{ Γ ⊢s σ2 : Γ2 }} /\ {{ Γ2 ⊢s σ1 : Δ }}) by (eapply IHwf_sub; mauto).
  destruct_conjs.
  eexists; split; mauto.
Qed.

#[export]
Hint Resolve wf_sub_compose_inversion : mcpts.

Lemma wf_sub_extend_inversion {P : PtsSig} : forall {Γ : ctx P} {σ M Δ},
    {{ Γ ⊢s σ,,M : Δ }} ->
    exists Δ' A', {{ ⊢ Δ', A' ≈ Δ }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}.
Proof with mautosolve 4.
  intros * H.
  dependent induction H;
    gen_core_presups.
  - repeat eexists...
  - assert (exists Δ' A', {{ ⊢ Δ', A' ≈ Δ0 }} /\ {{ Γ ⊢s σ : Δ' }} /\ {{ Γ ⊢ M : A'[σ] }}) by (eapply IHwf_sub; mauto).
    destruct_conjs.
    repeat eexists...
Qed.

#[export]
Hint Resolve wf_sub_extend_inversion : mcpts.
    
