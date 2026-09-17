From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic.System Require Import Definitions Lemmas.Instances Lemmas.CorePresup Lemmas.SortLemmas Lemmas.NatLemmas Lemmas.SubstitutionLemmas.
Import Syntax_Notations.

(** * Lemmas about well-formedness and equality of variables *)
(** Well-formedness of variables under substitution composition  *)
Lemma var_compose_subs {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' τ σ A x},
    {{ Γ'' ⊢ A }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ #x : A[σ][τ] ∈ Γ }} ->
    {{ Γ ⊢ #x : A[σ∘τ] }}.
Proof.
  intros.
  assert {{ Γ' ⊢ A[σ] }} by mauto 4.
  assert {{ Γ ⊢ A[σ][τ] }} by mauto 3.
  assert {{ Γ ⊢ A[σ∘τ] }} by mauto 3.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve var_compose_subs : mcpts.

(** ** Propagation of substitutions in variables *)
Lemma sub_lookup_var0 {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M1 M2 B},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ' ⊢ M1 : B[σ] }} ->
    {{ Γ' ⊢ M2 : B[σ] }} ->
    {{ Γ' ⊢ #0[σ,,M1,,M2] ≈ M2 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] }} by mauto 4.
  assert {{ Γ' ⊢s σ,,M1 : Γ, B }} by mauto 3.
  assert {{ Γ' ⊢ B[Wk][σ,,M1] }} by mauto 4.
  assert {{ Γ' ⊢ B[Wk][σ,,M1] ≈ B[σ] }} by mauto.
  eapply wf_exp_eq_conv_typ_eq; mauto 3.
  eapply wf_exp_eq_var_0_sub; [| | econstructor]; mauto.
Qed.

#[export]
Hint Resolve sub_lookup_var0 : mcpts.

Lemma id_sub_lookup_var0 {P : PtsSig} : forall {Γ : ctx P} {M1 M2 B},
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var0 | |];
    mauto 4.
Qed.

#[export]
Hint Resolve id_sub_lookup_var0 : mcpts.
 
Lemma sub_lookup_var1 {P : PtsSig} : forall {Γ : ctx P} {Γ' σ M1 M2 B},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ' ⊢ M1 : B[σ] }} ->
    {{ Γ' ⊢ M2 : B[σ] }} ->
    {{ Γ' ⊢ #1[σ,,M1,,M2] ≈ M1 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] }} by mauto 4.
  assert {{ Γ' ⊢s σ,,M1 : Γ, B }} by mauto 3.
  assert {{ Γ' ⊢ B[Wk][σ,,M1] }} by mauto 4.
  assert {{ Γ' ⊢ B[Wk][σ,,M1] ≈ B[σ] }} by mauto 3.
  assert {{ Γ' ⊢ B[σ]}} by mauto 4.
  assert {{ Γ' ⊢ M2 : B[Wk][σ,,M1] }} by mauto 3.
  transitivity {{{ #0[σ,,M1] }}}; mauto 3.
Qed.

#[export]
Hint Resolve sub_lookup_var1 : mcpts.

Lemma id_sub_lookup_var1 {P : PtsSig} : forall {Γ : ctx P} {M1 M2 B},
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var1 | |];
    mauto 4.
Qed.

#[export]
Hint Resolve id_sub_lookup_var1 : mcpts.

Lemma wf_exp_eq_var_1_sub_q_sigma {P : PtsSig} : forall {Γ : ctx P} {Γ' A B σ},
    {{ Γ' ⊢ B }} ->
    {{ Γ', B ⊢ A }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s q σ : Γ', B }} by mauto 2.
  assert {{ ⊢ Γ, B[σ] }} by mauto 3.
  assert {{ ⊢ Γ, B[σ], A[q σ] }} by mauto 3.
  assert {{ Γ', B ⊢ B[Wk]  }} by mauto 4.
  assert {{ Γ' ⊢ B }} by mauto 2.
  assert {{ Γ', B ⊢ #0 : B[Wk] }} by mauto 4.
  assert {{ Γ, B[σ] ⊢ A[q σ] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢s q σ∘Wk : Γ', B }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ∘Wk] }} by mauto 3.
  assert {{ Γ ⊢ B[σ]  }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk : Γ, B[σ] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[σ][Wk]  }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ] ⊢s Wk∘(q σ) ≈ σ∘Wk : Γ' }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[Wk∘(q σ)] }} by mauto.
  assert {{ Γ, B[σ] ⊢ B[Wk∘(q σ)] ≈ B[σ∘Wk] }} by mauto 3.
  assert {{ Γ, B[σ] ⊢ B[σ∘Wk] ≈ B[σ][Wk] }} by mauto.
  assert {{ Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk] }} by mauto 3. 
  assert {{ Γ, B[σ], A[q σ] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk] }} by (transitivity {{{ B[Wk][q σ][Wk] }}}; mauto 3).
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : B[σ][Wk][Wk] }} by (econstructor; mauto).
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : B[σ][Wk][Wk] }} by (econstructor; mauto).
  assert {{ Γ, B[σ] ⊢s σ∘Wk : Γ' }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0 : B[σ∘Wk] }} by mauto 3.
  assert {{ Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ∘Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ∘Wk][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ∘Wk][Wk] ≈ B[σ][Wk][Wk]  }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ][Wk][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk][Wk] }} by (do 2 etransitivity; mauto 2).
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk] ≈ B[σ][Wk∘Wk] }} by mauto 3.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_1_sub_q_sigma : mcpts.    
