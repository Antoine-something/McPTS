From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

(** ** Subtyping and equality preserves length *)
Lemma wf_ctx_subtyp_length {P : PtsSig} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ ⊆ Γ' }} ->
    length Γ = length Γ'.
Proof. induction 1; simpl; auto. Qed.

Lemma wf_ctx_eq_length {P : PtsSig} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ ≈ Γ' }} ->
    length Γ = length Γ'.
Proof. induction 1; simpl; auto. Qed.

Open Scope list_scope.

(** ** Deep variable lookups in local contexts *)
Lemma app_ctx_lookup {P : PtsSig} : forall (Γ' : ctx P) A Γ n,
    length Γ' = n ->
    {{ #n : ^(iter (S n) (fun A' => {{{ A'[Wk] }}}) A) ∈ ^(Γ' ++ A :: Γ) }}.
Proof.
  induction Γ'; intros; simpl in *; subst; mauto.
Qed.

Lemma app_ctx_vlookup {P : PtsSig} : forall (Γ' : ctx P) A Γ n,
    {{ ⊢ ^(Γ' ++ A :: Γ) }} ->
    length Γ' = n ->
    {{ ^(Γ' ++ A :: Γ) ⊢ #n : ^(iter (S n) (fun A' => {{{ A'[Wk] }}}) A) }}.
Proof.
  intros.
  assert {{ #n : ^(iter (S n) (fun A' => {{{ A'[Wk] }}}) A) ∈ ^(Γ' ++ A :: Γ) }} by (eapply app_ctx_lookup; mauto).
  subst.
  mauto 2.
Qed.


(** ** Derived stability under context equality *)
Lemma wf_ctx_eq_extend_wf_exp {P} : forall {Γ : ctx P} {Γ' A B M},
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ Γ, A ⊢ M : B }} ->
    {{ Γ', A ⊢ M : B }}.
Proof.
  intros; gen_presups.
  assert {{ Γ ⊢ A ≈ A }} by mauto 3.
  assert {{ ⊢ Γ, A ≈ Γ', A }} by mauto 3.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_ctx_eq_extend_wf_exp : mcpts.
