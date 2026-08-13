From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Import Definitions.
Import Syntax_Notations.

(** * Immediately admissible rules *)
(** All equality judgments are reflexive on well-formed objects *)
Lemma exp_eq_refl {P : PtsSig} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M : A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_refl : mcpts.

Lemma wf_typ_eq_refl {P : PtsSig} : forall (Δ : gctx P) (Γ : ctx P) (A : typ P),
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ A ≈ A }}.
Proof.
  intros.
  apply wf_typ_eq_per_elem; eassumption.
Qed.

#[export]
Hint Resolve wf_typ_eq_refl : mcpts.

Lemma sub_eq_refl {P : PtsSig} : forall {Δ : gctx P} {σ Γ Γ'},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ ≈ σ : Γ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve sub_eq_refl : mcpts.

Lemma gctx_eq_refl {P : PtsSig} : forall {Δ : gctx P},
    {{ ▶ Δ }} ->
    {{ ▶ Δ ≈ Δ }}.
Proof.
  induction 1; mauto 2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve gctx_eq_refl : mcpts.

Lemma ctx_eq_refl {P : PtsSig} : forall {Δ : gctx P} {Γ},
    {{ Δ ▶ Γ }} ->
    {{ Δ ▶ Γ ≈ Γ }}.
Proof.
  induction 1; mauto 4.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

(** Equality of local and global contexts is symmetric (follows trivially from PER instances) *)
Lemma wf_gctx_eq_sym {P : PtsSig} : forall {Δ Δ' : gctx P}, {{ ▶ Δ ≈ Δ' }} -> {{ ▶ Δ' ≈ Δ }}.
Proof. intros; symmetry; eauto. Qed.

Lemma wf_ctx_eq_sym {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'}, {{ Δ ▶ Γ ≈ Γ' }} -> {{ Δ ▶ Γ' ≈ Γ }}.
Proof. intros; symmetry; eauto. Qed.

#[export]
Hint Resolve wf_gctx_eq_sym wf_ctx_eq_sym : mcpts.
 
(** Admissible subtyping rules *)
Lemma wf_typ_subtyp_sort_st_subtyp {P : PtsSig} : forall (Δ : gctx P) (Γ : ctx P) (s1 s2 : P),
    {{ Δ ▶ Γ }} ->
    st_subtyp s1 s2 ->
    {{ Δ ▶ Γ ⊢ Sort@s1 ⊆ Sort@s2 }}.
Proof.
  intros.
  induction H0.
  - enough {{ Δ ▶ Γ ⊢ Sort@s ≈ Sort@s }} by mauto 3.
    enough {{ Δ ▶ Γ ⊢ Sort@s }}; mauto 2.
  - transitivity {{{ Sort@s2 }}}; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sort_st_subtyp : mcpts.

Lemma wf_exp_eq_sort_subtyp {P : PtsSig} : forall {Δ : gctx P} {Γ A B s},
    {{ Δ ▶ Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ A ⊆ B }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ ⊢ A ≈ B }} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_sort_subtyp : mcpts.


(** * Basic Context Properties *)

(** ** Lemmas about fresh variables *)
Lemma gctx_lookup_var_not_eq_fresh_var {P : PtsSig} : forall {Δ : gctx P} {x x' A},
    {{ `#x : A ∈ Δ }} ->
    {{ `#x' ∉ Δ }} ->
    x <> x'.
Proof.
  induction 1; inversion_clear 1; intuition.
Qed.

#[export]
Hint Resolve gctx_lookup_var_not_eq_fresh_var : mcpts.

Lemma wf_gctx_eq_fresh_iff {P} : forall {Δ Δ' : gctx P} {x},
    {{ ▶ Δ ≈ Δ' }} ->
    {{ `#x ∉ Δ }} -> {{ `#x ∉ Δ' }}.
Proof.
  induction 1; mauto 2;
    inversion_clear 1; mauto 2;
    destruct IHwf_gctx_eq;
    mauto 3.
Qed.


Lemma wf_gctx_subtyp_fresh_iff {P} : forall {Δ Δ' : gctx P} {x},
    {{ ▶ Δ ⊆ Δ' }} ->
    {{ `#x ∉ Δ }} -> {{ `#x ∉ Δ' }}.
Proof.
  induction 1; mauto 2;
    inversion_clear 1; mauto 2;
    destruct IHwf_gctx_subtyp;
    mauto 3.
Qed.

#[export]
Hint Resolve wf_gctx_eq_fresh_iff wf_gctx_subtyp_fresh_iff : mcpts.

(** ** Properties of context lookups *)
Lemma functional_gctx_lookup {P} : forall {Δ : gctx P} {A A' x},
    {{ `#x : A ∈ Δ }} ->
    {{ `#x : A' ∈ Δ }} ->
    A = A'.
Proof.
  intros * Hx Hx'; gen A'.
  dependent induction Hx;
    intros; dependent destruction Hx';
    intuition.
Qed.

#[export]
Hint Resolve functional_gctx_lookup : mcpts.

Lemma ctx_lookup_lt {P : PtsSig} : forall {Γ : ctx P} {A x},
    {{ #x : A ∈ Γ }} ->
    x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.
#[export]
Hint Resolve ctx_lookup_lt : mcpts.

Lemma functional_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {A A' x},
    {{ #x : A ∈ Γ }} ->
    {{ #x : A' ∈ Γ }} ->
    A = A'.
Proof with mautosolve.
  intros * Hx Hx'; gen A'.
  dependent induction Hx; intros; inversion_clear Hx'; 
    f_equal;
    intuition.
Qed.

#[export]
Hint Resolve functional_ctx_lookup : mcpts. 

(** ** Basic inversion principles *)
Lemma gctx_decomp {P : PtsSig} : forall {Δ : gctx P} {x A}, {{ ▶ Δ, x : A }} -> {{ ▶ Δ }} /\ {{ Δ ▶ ⋅ ⊢ A }} /\ {{ `#x ∉ Δ }}.
Proof with now eauto.
  inversion 1; split; mauto 2.
Qed.

#[export]
Hint Resolve gctx_decomp : mcpts.

Corollary gctx_decomp_left {P : PtsSig} : forall {Δ : gctx P} {x A}, {{ ▶ Δ, x : A }} -> {{ ▶ Δ }}. 
Proof with easy.
  intros * ?%gctx_decomp...
Qed.

Corollary gctx_decomp_right {P : PtsSig} : forall {Δ : gctx P} {x A}, {{ ▶ Δ, x : A }} -> {{ Δ ▶ ⋅ ⊢ A }}.
Proof with easy.
  intros * ?%gctx_decomp...
Qed.

Corollary gctx_decomp_fresh {P : PtsSig} : forall {Δ : gctx P} {x A}, {{ ▶ Δ, x:A }} -> {{ `#x ∉ Δ }}.
Proof with easy.
  intros * ?%gctx_decomp...
Qed.

#[export]
Hint Resolve gctx_decomp_left gctx_decomp_right gctx_decomp_fresh : mcpts.


Lemma ctx_decomp {P : PtsSig} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ, A }} -> {{ Δ ▶ Γ }} /\ {{ Δ ▶ Γ ⊢ A }}.
Proof with now eauto.
  inversion 1; split; mauto 2.
Qed.

#[export]
Hint Resolve ctx_decomp : mcpts.

Corollary ctx_decomp_left {P : PtsSig} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ, A }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ, A }} -> {{ Δ ▶ Γ ⊢ A }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mcpts.

(** ** Weakening principle for global contexts *)
Lemma gctx_weakening {P : PtsSig} :
    (forall (Δ : gctx P) Γ, {{ Δ ▶ Γ }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ }}) /\
    (forall (Δ : gctx P) Γ Γ', {{ Δ ▶ Γ ⊆ Γ' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊆ Γ' }}) /\
    (forall (Δ : gctx P) Γ A M, {{ Δ ▶ Γ ⊢ M : A }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ M : A }}) /\
    (forall (Δ : gctx P) Γ A M M', {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ M ≈ M' : A }}) /\
    (forall (Δ : gctx P) Γ A, {{ Δ ▶ Γ ⊢ A }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ A }}) /\
    (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ≈ A' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ A ≈ A' }}) /\
    (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ A ⊆ A' }}) /\
    (forall (Δ : gctx P) Γ Γ' σ, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢s σ : Γ' }}) /\
    (forall (Δ : gctx P) Γ Γ' σ σ', {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢s σ ≈ σ' : Γ' }}).
Proof.
  apply syntactic_wf_local_mut_ind;
    intros;
    try mauto 2;
    try solve [econstructor; mauto 3].

  - inversion_clear H0.
    econstructor; mauto 3.
  - mautosolve.
  - inversion_clear H0.
    econstructor; mauto 3.
Qed.      

Corollary wf_ctx_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ},
    {{ Δ ▶ Γ }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

Corollary wf_ctx_subtyp_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'}, {{ Δ ▶ Γ ⊆ Γ' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊆ Γ' }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

Corollary wf_exp_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ A M}, {{ Δ ▶ Γ ⊢ M : A }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ M : A }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

Corollary wf_exp_eq_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ A M M'}, {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ M ≈ M' : A }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

Corollary wf_typ_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ ⊢ A }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ A }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.
  
Corollary wf_typ_eq_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ≈ A' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ A ≈ A' }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

Corollary wf_typ_subtyp_gctx_weakening {P : PtsSig} :  forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢ A ⊆ A' }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

Corollary wf_sub_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ}, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢s σ : Γ' }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

Corollary wf_sub_eq_gctx_weakening {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ'}, {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> forall x B, {{ ▶ Δ, x:B }} -> {{ Δ, x:B ▶ Γ ⊢s σ ≈ σ' : Γ' }}.
Proof. intros; eapply gctx_weakening; mauto 2. Qed.

#[export]  
Hint Resolve wf_ctx_gctx_weakening wf_ctx_subtyp_gctx_weakening wf_exp_gctx_weakening wf_exp_eq_gctx_weakening wf_typ_gctx_weakening wf_typ_eq_gctx_weakening wf_typ_subtyp_gctx_weakening wf_sub_gctx_weakening wf_sub_eq_gctx_weakening : mcpts.



(** * Core presupposition results *)

(** For equality of global contexts *)
Lemma presup_wf_gctx_eq {P} : forall {Δ Δ' : gctx P}, {{ ▶ Δ ≈ Δ' }} -> {{ ▶ Δ }} /\ {{ ▶ Δ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_gctx_eq_left {P} : forall {Δ Δ' : gctx P}, {{ ▶ Δ ≈ Δ' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_gctx_eq...
Qed.

Corollary presup_wf_gctx_eq_right {P} : forall {Δ Δ' : gctx P}, {{ ▶ Δ ≈ Δ' }} -> {{ ▶ Δ' }}.
Proof with easy.
  intros * ?%presup_wf_gctx_eq...
Qed.

#[export]
Hint Resolve presup_wf_gctx_eq presup_wf_gctx_eq_left presup_wf_gctx_eq_right : mcpts.

(** For subtyping of global contexts *)
Lemma presup_wf_gctx_subtyp {P} : forall {Δ Δ' : gctx P}, {{ ▶ Δ ⊆ Δ' }} -> {{ ▶ Δ }} /\ {{ ▶ Δ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_gctx_subtyp_left {P} : forall {Δ Δ' : gctx P}, {{ ▶ Δ ⊆ Δ' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_gctx_subtyp...
Qed.

Corollary presup_wf_gctx_subtyp_right {P} : forall {Δ Δ' : gctx P}, {{ ▶ Δ ⊆ Δ' }} -> {{ ▶ Δ' }}.
Proof with easy.
  intros * ?%presup_wf_gctx_subtyp...
Qed.

#[export]
Hint Resolve presup_wf_gctx_subtyp presup_wf_gctx_subtyp_left presup_wf_gctx_subtyp_right : mcpts.

(** For well-formedness of local contexts *)
Lemma presup_wf_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ : ctx P}, {{ Δ ▶ Γ }} -> {{ ▶ Δ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_wf_ctx : mcpts.
 
(** For equality of local contexts *)
Lemma presup_wf_ctx_eq {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ≈ Γ' }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }} /\ {{ Δ ▶ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_ctx_eq_gctx {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ≈ Γ' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_eq...
Qed.

Corollary presup_wf_ctx_eq_left {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ≈ Γ' }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_eq...
Qed.

Corollary presup_wf_ctx_eq_right {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ≈ Γ' }} -> {{ Δ ▶ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_ctx_eq...
Qed.

#[export]
Hint Resolve presup_wf_ctx_eq presup_wf_ctx_eq_gctx presup_wf_ctx_eq_left presup_wf_ctx_eq_right : mcpts.

(** For subtyping of local contexts *)
Lemma presup_wf_ctx_subtyp {P} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ⊆ Γ' }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }} /\ {{ Δ ▶ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_ctx_subtyp_gctx {P} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ⊆ Γ' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_subtyp...
Qed.

Corollary presup_wf_ctx_subtyp_left {P} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ⊆ Γ' }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_subtyp...
Qed.

Corollary presup_wf_ctx_subtyp_right {P} : forall {Δ : gctx P} {Γ Γ' : ctx P}, {{ Δ ▶ Γ ⊆ Γ' }} -> {{ Δ ▶ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_ctx_subtyp...
Qed.

#[export]
Hint Resolve presup_wf_ctx_subtyp presup_wf_ctx_subtyp_gctx presup_wf_ctx_subtyp_left presup_wf_ctx_subtyp_right : mcpts.


(** ** Context Presuppositions *)

(** For well-formedness of substitutions *)
Lemma presup_wf_sub {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ}, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }} /\ {{ Δ ▶ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_sub_gctx {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ}, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_sub...
Qed.
  
Corollary presup_wf_sub_left {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ}, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_sub...
Qed.

Corollary presup_wf_sub_right {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ}, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> {{ Δ ▶ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_sub...
Qed.

#[export]
Hint Resolve presup_wf_sub presup_wf_sub_gctx presup_wf_sub_left presup_wf_sub_right : mcpts.


(** For well-formedness of expressions *)
Lemma presup_wf_exp_gctx_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ M A}, {{ Δ ▶ Γ ⊢ M : A }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

Corollary presup_wf_exp_gctx {P : PtsSig} : forall {Δ : gctx P} {Γ M A}, {{ Δ ▶ Γ ⊢ M : A }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_exp_gctx_ctx...
Qed.

Corollary presup_wf_exp_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ M A}, {{ Δ ▶ Γ ⊢ M : A }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_exp_gctx_ctx...
Qed.

#[export]
Hint Resolve presup_wf_exp_gctx_ctx presup_wf_exp_gctx presup_wf_exp_ctx : mcpts.

(** For well-formedness of types *)
Lemma presup_wf_typ {P} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ ⊢ A }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

Corollary presup_wf_typ_gctx {P} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ ⊢ A }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_typ...
Qed.

Corollary presup_wf_typ_ctx {P} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ ⊢ A }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_typ...
Qed.

#[export]
Hint Resolve presup_wf_typ presup_wf_typ_gctx presup_wf_typ_ctx : mcpts.


(** For equality of substitutions *)
Lemma presup_wf_sub_eq_gctx_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ'}, {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }} /\ {{ Δ ▶ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_sub_eq_gctx {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ'}, {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_sub_eq_gctx_ctx...
Qed.

Corollary presup_wf_sub_eq_ctx_left {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ'}, {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_sub_eq_gctx_ctx...
Qed.

Corollary presup_wf_sub_eq_ctx_right {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ'}, {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ Δ ▶ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_sub_eq_gctx_ctx...
Qed.

#[export]
Hint Resolve presup_wf_sub_eq_gctx_ctx presup_wf_sub_eq_gctx presup_wf_sub_eq_ctx_left presup_wf_sub_eq_ctx_right : mcpts.

(** For equality of expressions *)
Lemma presup_wf_exp_eq_gctx_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A}, {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }}.
Proof with mautosolve 2.
  induction 1; destruct_pairs; split...
Qed.

Corollary presup_wf_exp_eq_gctx {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A}, {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_exp_eq_gctx_ctx...
Qed.

Corollary presup_wf_exp_eq_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A}, {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_exp_eq_gctx_ctx...
Qed.

#[export]
Hint Resolve presup_wf_exp_eq_gctx_ctx presup_wf_exp_eq_gctx presup_wf_exp_eq_ctx : mcpts.

(** For equality of types *)
Lemma presup_wf_typ_eq_gctx_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ≈ A' }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }}.
Proof with mautosolve 2.
  induction 1; destruct_pairs; split...
Qed.

Corollary presup_wf_typ_eq_gctx {P : PtsSig} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ≈ A' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_typ_eq_gctx_ctx...
Qed.

Corollary presup_wf_typ_eq_ctx {P : PtsSig} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ≈ A' }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_typ_eq_gctx_ctx...
Qed.

#[export]
Hint Resolve presup_wf_exp_eq_gctx_ctx presup_wf_exp_eq_gctx presup_wf_exp_eq_ctx : mcpts.

(** For subtyping of types *)
Lemma presup_wf_typ_subtyp_core {P} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> {{ ▶ Δ }} /\ {{ Δ ▶ Γ }} /\ {{ Δ ▶ Γ ⊢ A' }}.
Proof with mautosolve 2.
  induction 1; destruct_conjs; repeat split; mauto 3.
Qed.

Corollary presup_wf_typ_subtyp_gctx {P} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> {{ ▶ Δ }}.
Proof with easy.
  intros * ?%presup_wf_typ_subtyp_core...
Qed.

Corollary presup_wf_typ_subtyp_ctx {P} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> {{ Δ ▶ Γ }}.
Proof with easy.
  intros * ?%presup_wf_typ_subtyp_core...
Qed.

Corollary presup_wf_typ_subtyp_right {P} : forall {Δ : gctx P} {Γ : ctx P} {A B}, {{ Δ ▶ Γ ⊢ A ⊆ B }} -> {{ Δ ▶ Γ ⊢ B }}.
Proof with easy.
  intros * ?%presup_wf_typ_subtyp_core...
Qed.

#[export]
Hint Resolve presup_wf_typ_subtyp_core presup_wf_typ_subtyp_gctx presup_wf_typ_subtyp_ctx presup_wf_typ_subtyp_right : mcpts.

(** Presupposition for context lookups *)    
Lemma presup_ctx_lookup_typ {P : PtsSig} : forall {Δ : gctx P} {Γ A x},
    {{ Δ ▶ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Δ ▶ Γ ⊢ A }}.
Proof with mautosolve 4.
  intros * HΓ.
  induction 1; inversion_clear HΓ.
  - assert {{ Δ ▶ Γ, A ⊢s Wk : Γ }} by mauto 3.
    eapply wf_typ_sub; mauto 2.
  - assert {{ Δ ▶ Γ, B ⊢s Wk : Γ }} by mauto 3.
    assert {{ Δ ▶ Γ ⊢ A  }} by mauto 2.
    eapply wf_typ_sub; mauto 2.
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mcpts.

Lemma presup_gctx_lookup_typ {P : PtsSig} : forall {Δ : gctx P} {A x},
    {{ ▶ Δ }} ->
    {{ `#x : A ∈ Δ }} ->
    {{ Δ ▶ ⋅ ⊢ A }}.
Proof with mautosolve 4.
  intros * HΔ.
  induction 1; inversion_clear HΔ; mauto 4.
Qed.

#[export]
Hint Resolve presup_gctx_lookup_typ : mcpts.
 
(** ** Immediate Results of Context Presuppositions *)
Lemma wf_gctx_sub_refl {P} : forall (Δ Δ' : gctx P),
    {{ ▶ Δ ≈ Δ' }} ->
    {{ ▶ Δ ⊆ Δ' }}.
Proof. induction 1; mauto. Qed.

#[export]
Hint Resolve wf_gctx_sub_refl : mcpts.

Lemma wf_ctx_sub_refl {P} : forall (Δ : gctx P) Γ Γ',
    {{ Δ ▶ Γ ≈ Γ' }} ->
    {{ Δ ▶ Γ ⊆ Γ' }}.
Proof. induction 1; mauto. Qed.

#[export]
Hint Resolve wf_ctx_sub_refl : mcpts.


(** *** Equality-based conversions *)
(** For well-formedness of expressions *)
Lemma wf_exp_conv_exp_eq {P} : forall (Δ : gctx P) Γ M A s A',
    {{ Δ ▶ Γ ⊢ M : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Δ ▶ Γ ⊢ A : Sort@s }} -> 
    {{ Δ ▶ Γ ⊢ A' : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M : A' }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ ⊢ A }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ A' }} by mauto 2.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_conv_exp_eq : mcpts.
  
Lemma wf_exp_conv_typ_eq {P} : forall (Δ : gctx P) Γ M A A',
    {{ Δ ▶ Γ ⊢ M : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ A' }} ->
    {{ Δ ▶ Γ ⊢ A ≈ A'  }} ->
    {{ Δ ▶ Γ ⊢ M : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_conv_typ_eq : mcpts.

(** For well-formedness of substitutions *)
Lemma wf_sub_conv_eq {P : PtsSig} : forall (Δ : gctx P) σ Γ Γ' Γ'',
  {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
  {{ Δ ▶ Γ' ≈ Γ'' }} ->
  {{ Δ ▶ Γ ⊢s σ : Γ'' }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ'' }} by mauto 2.
  eapply wf_sub_conv; mauto.
Qed.

#[export]
Hint Resolve wf_sub_conv_eq : mcpts.

Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : (wf_sub Δ Γ)
    with signature wf_ctx_eq Δ ==> eq ==> iff as wf_sub_morphism_iff1.
Proof.
  intros Γ' Γ'' H **; split; [| symmetry in H]; mauto.
Qed.

(** For equality of expressions *)
Lemma wf_exp_eq_conv_exp_eq {P} : forall (Δ : gctx P) Γ M M' A A' s,
    {{ Δ ▶ Γ ⊢ M ≈ M' : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Δ ▶ Γ ⊢ A : Sort@s }} -> 
    {{ Δ ▶ Γ ⊢ A' : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed. 

#[export]
Hint Resolve wf_exp_eq_conv_exp_eq : mcpts.

Lemma wf_exp_eq_conv_typ_eq {P} : forall (Δ : gctx P) Γ M M' A A',
    {{ Δ ▶ Γ ⊢ M ≈ M' : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Δ ▶ Γ ⊢ A }} -> 
    {{ Δ ▶ Γ ⊢ A' }} ->
    {{ Δ ▶ Γ ⊢ A ≈ A' }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_conv_typ_eq : mcpts.

(** For equality of substitutions *)
Lemma wf_sub_eq_conv_eq {P : PtsSig} : forall (Δ : gctx P) σ σ' Γ Γ' Γ'',
    {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Δ ▶ Γ' ≈ Γ'' }} ->
    {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ'' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_eq_conv_eq : mcpts.

Add Parametric Morphism {P : PtsSig} (Δ : gctx P) (Γ : ctx P) : (wf_sub_eq Δ Γ)
    with signature wf_ctx_eq Δ ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  intros Γ' Γ'' H **; split; [| symmetry in H]; mauto.
Qed.

(** Other admissible rules following context presupposition *)
Lemma wf_typ_eq_sub_id {P : PtsSig} : forall {Δ : gctx P} {Γ A},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ A[Id] ≈ A }}.
Proof.
  induction 1; mauto 3.
  transitivity {{{ A[σ∘Id] }}}; mauto 4.
  symmetry.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_id : mcpts.


(** ** Lemmas for [exp] of [{{{ Sort@s }}}] *)
Lemma wf_typ_subtyp_sort_sub_left {P} : forall {Δ : gctx P} { Γ Γ' σ s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ Sort@s[σ] ⊆ Sort@s }}.
Proof.
  intros.
  econstructor; mauto 3.
Qed.

Lemma wf_typ_subtyp_sort_sub_right {P} : forall {Δ : gctx P} {Γ Γ' σ s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ Sort@s ⊆ Sort@s[σ] }}.
Proof.
  intros.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sort_sub_left wf_typ_subtyp_sort_sub_right : mcpts.
 
Lemma wf_exp_sub_sorted {P} : forall {Δ : gctx P} {Γ Γ' A σ s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ A[σ] : Sort@s }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ ⊢ A[σ] : Sort@s[σ] }} by mauto 4.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ Sort@s[σ] ⊆ Sort@s }} by mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_sorted : mcpts.

Lemma wf_exp_eq_sub_cong_sorted1 {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A A' σ s},
    {{ Δ ▶ Γ' ⊢ A ≈ A' : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ ⊢ Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢s σ ≈ σ : Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s[σ] }} by mauto 4.
  econstructor; mauto 3.
Qed.
             
Lemma wf_exp_eq_sub_cong_sorted2 {P} : forall {Δ : gctx P} {Γ Γ' A σ τ s},
    {{ Δ ▶ Γ' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ ⊢ Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ' ⊢ A ≈ A : Sort@s }} by mauto 3.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_cong_sorted1 wf_exp_eq_sub_cong_sorted2 : mcpts.
 
  
Lemma wf_exp_eq_sub_compose_sorted1 {P} : forall {Δ : gctx P} {Γ Γ' Γ'' A A' σ τ s},
    {{ Δ ▶ Γ'' ⊢ A' : Sort@s }} ->
    {{ Δ ▶ Γ'' ⊢ A ≈ A' : Sort@s }} ->
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ A[σ∘τ] ≈ A'[σ][τ] : Sort@s }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ ⊢ Sort@s[σ∘τ] ≈ Sort@s }} by mauto.
  assert {{ Δ ▶ Γ ⊢ Sort@s[σ∘τ] ⊆ Sort@s }} by mauto.
  assert {{ Δ ▶ Γ ⊢ A'[σ∘τ] ≈ A'[σ][τ] : Sort@s[σ∘τ] }} by mauto 4.
  transitivity {{{ A'[σ∘τ] }}}; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_sorted1 : mcpts.

Lemma wf_exp_eq_sub_compose_sorted2 {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' A σ τ s},
    {{ Δ ▶ Γ'' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_sorted2 : mcpts.

Lemma wf_exp_eq_sub_compose_weaken_extend_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' s σ A B M},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ' ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B[σ] }} ->
    {{ Δ ▶ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ', B ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢s Wk∘(σ,,M) ≈ σ : Γ' }} by mauto 3.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_weaken_extend_sorted : mcpts.


Lemma exp_eq_sub_compose_weaken_id_extend_typ {P : PtsSig} : forall {Δ : gctx P} {Γ s A B M},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B }} ->
    {{ Δ ▶ Γ ⊢ A[Wk][Id,,M] ≈ A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_double_extend_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' s σ A B M C N},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ' ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B[σ] }} ->
    {{ Δ ▶ Γ', B ⊢ C }} ->
    {{ Δ ▶ Γ ⊢ N : C[σ,,M] }} ->
    {{ Δ ▶ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  assert {{ Δ ▶ Γ', B ⊢ Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ', B ⊢ A[Wk] : Sort@s }} by mauto 3.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply wf_exp_eq_sub_cong_sorted1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_double_extend_sorted : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_id_double_extend_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ s A B M C N},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B }} ->
    {{ Δ ▶ Γ, B ⊢ C }} ->
    {{ Δ ▶ Γ ⊢ N : C[Id,,M] }} ->
    {{ Δ ▶ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ B ≈ B[Id]  }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M : B[Id] }} by mauto 3.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_id_double_extend_sorted : mcpts.

Lemma wf_exp_eq_sort_sub_sub {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' σ τ s1 s2},
    {{ Δ ▶ Γ'' ⊢ Sort@s1 : Sort@s2 }} ->
    {{ Δ ▶ Γ ⊢ Sort@s1 : Sort@s2 }} ->
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ Sort@s1[σ][τ] ≈ Sort@s1 : Sort@s2 }}.
Proof.
  intros.
  transitivity {{{ Sort@s1[σ∘τ] }}}; [symmetry |]; mauto 3.  
Qed.

#[export]
Hint Resolve wf_exp_eq_sort_sub_sub : mcpts.
#[export]
Hint Rewrite -> @wf_exp_eq_sort_sub_sub using mauto 4 : mcpts.

Lemma vlookup_0_typ {P : PtsSig} : forall {Δ : gctx P} {Γ s},
    {{ Δ ▶ Γ }} ->
    {{ Δ ▶ Γ, Sort@s ⊢ #0 : Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  eapply wf_exp_conv_typ_eq with (A := {{{ Sort@s[Wk] }}}); mauto 3. 
Qed.

Lemma vlookup_1_typ {P : PtsSig} : forall {Δ : gctx P} {Γ s A},
    {{ Δ ▶ Γ, Sort@s ⊢ A }} ->
    {{ Δ ▶ Γ, Sort@s, A ⊢ #1 : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ▶ Γ, Sort@s, A ⊢s Wk : Γ, Sort@s }} by (econstructor; mauto 4).
  assert {{ Δ ▶ Γ, Sort@s, A }} by mauto 3.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ, Sort@s ⊢ Sort@s[Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ, Sort@s, A ⊢ Sort@s[Wk][Wk] }} by mauto 3.
  eapply wf_exp_conv with (A := {{{ Sort@s[Wk][Wk] }}}); mauto 3.
  econstructor; mauto 3.
  transitivity {{{ Sort@s[Wk] }}}; mauto 4.
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mcpts.

Lemma wf_exp_sub_typ_helper {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ M s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M : Sort@s[σ] }}.
Proof.
  intros.
  do 3 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve wf_exp_sub_typ_helper : mcpts.

Lemma wf_exp_eq_var_0_sub_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ M s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ #0[σ,,M] ≈ M : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ Sort@s[σ] ⊆ Sort@s  }} by mauto 5.
  eapply wf_exp_eq_conv; mauto 4.
Qed.

Lemma wf_exp_eq_var_1_sub_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A M s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ M : A[σ] }} ->
    {{ #0 : Sort@s[Wk] ∈ Γ' }} ->
    {{ Δ ▶ Γ ⊢ #1[σ,,M] ≈ #0[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  inversion H2; subst.
  assert {{ Δ ▶ Γ0 }} by mauto 3.
  assert {{ Δ ▶ Γ0, Sort@s ⊢s Wk : Γ0 }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 3.
  transitivity {{{ Sort@s[σ] }}}; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_sub_typ wf_exp_eq_var_1_sub_typ : mcpts.
#[export]
Hint Rewrite -> @wf_exp_eq_var_0_sub_typ @wf_exp_eq_var_1_sub_typ : mcpts.

Lemma wf_exp_eq_var_0_weaken_typ {P : PtsSig} : forall {Δ : gctx P} {Γ A s},
    {{ Δ ▶ Γ, A }} ->
    {{ #0 : Sort@s[Wk] ∈ Γ }} ->
    {{ Δ ▶ Γ, A ⊢ #0[Wk] ≈ #1 : Sort@s }}.
Proof with mautosolve 3.
  inversion_clear 1.
  inversion 1 as [? Γ'|]; subst.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ', Sort@s ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ', Sort@s, A ⊢s Wk : Γ', Sort@s }} by mauto 4.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 3.
  transitivity {{{ Sort@s[Wk] }}}; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_weaken_typ : mcpts.


(** Substitution cases *)
Lemma wf_sub_extend_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ M s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s σ,,M : Γ', Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_extend_typ : mcpts.

Lemma wf_sub_eq_extend_cong_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ σ' M M' s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s σ,,M ≈ σ',,M' : Γ', Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  econstructor; mauto 2.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

Lemma wf_sub_eq_extend_compose_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' τ σ A s M},
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ'' ⊢ A }} ->
    {{ Δ ▶ Γ' ⊢ M : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

Lemma wf_sub_eq_p_extend_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ M s},
    {{ Δ ▶ Γ' ⊢s σ : Γ }} ->
    {{ Δ ▶ Γ' ⊢ M : Sort@s }} ->
    {{ Δ ▶ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_extend_cong_typ wf_sub_eq_extend_compose_typ wf_sub_eq_p_extend_typ : mcpts.

Lemma wf_exp_eq_sub_sub_compose_cong_typ {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'1 Γ'2 Γ'' σ τ σ' τ' A s},
    {{ Δ ▶ Γ'' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ'1 }} ->
    {{ Δ ▶ Γ ⊢s τ' : Γ'2 }} ->
    {{ Δ ▶ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Sort@s }} by mauto 3.
  enough {{ Δ ▶ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] : Sort@s }}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_sub_compose_cong_typ : mcpts.




(** This removes the extra premise {{ Γ ⊢ A : Sort@s }} in wf_vlookup, which we use in soundness *)
(* Corollary wf_vlookup' {P} : forall {Γ : ctx P} {x A}, *)
(*     {{ ⊢ Γ }} -> *)
(*     {{ #x : A ∈ Γ }} -> *)
(*     {{ Γ ⊢ #x : A }}. *)
(* Proof. *)
(*   intros. *)
(*   assert {{ Γ ⊢ A }} by mauto 2. *)
(*   econstructor; mauto 2. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve wf_vlookup' : mcpts. *)
(* #[export] *)
(* Remove Hints wf_vlookup : mcpts. *)



(** ** Lemmas for [exp] of [{{{ ℕ }}}] *)
Lemma wf_typ_subtyp_nat_sub_left {P} : forall {Δ : gctx P} {Γ Γ' σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ ℕ[σ] ⊆ ℕ }}.
Proof.
  intros.
  econstructor; mauto 4.
Qed. 

Lemma wf_typ_subtyp_nat_sub_right {P} : forall {Δ : gctx P} {Γ Γ' σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ ℕ ⊆ ℕ[σ] }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ[σ] }} by mauto 3.
  enough {{ Δ ▶ Γ ⊢ ℕ ≈ ℕ[σ] }} by mauto 2.
  symmetry; mauto 3.
Qed. 

#[export]
Hint Resolve wf_typ_subtyp_nat_sub_left wf_typ_subtyp_nat_sub_right : mcpts.


Lemma wf_exp_sub_nat {P} : forall {Δ : gctx P} {Γ Γ' M σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M[σ] : ℕ[σ] }} by mauto 3.  
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_sub_nat : mcpts.

Lemma wf_exp_eq_sub_cong_nat1 {P} : forall {Δ : gctx P} {Γ Γ' M M' σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ' ⊢ M ≈ M' : ℕ }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M[σ] ≈ M'[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ }} by mauto 3.
  econstructor; mauto 3.
Qed.

Lemma wf_exp_eq_sub_cong_nat2 {P} : forall {Δ : gctx P} {Γ Γ' M σ τ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M[σ] ≈ M[τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ }} by mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_cong_nat1 wf_exp_eq_sub_cong_nat2 : mcpts.
  
Lemma wf_exp_eq_sub_compose_nat {P} : forall {Δ : gctx P} {Γ Γ' Γ'' M σ τ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ'' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ'}} ->
    {{ Δ ▶ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ'' }} by mauto 2.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ'' ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : ℕ[σ∘τ] }} by mauto 3.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_nat : mcpts.

Lemma wf_exp_eq_nat_sub_sub {P} : forall {Δ : gctx P} {Γ Γ' Γ'' σ τ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ ℕ[σ][τ] ≈ ℕ : Sort@s }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub_sub : mcpts.

Lemma wf_exp_eq_nat_sub_sub_to_nat_sub {P} : forall {Δ : gctx P} {Γ Γ' Γ''1 Γ''2 σ τ σ' s} {r : Ru_nat P s},
    {{ Δ ▶ Γ' ⊢s σ : Γ''1 }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ' : Γ''2 }} ->
    {{ Δ ▶ Γ ⊢ ℕ[σ][τ] ≈ ℕ[σ'] : Sort@s}}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub_sub_to_nat_sub : mcpts.

Lemma wf_exp_eq_sub_compose_weaken_extend_nat {P} : forall {Δ : gctx P} {Γ Γ' σ M B N s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ' ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ N : B[σ] }} ->
    {{ Δ ▶ Γ ⊢ M[Wk][σ,,N] ≈ M[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢s σ,,N : Γ', B }} by mauto 2.
  transitivity {{{ M[Wk∘(σ,,N)] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_weaken_extend_nat : mcpts.

Lemma wf_exp_eq_sub_compose_weaken_id_extend_nat {P} : forall {Δ : gctx P} {Γ M B N s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ N : B }} ->
    {{ Δ ▶ Γ ⊢ M[Wk][Id,,N] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ N : B[Id] }} by mauto 4.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_weaken_id_extend_nat : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_double_extend_nat {P} : forall {Δ : gctx P} {Γ Γ' σ M B N C L s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ' ⊢ B  }} ->
    {{ Δ ▶ Γ ⊢ N : B[σ] }} ->
    {{ Δ ▶ Γ', B ⊢ C }} ->
    {{ Δ ▶ Γ ⊢ L : C[σ,,N] }} ->
    {{ Δ ▶Γ ⊢ M[Wk∘Wk][σ,,N,,L] ≈ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢s σ,,N : Γ', B }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢s σ,,N,,L : Γ', B, C }} by mauto 2.
  transitivity {{{ M[Wk][Wk][σ,,N,,L] }}}; [econstructor; mautosolve 3|].
  transitivity {{{ M[Wk][σ,,N] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_double_extend_nat : mcpts.

Lemma wf_exp_eq_sub_compose_double_weaken_id_double_extend_nat {P} : forall {Δ : gctx P} {Γ M B N C L s } {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ N : B }} ->
    {{ Δ ▶ Γ, B ⊢ C }} ->
    {{ Δ ▶ Γ ⊢ L : C[Id,,N] }} ->
    {{ Δ ▶ Γ ⊢ M[Wk∘Wk][Id,,N,,L] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ N : B[Id] }} by mauto 4.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_compose_double_weaken_id_double_extend_nat : mcpts.

Lemma vlookup_0_nat {P} : forall {Δ : gctx P} {Γ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ }} ->
    {{ Δ ▶ Γ, ℕ ⊢ #0 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  eapply wf_exp_conv...
Qed.

Lemma vlookup_1_nat {P} : forall {Δ : gctx P} {Γ A s} {r : Ru_nat P s},
    {{ Δ ▶ Γ, ℕ ⊢ A }} ->
    {{ Δ ▶ Γ, ℕ, A ⊢ #1 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ : Sort@s }} by mauto 2.
  assert {{ Δ ▶ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 5.
  assert {{ Δ ▶ Γ, ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  eapply wf_exp_conv_exp_eq; mauto 3.
Qed.

#[export]
Hint Resolve vlookup_0_nat vlookup_1_nat : mcpts.

Lemma wf_exp_sub_nat_helper {P} : forall {Δ : gctx P} {Γ Γ' σ M s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢ M : ℕ[σ] }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mauto 2.
  mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_nat_helper : mcpts.

Lemma wf_exp_eq_var_0_sub_nat {P} : forall {Δ : gctx P} {Γ Γ' σ M s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢ #0[σ,,M] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma wf_exp_eq_var_1_sub_nat {P} : forall {Δ : gctx P} {Γ Γ' σ A M s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ M : A[σ] }} ->
    {{ #0 : ℕ[Wk] ∈ Γ' }} ->
    {{ Δ ▶ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ }}.
Proof with mautosolve 4.
  inversion 5 as [? Γ''|]; subst.
  assert {{ Δ ▶ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ[Wk][σ] }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_sub_nat wf_exp_eq_var_1_sub_nat : mcpts.

Lemma wf_exp_eq_var_0_weaken_nat {P} : forall {Δ : gctx P} {Γ A s} {r : Ru_nat P s},
    {{ Δ ▶ Γ, A }} ->
    {{ #0 : ℕ[Wk] ∈ Γ }} ->
    {{ Δ ▶ Γ, A ⊢ #0[Wk] ≈ #1 : ℕ }}.
Proof with mautosolve 4.
  inversion 2; subst.
  inversion 1; subst.
  assert {{ Δ ▶ Γ0, ℕ, A ⊢ #0[Wk] ≈ #1 : ℕ[Wk][Wk] }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_0_weaken_nat : mcpts.

(** *** Substitution cases *)
Lemma wf_sub_extend_nat {P} : forall {Δ : gctx P} {Γ Γ' σ M s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢s σ,,M : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_extend_nat : mcpts.

Lemma wf_sub_eq_extend_cong_nat {P} : forall {Δ : gctx P} {Γ Γ' σ σ' M M' s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Δ ▶ Γ ⊢s σ,,M ≈ σ',,M' : Γ', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 4.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ ℕ ≈ ℕ[σ] : Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ' ⊢ ℕ : Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ[σ] : Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mauto 2.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

Lemma wf_sub_eq_extend_compose_nat {P} : forall {Δ : gctx P} {Γ Γ' Γ'' τ σ M s} {r : Ru_nat P s},
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

Lemma wf_sub_eq_p_extend_nat {P} : forall {Δ : gctx P} {Γ Γ' σ M s} {r : Ru_nat P s},
    {{ Δ ▶ Γ' ⊢s σ : Γ }} ->
    {{ Δ ▶ Γ' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve.
  intros.
  assert {{ Δ ▶ Γ ⊢ ℕ : Sort@s }} by mauto 3.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_extend_cong_nat wf_sub_eq_extend_compose_nat wf_sub_eq_p_extend_nat : mcpts.

Lemma wf_exp_eq_sub_sub_compose_cong_nat {P} : forall {Δ : gctx P} {Γ Γ'1 Γ'2 Γ'' σ τ σ' τ' M s} {r : Ru_nat P s},
    {{ Δ ▶ Γ'' ⊢ M : ℕ }} ->
    {{ Δ ▶ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ'1 }} ->
    {{ Δ ▶ Γ ⊢s τ' : Γ'2 }} ->
    {{ Δ ▶ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }} by mauto.
  assert {{ Δ ▶ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : ℕ }} by mauto.
  enough {{ Δ ▶ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : ℕ }}...
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_sub_compose_cong_nat : mcpts.

Lemma wf_typ_eq_sub_compose_cong {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'1 Γ'2 Γ'' σ τ σ' τ' A},
    {{ Δ ▶ Γ'' ⊢ A }} ->
    {{ Δ ▶ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ'1 }} ->
    {{ Δ ▶ Γ ⊢s τ' : Γ'2 }} ->
    {{ Δ ▶ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto 3.
  enough {{ Δ ▶ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] }}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_cong : mcpts.


(** ** Lemmas for [typ] *)
Lemma wf_typ_eq_refl_sort {P : PtsSig} : forall {Δ : gctx P} {Γ s},
    {{ Δ ▶ Γ }} ->
    {{ Δ ▶ Γ ⊢ Sort@s ≈ Sort@s }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_refl_sort : mcpts.

Lemma wf_typ_eq_sub_cong1 {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A A' σ},
    {{ Δ ▶ Γ' ⊢ A ≈ A' }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ A[σ] ≈ A'[σ] }}.
Proof. mauto. Qed.

Lemma wf_typ_eq_sub_cong2  {P} : forall {Δ : gctx P} {Γ Γ' A σ τ},
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢s σ ≈ τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_sub_cong1 wf_typ_eq_sub_cong2 : mcpts.
  
Lemma wf_typ_eq_sub_compose_typ  {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' A σ τ},
    {{ Δ ▶ Γ'' ⊢ A }} ->
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_typ : mcpts.

Lemma wf_typ_eq_sub_compose_weaken_extend {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A B M},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ' ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B[σ] }} ->
    {{ Δ ▶ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] }}.
Proof with mautosolve 3.
  intros.  
  assert {{ Δ ▶ Γ', B ⊢s Wk : Γ' }} by mauto 4.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; [mautosolve 4 |].
  eapply wf_typ_eq_sub_cong2...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_weaken_extend : mcpts.

Lemma wf_typ_eq_sub_compose_weaken_id_extend {P : PtsSig} : forall {Δ : gctx P} {Γ A B M},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B }} ->
    {{ Δ ▶ Γ ⊢ A[Wk][Id,,M] ≈ A }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_weaken_id_extend : mcpts.

Lemma wf_typ_eq_sub_compose_double_weaken_double_extend {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ A B M C N},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ' ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B[σ] }} ->
    {{ Δ ▶ Γ', B ⊢ C }} ->
    {{ Δ ▶ Γ ⊢ N : C[σ,,M] }} ->
    {{ Δ ▶ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ', B ⊢s Wk : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ', B, C ⊢s Wk : Γ', B }} by mauto 4.
  assert {{ Δ ▶ Γ', B ⊢ A[Wk] }} by mauto 3.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply wf_typ_eq_sub_cong1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_double_weaken_double_extend : mcpts.

Lemma wf_typ_eq_sub_compose_double_weaken_id_double_extend {P : PtsSig} : forall {Δ : gctx P} {Γ A B M C N},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M : B }} ->
    {{ Δ ▶ Γ, B ⊢ C }} ->
    {{ Δ ▶ Γ ⊢ N : C[Id,,M] }} ->
    {{ Δ ▶ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M : B[Id] }} by mauto 3.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_compose_double_weaken_id_double_extend : mcpts.

Lemma wf_typ_eq_sort_sub_sub {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' σ τ s1},
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ Sort@s1[σ][τ] ≈ Sort@s1 }}.
Proof.
  intros.
  transitivity {{{ Sort@s1[σ∘τ] }}}; mauto.
Qed.

#[export]
Hint Resolve wf_typ_eq_sort_sub_sub : mcpts.
#[export]
Hint Rewrite -> @wf_typ_eq_sort_sub_sub using mauto 4 : mcpts.

(** *** Lemmas for [wf_subtyp] *)

(* Fact wf_typ_subtyp_refl_sorted {P} : forall {Δ : gctx P} {Γ A s}, *)
(*     {{ Δ ; Γ ⊢ A : Sort@s }} -> *)
(*     {{ Δ ; Γ ⊢ A ⊆ A }}. *)
(* Proof. mauto. Qed. *)

(* #[export] *)
(* Hint Resolve wf_typ_subtyp_refl_sorted : mcpts. *)

(* Lemma wf_typ_subtyp_sub {P} : forall {Δ : gctx P} {Γ' A A'}, *)
(*     {{ Δ ; Γ' ⊢ A ⊆ A' }} -> *)
(*     forall Γ σ, *)
(*       {{ Δ ; Γ ⊢s σ : Γ' }} -> *)
(*       {{ Δ ; Γ ⊢ A[σ] ⊆ A'[σ] }}. *)
(* Proof. *)
(*   induction 1; intros; mauto 4. *)
(*   (* - assert {{ Δ ; Γ0 ⊢ A[σ] ≈ B[σ] }} by mauto 3. *) *)
(*   (*   assert {{ Γ0 ⊢ B[σ] }} by mauto 3. *) *)
(*   (*   mauto 3. *) *)
(*   - assert {{ Δ ⊢ Γ0 }} by mauto 2. *)
(*     assert {{ Δ ; Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto. *)
(*     assert {{ Δ ; Γ ⊢ Sort@s1 }} by mauto. *)
(*     assert {{ Δ ; Γ0 ⊢ Sort@s1[σ] ≈ Sort@s1 }} by mauto. *)
(*     assert {{ Δ ; Γ0 ⊢ Sort@s2 ≈ Sort@s2[σ] }} by (symmetry; mauto). *)
(*     transitivity {{{ Sort@s1 }}}; mauto 3. *)
(*     transitivity {{{ Sort@s2 }}}; mauto 3. *)
(*     mauto 4. *)
(*   - assert {{ Δ ; Γ0 ⊢ A[σ] : Sort@s1 }} by mauto 3. *)
(*     assert {{ Δ ; Γ0, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 4. *)
(*     assert {{ Δ ; Γ0 ⊢ Π r A[σ] B[q σ] }} by mauto. *)
(*     transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; [econstructor; mauto 3|]. *)
(*     transitivity {{{ Π r (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4]. *)
(*     eapply wf_subtyp_pi; mauto 4. *)
(* Qed. *)


(* #[export] *)
(* Hint Resolve wf_subtyp_sub : mcpts. *)


(* Lemma wf_subtyp_sort_weaken {P} : forall {Γ : ctx P} {s1 s2 A}, *)
(*     {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} -> *)
(*     {{ ⊢ Γ, A }} -> *)
(*     {{ Γ, A ⊢ Sort@s1 ⊆ Sort@s2 }}. *)
(* Proof.     *)
(*   intros. *)
(*   assert {{ Γ ⊢ Sort@s2  }} by mauto 2. *)
(*   assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2. *)
(*   dependent induction H; mauto 2. *)
(*   - assert {{ Γ, A ⊢ Sort@s1[Wk] ≈ Sort@s2[Wk] }} by mauto. *)
(*     assert {{ Γ, A ⊢ Sort@s1[Wk] ≈ Sort@s1  }} by mauto. *)
(*     assert {{ Γ, A ⊢ Sort@s2[Wk] ≈ Sort@s2  }} by mauto. *)
(*     assert {{ Γ, A ⊢ Sort@s1 ≈ Sort@s2  }} by mauto. *)
(*     mauto 3. *)
(*   - assert {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto 3. *)
(*     assert {{ Γ, A ⊢ Sort@s1[Wk] ⊆ Sort@s2[Wk] }} by mauto 2. *)
(*     assert {{ Γ, A ⊢ Sort@s1[Wk] }} by mauto 4. *)
(*     assert {{ Γ, A ⊢ Sort@s1 ⊆ Sort@s1[Wk] }} by mauto 4. *)
(*     transitivity {{{ Sort@s1[Wk] }}}; mauto. *)
(* Qed. *)

(* Lemma ctx_sub_ctx_lookup {P} : forall {Γ Δ : ctx P}, *)
(*     {{ ⊢ Δ ⊆ Γ }} -> *)
(*     forall {A x}, *)
(*       {{ #x : A ∈ Γ }} -> *)
(*       exists B, *)
(*         {{ #x : B ∈ Δ }} /\ *)
(*           {{ Δ ⊢ B ⊆ A }}. *)
(* Proof with (do 2 eexists; repeat split; mautosolve). *)
(*   induction 1; intros * Hx; progressive_inversion. *)
(*   dependent destruction Hx. *)
(*   - eexists; split; mauto 3. *)
(*     eapply wf_subtyp_sub; mauto 4. *)
(*   - edestruct IHwf_ctx_sub as [? []]; try eassumption... *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve ctx_sub_ctx_lookup : mcpts. *)


(** ** Lemmas about context lookups *)
Lemma wf_gctx_eq_gctx_lookup {P : PtsSig} : forall {Δ : gctx P} {Δ' A x},
    {{ ▶ Δ ≈ Δ' }} ->
    {{ `#x : A ∈ Δ }} ->
    exists B,
      {{ `#x : B ∈ Δ' }} /\
        {{ Δ ▶ ⋅ ⊢ A ≈ B }} /\
        {{ Δ' ▶ ⋅ ⊢ A ≈ B }} /\
        {{ Δ' ▶ ⋅ ⊢ A }}.
Proof.
  intros * HΔΔ' Hx.
  assert {{ ▶ Δ }} by mauto 2.
  assert {{ Δ ▶ ⋅ ⊢ A }} by mauto 2.
  gen Δ' Hx.
  induction 1 as [|* ? IHHx]; inversion_clear 1 as [| ? ? ? ? ? HΔΔ'0];
    assert {{ ▶ Δ'0 }} by mauto 2.
  - eexists; repeat split; mauto 3.
  - specialize (IHHx ltac:(mauto 2) ltac:(mauto 3) _ HΔΔ'0).
    destruct_conjs.
    eexists; repeat split; mauto 3.
Qed.    

#[export]
Hint Resolve wf_gctx_eq_gctx_lookup : mcpts.
 
Lemma wf_ctx_eq_ctx_lookup {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A x},
    {{ Δ ▶ Γ ≈ Γ' }} ->
    {{ #x : A ∈ Γ }} ->
    exists B,
      {{ #x : B ∈ Γ' }} /\
        {{ Δ ▶ Γ ⊢ A ≈ B }} /\
        {{ Δ ▶ Γ' ⊢ A ≈ B }} /\
        {{ Δ ▶ Γ' ⊢ A }}.
Proof with (repeat eexists; mautosolve 3).
  intros * HΓΓ' Hx.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ A }} by mauto 3.
  gen Γ' Hx.
  induction 1 as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? ? HΓΓ'0];
    assert {{ Δ ▶ Γ'0 }} by mauto 2.
  - assert {{ Δ ▶ Γ, A }} by mauto 3.
    assert {{ Δ ▶ Γ, A ⊢s Wk : Γ }} by mauto 2.
    assert {{ Δ ▶ Γ'0, A' ⊢s Wk : Γ'0 }} by mauto 3.
    eexists.
    do 3 (split; mauto 3).
  - specialize (IHHx ltac:(mauto 2) ltac:(mauto 3) _ HΓΓ'0).
    destruct_conjs.
    assert {{ Δ ▶ Γ, B ⊢s Wk : Γ }} by mauto 2.
    assert {{ Δ ▶ Γ'0, A' ⊢s Wk : Γ'0 }} by mauto 3.
    eexists.
    do 3 (split; mauto 3).
Qed.

#[export]
Hint Resolve wf_ctx_eq_ctx_lookup : mcpts.


(** ** Other Tedious Lemmas *)
Lemma wf_sub_eq_weaken_var0_id {P : PtsSig} : forall {Δ : gctx P} {Γ A},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof with mautosolve 4.
  intros * ?.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ A }} by mauto 2.
  assert {{ Δ ▶ Γ, A }} by mauto 3.
  assert {{ Δ ▶ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Δ ▶ Γ, A ⊢s (Wk∘Id),,#0[Id] ≈ Id : Γ, A }} by mauto.
  assert {{ Δ ▶ Γ, A ⊢s Wk ≈ Wk∘Id : Γ }} by mauto.
  assert {{ Δ ▶ Γ, A ⊢s Wk,,#0 ≈ Wk∘Id,,#0[Id] : Γ, A }} by (eapply wf_sub_eq_extend_cong; mauto 4).
  enough {{ Δ ▶ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }} by (etransitivity; mauto 3).
  symmetry; econstructor; econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_sub_eq_weaken_var0_id : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_weaken_var0_id using mauto 4 : mcpts.

Lemma wf_exp_eq_sub_sub_compose_cong {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'1 Γ'2 Γ'' σ τ σ' τ' M A},
    {{ Δ ▶ Γ'' ⊢ A }} ->
    {{ Δ ▶ Γ'' ⊢ M : A }} ->
    {{ Δ ▶ Γ'1 ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ'2 ⊢s σ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ'1 }} ->
    {{ Δ ▶ Γ ⊢s τ' : Γ'2 }} ->
    {{ Δ ▶ Γ ⊢s σ∘τ ≈ σ'∘τ' : Γ'' }} ->
    {{ Δ ▶ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto.
  assert {{ Δ ▶ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Δ ▶ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_sub_compose_cong : mcpts.

Lemma wf_exp_sub_id_on_typ {P : PtsSig} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢ M : A[Id] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_sub_id_on_typ : mcpts.

Lemma wf_exp_sub_id_on_typ_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ M A s},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢ M : A[Id] }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_exp_sub_id_on_typ_sorted : mcpts.

Lemma wf_sub_id_extend {P : PtsSig} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s Id,,M : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_id_extend : mcpts.

Lemma wf_sub_id_extend_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ M A s},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s Id,,M : Γ, A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_id_extend_sorted : mcpts.

Lemma wf_exp_eq_sub_id_on_typ {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 3.
  eapply wf_exp_eq_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_exp_eq_sub_id_on_typ : mcpts.

Lemma wf_exp_eq_sub_id_on_typ_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A s},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A[Id] }}.
Proof. mauto 3. Qed.
  
#[export]
Hint Resolve wf_exp_eq_sub_id_on_typ_sorted : mcpts.

Lemma wf_sub_eq_p_id_extend {P : PtsSig} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_p_id_extend : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_p_id_extend using mauto 4 : mcpts.


Lemma wf_sub_eq_p_id_extend_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ M A s},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_p_id_extend_sorted : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_p_id_extend_sorted using mauto 4 : mcpts.


Lemma wf_sub_eq_id_extend_cong {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ▶ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_cong : mcpts.


Lemma wf_sub_eq_id_extend_cong_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ M M' A s},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ▶ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_cong_sorted : mcpts.


Lemma wf_sub_q {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A σ},
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, A[σ] ⊢s q σ : Γ', A }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Δ ▶ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Δ ▶ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  econstructor; mauto 2.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

Lemma wf_sub_q_sort {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, Sort@s ⊢s q σ : Γ', Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ▶ Γ, Sort@s ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ, Sort@s ⊢ Sort@s[Wk] ≈ Sort@s }} by mauto 4.
  assert {{ Δ ▶ Γ, Sort@s ⊢ #0 : Sort@s }} by mauto 3.
  econstructor...
Qed.

Lemma wf_sub_q_nat {P} : forall {Δ : gctx P} {Γ Γ' σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ ⊢s q σ : Γ', ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 2.
  assert {{ Δ ▶ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve wf_sub_q wf_sub_q_sort wf_sub_q_nat : mcpts.

Lemma wf_exp_eq_var_1_sub_q_q_sigma_nat {P} : forall {Δ : gctx P} {Γ Γ' A σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ', ℕ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ, ℕ ⊢s q σ : Γ', ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] }} by (econstructor; mauto 2).
  assert {{ Δ ▶ Γ', ℕ ⊢ #0 : ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Γ', ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk]  }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ∘Wk] }} by (eapply wf_exp_conv_typ_eq; mauto 4).
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Γ', ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : ℕ }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ ⊢ #0 : ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢ #0 : ℕ[σ∘Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢ #0[q σ] ≈ #0 : ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : ℕ }} by mauto 3.
  etransitivity; [eassumption |].
  etransitivity...
Qed.

#[export]
Hint Resolve wf_exp_eq_var_1_sub_q_q_sigma_nat : mcpts.

Lemma wf_exp_eq_var_1_sub_q_q_sigma_nat_sorted {P} : forall {Δ : gctx P} {Γ Γ' A σ s s'} {r : Ru_nat P s},
    {{ Δ ▶ Γ', ℕ ⊢ A : Sort@s' }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_exp_eq_var_1_sub_q_q_sigma_nat_sorted : mcpts.

Lemma wf_sub_id_extend_zero {P} : forall {Δ : gctx P} {Γ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ }} ->
    {{ Δ ▶ Γ ⊢s Id,,zero : Γ, ℕ }}.
Proof. mauto 4. Qed.

#[export]
Hint Resolve wf_sub_id_extend_zero : mcpts.
  
Lemma wf_sub_weak_compose_weak_extend_succ_var1 {P} : forall {Δ : gctx P} {Γ A s} {r : Ru_nat P s},
    {{ Δ ▶ Γ, ℕ ⊢ A }} ->
    {{ Δ ▶ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ, ℕ, A ⊢s Wk : Γ, ℕ  }} by mauto 4.
  enough {{ Δ ▶ Γ, ℕ, A ⊢s Wk∘Wk : Γ }}...
Qed.

#[export]
Hint Resolve wf_sub_weak_compose_weak_extend_succ_var1 : mcpts.

Lemma wf_sub_weak_compose_weak_extend_succ_var1_sorted {P} : forall {Δ : gctx P} {Γ A s s'} {r : Ru_nat P s},
    {{ Δ ▶ Γ, ℕ ⊢ A : Sort@s' }} ->
    {{ Δ ▶ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_weak_compose_weak_extend_succ_var1_sorted : mcpts.

Lemma wf_sub_eq_id_extend_compose {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' M A σ},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ' ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ' ⊢s Id : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ' ⊢ M : A[Id] }} by mauto.
  assert {{ Δ ▶ Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Γ', A }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M[σ] : A[Id][σ] }} by mauto.
  assert {{ Δ ▶ Γ ⊢ A[Id][σ] ≈ A[Id∘σ] }} by (symmetry; mauto 3).
  assert {{ Δ ▶ Γ ⊢ A[Id∘σ] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ A[Id][σ] ⊆ A[Id∘σ] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ M[σ] : A[Id∘σ] }} by (eapply wf_exp_conv_typ_eq; mauto 3).
  enough {{ Δ ▶ Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_compose : mcpts.

Lemma wf_sub_eq_id_extend_compose_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' M A σ s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ' ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Γ', A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_id_extend_compose_sorted : mcpts.

Lemma wf_sub_eq_sigma_compose_weak_id_extend {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' M A σ},
    {{ Δ ▶ Γ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }}.
Proof with mautosolve.
  intros.
  assert {{ Δ ▶ Γ ⊢s Id,,M : Γ, A }} by mauto.
  assert {{ Δ ▶ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ∘(Wk∘(Id,,M)) : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }} by mauto.
  enough {{ Δ ▶ Γ ⊢s σ∘(Wk∘ (Id,,M)) ≈ σ∘Id : Γ' }} by mauto 4.
  econstructor...
Qed.

#[export]
Hint Resolve wf_sub_eq_sigma_compose_weak_id_extend : mcpts.

Lemma wf_sub_eq_sigma_compose_weak_id_extend_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' M A σ s},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_sigma_compose_weak_id_extend_sorted : mcpts.

Lemma wf_sub_eq_q_sigma_id_extend {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' M A σ},
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : A[σ] }} ->
    {{ Δ ▶ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Γ', A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ▶ Γ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ M : A[σ] }} by mauto.
  assert {{ Δ ▶ Γ ⊢s Id,,M : Γ, A[σ] }} by mauto.
  assert {{ Δ ▶ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ A[σ] }} by mauto 2.
  assert {{ Δ ▶ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by (eapply wf_exp_conv_typ_eq; mauto 3).
  assert {{ Δ ▶ Γ ⊢s q σ∘(Id,,M) ≈ ((σ∘Wk)∘(Id,,M)),,#0[Id,,M] : Γ', A }} by mauto.
  assert {{ Δ ▶ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Γ' }} by mauto.
  assert {{ Δ ▶ Γ ⊢ M : A[σ][Id] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ #0[Id,,M] ≈ M : A[σ][Id] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ #0[Id,,M] ≈ M : A[σ] }} by mauto 4.
  enough {{ Δ ▶ Γ ⊢ #0[Id,,M] ≈ M : A[(σ∘Wk)∘(Id,,M)] }} by mauto.
  assert {{ Δ ▶ Γ ⊢s (σ∘Wk)∘(Id,,M) : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ A[(σ∘Wk)∘(Id,,M)] }} by mauto 3.
  eapply wf_exp_eq_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_id_extend : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_id_extend using mauto 4 : mcpts.

Lemma wf_sub_eq_q_sigma_id_extend_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' M A σ s},
    {{ Δ ▶ Γ' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ ⊢ M : A[σ] }} ->
    {{ Δ ▶ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Γ', A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_id_extend_sorted : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_id_extend_sorted using mauto 4 : mcpts.

Lemma wf_sub_eq_q_sigma_extend_tau {P} : forall {Δ : gctx P } {Γ1 Γ2 Γ3 A σ τ M},
    {{ Δ ▶ Γ3 ⊢ A }} ->
    {{ Δ ▶ Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ▶ Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ▶ Γ1 ⊢ M : A[σ][τ] }} ->
    {{ Δ ▶ Γ1 ⊢s (q σ)∘(τ,,M) ≈ (σ∘τ),,M : Γ3, A }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ2, A[σ] ⊢s σ ∘ Wk : Γ3 }} by mauto.
  assert {{ Δ ▶ Γ2 ⊢ A[σ] }} by mauto 3.
  assert {{ Δ ▶ Γ2, A[σ] ⊢s Wk : Γ2 }} by mauto 3.
  assert {{ Δ ▶ Γ2, A[σ] ⊢ A[σ][Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ2, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ2, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] }} by mauto.
  assert {{ Δ ▶ Γ2, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ1 ⊢s (q σ) ∘ (τ,,M) ≈ ((σ∘Wk)∘(τ,,M)),,#0[τ,,M] : Γ3, A }} by mauto 3.
  assert {{ Δ ▶ Γ1 ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘(Wk∘(τ,,M)) : Γ3 }} by (econstructor; mauto 3).
  assert {{ Δ ▶ Γ1 ⊢s σ∘(Wk∘(τ,,M)) ≈ σ∘τ : Γ3 }} by mauto 4.
  assert {{ Δ ▶ Γ1 ⊢s (σ ∘ Wk) ∘ (τ,,M) ≈ σ∘τ : Γ3 }} by (etransitivity; mauto).
  assert {{ Δ ▶ Γ1 ⊢ #0[τ,,M] ≈ M : A[σ][τ] }} by mauto.
  assert {{ Δ ▶ Γ3 ⊢ A }} by mauto 2.
  assert {{ Δ ▶ Γ1 ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto 3.
  assert {{ Δ ▶ Γ1 ⊢ A[σ][τ] ≈ A[(σ∘Wk)∘(τ,,M)] }} by (etransitivity; mauto 4).
  assert {{ Δ ▶ Γ1 ⊢s (σ∘Wk)∘(τ,,M) : Γ3 }} by mauto 3.
  assert {{ Δ ▶ Γ1 ⊢ A[(σ∘Wk)∘(τ,,M)] }} by mauto 2.
  assert {{ Δ ▶ Γ1 ⊢s (σ∘Wk)∘(τ,,M),,#0[τ,,M] ≈ σ∘τ,,M : Γ3, A }} by (econstructor; mauto).
  do 2 etransitivity; mauto.
Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_extend_tau : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_extend_tau using mauto 4 : mcpts.

Lemma wf_sub_eq_q_sigma_extend_tau_sorted {P} : forall {Δ : gctx P } {Γ1 Γ2 Γ3 A σ τ M s},
    {{ Δ ▶ Γ3 ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ2 ⊢s σ : Γ3 }} ->
    {{ Δ ▶ Γ1 ⊢s τ : Γ2 }} ->
    {{ Δ ▶ Γ1 ⊢ M : A[σ][τ] }} ->
    {{ Δ ▶ Γ1 ⊢s (q σ)∘(τ,,M) ≈ (σ∘τ),,M : Γ3, A }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_extend_tau : mcpts.
#[export]
Hint Rewrite -> @wf_sub_eq_q_sigma_extend_tau using mauto 4 : mcpts.


Lemma wf_sub_eq_p_q_sigma {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A σ},
    {{ Δ ▶ Γ' ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Δ ▶ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  enough {{ Δ ▶ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve wf_sub_eq_p_q_sigma : mcpts.

Lemma wf_sub_eq_p_q_sigma_sorted {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A σ s},
    {{ Δ ▶ Γ' ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_p_q_sigma_sorted : mcpts.

Lemma wf_sub_eq_p_q_sigma_nat {P} : forall {Δ : gctx P} {Γ Γ' σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ, ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢s Wk : Γ }} by mauto 2.
  assert {{ Δ ▶ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_p_q_sigma_nat : mcpts.

Lemma wf_sub_eq_p_p_q_q_sigma_nat {P} : forall {Δ : gctx P} {Γ Γ' A σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ', ℕ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Γ' }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] }} by mauto 3.
  assert {{ Δ ▶ Γ', ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s Wk∘q (q σ) ≈ q σ∘Wk : Γ', ℕ }} by mauto.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ Wk∘(q σ∘Wk) : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ', ℕ ⊢s Wk : Γ' }} by mauto.
  assert {{ Δ ▶ Γ, ℕ ⊢s q σ : Γ', ℕ }} by mauto.
  assert {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s Wk∘(q σ∘Wk) ≈ (Wk∘q σ)∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Γ' }} by mauto.
  enough {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s (Wk∘q σ)∘Wk ≈ (σ∘Wk)∘Wk : Γ' }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_p_p_q_q_sigma_nat : mcpts.

Lemma wf_sub_eq_p_p_q_q_sigma_nat_sorted {P} : forall {Δ : gctx P} {Γ Γ' A σ s s'} {r : Ru_nat P s},
    {{ Δ ▶ Γ', ℕ ⊢ A : Sort@s' }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Γ' }}.
Proof. mauto 3. Qed.

#[export]
Hint Resolve wf_sub_eq_p_p_q_q_sigma_nat_sorted : mcpts.

Lemma wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1 {P} : forall {Δ : gctx P} {Γ Γ' A σ s} {r : Ru_nat P s},
    {{ Δ ▶ Γ', ℕ ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ', ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ', ℕ, A }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢s σ∘Wk : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  set (Γ'' := {{{ Γ, ℕ, A[q σ] }}}).
  set (WkWksucc := {{{ (Wk∘Wk),,succ #1 }}}).
  assert {{ Δ ▶ Γ'' }} by mauto 2.
  assert {{ Δ ▶ Γ'' ⊢s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢s WkWksucc : Γ, ℕ }} by mauto 4.
  assert {{ Δ ▶ Γ, ℕ ⊢ #0 : ℕ}} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢s q σ∘WkWksucc ≈ ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] : Γ', ℕ }} by mautosolve 3.
  assert {{ Δ ▶ Γ'' ⊢ #1 : ℕ[Wk][Wk] }} by mauto.
  assert {{ Δ ▶ Γ'' ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Δ ▶ Γ'' ⊢ succ #1 : ℕ }} by mauto.
  assert {{ Δ ▶ Γ'' ⊢s Wk∘WkWksucc : Γ }} by mauto 4.
  assert {{ Δ ▶ Γ'' ⊢s Wk∘WkWksucc ≈ Wk∘Wk : Γ }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢s σ ≈ σ : Γ' }} by mauto.
  assert {{ Δ ▶ Γ'' ⊢s σ∘(Wk∘WkWksucc) ≈ σ∘(Wk∘Wk) : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢s (σ∘Wk)∘WkWksucc ≈ σ∘(Wk∘Wk) : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢s σ∘(Wk∘Wk) ≈ (σ∘Wk)∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ'' ⊢s (σ∘Wk)∘Wk ≈ Wk∘(Wk∘q (q σ)) : Γ' }} by mauto.
  assert {{ Δ ▶ Γ', ℕ ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ', ℕ, A ⊢s Wk : Γ', ℕ }} by mauto 4.
  assert {{ Δ ▶ Γ', ℕ, A ⊢s Wk∘Wk : Γ' }} by mauto 4.
  assert {{ Δ ▶ Γ'' ⊢s q (q σ) : Γ', ℕ, A }} by mauto.
  assert {{ Δ ▶ Γ'' ⊢s Wk∘(Wk∘q (q σ)) ≈ (Wk∘Wk)∘q (q σ) : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢s σ∘(Wk∘Wk) ≈ (Wk∘Wk)∘q (q σ) : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢ #0[WkWksucc] ≈ succ #1 : ℕ }} by mauto.
  assert {{ Δ ▶ Γ'' ⊢ succ #1[q (q σ)] ≈ succ #1 : ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ', ℕ, A ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Δ ▶ Γ'' ⊢ succ #1 ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 4.
  assert {{ Δ ▶ Γ'' ⊢ #0[WkWksucc] ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 2.
  assert {{ Δ ▶ Γ'' ⊢s (σ∘Wk)∘WkWksucc : Γ' }} by mauto 3.
  assert {{ Δ ▶ Γ'' ⊢s ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] ≈ ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] : Γ', ℕ }} by mauto 3.
  assert {{ Δ ▶ Γ', ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ', ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ Δ ▶ Γ', ℕ, A ⊢ succ #1 : ℕ }} by mauto 4.
  enough {{ Δ ▶ Γ'' ⊢s ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] ≈ WkWksucc∘q (q σ) : Γ', ℕ }}...
Qed.

#[export]
Hint Resolve wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1 : mcpts.

Lemma wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1_unsorted {P} : forall {Δ : gctx P} {Γ Γ' A σ s s'} {r : Ru_nat P s},
    {{ Δ ▶ Γ', ℕ ⊢ A : Sort@s' }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Γ', ℕ }}.
Proof. mauto 3. Qed.
#[export]
Hint Resolve wf_sub_eq_q_sigma_compose_weak_weak_extend_succ_var1_unsorted : mcpts.


(** *** Lemmas for [wf_subtyp] *)

Fact wf_typ_subtyp_refl_sorted {P} : forall {Δ : gctx P} {Γ A s},
    {{ Δ ▶ Γ ⊢ A : Sort@s }} ->
    {{ Δ ▶ Γ ⊢ A ⊆ A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_subtyp_refl_sorted : mcpts.

Lemma wf_typ_subtyp_sub {P} : forall {Δ : gctx P} {Γ' A A'},
    {{ Δ ▶ Γ' ⊢ A ⊆ A' }} ->
    forall Γ σ,
      {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
      {{ Δ ▶ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  induction 1; intros; mauto 4.
  (* - assert {{ Γ0 ⊢ A[σ] ≈ B[σ] }} by mauto 3. *)
  (*   assert {{ Γ0 ⊢ B[σ] }} by mauto 3. *)
  (*   mauto 3. *)
  - assert {{ Δ ▶ Γ0 }} by mauto 2.
    assert {{ Δ ▶ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto.
    assert {{ Δ ▶ Γ ⊢ Sort@s1 }} by mauto.
    assert {{ Δ ▶ Γ0 ⊢ Sort@s1[σ] ≈ Sort@s1 }} by mauto.
    assert {{ Δ ▶ Γ0 ⊢ Sort@s2 ≈ Sort@s2[σ] }} by (symmetry; mauto).
    transitivity {{{ Sort@s1 }}}; mauto 3.
    transitivity {{{ Sort@s2 }}}; mauto 3.
  - assert {{ Δ ▶ Γ0 ⊢ A[σ] : Sort@s1 }} by mauto 3.
    assert {{ Δ ▶ Γ0, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 4.
    assert {{ Δ ▶ Γ0 ⊢ Π r A[σ] B[q σ] }} by mauto 3.
    transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; [econstructor; mauto 3|].
    transitivity {{{ Π r (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4].
    eapply wf_typ_subtyp_pi; mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sub : mcpts.

Lemma wf_subtyp_sort_weaken {P} : forall {Δ : gctx P} {Γ s1 s2 A},
    {{ Δ ▶ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} ->
    {{ Δ ▶ Γ, A }} ->
    {{ Δ ▶ Γ, A ⊢ Sort@s1 ⊆ Sort@s2 }}.
Proof.    
  intros.
  assert {{ Δ ▶ Γ ⊢ Sort@s2  }} by mauto 2.
  assert {{ Δ ▶ Γ, A ⊢s Wk : Γ }} by mauto 2.
  transitivity {{{ Sort@s1[Wk] }}}; mauto 3.
  transitivity {{{ Sort@s2[Wk] }}}; mauto 3.
Qed.

#[export]
Hint Resolve wf_subtyp_sort_weaken : mcpts.

Lemma wf_ctx_subtyp_ctx_lookup {P} : forall {Δ : gctx P} {Γ Γ'},
    {{ Δ ▶ Γ' ⊆ Γ }} ->
    forall {A x},
      {{ #x : A ∈ Γ }} ->
      exists B,
        {{ #x : B ∈ Γ' }} /\
          {{ Δ ▶ Γ' ⊢ B ⊆ A }}.
Proof with (do 2 eexists; repeat split; mautosolve).
  induction 1; intros * Hx; progressive_inversion.
  dependent destruction Hx.
  - eexists; split; mauto 3.
    eapply wf_typ_subtyp_sub; mauto 4.
  - edestruct IHwf_ctx_subtyp as [? []]; try eassumption...
Qed.

#[export]
Hint Resolve wf_ctx_subtyp_ctx_lookup : mcpts.

Lemma wf_gctx_subtyp_gctx_lookup {P} : forall {Δ Δ' : gctx P},
    {{ ▶ Δ' ⊆ Δ }} ->
    forall {A x},
      {{ `#x : A ∈ Δ }} ->
      exists B,
        {{ `#x : B ∈ Δ' }} /\
          {{ Δ' ▶ ⋅ ⊢ B ⊆ A }}.
Proof with (do 2 eexists; repeat split; mautosolve).
  induction 1; intros * Hx; progressive_inversion.
  dependent destruction Hx.
  - eexists; split; mauto 3.
    eapply wf_typ_subtyp_gctx_weakening; mauto 3.
  - edestruct IHwf_gctx_subtyp as [? []]; try eassumption...
Qed.

#[export]
Hint Resolve wf_gctx_subtyp_gctx_lookup : mcpts.


(** *** Lemmas about variables *)
Lemma var_compose_subs {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' Γ'' τ σ A x},
    {{ Δ ▶ Γ'' ⊢ A }} ->
    {{ Δ ▶ Γ' ⊢s σ : Γ'' }} ->
    {{ Δ ▶ Γ ⊢s τ : Γ' }} ->
    {{ #x : A[σ][τ] ∈ Γ }} ->
    {{ Δ ▶ Γ ⊢ #x : A[σ∘τ] }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ' ⊢ A[σ] }} by mauto 4.
  assert {{ Δ ▶ Γ ⊢ A[σ][τ] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ A[σ∘τ] }} by mauto 3.
  eapply wf_exp_conv_typ_eq; mauto 3.
Qed.

#[export]
Hint Resolve var_compose_subs : mcpts.

Lemma sub_lookup_var0 {P : PtsSig} : forall (Δ : gctx P) Γ Γ' σ M1 M2 B,
    {{ Δ ▶ Γ' ⊢s σ : Γ }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ' ⊢ M1 : B[σ] }} ->
    {{ Δ ▶ Γ' ⊢ M2 : B[σ] }} ->
    {{ Δ ▶ Γ' ⊢ #0[σ,,M1,,M2] ≈ M2 : B[σ] }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ, B ⊢ B[Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ' ⊢s σ,,M1 : Γ, B }} by mauto 3.
  assert {{ Δ ▶ Γ' ⊢ B[Wk][σ,,M1] }} by mauto 4.
  assert {{ Δ ▶ Γ' ⊢ B[Wk][σ,,M1] ≈ B[σ] }} by mauto 3.
  eapply wf_exp_eq_conv_typ_eq; mauto 3.
  eapply wf_exp_eq_var_0_sub with (A := {{{ B[Wk] }}}); [| | econstructor]; mauto.
Qed.

#[export]
Hint Resolve sub_lookup_var0 : mcpts.

Lemma id_sub_lookup_var0 {P : PtsSig} : forall (Δ : gctx P) Γ M1 M2 B,
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M1 : B }} ->
    {{ Δ ▶ Γ ⊢ M2 : B }} ->
    {{ Δ ▶ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var0 | |];
    mauto 4.
Qed.

#[export]
Hint Resolve id_sub_lookup_var0 : mcpts.
 
Lemma sub_lookup_var1 {P : PtsSig} : forall (Δ : gctx P) Γ Γ' σ M1 M2 B,
    {{ Δ ▶ Γ' ⊢s σ : Γ }} ->
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ' ⊢ M1 : B[σ] }} ->
    {{ Δ ▶ Γ' ⊢ M2 : B[σ] }} ->
    {{ Δ ▶ Γ' ⊢ #1[σ,,M1,,M2] ≈ M1 : B[σ] }}.
Proof.
  intros.
  assert {{ Δ ▶ Γ, B ⊢ B[Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ' ⊢s σ,,M1 : Γ, B }} by mauto 3.
  assert {{ Δ ▶ Γ' ⊢ B[Wk][σ,,M1] }} by mauto 4.
  assert {{ Δ ▶ Γ' ⊢ B[Wk][σ,,M1] ≈ B[σ] }} by mauto 3.
  assert {{ Δ ▶ Γ' ⊢ B[σ]}} by mauto 4.
  assert {{ Δ ▶ Γ' ⊢ M2 : B[Wk][σ,,M1] }} by mauto 3.
  transitivity {{{ #0[σ,,M1] }}}; mauto 3.
Qed.

#[export]
Hint Resolve sub_lookup_var1 : mcpts.

Lemma id_sub_lookup_var1 {P : PtsSig} : forall (Δ : gctx P) Γ M1 M2 B,
    {{ Δ ▶ Γ ⊢ B }} ->
    {{ Δ ▶ Γ ⊢ M1 : B }} ->
    {{ Δ ▶ Γ ⊢ M2 : B }} ->
    {{ Δ ▶ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var1 | |];
    mauto 4.
Qed.

#[export]
Hint Resolve id_sub_lookup_var1 : mcpts.

Lemma wf_exp_eq_var_1_sub_q_sigma {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' A B σ},
    {{ Δ ▶ Γ' ⊢ B }} ->
    {{ Δ ▶ Γ', B ⊢ A }} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }} ->
    {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ ▶ Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ, B[σ] ⊢s q σ : Γ', B }} by mauto 2.
  assert {{ Δ ▶ Γ, B[σ] }} by mauto 3.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] }} by mauto 3.
  assert {{ Δ ▶ Γ', B ⊢ B[Wk]  }} by mauto 4.
  assert {{ Δ ▶ Γ' ⊢ B }} by mauto 2.
  assert {{ Δ ▶ Γ', B ⊢ #0 : B[Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ, B[σ] ⊢ A[q σ] }} by mauto 3.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢s q σ∘Wk : Γ', B }} by mauto 3.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ∘Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ ⊢ B[σ]  }} by mauto 2.
  assert {{ Δ ▶ Γ, B[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢s Wk : Γ, B[σ] }} by mauto 2.
  assert {{ Δ ▶ Γ, B[σ] ⊢ B[σ][Wk]  }} by mauto 2.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk] }} by (eapply wf_typ_eq_sub_compose_cong; mauto 3).
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk] }} by (transitivity {{{ B[Wk][q σ][Wk] }}}; mauto 3).
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : B[σ][Wk][Wk] }} by (econstructor; mauto).
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : B[σ][Wk][Wk] }} by (econstructor; mauto).
  assert {{ Δ ▶ Γ, B[σ] ⊢s σ∘Wk : Γ' }} by mauto 2.
  assert {{ Δ ▶ Γ, B[σ] ⊢ #0 : B[σ∘Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ∘Wk] }} by mauto 3.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ∘Wk][Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ B[σ∘Wk][Wk] ≈ B[σ][Wk][Wk]  }} by mauto 4.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ][Wk][Wk] }} by mauto 4.
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk][Wk] }} by (do 2 etransitivity; mauto 2).
  assert {{ Δ ▶ Γ, B[σ], A[q σ] ⊢s Wk∘Wk : Γ }} by mauto 2.
  econstructor; mauto 4.
Qed.

#[export]
Hint Resolve wf_exp_eq_var_1_sub_q_sigma : mcpts.

    
(** *** Type Presuppositions *)
Lemma presup_wf_exp_typ {P : PtsSig} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ Δ ▶ Γ ⊢ A }}.
Proof with mautosolve 3.
  induction 1; assert {{ Δ ▶ Γ }} by mauto 2; destruct_conjs; mauto 3.
  - enough {{ Δ ▶ Γ ⊢s Id,,N : Γ, A }}...
  - assert {{ Δ ▶ ⋅ ⊢ A }} by mauto 3.
    mauto 3.
Qed.

Lemma presup_wf_exp {P : PtsSig} : forall {Δ : gctx P} {Γ M A},
    {{ Δ ▶ Γ ⊢ M : A }} ->
    {{ ▶ Δ }} /\ {{ Δ ▶ Γ }} /\ {{ Δ ▶ Γ ⊢ A }}.
Proof.
  intros; repeat split; mauto 2 using presup_wf_exp_typ.
Qed.

  
(** *** Consistency Helper *)
Lemma no_closed_neutral {P : PtsSig} : forall {A : exp P} {W : ne P},
    ~ {{ ⋅ ▶ ⋅ ⊢ W : A }}.
Proof.
  intros * H.
  dependent induction H; destruct W;
    try (simpl in *; congruence);
    autoinjections;
    intuition.
  - inversion_by_head (@ctx_lookup P).
  - inversion_by_head (@gctx_lookup P).
Qed.
#[export]
Hint Resolve no_closed_neutral : mcpts.
