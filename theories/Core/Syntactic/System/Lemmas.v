From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Import Definitions.
Import Syntax_Notations.

(** ** Basic Context Properties *)

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

Lemma ctx_decomp {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A }}.
Proof with now eauto.
  inversion 1; split; mauto 2.
Qed.

#[export]
Hint Resolve ctx_decomp : mcpts.

Corollary ctx_decomp_left {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> {{ Γ ⊢ A }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mcpts.

(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_ctx_eq_left {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

Corollary presup_ctx_eq_right {P : PtsSig} : forall {Γ Δ : ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mcpts.

Lemma presup_sub {P : PtsSig} : forall {Γ : ctx P} {Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_sub_left {P : PtsSig} : forall {Γ : ctx P} {Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

Corollary presup_sub_right {P : PtsSig} : forall {Γ : ctx P} {Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

#[export]
Hint Resolve presup_sub presup_sub_left presup_sub_right : mcpts.

(** With [presup_sub], we can prove similar for [exp]. *)

Lemma presup_exp_ctx {P : PtsSig} : forall {Γ : ctx P} {M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_ctx : mcpts.

Lemma presup_typ {P} : forall {Γ : ctx P} {A}, {{ Γ ⊢ A }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_typ : mcpts.

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; destruct_pairs; mauto 3.
Qed.

Corollary presup_sub_eq_ctx_left {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

Corollary presup_sub_eq_ctx_right {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

#[export]
Hint Resolve presup_sub_eq_ctx presup_sub_eq_ctx_left presup_sub_eq_ctx_right : mcpts.

Lemma presup_exp_eq_ctx {P : PtsSig} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mcpts.
  
Lemma presup_typ_eq_ctx {P : PtsSig} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ≈ A' }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mcpts.


Lemma presup_subtyp_ctx {P} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ⊆ A' }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_subtyp_ctx : mcpts.
 
Lemma presup_wf_ctx_sub {P} : forall {Γ Δ : ctx P},
    {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve 2.  
  induction 1; split; destruct_conjs; mauto 2.
Qed.

Lemma presup_wf_ctx_sub_left {P} : forall {Γ Δ : ctx P},
    {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  intros * []%presup_wf_ctx_sub...
Qed.
  
Lemma presup_wf_ctx_sub_right {P} : forall {Γ Δ : ctx P},
    {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Δ }}.
Proof with mautosolve.
  intros * []%presup_wf_ctx_sub...
Qed.


(** *** Immediate Results of Context Presuppositions *)
Lemma wf_ctx_sub_refl {P} : forall (Γ Δ : ctx P),
    {{ ⊢ Γ ≈ Δ }} ->
    {{ ⊢ Γ ⊆ Δ }}.
Proof. induction 1; mauto. Qed.

#[export]
Hint Resolve wf_ctx_sub_refl : mcpts.


(** Equality-based conversions *)
Lemma wf_conv_sorted {P} : forall (Γ : ctx P) M A s A',
    {{ Γ ⊢ M : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A : Sort@s }} -> 
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  assert {{ Γ ⊢ A }} by mauto 2.
  assert {{ Γ ⊢ A' }} by mauto 2.
  mauto.
Qed.

#[export]
Hint Resolve wf_conv_sorted : mcpts.

Lemma wf_conv {P} : forall (Γ : ctx P) M A A',
    {{ Γ ⊢ M : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ A' }} ->
    {{ Γ ⊢ A ≈ A'  }} ->
    {{ Γ ⊢ M : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_conv : mcpts.


Lemma wf_sub_conv_eq {P : PtsSig} : forall (Γ : ctx P) σ Δ Δ',
  {{ Γ ⊢s σ : Δ }} ->
  {{ ⊢ Δ ≈ Δ' }} ->
  {{ Γ ⊢s σ : Δ' }}.
Proof.
  intros.
  assert {{ ⊢ Δ' }} by (eapply presup_ctx_eq; eassumption).
  eapply wf_sub_conv; mauto.
Qed.

#[export]
Hint Resolve wf_sub_conv_eq : mcpts.

Lemma wf_exp_eq_sort_subtyp {P} : forall {Γ : ctx P} {A B s},
    {{ Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ B }} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_sort_subtyp : mcpts.

Lemma wf_eq_conv_sorted {P} : forall (Γ : ctx P) M M' A s A',
    {{ Γ ⊢ M ≈ M' : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A : Sort@s }} -> 
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed. 

#[export]
Hint Resolve wf_eq_conv_sorted : mcpts.

Lemma wf_eq_conv {P} : forall (Γ : ctx P) M M' A A',
    {{ Γ ⊢ M ≈ M' : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A }} -> 
    {{ Γ ⊢ A' }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed. 

#[export]
Hint Resolve wf_eq_conv : mcpts.


Lemma wf_sub_eq_conv_eq {P : PtsSig} : forall (Γ : ctx P) σ σ' Δ Δ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_eq_conv_eq : mcpts.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) : (wf_sub_eq Γ)
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  intros Δ Δ' H **; split; [| symmetry in H]; mauto.
Qed.

(** We can prove some additional lemmas for type presuppositions as well. *)


(** *** Additional Lemmas for Syntactic PERs *)

Lemma exp_eq_refl {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M ≈ M : A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_refl : mcpts.

Lemma sub_eq_refl {P : PtsSig} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof. mauto. Qed.

#[export]
Hint Resolve sub_eq_refl : mcpts.

Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ≈ Γ }}.
Proof.
  induction 1; mauto 2.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

(** *** Lemmas for [exp] of [{{{ Sort@s }}}] *)
Lemma wf_exp_sort_sub {P} : forall {Γ Γ' : ctx P} {A σ s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s }} ->
    {{ Γ ⊢ A[σ] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s[σ] }} by mauto 4.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ Sort@s[σ] ≈ Sort@s }} by mauto 3.
  assert {{ Γ ⊢ Sort@s[σ] ⊆ Sort@s }} by mauto 3.
  econstructor; mauto 3.
  solve [econstructor; mauto 3].
Qed.

#[export]
Hint Resolve wf_exp_sort_sub : mcpts.


Lemma exp_eq_sub_compose_typ_sort {P} : forall {Γ Γ' Γ'' : ctx P} {A A' σ τ s},
    {{ Γ'' ⊢ A' : Sort@s }} ->
    {{ Γ'' ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢ A[σ∘τ] ≈ A'[σ][τ] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ ⊢ Sort@s[σ∘τ] ≈ Sort@s }} by mauto.
  assert {{ Γ ⊢ Sort@s[σ∘τ] ⊆ Sort@s }} by mauto.
  assert {{ Γ ⊢ A'[σ∘τ] ≈ A'[σ][τ] : Sort@s[σ∘τ] }} by mauto 4.    
  transitivity {{{ A'[σ∘τ] }}}; mauto 4.
  assert {{ Γ ⊢s σ∘τ ≈ σ∘τ : Γ'' }} by mauto.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A'[σ∘τ] : Sort@s[σ∘τ] }} by mauto 4.
  mauto.                              
Qed.

#[export]
  Hint Resolve exp_eq_sub_compose_typ_sort : mcpts.

Lemma presup_ctx_lookup_typ {P : PtsSig} : forall {Γ : ctx P} {A x},
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊢ A }}.
Proof with mautosolve 4.
  intros * HΓ.
  induction 1; inversion_clear HΓ.
  - assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    eapply wf_typ_sub_sort; mauto 2.
  - assert {{ Γ, B ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ ⊢ A  }} by (eapply IHctx_lookup; eauto).
    eapply wf_typ_sub_sort; mauto 2.
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mcpts.

(** This removes the extra premise {{ Γ ⊢ A : Sort@s }} in wf_vlookup, which we use in soundness *)
Corollary wf_vlookup' {P} : forall {Γ : ctx P} {x A},
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊢ #x : A }}.
Proof.
  intros.
  assert {{ Γ ⊢ A }} by mauto 2.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_vlookup' : mcpts.
#[export]
Remove Hints wf_vlookup : mcpts.


Lemma exp_eq_sub_cong_typ1_sorted {P : PtsSig} : forall {Δ : ctx P} {Γ A A' σ s},
    {{ Δ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ Sort@s }} by mauto 3.
  assert {{ Γ ⊢s σ ≈ σ : Δ }} by mauto 2.
  assert {{ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s[σ] }} by mauto 4.
  econstructor; mauto 3.
Qed.

Lemma exp_eq_sub_cong_typ2_sorted {P} : forall {Δ : ctx P} {Γ A σ τ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ Sort@s }} by mauto 3.
  assert {{ Δ ⊢ A ≈ A : Sort@s }} by mauto 3.
  econstructor; mauto 4.
Qed.


Lemma exp_eq_sub_compose_typ_sorted {P : PtsSig} : forall {Ψ : ctx P} {Δ Γ A σ τ s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ1_sorted exp_eq_sub_cong_typ2_sorted exp_eq_sub_compose_typ_sorted : mcpts.

Lemma exp_eq_sub_compose_weaken_extend_typ {P : PtsSig} : forall {Γ : ctx P} {s σ Δ A B M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; [mautosolve 4 |].
  eapply exp_eq_sub_cong_typ2_sorted...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mcpts.

Lemma exp_eq_sub_compose_weaken_id_extend_typ {P : PtsSig} : forall {Γ : ctx P} {s A B M},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ A[Wk][Id,,M] ≈ A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mcpts.

Lemma exp_eq_sub_compose_double_weaken_double_extend_typ {P : PtsSig} : forall {Γ : ctx P} {s σ Δ A B M C N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Δ, B ⊢ C }} ->
    {{ Γ ⊢ N : C[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, B, C ⊢s Wk : Δ, B }} by mauto 4.
  assert {{ Δ, B ⊢ Sort@s }} by mauto 3.
  assert {{ Δ, B ⊢ A[Wk] : Sort@s }} by mauto 3.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply exp_eq_sub_cong_typ1_sorted; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_typ : mcpts.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_typ {P : PtsSig} : forall {Γ : ctx P} {s A B M C N},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B ⊢ C }} ->
    {{ Γ ⊢ N : C[Id,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id]  }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 3.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_typ : mcpts.

Lemma exp_eq_typ_sub_sub {P : PtsSig} : forall {Γ : ctx P} {Δ Ψ σ τ s1 s2},
    {{ Ψ ⊢ Sort@s1 : Sort@s2 }} ->
    {{ Γ ⊢ Sort@s1 : Sort@s2 }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ Sort@s1[σ][τ] ≈ Sort@s1 : Sort@s2 }}.
Proof.
  intros.
  transitivity {{{ Sort@s1[σ∘τ] }}}; [symmetry |]; mauto 3.  
Qed.

#[export]
Hint Resolve exp_eq_typ_sub_sub : mcpts.
#[export]
Hint Rewrite -> @exp_eq_typ_sub_sub using mauto 4 : mcpts.

Lemma wf_exp_sort_sort_implies_axiom {P} : forall {Γ : ctx P} {s1 K},
    {{ Γ ⊢ Sort@s1 : K }} ->
    exists s2,
      Ax_typ P s1 s2 /\
        {{ Γ ⊢ Sort@s2 ⊆ K }}.
Proof.
  intros * H.
  dependent induction H.
  - eexists; split; mauto 2.
  - specialize (IHwf_exp s1 A ltac:(reflexivity) ltac:(reflexivity)) as [s2 []].
    eexists; mauto.
Qed.

#[export]
Hint Resolve wf_exp_sort_sort_implies_axiom : mcpts.

(** *** Lemmas for [exp] of [{{{ ℕ }}}] *)

Lemma wf_exp_subtyp_nat_sub {P} : forall {Γ : ctx P} {Δ σ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ ℕ[σ] ⊆ ℕ }}.
Proof.
  intros.
  econstructor; mauto 3.
  econstructor; mauto 3.
Qed. 

#[export]
Hint Resolve wf_exp_subtyp_nat_sub : mcpts.
 
Lemma exp_sub_nat {P} : forall {Γ : ctx P} {Δ M σ s} {r : Ru_nat P s},
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : ℕ[σ] }} by mauto 3.  
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve exp_sub_nat : mcpts.

Lemma exp_eq_sub_cong_nat1 {P} : forall {Γ : ctx P} {Δ M M' σ s} {r : Ru_nat P s},
    {{ Δ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] ≈ M'[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.  
  econstructor; mauto.
Qed.

Lemma exp_eq_sub_cong_nat2 {P} : forall {Γ : ctx P} {Δ M σ τ s} {r : Ru_nat P s},
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ M[σ] ≈ M[τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  econstructor; mauto.
Qed.


Lemma exp_eq_sub_compose_nat {P} : forall {Γ : ctx P} {Ψ Δ M σ τ s} {r : Ru_nat P s},
    {{ Ψ ⊢ M : ℕ }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Ψ }} by mauto 2.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Ψ ⊢ ℕ }} by mauto 3.
  assert {{ Δ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ][τ] : ℕ[σ∘τ] }} by mauto 3.
  econstructor; mauto 3.
Qed.


#[export]
Hint Resolve exp_sub_nat exp_eq_sub_cong_nat1 exp_eq_sub_cong_nat2 exp_eq_sub_compose_nat : mcpts.

Lemma exp_eq_nat_sub_sub {P} : forall {Γ : ctx P} {Δ Ψ σ τ s} {r : Ru_nat P s},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ : Sort@s }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub : mcpts.

Lemma exp_eq_nat_sub_sub_to_nat_sub {P} : forall {Γ : ctx P} {Δ Ψ Ψ' σ τ σ' s} {r : Ru_nat P s},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s σ' : Ψ' }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ[σ'] : Sort@s}}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_nat_sub_sub_to_nat_sub : mcpts.

Lemma exp_eq_sub_compose_weaken_extend_nat {P} : forall {Γ : ctx P} {σ Δ M B N s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Δ ⊢ B }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Γ ⊢ M[Wk][σ,,N] ≈ M[σ] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 3.
  assert {{ Γ ⊢s σ,,N : Δ, B }} by mauto 2.
  transitivity {{{ M[Wk∘(σ,,N)] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_nat : mcpts.

Lemma exp_eq_sub_compose_weaken_id_extend_nat {P} : forall {Γ : ctx P} {M B N s} {r : Ru_nat P s},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ ⊢ M[Wk][Id,,N] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ N : B[Id] }} by mauto 4.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_nat : mcpts.

Lemma exp_eq_sub_compose_double_weaken_double_extend_nat {P} : forall {Γ : ctx P} {σ Δ M B N C L s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Δ ⊢ B  }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Δ, B ⊢ C }} ->
    {{ Γ ⊢ L : C[σ,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][σ,,N,,L] ≈ M[σ] : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, B, C ⊢s Wk : Δ, B }} by mauto 4.
  assert {{ Γ ⊢s σ,,N : Δ, B }} by mauto 2.
  assert {{ Γ ⊢s σ,,N,,L : Δ, B, C }} by mauto 2.
  transitivity {{{ M[Wk][Wk][σ,,N,,L] }}}; [econstructor; mautosolve 3|].
  transitivity {{{ M[Wk][σ,,N] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_nat : mcpts.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_nat {P} : forall {Γ : ctx P} {M B N C L s } {r : Ru_nat P s},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ, B ⊢ C }} ->
    {{ Γ ⊢ L : C[Id,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][Id,,N,,L] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ N : B[Id] }} by mauto 4.
  transitivity {{{ M[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_nat : mcpts.

Lemma vlookup_0_nat {P} : forall {Γ : ctx P} {s} {r : Ru_nat P s},
    {{ ⊢ Γ }} ->
    {{ Γ, ℕ ⊢ #0 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  eapply wf_exp_conv...
Qed.

Lemma vlookup_1_nat {P} : forall {Γ : ctx P} {A s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ, ℕ, A ⊢ #1 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }} by mauto 5.
  assert {{ Γ, ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  eapply wf_conv; mauto 4.
Qed.

#[export]
Hint Resolve vlookup_0_nat vlookup_1_nat : mcpts.

Lemma exp_sub_nat_helper {P} : forall {Γ : ctx P} {σ Δ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M : ℕ[σ] }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] }} by mauto 3.
  assert {{ Γ ⊢ ℕ ≈ ℕ[σ] }} by (symmetry; mauto 3).
  assert {{ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mauto 2.
  eapply wf_exp_conv; mauto 2.
Qed.

#[export]
Hint Resolve exp_sub_nat_helper : mcpts.

Lemma exp_eq_var_0_sub_nat {P} : forall {Γ : ctx P} {σ Δ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ ℕ }} by mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma exp_eq_var_1_sub_nat {P} : forall {Γ : ctx P} {σ Δ A M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : ℕ[Wk] ∈ Δ }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ }}.
Proof with mautosolve 4.
  inversion 5 as [? Δ'|]; subst.
  assert {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ[Wk][σ] }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_nat exp_eq_var_1_sub_nat : mcpts.

Lemma exp_eq_var_0_weaken_nat {P} : forall {Γ : ctx P} {A s} {r : Ru_nat P s},
    {{ ⊢ Γ, A }} ->
    {{ #0 : ℕ[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : ℕ }}.
Proof with mautosolve 4.
  inversion 2; subst.
  inversion 1; subst.
  assert {{ Γ0, ℕ, A ⊢ #0[Wk] ≈ #1 : ℕ[Wk][Wk] }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_nat : mcpts.

Lemma sub_extend_nat {P} : forall {Γ : ctx P} {σ Δ M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ,,M : Δ, ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_extend_nat : mcpts.

Lemma sub_eq_extend_cong_nat {P} : forall {Γ : ctx P} {σ σ' Δ M M' s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 4.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ ℕ ≈ ℕ[σ] : Sort@s }} by mauto 3.
  assert {{ Δ ⊢ ℕ : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ ℕ[σ] : Sort@s }} by mauto 3.
  assert {{ Γ ⊢ ℕ ⊆ ℕ[σ] }} by mauto 4.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

Lemma sub_eq_extend_compose_nat {P} : forall {Γ : ctx P} {τ Γ' σ Γ'' M s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', ℕ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_nat {P} : forall {Γ : ctx P} {σ Γ' M s} {r : Ru_nat P s},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve.
  intros.
  assert {{ Γ ⊢ ℕ : Sort@s }} by (econstructor; mauto 3).
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_nat sub_eq_extend_compose_nat sub_eq_p_extend_nat : mcpts.

Lemma exp_eq_sub_sub_compose_cong_nat {P} : forall {Γ : ctx P} {Δ Δ' Ψ σ τ σ' τ' M s} {r : Ru_nat P s},
    {{ Ψ ⊢ M : ℕ }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : ℕ }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : ℕ }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_nat : mcpts.

(** Lemmas about variables *)

Lemma vlookup_0_typ {P : PtsSig} : forall {Γ : ctx P} {s},
    {{ ⊢ Γ }} ->
    {{ Γ, Sort@s ⊢ #0 : Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, Sort@s ⊢s Wk : Γ }} by (econstructor; mauto 3).
  eapply wf_exp_conv with (A := {{{ Sort@s[Wk] }}}); mauto 3.
  econstructor...
Qed.

Lemma vlookup_1_typ {P : PtsSig} : forall {Γ : ctx P} {s A},
    {{ Γ, Sort@s ⊢ A }} ->
    {{ Γ, Sort@s, A ⊢ #1 : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Sort@s, A ⊢s Wk : Γ, Sort@s }} by (econstructor; mauto 4).
  assert {{ ⊢ Γ, Sort@s, A }} by mauto 3.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ, Sort@s ⊢ Sort@s[Wk] }} by mauto 3.
  assert {{ Γ, Sort@s, A ⊢ Sort@s[Wk][Wk] }} by mauto 3.
  eapply wf_exp_conv with (A := {{{ Sort@s[Wk][Wk] }}}); mauto 3.
  econstructor; mauto 3.
  transitivity {{{ Sort@s[Wk] }}}; mauto 4.
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mcpts.

Lemma exp_sub_typ_helper {P : PtsSig} : forall {Γ : ctx P} {σ Δ M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢ M : Sort@s[σ] }}.
Proof.
  intros.
  do 3 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve exp_sub_typ_helper : mcpts.

Lemma exp_eq_var_0_sub_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Γ ⊢ Sort@s [σ] ⊆ Sort@s  }} by mauto 5.
  eapply wf_exp_eq_conv; mauto 4.
Qed.

Lemma exp_eq_var_1_sub_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : Sort@s[Wk] ∈ Δ }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  inversion H2; subst.
  assert {{ ⊢ Γ0 }} by mauto 3.
  assert {{ Γ0, Sort@s ⊢s Wk : Γ0 }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 3.
  transitivity {{{ Sort@s[σ] }}}; mauto 4.
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_typ exp_eq_var_1_sub_typ : mcpts.
#[export]
Hint Rewrite -> @exp_eq_var_0_sub_typ @exp_eq_var_1_sub_typ : mcpts.

Lemma exp_eq_var_0_weaken_typ {P : PtsSig} : forall {Γ : ctx P} {A s},
    {{ ⊢ Γ, A }} ->
    {{ #0 : Sort@s[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : Sort@s }}.
Proof with mautosolve 3.
  inversion_clear 1.
  inversion 1 as [? Γ'|]; subst.
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ', Sort@s ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Γ', Sort@s, A ⊢s Wk : Γ', Sort@s }} by mauto 4.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 3.
  transitivity {{{ Sort@s[Wk] }}}; mauto 4.
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_typ : mcpts.

Lemma sub_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢s σ,,M : Δ, Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_extend_typ : mcpts.

Lemma sub_eq_extend_cong_typ {P : PtsSig} : forall {Γ : ctx P} {σ σ' Δ M M' s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : Sort@s }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  econstructor; mauto 2.
  eapply wf_exp_eq_conv; mauto 3.
  econstructor; mauto 3.
Qed.

Lemma sub_eq_extend_compose_typ {P : PtsSig} : forall {Γ : ctx P} {τ Γ' σ Γ'' A s M},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A }} ->
    {{ Γ' ⊢ M : Sort@s }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Γ' M s},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : Sort@s }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_typ sub_eq_extend_compose_typ sub_eq_p_extend_typ : mcpts.

Lemma exp_eq_sub_sub_compose_cong_typ {P : PtsSig} : forall {Γ : ctx P} {Δ Δ' Ψ σ τ σ' τ' A s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} by mauto 2.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Sort@s }} by mauto 3.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] : Sort@s }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mcpts.

Lemma typ_eq_sub_sub_compose_cong_typ {P : PtsSig} : forall {Γ : ctx P} {Δ Δ' Ψ σ τ σ' τ' A},
    {{ Ψ ⊢ A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto 3.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto 3.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] }}...
Qed.

#[export]
Hint Resolve typ_eq_sub_sub_compose_cong_typ : mcpts.


(** *** Other Tedious Lemmas *)

Lemma sub_eq_weaken_var0_id {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof with mautosolve 4.
  intros * ?.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ A }} by mauto 2.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, A ⊢s (Wk∘Id),,#0[Id] ≈ Id : Γ, A }} by mauto.
  assert {{ Γ, A ⊢s Wk ≈ Wk∘Id : Γ }} by mauto.
  assert {{ Γ, A ⊢s Wk,,#0 ≈ Wk∘Id,,#0[Id] : Γ, A }} by (eapply wf_sub_eq_extend_cong; mauto 4).
  enough {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }} by (etransitivity; mauto 3).
  symmetry; econstructor; econstructor; mauto 2.
Qed.

#[export]
Hint Resolve sub_eq_weaken_var0_id : mcpts.
#[export]
Hint Rewrite -> @sub_eq_weaken_var0_id using mauto 4 : mcpts.

Lemma exp_eq_sub_sub_compose_cong_sorted {P : PtsSig} : forall {Γ : ctx P} {Δ Δ' Ψ σ τ σ' τ' M A s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Ψ ⊢ M : A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto 4.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto 4.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv; mauto 4.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ∘τ] }} by (econstructor; mauto 4).
  mauto 4.
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_sorted : mcpts.

Lemma exp_eq_sub_sub_compose_cong {P : PtsSig} : forall {Γ : ctx P} {Δ Δ' Ψ σ τ σ' τ' M A},
    {{ Ψ ⊢ A }} ->
    {{ Ψ ⊢ M : A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv; mauto 4.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ∘τ] }} by (econstructor; mauto 4).
  mauto 4.
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mcpts.

Lemma ctxeq_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {Δ A x},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ #x : A ∈ Γ }} ->
    exists B,
      {{ #x : B ∈ Δ }} /\
        {{ Γ ⊢ A ≈ B }} /\
        {{ Δ ⊢ A ≈ B }} /\
        {{ Δ ⊢ A }}.
Proof with (repeat eexists; mautosolve 3).
  intros * HΓΔ Hx.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ A }} by mauto 3.
  gen Δ Hx.
  induction 1 as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? HΓΔ'];
    assert {{ ⊢ Δ0 }} by mauto 2.
  - assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
    assert {{ Δ0, A' ⊢s Wk : Δ0 }} by mauto 3.
    eexists.
    do 3 (split; mauto 3).
  - specialize (IHHx ltac:(mauto 2) ltac:(mauto 3) _ HΓΔ').
    destruct_conjs.
    assert {{ Γ, B ⊢s Wk : Γ }} by mauto 2.
    assert {{ Δ0, A' ⊢s Wk : Δ0 }} by mauto 3.
    eexists.
    do 3 (split; mauto 3).
Qed.

#[export]
Hint Resolve ctxeq_ctx_lookup : mcpts.

Lemma sub_id_on_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  eapply wf_conv; mauto 4.
Qed.

#[export]
Hint Resolve sub_id_on_typ_sorted : mcpts.

Lemma sub_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  eapply wf_conv; mauto 3.
Qed.

#[export]
Hint Resolve sub_id_on_typ : mcpts.


Lemma sub_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_id_extend : mcpts.

Lemma sub_eq_id_on_typ_sorted {P : PtsSig} : forall {Γ : ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  eapply wf_eq_conv; mauto 3;
    econstructor...
Qed.

#[export]
Hint Resolve sub_eq_id_on_typ_sorted : mcpts.

Lemma sub_eq_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M M' A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  eapply wf_exp_eq_conv; mauto 3;
    econstructor...
Qed.

#[export]
Hint Resolve sub_eq_id_on_typ : mcpts.

Lemma sub_eq_id_extend_cong_sorted {P : PtsSig} : forall {Γ : ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_id_extend_cong_sorted : mcpts.

Lemma sub_eq_p_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_p_id_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_p_id_extend using mauto 4 : mcpts.

Lemma sub_q {P : PtsSig} : forall {Γ : ctx P} {A σ Δ},
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s q σ : Δ, A }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  econstructor; mauto 2.
  eapply wf_conv; mauto 3.
Qed.

Lemma sub_q_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, Sort@s ⊢s q σ : Δ, Sort@s }}.
Proof with mautosolve 3.

  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ, Sort@s ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Sort@s ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, Sort@s ⊢ Sort@s[Wk] ≈ Sort@s }} by mauto 4.
  assert {{ Γ, Sort@s ⊢ #0 : Sort@s }} by mauto 3.
  econstructor...
Qed.

#[export]
Hint Resolve sub_q sub_q_typ : mcpts.

Lemma sub_q_nat {P} : forall {Γ : ctx P} {σ Δ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ ⊢s q σ : Δ, ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_q sub_q_typ sub_q_nat : mcpts.

Lemma exp_eq_var_1_sub_q_sigma_nat {P} : forall {Γ : ctx P} {A σ Δ s} {r : Ru_nat P s},
    {{ Δ, ℕ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  assert {{ ⊢ Γ, ℕ, A[q σ] }} by (econstructor; mauto 2).
  assert {{ Δ, ℕ ⊢ #0 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Δ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk]  }} by mauto 4.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0 : A[q σ∘Wk] }} by (eapply wf_conv; mauto 4).
  assert {{ Γ, ℕ, A[q σ] ⊢s q σ∘Wk : Δ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : ℕ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ #0 : ℕ[σ∘Wk] }} by mauto 3.
  assert {{ Γ, ℕ ⊢ #0[q σ] ≈ #0 : ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : ℕ }} by mauto 3.
  etransitivity; [eassumption |].
  etransitivity...
Qed.

#[export]
Hint Resolve exp_eq_var_1_sub_q_sigma_nat : mcpts.

Lemma sub_id_extend_zero {P} : forall {Γ : ctx P} {s} {r : Ru_nat P s},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s Id,,zero : Γ, ℕ }}.
Proof. mauto 4. Qed.

Lemma sub_weak_compose_weak_extend_succ_var_1 {P} : forall {Γ : ctx P} {A s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ  }} by mauto 4.
  enough {{ Γ, ℕ, A ⊢s Wk∘Wk : Γ }}...
Qed.

Lemma sub_eq_id_extend_compose_sigma {P : PtsSig} : forall {Γ : ctx P} {M A σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ⊢s Id : Δ }} by mauto 3.
  assert {{ Δ ⊢ M : A[Id] }} by mauto.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : A[Id][σ] }} by mauto.
  assert {{ Γ ⊢ A[Id][σ] ≈ A[Id∘σ] }} by (symmetry; mauto 3).
  assert {{ Γ ⊢ A[Id∘σ] }} by mauto 4.
  assert {{ Γ ⊢ A[Id][σ] ⊆ A[Id∘σ] }} by mauto 4.
  assert {{ Γ ⊢ M[σ] : A[Id∘σ] }} by (eapply wf_exp_conv; mauto 4).
  enough {{ Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve sub_eq_id_extend_compose_sigma : mcpts.

Lemma sub_eq_sigma_compose_weak_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A σ Δ},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }}.
Proof with mautosolve.
  intros.
  assert {{ Γ ⊢s Id,,M : Γ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ∘(Wk∘(Id,,M)) : Δ }} by mauto 4.
  assert {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }} by mauto.
  enough {{ Γ ⊢s σ∘(Wk∘ (Id,,M)) ≈ σ∘Id : Δ }} by mauto.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_sigma_compose_weak_id_extend : mcpts.

Lemma sub_eq_q_sigma_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A σ Δ},
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Γ ⊢ M : A[σ] }} by mauto.
  assert {{ Γ ⊢s Id,,M : Γ, A[σ] }} by mauto.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ ⊢ A[σ] }} by mauto 2.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by (eapply wf_conv; mauto 3).
  assert {{ Γ ⊢s q σ∘(Id,,M) ≈ ((σ∘Wk)∘(Id,,M)),,#0[Id,,M] : Δ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }} by mauto.
  assert {{ Γ ⊢ M : A[σ][Id] }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ][Id] }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ] }} by mauto 4.
  enough {{ Γ ⊢ #0[Id,,M] ≈ M : A[(σ∘Wk)∘(Id,,M)] }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) : Δ }} by mauto 3.
  assert {{ Γ ⊢ A[(σ∘Wk)∘(Id,,M)] }} by mauto 3.
  eapply wf_exp_eq_conv; mauto.
Qed.


#[export]
Hint Resolve sub_eq_q_sigma_id_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_id_extend using mauto 4 : mcpts.


Lemma sub_eq_q_sigma_sigma0_extend {P} : forall {Γ1 Γ2 Γ3 : ctx P} {A σ σ0 M},
    {{ Γ3 ⊢ A }} ->
    {{ Γ2 ⊢s σ : Γ3 }} ->
    {{ Γ1 ⊢s σ0 : Γ2 }} ->
    {{ Γ1 ⊢ M : A[σ][σ0] }} ->
    {{ Γ1 ⊢s (q σ)∘(σ0,,M) ≈ (σ∘σ0),,M : Γ3, A }}.
Proof.
  intros.
  assert {{ Γ2, A[σ] ⊢s σ ∘ Wk : Γ3 }} by mauto.
  assert {{ Γ2 ⊢ A[σ] }} by mauto 3.
  assert {{ Γ2, A[σ] ⊢s Wk : Γ2 }} by mauto 3.
  assert {{ Γ2, A[σ] ⊢ A[σ][Wk] }} by mauto 3.
  assert {{ Γ2, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  assert {{ Γ2, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] }} by mauto.
  assert {{ Γ2, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  assert {{ Γ1 ⊢s (q σ) ∘ (σ0,,M) ≈ ((σ∘Wk)∘(σ0,,M)),,#0[σ0,,M] : Γ3, A }} by mauto 3.
  assert {{ Γ1 ⊢s (σ∘Wk)∘(σ0,,M) ≈ σ∘(Wk∘(σ0,,M)) : Γ3 }} by (econstructor; mauto 3).
  assert {{ Γ1 ⊢s σ∘(Wk∘(σ0,,M)) ≈ σ∘σ0 : Γ3 }} by mauto 4.
  assert {{ Γ1 ⊢s (σ ∘ Wk) ∘ (σ0,,M) ≈ σ∘σ0 : Γ3 }} by (etransitivity; mauto).
  assert {{ Γ1 ⊢ #0[σ0,,M] ≈ M : A[σ][σ0] }} by mauto.
  assert {{ Γ3 ⊢ A }} by mauto 2.
  assert {{ Γ1 ⊢ A[σ][σ0] ≈ A[σ∘σ0] }} by mauto 3.
  assert {{ Γ1 ⊢ A[σ][σ0] ≈ A[(σ∘Wk)∘(σ0,,M)] }} by (etransitivity; mauto 4).
  assert {{ Γ1 ⊢s (σ∘Wk)∘(σ0,,M) : Γ3 }} by mauto 3.
  assert {{ Γ1 ⊢ A[(σ∘Wk)∘(σ0,,M)] }} by mauto 2.
  assert {{ Γ1 ⊢s (σ∘Wk)∘(σ0,,M),,#0[σ0,,M] ≈ σ∘σ0,,M : Γ3, A }} by (econstructor; mauto).
  do 2 etransitivity; mauto.
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_sigma0_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_sigma0_extend using mauto 4 : mcpts.

Lemma sub_eq_p_q_sigma {P : PtsSig} : forall {Γ : ctx P} {A σ Δ},
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ ⊢ A[σ] }} by mauto 3.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  enough {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  eapply wf_conv; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma : mcpts.

Lemma sub_eq_p_q_sigma_nat {P} : forall {Γ : ctx P} {σ Δ s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, ℕ ⊢ #0 : ℕ }}...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_nat : mcpts.

Lemma sub_eq_p_p_q_q_sigma_nat {P} : forall {Γ : ctx P} {A σ Δ s} {r : Ru_nat P s},
    {{ Δ, ℕ ⊢ A  }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  assert {{ ⊢ Γ, ℕ, A[q σ] }} by mauto 3.
  assert {{ ⊢ Δ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘q (q σ) ≈ q σ∘Wk : Δ, ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ Wk∘(q σ∘Wk) : Δ }} by mauto 3.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto.
  assert {{ Γ, ℕ ⊢s q σ : Δ, ℕ }} by mauto.
  assert {{ Γ, ℕ, A[q σ] ⊢s Wk∘(q σ∘Wk) ≈ (Wk∘q σ)∘Wk : Δ }} by mauto 4.
  assert {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Δ }} by mauto.
  enough {{ Γ, ℕ, A[q σ] ⊢s (Wk∘q σ)∘Wk ≈ (σ∘Wk)∘Wk : Δ }}...
Qed.

#[export]
Hint Resolve sub_eq_p_p_q_q_sigma_nat : mcpts.

Lemma sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 {P} : forall {Γ : ctx P} {A σ Δ s} {r : Ru_nat P s},
    {{ Δ, ℕ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ, A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Δ, ℕ }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Δ, ℕ, A }} by mauto 3.
  assert {{ ⊢ Γ, ℕ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, ℕ ⊢s σ∘Wk : Δ }} by mauto 3.
  assert {{ Γ, ℕ ⊢ A[q σ] }} by mauto 4.
  set (Γ' := {{{ Γ, ℕ, A[q σ] }}}).
  set (WkWksucc := {{{ (Wk∘Wk),,succ #1 }}}).
  assert {{ ⊢ Γ' }} by mauto 2.
  assert {{ Γ' ⊢s Wk∘Wk : Γ }} by mauto 3.
  assert {{ Γ' ⊢s WkWksucc : Γ, ℕ }} by mauto 4.
  assert {{ Γ, ℕ ⊢ #0 : ℕ}} by mauto 3.
  assert {{ Γ' ⊢s q σ∘WkWksucc ≈ ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] : Δ, ℕ }} by mautosolve 3.
  assert {{ Γ' ⊢ #1 : ℕ[Wk][Wk] }} by mauto.
  assert {{ Γ' ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ Γ' ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Γ' ⊢ succ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢s Wk∘WkWksucc : Γ }} by mauto 4.
  assert {{ Γ' ⊢s Wk∘WkWksucc ≈ Wk∘Wk : Γ }} by mauto 4.
  assert {{ Γ ⊢s σ ≈ σ : Δ }} by mauto.
  assert {{ Γ' ⊢s σ∘(Wk∘WkWksucc) ≈ σ∘(Wk∘Wk) : Δ }} by mauto 3.
  assert {{ Γ' ⊢s (σ∘Wk)∘WkWksucc ≈ σ∘(Wk∘Wk) : Δ }} by mauto 3.
  assert {{ Γ' ⊢s σ∘(Wk∘Wk) ≈ (σ∘Wk)∘Wk : Δ }} by mauto 4.
  assert {{ Γ' ⊢s (σ∘Wk)∘Wk ≈ Wk∘(Wk∘q (q σ)) : Δ }} by mauto.
  assert {{ Δ, ℕ ⊢s Wk : Δ }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢s Wk : Δ, ℕ }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢s Wk∘Wk : Δ }} by mauto 4.
  assert {{ Γ' ⊢s q (q σ) : Δ, ℕ, A }} by mauto.
  assert {{ Γ' ⊢s Wk∘(Wk∘q (q σ)) ≈ (Wk∘Wk)∘q (q σ) : Δ }} by mauto 3.
  assert {{ Γ' ⊢s σ∘(Wk∘Wk) ≈ (Wk∘Wk)∘q (q σ) : Δ }} by mauto 3.
  assert {{ Γ' ⊢ #0[WkWksucc] ≈ succ #1 : ℕ }} by mauto.
  assert {{ Γ' ⊢ succ #1[q (q σ)] ≈ succ #1 : ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢ #1 : ℕ }} by mauto 2.
  assert {{ Γ' ⊢ succ #1 ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 4.
  assert {{ Γ' ⊢ #0[WkWksucc] ≈ (succ #1)[q (q σ)] : ℕ }} by mauto 2.
  assert {{ Γ' ⊢s (σ∘Wk)∘WkWksucc : Δ }} by mauto 3.
  assert {{ Γ' ⊢s ((σ∘Wk)∘WkWksucc),,#0[WkWksucc] ≈ ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] : Δ, ℕ }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢ #1 : ℕ[Wk][Wk] }} by mauto 4.
  assert {{ Δ, ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 3.
  assert {{ Δ, ℕ, A ⊢ succ #1 : ℕ }} by mauto 4.
  enough {{ Γ' ⊢s ((Wk∘Wk)∘q (q σ)),,(succ #1)[q (q σ)] ≈ WkWksucc∘q (q σ) : Δ, ℕ }}...
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : mcpts.

(** *** Lemmas for [wf_subtyp] *)

Fact wf_subtyp_refl_sorted {P} : forall {Γ : ctx P} {A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ A ⊆ A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_subtyp_refl_sorted : mcpts.

Lemma wf_subtyp_sub {P} : forall {Δ : ctx P} {A A'},
    {{ Δ ⊢ A ⊆ A' }} ->
    forall Γ σ,
      {{ Γ ⊢s σ : Δ }} ->
      {{ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  induction 1; intros; mauto 4.
  - assert {{ Γ0 ⊢ A[σ] ≈ B[σ] }} by mauto 3.
    assert {{ Γ0 ⊢ B[σ] }} by mauto 3.
    mauto 3.
  - assert {{ ⊢ Γ0 }} by mauto 2.
    assert {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto.
    assert {{ Γ ⊢ Sort@s1 }} by mauto.
    assert {{ Γ0 ⊢ Sort@s1[σ] ≈ Sort@s1 }} by mauto.
    assert {{ Γ0 ⊢ Sort@s2 ≈ Sort@s2[σ] }} by (symmetry; mauto).
    transitivity {{{ Sort@s1 }}}; mauto 3.
    transitivity {{{ Sort@s2 }}}; mauto 3.
    mauto 4.
  - assert {{ Γ0 ⊢ A[σ] : Sort@s1 }} by mauto 3.
    assert {{ Γ0, A[σ] ⊢ B[q σ] : Sort@s2 }} by mauto 4.
    assert {{ Γ0 ⊢ Π r A[σ] B[q σ] }} by mauto.
    transitivity {{{ Π r (A[σ]) (B[q σ]) }}}; [econstructor; mauto 3|].
    transitivity {{{ Π r (A'[σ]) (B'[q σ]) }}}; [ | econstructor; mauto 4].
    eapply wf_subtyp_pi; mauto 4.
Qed.


#[export]
Hint Resolve wf_subtyp_sub : mcpts.


Lemma wf_subtyp_sort_weaken {P} : forall {Γ : ctx P} {s1 s2 A},
    {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ Sort@s1 ⊆ Sort@s2 }}.
Proof.    
  intros.
  assert {{ Γ ⊢ Sort@s2  }} by mauto 2.
  assert {{ Γ, A ⊢s Wk : Γ }} by mauto 2.
  dependent induction H; mauto 2.
  - assert {{ Γ, A ⊢ Sort@s1[Wk] ≈ Sort@s2[Wk] }} by mauto.
    assert {{ Γ, A ⊢ Sort@s1[Wk] ≈ Sort@s1  }} by mauto.
    assert {{ Γ, A ⊢ Sort@s2[Wk] ≈ Sort@s2  }} by mauto.
    assert {{ Γ, A ⊢ Sort@s1 ≈ Sort@s2  }} by mauto.
    mauto 3.
  - assert {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }} by mauto 3.
    assert {{ Γ, A ⊢ Sort@s1[Wk] ⊆ Sort@s2[Wk] }} by mauto 2.
    assert {{ Γ, A ⊢ Sort@s1[Wk] }} by mauto 4.
    assert {{ Γ, A ⊢ Sort@s1 ⊆ Sort@s1[Wk] }} by mauto 4.
    transitivity {{{ Sort@s1[Wk] }}}; mauto.
Qed.

Lemma ctx_sub_ctx_lookup {P} : forall {Γ Δ : ctx P},
    {{ ⊢ Δ ⊆ Γ }} ->
    forall {A x},
      {{ #x : A ∈ Γ }} ->
      exists B,
        {{ #x : B ∈ Δ }} /\
          {{ Δ ⊢ B ⊆ A }}.
Proof with (do 2 eexists; repeat split; mautosolve).
  induction 1; intros * Hx; progressive_inversion.
  dependent destruction Hx.
  - eexists; split; mauto 3.
    eapply wf_subtyp_sub; mauto 4.
  - edestruct IHwf_ctx_sub as [? []]; try eassumption...
Qed.

#[export]
Hint Resolve ctx_sub_ctx_lookup : mcpts.

(** *** Lemmas for [wf_typ_eq] *)

Fact wf_typ_eq_refl {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ A ≈ A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_refl : mcpts.

Lemma wf_typ_eq_sub_sorted {P : PtsSig} : forall {Δ : ctx P} {s A A'},
    {{ Δ ⊢ A ≈ A' : Sort@s }} ->
    forall Γ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_sub_sorted : mcpts.

Lemma wf_typ_sort_weaken {P : PtsSig} : forall {Γ : ctx P} {s A},
    {{ Γ ⊢ Sort@s ≈ Sort@s }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ Sort@s ≈ Sort@s }}.
Proof. mauto. Qed.

Lemma wf_typ_sort_sub {P} : forall {Γ Γ' : ctx P} {A σ},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A }} ->
    {{ Γ ⊢ A[σ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_sort_sub : mcpts.

Lemma wf_typ_eq_sub_unsorted {P : PtsSig} : forall {Δ : ctx P} {A A'},
    {{ Δ ⊢ A ≈ A' }} ->
    forall Γ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_sub_unsorted : mcpts.

Lemma typ_eq_sub_cong_typ1 {P : PtsSig} : forall {Δ : ctx P} {Γ A A' σ},
    {{ Δ ⊢ A ≈ A' }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] }}.
Proof. mauto. Qed.

Lemma typ_eq_sub_cong_typ2  {P} : forall {Δ : ctx P} {Γ A σ τ},
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof. mauto. Qed.

Lemma typ_eq_sub_compose_typ  {P : PtsSig} : forall {Ψ : ctx P} {Δ Γ A σ τ},
    {{ Ψ ⊢ A  }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve typ_eq_sub_cong_typ1 typ_eq_sub_cong_typ2 typ_eq_sub_compose_typ : mcpts.

Lemma typ_eq_sub_compose_weaken_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Δ ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] }}.
Proof with mautosolve 3.
  intros.  
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; [mautosolve 4 |].
  eapply typ_eq_sub_cong_typ2...
Qed.

#[export]
Hint Resolve typ_eq_sub_compose_weaken_extend_typ : mcpts.

Lemma typ_eq_sub_compose_weaken_id_extend_typ {P : PtsSig} : forall {Γ : ctx P} {A B M},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ A[Wk][Id,,M] ≈ A }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 2.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve typ_eq_sub_compose_weaken_id_extend_typ : mcpts.

Lemma typ_eq_sub_compose_double_weaken_double_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B M C N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Δ ⊢ B }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Δ, B ⊢ C }} ->
    {{ Γ ⊢ N : C[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, B, C ⊢s Wk : Δ, B }} by mauto 4.
  assert {{ Δ, B ⊢ A[Wk] }} by mauto 3.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply typ_eq_sub_cong_typ1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve typ_eq_sub_compose_double_weaken_double_extend_typ : mcpts.

Lemma typ_eq_sub_compose_double_weaken_id_double_extend_typ {P : PtsSig} : forall {Γ : ctx P} {A B M C N},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B ⊢ C }} ->
    {{ Γ ⊢ N : C[Id,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Γ }} by mauto 2.
  assert {{ Γ ⊢ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 3.
  assert {{ Γ ⊢ M : B[Id] }} by mauto 3.
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve typ_eq_sub_compose_double_weaken_id_double_extend_typ : mcpts.

Lemma typ_eq_typ_sub_sub {P : PtsSig} : forall {Γ : ctx P} {Δ Ψ σ τ s1},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ Sort@s1[σ][τ] ≈ Sort@s1 }}.
Proof.
  intros.
  transitivity {{{ Sort@s1[σ∘τ] }}}; mauto.
Qed.

#[export]
Hint Resolve typ_eq_typ_sub_sub : mcpts.
#[export]
Hint Rewrite -> @typ_eq_typ_sub_sub using mauto 4 : mcpts.

Lemma var_compose_subs {P : PtsSig} : forall {Γ : ctx P} {τ Δ σ Ψ A x},
    {{ Ψ ⊢ A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ #x : A[σ][τ] ∈ Γ }} ->
    {{ Γ ⊢ #x : A[σ∘τ] }}.
Proof.
  intros.
  assert {{ Δ ⊢ A[σ] }} by mauto 4.
  assert {{ Γ ⊢ A[σ][τ] }} by mauto 3.
  assert {{ Γ ⊢ A[σ∘τ] }} by mauto 3.
  eapply wf_conv; mauto 3.
Qed.

#[export]
Hint Resolve var_compose_subs : mcpts.

Lemma sub_lookup_var0 {P : PtsSig} : forall (Δ : ctx P) Γ σ M1 M2 B,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #0[σ,,M1,,M2] ≈ M2 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] }} by mauto 4.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 3.
  assert {{ Δ ⊢ B[Wk][σ,,M1] }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] }} by mauto 3.
  eapply wf_eq_conv; mauto 3.
  eapply wf_exp_eq_var_0_sub with (A := {{{ B[Wk] }}}); [| | econstructor]; mauto.
Qed.

Lemma id_sub_lookup_var0 {P : PtsSig} : forall (Γ : ctx P) M1 M2 B,
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


Lemma sub_lookup_var1 {P : PtsSig} : forall (Δ : ctx P) Γ σ M1 M2 B,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #1[σ,,M1,,M2] ≈ M1 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] }} by mauto 4.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 3.
  assert {{ Δ ⊢ B[Wk][σ,,M1] }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] }} by mauto 3.
  assert {{ Δ ⊢ B[σ]}} by mauto 4.
  assert {{ Δ ⊢ M2 : B[Wk][σ,,M1] }} by mauto 3.
  transitivity {{{ #0[σ,,M1] }}}; mauto 3.
Qed.

Lemma id_sub_lookup_var1 {P : PtsSig} : forall (Γ : ctx P) M1 M2 B,
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

Lemma exp_eq_var_1_sub_q_sigma {P : PtsSig} : forall {Γ : ctx P} {A B σ Δ},
    {{ Δ ⊢ B }} ->
    {{ Δ, B ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof with mautosolve 3.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s q σ : Δ, B }} by mauto 2.
  assert {{ ⊢ Γ, B[σ] }} by mauto 3.
  assert {{ ⊢ Γ, B[σ], A[q σ] }} by mauto 3.
  assert {{ Δ, B ⊢ B[Wk]  }} by mauto 4.
  assert {{ Δ ⊢ B }} by mauto 2.
  assert {{ Δ, B ⊢ #0 : B[Wk] }} by mauto 4.
  assert {{ Γ, B[σ] ⊢ A[q σ] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢s q σ∘Wk : Δ, B }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ∘Wk] }} by mauto 3.
  assert {{ Γ ⊢ B[σ]  }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk : Γ, B[σ] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[σ][Wk]  }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk]  }} by mauto 3.
  assert {{ Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk]  }} by (eapply typ_eq_sub_sub_compose_cong_typ; mauto 3).
  assert {{ Γ, B[σ], A[q σ] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk]  }} by (transitivity {{{ B[Wk][q σ][Wk] }}}; mauto 3).
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : B[σ][Wk][Wk] }} by (econstructor; mauto).
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : B[σ][Wk][Wk] }} by (econstructor; mauto).
  assert {{ Γ, B[σ] ⊢s σ∘Wk : Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0 : B[σ∘Wk] }} by mauto 3.
  assert {{ Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ∘Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ∘Wk][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ∘Wk][Wk] ≈ B[σ][Wk][Wk]  }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ][Wk][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk][Wk] }} by (do 2 etransitivity; mauto 2).
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk∘Wk : Γ }} by mauto 2.
  econstructor; mauto 4.
Qed.


(** Lemmas about judgments for types *)
Lemma wf_typ_sub_cong {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    forall Δ σ τ,
      {{ Δ ⊢s σ : Γ }} ->
      {{ Δ ⊢s τ : Γ }} ->
      {{ Δ ⊢s σ ≈ τ : Γ }} ->
      {{ Δ ⊢ A[σ] ≈ A[τ] }}.
Proof.
  induction 1;
    intros;
    assert {{ ⊢ Δ }} by mauto 3.
  - transitivity {{{ Sort@s }}}; mauto 3.
  - assert {{ Δ ⊢ A[σ] ≈ A[τ]  }} by mauto 3.
    mauto 3.
  - transitivity {{{ A[σ∘σ0] }}}; mauto 3.
    transitivity {{{ A[σ∘τ] }}}; mauto 3.
    eapply IHwf_typ; mauto 3.
Qed.

  
Lemma wf_exp_sort_sort_all_ctx {P} : forall {Γ Δ : ctx P} {s1 s2},
    {{ ⊢ Δ }} ->
    {{ Γ ⊢ Sort@s1 : Sort@s2 }} ->
    {{ Δ ⊢ Sort@s1 : Sort@s2 }}.
Proof.
  intros.
  assert (exists s3, Ax_typ P s1 s3 /\ {{ Γ ⊢ Sort@s3 ⊆ Sort@s2 }}) as [s3 []] by mauto 2.
  assert {{ Δ ⊢ Sort@s3 ⊆ Sort@s2 }} by admit.   (** Not convinced this is provable *)
  assert {{ Δ ⊢ Sort@s1 : Sort@s3 }} by mauto 2.
  eapply wf_exp_conv; mauto 2.
Abort.
  

(** *** Type Presuppositions *)

Lemma presup_exp_typ {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A }}.
Proof with mautosolve 3.
  induction 1; assert {{ ⊢ Γ }} by mauto 3; destruct_conjs; mauto 3.
  - enough {{ Γ ⊢s Id,,N : Γ, A }}...
Qed.

Lemma presup_exp {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ {{ Γ ⊢ A }}.
Proof.
  mauto 4 using presup_exp_typ.
Qed.


(* Lemma presup_typ {P : PtsSig} : forall {Γ : ctx P} {A}, *)
(*     {{ Γ ⊢ A }} -> *)
(*     {{ ⊢ Γ }}. *)
(* Proof. *)
(*   intros *. *)
(*   inversion_clear 1. *)
(*   - eassumption. *)
(*   - eapply presup_exp; mauto 2. *)
(*   - eapply presup_typ_ctx; mauto 2. *)
(* Qed. *)
  
(** *** Consistency Helper *)

Lemma no_closed_neutral {P : PtsSig} : forall {A : exp P} {W : ne P},
    ~ {{ ⋅ ⊢ W : A }}.
Proof.
  intros * H.
  dependent induction H; destruct W;
    try (simpl in *; congruence);
    autoinjections;
    intuition.
  inversion_by_head (@ctx_lookup P).
Qed.
#[export]
Hint Resolve no_closed_neutral : mcpts.
