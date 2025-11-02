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
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx';
    f_equal;
    intuition.
Qed.

Lemma ctx_decomp {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }} /\ (exists s, {{ Γ ⊢ A : Sort@s }}).
Proof with now eauto.
  inversion 1...
Qed.

#[export]
Hint Resolve ctx_decomp : mcpts.

Corollary ctx_decomp_left {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ , A }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> (exists s, {{ Γ ⊢ A : Sort@s }}).
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

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx {P : PtsSig} : forall {Γ : ctx P} {Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
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

(** *** Immediate Results of Context Presuppositions *)

(** Recover some rules we had before adding subtyping.
    Rest are recovered after presupposition lemmas (in SystemOpt). *)

Lemma wf_conv {P : PtsSig} : forall (Γ : ctx P) M A A',
    {{ Γ ⊢ M : A }} ->
    (** The next argument will be removed in SystemOpt *)
    {{ Γ ⊢ A' }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ M : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_conv : mcpts.

Lemma wf_sub_conv {P : PtsSig} : forall (Γ : ctx P) σ Δ Δ',
  {{ Γ ⊢s σ : Δ }} ->
  {{ ⊢ Δ ≈ Δ' }} ->
  {{ Γ ⊢s σ : Δ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_conv : mcpts.

Lemma wf_exp_eq_conv {P : PtsSig} : forall (Γ : ctx P) M M' A A',
   {{ Γ ⊢ M ≈ M' : A }} ->
   (** The next argument will be removed in SystemOpt *)
   {{ Γ ⊢ A' }} ->
   {{ Γ ⊢ A ≈ A' }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_conv : mcpts.

Lemma wf_sub_eq_conv {P : PtsSig} : forall (Γ : ctx P) σ σ' Δ Δ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_eq_conv : mcpts.

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
  induction 1; mauto 4.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.

(** *** Lemmas for [exp] of [{{{ Type@i }}}] *)

Lemma exp_sub_typ {P : PtsSig} : forall {Δ : ctx P} {Γ A σ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve exp_sub_typ : mcpts.

Lemma eq_exp_sub_typ {P: PtsSig} : forall {Δ : ctx P} {Γ A A' σ s},
    {{ Δ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve eq_exp_sub_typ : mcpts.


Lemma presup_ctx_lookup_typ {P : PtsSig} : forall {Γ : ctx P} {A x},
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    exists s, {{ Γ ⊢ A : Sort@s }}.
Proof with mautosolve 4.
  intros * HΓ.
  induction 1; inversion_clear HΓ;
    [eexists; mauto 4
    | assert (exists s, {{ Γ ⊢ A : Sort@s }}) as [] by eauto]; econstructor...
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mcpts.

Lemma exp_eq_sub_cong_typ1 {P : PtsSig} : forall {Δ : ctx P} {Γ A A' σ},
    {{ Δ ⊢ A ≈ A' }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

Lemma exp_eq_sub_cong_typ2' {P : PtsSig} : forall {Δ : ctx P} {Γ A σ τ},
    {{ Δ ⊢ A }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

Lemma exp_eq_sub_compose_typ {P : PtsSig} : forall {Ψ : ctx P} {Δ Γ A σ τ},
    {{ Ψ ⊢ A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }}.
Proof with mautosolve 3.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mcpts.

Lemma exp_eq_sub_compose_weaken_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Δ ⊢ B : Sort@s }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] }}.
Proof with mautosolve 3.
  intros.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; [mautosolve 4 |].
  eapply exp_eq_sub_cong_typ2'...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mcpts.

Lemma exp_eq_sub_compose_weaken_id_extend_typ {P : PtsSig} : forall {Γ : ctx P} {A s B M},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B : Sort@s }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ A[Wk][Id,,M] ≈ A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ B[Id] : Sort@s }} by mauto 4.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ M : B[Id] }} by (eapply wf_conv; mauto 2).
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mcpts.

Lemma exp_eq_sub_compose_double_weaken_double_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ A s1 B M s2 C N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A }} ->
    {{ Δ ⊢ B : Sort@s1 }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Δ, B ⊢ C : Sort@s2 }} ->
    {{ Γ ⊢ N : C[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ, B ⊢s Wk : Δ }} by mauto 4.
  assert {{ Δ, B, C ⊢s Wk : Δ, B }} by mauto 4.
  transitivity {{{ A[Wk][Wk][σ,,M,,N] }}}; [eapply exp_eq_sub_cong_typ1; mautosolve 3 |].
  transitivity {{{ A[Wk][σ,,M] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_typ : mcpts.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_typ {P : PtsSig} : forall {Γ : ctx P} {A s1 B M s2 C N},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ B : Sort@s1 }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B ⊢ C : Sort@s2 }} ->
    {{ Γ ⊢ N : C[Id,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ B[Id] : Sort@s1 }} by mauto 4.
  assert {{ Γ ⊢ B ≈ B[Id] }} by mauto 4.
  assert {{ Γ ⊢ M : B[Id] }} by (eapply wf_conv; mauto 2).
  transitivity {{{ A[Id] }}}...
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_typ : mcpts.

Lemma exp_eq_typ_sub_sub {P : PtsSig} : forall {Γ : ctx P} {Δ Ψ σ τ s},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ Sort@s[σ][τ] ≈ Sort@s }}.
Proof. mauto. Qed.

#[export]
Hint Resolve exp_eq_typ_sub_sub : mcpts.
#[export]
Hint Rewrite -> @exp_eq_sub_compose_typ @exp_eq_typ_sub_sub using mauto 4 : mcpts.

Lemma vlookup_0_typ {P : PtsSig} : forall {Γ : ctx P} {s1 s2},
    Ax P s1 s2 ->
    {{ ⊢ Γ }} ->
    {{ Γ, Sort@s1 ⊢ #0 : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv; mauto 4.
  econstructor...
Qed.

Lemma vlookup_1_typ {P : PtsSig} : forall {Γ : ctx P} {s1 s2 A s3},
    Ax P s1 s2 ->
    {{ Γ, Sort@s1 ⊢ A : Sort@s3 }} ->
    {{ Γ, Sort@s1, A ⊢ #1 : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, Sort@s1 ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Sort@s1, A ⊢s Wk : Γ, Sort@s1 }} by mauto 4.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mcpts.

Lemma exp_sub_typ_helper {P : PtsSig} : forall {Γ : ctx P} {σ Δ M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢ M : Sort@s[σ] }}.
Proof.
  intros.
  do 2 (econstructor; mauto 4).
Qed.

#[export]
Hint Resolve exp_sub_typ_helper : mcpts.

Lemma exp_eq_var_0_sub_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s1 }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv with (A := {{{ Sort@s1[σ] }}}); mauto 3.
  econstructor...
Qed.

Lemma exp_eq_var_1_sub_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ A s1 M s2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : Sort@s2[Wk] ∈ Δ }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : Sort@s2 }}.
Proof with mautosolve 4.
  inversion 4 as [? Δ'|]; subst.
  assert {{ ⊢ Δ' }} by mauto 4.
  assert {{ Δ', Sort@s2 ⊢s Wk : Δ' }} by mauto 4.
  eapply wf_exp_eq_conv...
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
  assert {{ ⊢ Γ' }} by mauto.
  assert {{ Γ', Sort@s ⊢s Wk : Γ' }} by mauto 4.
  assert {{ Γ', Sort@s, A ⊢s Wk : Γ', Sort@s }} by mauto 4.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_var_0_weaken_typ : mcpts.

Lemma sub_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s1 }} ->
    {{ Γ ⊢s σ,,M : Δ, Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_extend_typ : mcpts.

Lemma sub_eq_extend_cong_typ {P : PtsSig} : forall {Γ : ctx P} {σ σ' Δ M M' s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : Sort@s1 }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
  eapply wf_exp_eq_conv...
Qed.

Lemma sub_eq_extend_compose_typ {P : PtsSig} : forall {Γ : ctx P} {τ Γ' σ Γ'' A s1 s2 s3 M},
    Ax P s2 s3 ->
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A : Sort@s1 }} ->
    {{ Γ' ⊢ M : Sort@s2 }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', Sort@s2 }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

Lemma sub_eq_p_extend_typ {P : PtsSig} : forall {Γ : ctx P} {σ Γ' M s1 s2},
    Ax P s1 s2 ->
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : Sort@s1 }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ Sort@s1 : Sort@s2 }} by mauto.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_typ sub_eq_extend_compose_typ sub_eq_p_extend_typ : mcpts.


Lemma exp_eq_sub_sub_compose_cong_typ {P : PtsSig} : forall {Γ : ctx P} {Δ Δ' Ψ σ τ σ' τ' A},
    {{ Ψ ⊢ A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] }} by mauto.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mcpts.


(** *** Other Tedious Lemmas *)

Lemma sub_eq_weaken_var0_id {P : PtsSig} : forall {Γ : ctx P} {A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof with mautosolve 4.
  intros * ?.
  assert {{ ⊢ Γ, A }} by mauto 3.
  assert {{ Γ, A ⊢s (Wk∘Id),,#0[Id] ≈ Id : Γ, A }} by mauto.
  assert {{ Γ, A ⊢s Wk ≈ Wk∘Id : Γ }} by mauto.
  enough {{ Γ, A ⊢ #0 ≈ #0[Id] : A[Wk] }}...
Qed.

#[export]
Hint Resolve sub_eq_weaken_var0_id : mcpts.
#[export]
Hint Rewrite -> @sub_eq_weaken_var0_id using mauto 4 : mcpts.

Lemma exp_eq_sub_sub_compose_cong {P : PtsSig} : forall {Γ : ctx P} {Δ Δ' Ψ σ τ σ' τ' M A s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Ψ ⊢ M : A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Sort@s }} by (eapply wf_exp_eq_conv; mauto).
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mcpts.

Lemma ctxeq_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {Δ A x},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ #x : A ∈ Γ }} ->
    exists B s,
      {{ #x : B ∈ Δ }} /\
        {{ Γ ⊢ A ≈ B : Sort@s }} /\
        {{ Δ ⊢ A ≈ B : Sort@s }} /\
        {{ Δ ⊢ A : Sort@s }}.
Proof with mautosolve.
  intros * HΓΔ Hx; gen Δ.
  induction Hx as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? ? HΓΔ'];
    [|specialize (IHHx _ HΓΔ')]; destruct_conjs; repeat eexists...
Qed.

#[export]
Hint Resolve ctxeq_ctx_lookup : mcpts.

Lemma sub_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv with (A := A); mauto.
Qed.

#[export]
Hint Resolve sub_id_on_typ : mcpts.

Lemma sub_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_id_extend : mcpts.

Lemma sub_eq_id_on_typ {P : PtsSig} : forall {Γ : ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv; mauto.
Qed.

#[export]
Hint Resolve sub_eq_id_on_typ : mcpts.

Lemma sub_eq_id_extend_cong {P : PtsSig} : forall {Γ : ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_id_extend_cong : mcpts.

Lemma sub_eq_p_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_eq_p_id_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_p_id_extend using mauto 4 : mcpts.

Lemma sub_q {P : PtsSig} : forall {Γ : ctx P} {A s σ Δ},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s q σ : Δ, A }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ] : Sort@s }} by mauto 4.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  econstructor; mauto 3.
  eapply wf_conv; mauto.
Qed.

Lemma sub_q_typ {P : PtsSig} : forall {Γ σ Δ s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, Sort@s1 ⊢s q σ : Δ, Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ, Sort@s1 ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Sort@s1 ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, Sort@s1 ⊢ #0 : Sort@s1 }}...
Qed.

#[export]
Hint Resolve sub_q sub_q_typ : mcpts.

Lemma sub_eq_id_extend_compose_sigma {P : PtsSig} : forall {Γ : ctx P} {M A σ Δ s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ⊢s Id : Δ }} by mauto.
  assert {{ Δ ⊢ M : A[Id] }} by mauto.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : A[Id][σ] }} by mauto.
  assert {{ Γ ⊢ A[Id][σ] ≈ A[Id∘σ] : Sort@s }} by (eapply wf_exp_eq_conv; mauto).
  assert {{ Γ ⊢ M[σ] : A[Id∘σ] }} by (eapply wf_conv; mauto 4).
  enough {{ Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve sub_eq_id_extend_compose_sigma : mcpts.

Lemma sub_eq_sigma_compose_weak_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A s σ Δ},
    {{ Γ ⊢ A : Sort@s }} ->
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

Lemma sub_eq_q_sigma_id_extend {P : PtsSig} : forall {Γ : ctx P} {M A s σ Δ},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ A[σ] : Sort@s }} by mauto.
  assert {{ Γ ⊢ M : A[σ] }} by mauto.
  assert {{ Γ ⊢s Id,,M : Γ, A[σ] }} by mauto.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by (eapply wf_conv; mauto 4).
  assert {{ Γ ⊢s q σ∘(Id,,M) ≈ ((σ∘Wk)∘(Id,,M)),,#0[Id,,M] : Δ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }} by mauto.
  assert {{ Γ ⊢ M : A[σ][Id] }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ][Id] }} by mauto 3.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ] }} by mauto.
  enough {{ Γ ⊢ #0[Id,,M] ≈ M : A[(σ∘Wk)∘(Id,,M)] }} by mauto.
  eapply wf_exp_eq_conv; mauto.
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_id_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_id_extend using mauto 4 : mcpts.


Lemma sub_eq_q_sigma_sigma0_extend {P} : forall {Γ1 Γ2 Γ3 : ctx P} {A s σ σ0 M},
    {{ Γ3 ⊢ A : Sort@s }} ->
    {{ Γ2 ⊢s σ : Γ3 }} ->
    {{ Γ1 ⊢s σ0 : Γ2 }} ->
    {{ Γ1 ⊢ M : A[σ][σ0] }} ->
    {{ Γ1 ⊢s (q σ)∘(σ0,,M) ≈ (σ∘σ0),,M : Γ3, A }}.
Proof.
  intros.
  assert {{ Γ2, A[σ] ⊢s σ ∘ Wk : Γ3 }} by mauto.
  assert {{ Γ2, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Γ2, A[σ] ⊢ A[σ][Wk] ≈ A[σ∘Wk] }} by mauto.
  assert {{ Γ2, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto 4.
  assert {{ Γ1 ⊢s (q σ) ∘ (σ0,,M) ≈ ((σ∘Wk)∘(σ0,,M)),,#0[σ0,,M] : Γ3, A }} by mauto 4.
  assert {{ Γ1 ⊢s (σ∘Wk)∘(σ0,,M) ≈ σ∘(Wk∘(σ0,,M)) : Γ3 }} by (econstructor; mauto 3).
  assert {{ Γ1 ⊢s σ∘(Wk∘(σ0,,M)) ≈ σ∘σ0 : Γ3 }} by mauto.
  assert {{ Γ1 ⊢s (σ ∘ Wk) ∘ (σ0,,M) ≈ σ∘σ0 : Γ3 }} by (etransitivity; mauto).
  assert {{ Γ1 ⊢ #0[σ0,,M] ≈ M : A[σ][σ0] }} by mauto.
  assert {{ Γ1 ⊢ A[σ][σ0] ≈ A[(σ∘Wk)∘(σ0,,M)] }} by (econstructor; mauto).
  assert {{ Γ1 ⊢s (σ∘Wk)∘(σ0,,M),,#0[σ0,,M] ≈ σ∘σ0,,M : Γ3, A }}.
  {
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv with (A := {{{ A[σ][σ0] }}}); mauto.
    econstructor; mauto.
  }
  do 2 etransitivity; mauto.
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_sigma0_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_sigma0_extend using mauto 4 : mcpts.

Lemma sub_eq_p_q_sigma {P : PtsSig} : forall {Γ : ctx P} {A s σ Δ},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  enough {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  eapply wf_conv; mauto.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma : mcpts.


(** *** Lemmas for [wf_typ_eq] *)

Fact wf_typ_eq_refl {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ A ≈ A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_refl : mcpts.

Lemma wf_typ_eq_sub {P : PtsSig} : forall {Δ : ctx P} {A A'},
    {{ Δ ⊢ A ≈ A' }} ->
    forall Γ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_typ_eq_sub : mcpts.

Lemma wf_subtyp_univ_weaken {P : PtsSig} : forall {Γ : ctx P} {s A},
    {{ Γ ⊢ Sort@s ≈ Sort@s }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ Sort@s ≈ Sort@s }}.
Proof. mauto. Qed.

Lemma var_compose_subs {P : PtsSig} : forall {Γ : ctx P} {τ Δ σ Ψ s A x},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ #x : A[σ][τ] ∈ Γ }} ->
    {{ Γ ⊢ #x : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve var_compose_subs : mcpts.

Lemma sub_lookup_var0 {P : PtsSig} : forall (Δ : ctx P) Γ σ M1 M2 B s,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Sort@s }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #0[σ,,M1,,M2] ≈ M2 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] : Sort@s }} by mauto.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] }}.
  {
    transitivity {{{ B[Wk∘(σ,,M1)] }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
    - eapply exp_eq_sub_cong_typ2'; mauto 4.
  }
  eapply wf_exp_eq_conv;
    [eapply wf_exp_eq_var_0_sub with (A := {{{ B[Wk] }}}) | |];
    mauto 4.
Qed.

Lemma id_sub_lookup_var0 {P : PtsSig} : forall (Γ : ctx P) M1 M2 B s,
    {{ Γ ⊢ B : Sort@s }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var0 | |];
    mauto 3.
Qed.

Lemma sub_lookup_var1 {P : PtsSig} : forall (Δ : ctx P) Γ σ M1 M2 B s,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Sort@s }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #1[σ,,M1,,M2] ≈ M1 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] : Sort@s }} by mauto.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] }}.
  {
    transitivity {{{ B[Wk∘(σ,,M1)] }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
    - eapply exp_eq_sub_cong_typ2'; mauto 4.
  }
  transitivity {{{ #0[σ,,M1] }}}.
  - eapply wf_exp_eq_conv;
      [eapply wf_exp_eq_var_S_sub | |];
      mauto 4.
  - eapply wf_exp_eq_conv;
    [eapply wf_exp_eq_var_0_sub with (A := B) | |];
    mauto.
Qed.

Lemma id_sub_lookup_var1 {P : PtsSig} : forall (Γ : ctx P) M1 M2 B s,
    {{ Γ ⊢ B : Sort@s }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var1 | |];
    mauto 3.
Qed.

Lemma exp_eq_var_1_sub_q_sigma {P : PtsSig} : forall {Γ : ctx P} {A s1 B s2 σ Δ},
    {{ Δ ⊢ B : Sort@s1 }} ->
    {{ Δ, B ⊢ A : Sort@s2 }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s q σ : Δ, B }} by mauto 2.
  assert {{ ⊢ Γ, B[σ] }} by mauto 3.
  assert {{ ⊢ Γ, B[σ], A[q σ] }} by mauto 3.
  assert {{ Δ, B ⊢ B[Wk] : Sort@s1 }} by mauto 4.
  assert {{ Δ, B ⊢ #0 : B[Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] : Sort@s2 }} by (eapply wf_exp_eq_conv; mauto 4).
  assert {{ Γ, B[σ], A[q σ] ⊢s q σ∘Wk : Δ, B }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ∘Wk] }} by mauto 3.
  assert {{ Γ ⊢ B[σ] : Sort@s1 }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk : Γ, B[σ] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[σ][Wk] : Sort@s1 }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk] : Sort@s1 }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk] }} by (eapply exp_eq_sub_sub_compose_cong_typ; mauto 3).  
  assert {{ Γ, B[σ] ,A[q σ] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk] }} by (transitivity {{{ B[Wk][q σ][Wk] }}}; mauto 3).
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : B[σ][Wk][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : B[σ][Wk][Wk] }} by mauto 4. 
  assert {{ Γ, B[σ] ⊢s σ∘Wk : Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ∘Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ∘Wk][Wk] ≈ B[σ][Wk][Wk] }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk][Wk] }} by (do 2 etransitivity; mauto 2).
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk∘Wk] : Sort@s1 }} by mauto 2.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

(** *** Type Presuppositions *)

Lemma presup_exp_typ {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A }}.
Proof.
  induction 1; assert {{ ⊢ Γ }} by mauto 3; destruct_conjs; mauto 3.

  - enough {{ Γ ⊢s Id,,N : Γ, A }}; mauto 3.
  - assert (exists s, {{ Γ ⊢ A : Sort@s }}) by mauto 2.
    destruct_conjs; mauto.
Qed.

Lemma presup_exp {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ {{ Γ ⊢ A }}.
Proof.
  mauto 4 using presup_exp_typ.
Qed.

Lemma presup_typ {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ ⊢ Γ }}.
Proof.
  intros *.
  inversion_clear 1; mauto.
Qed.


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


