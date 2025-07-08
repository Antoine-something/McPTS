From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Import Definitions.

(** ** Basic Context Properties *)

Lemma ctx_lookup_lt {P : PtsSig} : forall {Γ : Ctx P} {A x s},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.
#[export]
Hint Resolve ctx_lookup_lt : mctt.

Lemma functional_ctx_lookup_typ {P : PtsSig} : forall {Γ : Ctx P} {A A' x s s'},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ #x : A' :: Sort@s' ∈ Γ }} ->
    A = A'.
Proof with mautosolve.
  intros * Hx Hx'; gen s' A'.
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx';
    f_equal;
    intuition.
Qed.

Lemma functional_ctx_lookup_st {P : PtsSig} : forall {Γ : Ctx P} {A A' x s s'},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ #x : A' :: Sort@s' ∈ Γ }} ->
    s = s'.
Proof with mautosolve.
  intros * Hx Hx'; gen s' A'. dependent induction Hx; intros.
  - inversion_clear Hx'. auto. 
  - inversion_clear Hx'; auto.
    eapply IHHx; mauto.
Qed.

Lemma functional_ctx_lookup {P : PtsSig} : forall {Γ : Ctx P} {A A' x s s'},
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ #x : A' :: Sort@s' ∈ Γ }} ->
    A = A' /\ s = s'.
Proof.
  intros; split.
  - eapply functional_ctx_lookup_typ; mauto.
  - eapply functional_ctx_lookup_st; mauto.
Qed.

Lemma ctx_decomp {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ, A :: Sort@s }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A : Sort@s }}.
Proof with now eauto.
  inversion 1...
Qed.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ , A :: Sort@s }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Γ : Ctx P} {A s}, {{ ⊢ Γ, A :: Sort@s }} -> {{ Γ ⊢ A : Sort@s }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.



(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; destruct_pairs; econstructor; mauto.
Qed.

Corollary presup_ctx_eq_left {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

Corollary presup_ctx_eq_right {P : PtsSig} : forall {Γ Δ : Ctx P}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_ctx_eq...
Qed.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mcpts.

Lemma presup_sub {P : PtsSig}: forall {Γ Δ : Ctx P} {σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; mauto; destruct_pairs; mauto.
  - inversion H; mauto.
  - econstructor; assumption.
Qed.

Corollary presup_sub_left {P : PtsSig} : forall {Γ Δ : Ctx P} {σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

Corollary presup_sub_right {P : PtsSig} : forall {Γ Δ : Ctx P} {σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub...
Qed.

#[export]
Hint Resolve presup_sub presup_sub_left presup_sub_right : mcpts.

(** With [presup_sub], we can prove similar for [exp]. *)

Lemma presup_exp_ctx {P : PtsSig} : forall {Γ : Ctx P} {M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_ctx : mcpts.

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx {P : PtsSig} : forall {Γ Δ : Ctx P} {σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof with mautosolve.
  induction 1; split; destruct_pairs; mauto 2; econstructor; mauto 2.
Qed.

Corollary presup_sub_eq_ctx_left {P : PtsSig} : forall {Γ Δ : Ctx P} {σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

Corollary presup_sub_eq_ctx_right {P : PtsSig} : forall {Γ Δ : Ctx P} {σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Δ }}.
Proof with easy.
  intros * ?%presup_sub_eq_ctx...
Qed.

#[export]
Hint Resolve presup_sub_eq_ctx presup_sub_eq_ctx_left presup_sub_eq_ctx_right : mcpts.

Lemma presup_exp_eq_ctx {P : PtsSig} : forall {Γ : Ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1...
Qed.

#[export]
Hint Resolve presup_exp_eq_ctx : mcpts.

(** *** Immediate Results of Context Presuppositions *)

Lemma wf_conv {P : PtsSig} : forall (Γ : Ctx P) M A s A',
    {{ Γ ⊢ M : A }} ->
    (** The next argument will be removed in SystemOpt *)
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  econstructor; mauto.
  econstructor; mauto.  
Qed.

#[export]
Hint Resolve wf_conv : mcpts.

Lemma wf_sub_conv {P : PtsSig} : forall (Γ : Ctx P) σ Δ Δ',
  {{ Γ ⊢s σ : Δ }} ->
  {{ ⊢ Δ ≈ Δ' }} ->
  {{ Γ ⊢s σ : Δ' }}.
Proof.
  intros.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_sub_conv : mcpts.

Lemma wf_exp_eq_conv {P : PtsSig} : forall (Γ : Ctx P) M M' A A' i,
   {{ Γ ⊢ M ≈ M' : A }} ->
   (** The next argument will be removed in SystemOpt *)
   {{ Γ ⊢ A' : Sort@i }} ->
   {{ Γ ⊢ A ≈ A' : Sort@i }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof. 
  intros.
  eapply eq_exp_conv; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_conv : mcpts.

Lemma wf_sub_eq_conv {P : PtsSig} : forall (Γ : Ctx P) σ σ' Δ Δ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof.
  intros.
  eapply eq_sub_conv; mauto.
Qed.

#[export]
Hint Resolve wf_sub_eq_conv : mcpts.

Add Parametric Morphism {P : PtsSig} (Γ : Ctx P) : (eq_sub Γ)
    with signature eq_ctx ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  intros Δ Δ' H **; split; [| symmetry in H]; mauto.
Qed.


Lemma ctx_eq_refl {P : PtsSig} : forall {Γ : Ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ≈ Γ }}.
Proof.
  induction 1; econstructor; mauto 4.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve ctx_eq_refl : mcpts.


(** *** Lemmas for [exp] of [{{{ Type@i }}}] *)

Lemma exp_sub_typ {P : PtsSig} : forall {Δ Γ : Ctx P} {A σ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ]A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  econstructor; mauto 3.
  econstructor...
  econstructor; mauto.
Qed.

#[export]
Hint Resolve exp_sub_typ : mcpts.

Lemma presup_ctx_lookup_typ {P : PtsSig} : forall {Γ : Ctx P} {A x s},
    {{ ⊢ Γ }} ->
    {{ #x : A :: Sort@s ∈ Γ }} ->
    {{ Γ ⊢ A : Sort@s }}.
Proof with mautosolve 4.
  intros * HΓ.  
  induction 1; inversion_clear HΓ; eapply exp_sub_typ; mauto; econstructor; econstructor; assumption.
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mcpts.


Lemma exp_eq_sub_cong_typ1 {P : PtsSig} : forall {Δ Γ : Ctx P} {A A' σ s},
    {{ Δ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ]A ≈ [σ]A' : Sort@s }}.
Proof with mautosolve 3.
  intros.
  eapply eq_exp_conv.
  eapply eq_exp_cong_clo.
  econstructor; mauto.
  mauto.
  econstructor; mauto.
Qed.

Lemma exp_eq_sub_cong_typ2' {P : PtsSig} : forall {Δ Γ : Ctx P} {A σ τ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ [σ]A ≈ [τ]A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  eapply eq_exp_conv; mauto.
  eapply eq_exp_cong_clo; mauto.
  eapply eq_exp_refl; mauto.
  econstructor; mauto.
Qed.

Lemma exp_eq_sub_compose_typ {P : PtsSig} : forall {Ψ Δ Γ : Ctx P} {A σ τ s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s τ : Ψ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ][τ]A ≈ [σ∘τ]A : Sort@s }}.
Proof with mautosolve 3.
  intros.
  eapply eq_exp_conv; mauto.
  eapply eq_exp_sym.
  eapply eq_exp_prop_comp; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mcpts.

Lemma exp_eq_sub_compose_weaken_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 A s2 B M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : [σ]B }} ->
    {{ Γ ⊢ [σ,,M][Wk]A ≈ [σ]A : Sort@s1 }}.
Proof with mautosolve 3.
  intros.
  eapply eq_exp_conv.
  assert ({{ Γ ⊢ [σ,,M][Wk]A ≈ [(σ,,M) ∘ Wk]A : [(σ,,M) ∘ Wk]Sort@s1}}).
  {
    eapply eq_exp_sym.
    eapply eq_exp_prop_comp; mauto; econstructor; mauto.
    econstructor; mauto.
  }
  eapply eq_exp_trans; mauto.
  eapply eq_exp_cong_clo; mauto.
  econstructor; mauto.
  econstructor; mauto.
  eapply eq_exp_refl; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mcpts.


Lemma exp_eq_sub_compose_weaken_id_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {s1 A s2 B M},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ [Id,,M][Wk]A ≈ A : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ [Id,,M][Wk]A ≈ [Id]A : Sort@s1 }}.
  {
    eapply exp_eq_sub_compose_weaken_extend_typ; mauto.
    econstructor; mauto.
    eapply wf_exp_conv; mauto.
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢ [Id]A ≈ A : Sort@s1}}.
  {
    econstructor; mauto.
  }
  eapply eq_exp_trans; mauto.
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mcpts.


Lemma exp_eq_sub_compose_double_weaken_double_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 A s2 B M s3 C N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : [σ]B }} ->
    {{ Δ, B :: Sort@s2 ⊢ C : Sort@s3 }} ->
    {{ Γ ⊢ N : [σ,,M]C }} ->
    {{ Γ ⊢ [σ,,M,,N][Wk∘Wk]A ≈ [σ]A : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ, B::Sort@s2 ⊢s Wk : Δ }} by (econstructor; mauto 2).
  assert {{ Δ, B::Sort@s2, C::Sort@s3 ⊢s Wk : Δ, B::Sort@s2 }}.
  {
    econstructor; mauto 2.
    econstructor; mauto 2.
  }
  transitivity {{{ [(σ,,M,,N)∘(Wk∘Wk)]A }}}.
  symmetry.
  eapply eq_exp_conv; mauto 2.
  eapply eq_exp_prop_comp; econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  eapply eq_exp_conv; mauto 2.
  eapply eq_exp_cong_clo; mauto 2.
  transitivity {{{ ((σ,,M,,N)∘Wk)∘Wk }}}.
  symmetry.
  eapply eq_sub_prop_assoc.
  econstructor; mauto 2.
  econstructor; mauto 2.
  mauto 2.
  mauto 2.
  transitivity {{{ (σ,,M)∘Wk }}}.
  eapply eq_sub_cong_comp; econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
  eapply eq_exp_refl; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2; econstructor; mauto 2.
  econstructor; mauto 2.  
Qed.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_typ : mcpts.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {s1 A s2 B M s3 C N},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B :: Sort@s2 ⊢ C : Sort@s3 }} ->
    {{ Γ ⊢ N : [Id,,M]C }} ->
    {{ Γ ⊢ [Id,,M,,N][Wk∘Wk]A ≈ A : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ [Id]B : Sort@s2 }} by ( eapply wf_exp_conv; mauto 2; econstructor; mauto 2; econstructor; mauto 2).
  assert {{ Γ ⊢ B ≈ [Id]B }} by (symmetry; econstructor; mauto 2; econstructor; mauto 2).
  assert {{ Γ ⊢ M : [Id]B }} by (econstructor; mauto 2).  
  transitivity {{{ [Id]A }}}.
  eapply exp_eq_sub_compose_double_weaken_double_extend_typ.
  econstructor; mauto 2.
  mauto 2.
  apply H0.
  mauto 2.
  mauto 2.
  mauto 2.
  econstructor; mauto 2.
Qed.  

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_typ : mcpts.

Lemma exp_eq_typ_sub_sub {P : PtsSig} : forall {Γ Δ Ψ σ τ s1 s2},
    Ax P s1 s2 ->
    {{ Δ ⊢s τ : Ψ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ [σ][τ]Sort@s1 ≈ Sort@s1 : Sort@s2 }}.
Proof.
  intros; econstructor; mauto.
  econstructor; mauto.
  assert {{ Γ ⊢ [σ][τ]Sort@s1 ≈ [σ ∘ τ] Sort@s1 : Sort@s2 }}.
  {
    econstructor; mauto.
    eapply eq_exp_conv; mauto.
    eapply eq_exp_prop_comp; mauto.
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  eapply eq_exp_trans; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve exp_eq_typ_sub_sub : mcpts.
#[export]
Hint Rewrite -> @exp_eq_sub_compose_typ @exp_eq_typ_sub_sub using mauto 4 : mcpts.


Lemma vlookup_0_typ {P : PtsSig} : forall {Γ : Ctx P} {s1 s2},
    Ax P s1 s2 -> 
    {{ ⊢ Γ }} ->
    {{ Γ, Sort@s1 :: Sort@s2 ⊢ #0 : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv; mauto 4.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

Lemma vlookup_1_typ {P : PtsSig} : forall {Γ : Ctx P} {s1 s2 A s3},
    Ax P s1 s2 ->
    {{ Γ, Sort@s1 :: Sort@s2 ⊢ A : Sort@s3 }} ->
    {{ Γ, Sort@s1 :: Sort@s2, A :: Sort@s3 ⊢ #1 : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ, Sort@s1 :: Sort@s2 ⊢s Wk : Γ }} by (econstructor; mauto 4).
  assert {{ Γ, Sort@s1 :: Sort@s2, A :: Sort@s3 ⊢s Wk : Γ, Sort@s1 :: Sort@s2 }}.
  {
    econstructor; mauto.
    econstructor; mauto.
  }
  eapply wf_exp_conv; mauto.
  econstructor; mauto.  
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mcpts.

Lemma exp_sub_typ_helper {P : PtsSig} : forall {Γ : Ctx P} {σ Δ M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s }} ->
    {{ Γ ⊢ M : [σ]Sort@s }}.
Proof.
  intros.
  econstructor; mauto.
  eapply eq_typ_sym; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve exp_sub_typ_helper : mcpts.

Lemma exp_eq_var_0_sub_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ M s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s1 }} ->
    {{ Γ ⊢ [σ,,M]#0 ≈ M : Sort@s1 }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv; mauto 3; econstructor; mauto.
  do 2 (econstructor; mauto).
Qed.

Lemma exp_eq_var_1_sub_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ A s1 M s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢ M : [σ]A }} ->
    {{ #0 : [Wk]Sort@s2 :: Sort@s3 ∈ Δ }} ->
    {{ Γ ⊢ [σ,,M]#1 ≈ [σ]#0 : Sort@s2 }}.
Proof with mautosolve 4.
  inversion 4 as [? ? Δ'|]; subst.
  assert {{ ⊢ Δ' }} by (eapply ctx_decomp_left; mauto 2).
  assert {{ Δ', Sort@s2::Sort@s3 ⊢s Wk : Δ' }} by (econstructor; mauto 2).
  eapply eq_exp_conv; mauto 2.
  eapply eq_exp_prop_var_su; mauto 2.
  econstructor; mauto 2.
  transitivity {{{ [σ]Sort@s2 }}}; econstructor; mauto 2.
  econstructor; mauto 2.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve exp_eq_var_0_sub_typ exp_eq_var_1_sub_typ : mcpts.
#[export]
Hint Rewrite -> @exp_eq_var_0_sub_typ @exp_eq_var_1_sub_typ : mcpts.

Lemma exp_eq_var_0_weaken_typ {P : PtsSig} : forall {Γ : Ctx P} {A s1 s2 s3},
    {{ ⊢ Γ, A :: Sort@s1 }} ->
    {{ #0 : [Wk]Sort@s2 :: Sort@s3 ∈ Γ }} ->
    {{ Γ, A :: Sort@s1 ⊢ [Wk]#0 ≈ #1 : Sort@s2 }}.
Proof with mautosolve 3.
  inversion_clear 1.
  inversion 1 as [? ? Γ'|]; subst.
  assert {{ ⊢ Γ' }} by (eapply ctx_decomp_left; mauto 2).
  assert {{ Γ', Sort@s2::Sort@s3 ⊢s Wk : Γ' }} by (econstructor; mauto 2).
  assert {{ Γ', Sort@s2::Sort@s3, A::Sort@s1 ⊢s Wk : Γ', Sort@s2::Sort@s3 }}.
  {
    econstructor; mauto 2.
    econstructor; mauto 2.
  }  
  eapply wf_exp_eq_conv; mauto 2.
  
Admitted.


#[export]
Hint Resolve exp_eq_var_0_weaken_typ : mcpts.

Lemma sub_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ M s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Sort@s1 }} ->
    {{ Γ ⊢s σ,,M : Δ, Sort@s1 :: Sort@s2 }}.
Proof with mautosolve 4.
  intros.
  do 2 (econstructor; mauto).
Qed.

#[export]
Hint Resolve sub_extend_typ : mcpts.

Lemma sub_eq_extend_cong_typ {P : PtsSig} : forall {Γ σ σ' Δ M M' s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : Sort@s1 }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, Sort@s1 :: Sort@s2 }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto.
  econstructor; mauto.
  eapply eq_exp_conv; mauto.
  eapply eq_typ_sym; econstructor; mauto.
Qed.

Lemma sub_eq_extend_compose_typ {P : PtsSig} : forall {Γ τ Γ' σ Γ'' (*A s1*) M s2 s3},
    Ax P s2 s3 ->
    {{ Γ' ⊢s σ : Γ'' }} ->
(*    {{ Γ'' ⊢ A : Sort@s1 }} -> *)   (* Why is this premise here *)
    {{ Γ' ⊢ M : Sort@s2 }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s τ∘(σ,,M) ≈ (τ∘σ),,[τ]M : Γ'', Sort@s2::Sort@s3 }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto.
  econstructor; mauto.
Qed.


Lemma sub_eq_p_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Γ' M s1 s2},
    Ax P s1 s2 ->
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : Sort@s1 }} ->
    {{ Γ' ⊢s (σ,,M)∘Wk ≈ σ : Γ }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_eq_extend_cong_typ sub_eq_extend_compose_typ sub_eq_p_extend_typ : mcpts.


Lemma exp_eq_sub_sub_compose_cong_typ {P : PtsSig} : forall {Γ : Ctx P} {Δ Δ' Ψ σ τ σ' τ' A s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s τ∘σ ≈ τ'∘σ' : Ψ }} ->
    {{ Γ ⊢ [τ][σ]A ≈ [τ'][σ']A : Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ [τ][σ]A ≈ [τ∘σ]A : Sort@s }} by mauto.
  assert {{ Γ ⊢ [τ∘σ]A ≈ [τ'∘σ']A : Sort@s }}.
  {
    eapply eq_exp_conv; mauto.
    eapply eq_exp_cong_clo; mauto.
    eapply eq_exp_refl; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢ [τ'∘σ']A ≈ [τ'][σ']A : Sort@s }} by (econstructor; mauto).
  eapply eq_exp_trans; mauto.
  eapply eq_exp_trans; mauto.  
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mcpts.


(** *** Other Tedious Lemmas *)

Lemma sub_eq_weaken_var0_id {P : PtsSig} : forall {Γ : Ctx P} {A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ, A::Sort@s ⊢s Wk,,#0 ≈ Id : Γ, A::Sort@s }}.
Proof with mautosolve 4.
  intros * ?.
  assert {{ ⊢ Γ, A::Sort@s }} by (econstructor; mauto).
  assert {{ Γ, A::Sort@s ⊢s (Id∘Wk),,[Id]#0 ≈ Id : Γ, A::Sort@s }}.
  {
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.    
  }
  assert {{ Γ, A::Sort@s ⊢s Wk ≈ Id∘Wk : Γ }}.
  {
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  econstructor; mauto.
  assert {{ Γ, A::Sort@s ⊢s (Wk ∘ Id),,#0 ≈ Wk,,#0 : Γ, A::Sort@s }}.
  {
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  eapply eq_sub_trans; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_eq_weaken_var0_id : mcpts.
#[export]
Hint Rewrite -> @sub_eq_weaken_var0_id using mauto 4 : mcpts.

Lemma exp_eq_sub_sub_compose_cong {P : PtsSig} : forall {Γ : Ctx P} {Δ Δ' Ψ σ τ σ' τ' M A s},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Ψ ⊢ M : A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s τ∘σ ≈ τ'∘σ' : Ψ }} ->
    {{ Γ ⊢ [τ][σ]M ≈ [τ'][σ']M : [τ∘σ]A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ [τ∘σ]A ≈ [τ'∘σ']A : Sort@s }}.
  {
    eapply eq_exp_conv; mauto.
    eapply eq_exp_cong_clo; mauto.
    eapply eq_exp_refl; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢ [τ][σ]M ≈ [τ∘σ]M : [τ∘σ]A }}.
  {
    eapply eq_exp_sym; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢ [τ∘σ]M ≈ [τ'∘σ']M : [τ∘σ]A }}.
  {
    econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢ [τ'∘σ']M ≈ [τ'][σ']M : [τ'∘σ']A }} by (econstructor; mauto).
  assert {{ Γ ⊢ [τ'∘σ']M ≈ [τ'][σ']M : [τ∘σ]A }}.
  {
    eapply eq_exp_conv; mauto; econstructor; mauto.
    symmetry; mauto 2.
    eapply eq_typ_refl; econstructor; mauto 2.
  }
  eapply eq_exp_trans; mauto.
  eapply eq_exp_trans; mauto.
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mcpts.

Lemma ctxeq_ctx_lookup {P : PtsSig} : forall {Γ : Ctx P} {Δ A x s},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ #x : A :: Sort@s ∈ Γ }} ->
    exists B,
      {{ #x : B :: Sort@s ∈ Δ }} /\
        {{ Γ ⊢ A ≈ B : Sort@s }} /\
        {{ Δ ⊢ A ≈ B : Sort@s }}.
Proof with mautosolve.
  intros * HΓΔ Hx; gen Δ.
  induction Hx as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? ? HΓΔ'];
    [|specialize (IHHx _ HΓΔ')]; destruct_conjs; eexists.
  - split.
    + econstructor; mauto.
    + split.
      * eapply eq_exp_conv; mauto.
        eapply eq_exp_cong_clo; mauto.
        eapply eq_sub_refl; mauto.
        eapply wf_sub_conv; mauto.
        econstructor; mauto.
        econstructor; mauto.
        econstructor; mauto.
      * eapply eq_exp_conv; mauto.
        eapply eq_exp_cong_clo; mauto.
        eapply eq_sub_refl; mauto.
        econstructor; mauto.
        econstructor; mauto.
        econstructor; mauto.
  - split.
    + econstructor; mauto.
    + split.
      * eapply eq_exp_conv; mauto.
        eapply eq_exp_cong_clo; mauto.
        eapply eq_sub_refl; mauto.
        eapply wf_sub_conv; mauto.
        econstructor; mauto.
        econstructor; mauto.
        econstructor; mauto.
      * eapply eq_exp_conv; mauto.
        eapply eq_exp_cong_clo; mauto.
        eapply eq_sub_refl; mauto.
        econstructor; mauto.
        econstructor; mauto.
        econstructor; mauto.
Qed.

#[export]
Hint Resolve ctxeq_ctx_lookup : mcpts.

Lemma sub_id_on_typ {P : PtsSig} : forall {Γ : Ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : [Id]A }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_conv; mauto.
  econstructor; mauto.
  eapply eq_exp_conv; mauto.
  eapply eq_exp_sym.
  eapply eq_exp_prop_id; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_id_on_typ : mcpts.

Lemma sub_id_extend {P : PtsSig} : forall {Γ : Ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A::Sort@s }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_id_extend : mcpts.

Lemma sub_eq_id_on_typ {P : PtsSig} : forall {Γ : Ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : [Id]A }}.
Proof with mautosolve 4.
  intros.
  eapply eq_exp_conv; mauto.
  econstructor; mauto.
  eapply eq_exp_conv; mauto.
  eapply eq_exp_sym.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_eq_id_on_typ : mcpts.

Lemma sub_eq_id_extend_cong {P : PtsSig} : forall {Γ : Ctx P} {M M' A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A::Sort@s }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_eq_id_extend_cong : mcpts.

Lemma sub_eq_p_id_extend {P : PtsSig} : forall {Γ : Ctx P} {M A s},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘Wk ≈ Id : Γ }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto; econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_eq_p_id_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_p_id_extend using mauto 4 : mcpts.

Lemma sub_wk_ext {P : PtsSig} : forall {Γ : Ctx P} {A s σ Δ},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, [σ]A :: Sort@s ⊢s (Wk∘σ),,#0 : Δ, A::Sort@s }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ [σ]A : Sort@s }} by mauto 4.
  assert {{ Γ, [σ]A::Sort@s ⊢s Wk : Γ }} by (econstructor; mauto).
  assert {{ Γ, [σ]A::Sort@s ⊢ #0 : [Wk][σ]A }}.
  {
    econstructor; mauto.
    econstructor; mauto.
  }
  econstructor; mauto.
  econstructor; mauto.
  eapply wf_exp_conv; mauto.
  eapply eq_typ_sym.
  eapply eq_typ_exp.
  eapply eq_exp_conv; mauto.
  eapply eq_exp_prop_comp; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

Lemma sub_wk_ext_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, Sort@s1::Sort@s2 ⊢s (Wk∘σ),,#0 : Δ, Sort@s1::Sort@s2 }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ, Sort@s1::Sort@s2 ⊢s Wk : Γ }} by (econstructor; mauto).
  assert {{ Γ, Sort@s1::Sort@s2 ⊢s Wk∘σ : Δ }} by (econstructor; mauto).
  assert {{ Γ, Sort@s1::Sort@s2 ⊢ #0 : Sort@s1 }}...
Qed.


#[export]
Hint Resolve sub_wk_ext sub_wk_ext_typ : mcpts.

Lemma sub_eq_id_extend_compose_sigma {P : PtsSig} : forall {Γ : Ctx P} {M A σ Δ s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢s σ∘(Id,,M) ≈ σ,,[σ]M : Δ, A::Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ⊢s Id : Δ }} by (econstructor; mauto).
  assert {{ Δ ⊢ M : [Id]A }}.
  {
    eapply wf_exp_conv; mauto.
    eapply eq_typ_sym; econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢s σ∘(Id,,M) ≈ (σ∘Id),,[σ]M : Δ, A::Sort@s }} by (econstructor; mauto).
  assert {{ Γ ⊢ [σ]M : [σ][Id]A }} by (econstructor; mauto).
  assert {{ Γ ⊢ [σ][Id]A ≈ [σ∘Id]A : Sort@s }} by mauto.
  assert {{ Γ ⊢ [σ]M : [σ∘Id]A }}.
  {
    eapply wf_exp_conv; mauto.
    eapply eq_typ_sym; econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢ [σ]M ≈ [σ]M : [σ∘Id]A }} by (eapply eq_exp_refl; mauto).
  assert {{ Γ ⊢s (σ∘Id),,[σ]M ≈ σ,,[σ]M : Δ, A::Sort@s }}.
  {
    econstructor; mauto.
    econstructor; mauto.
  }
  eapply eq_sub_trans; mauto.
Qed.

#[export]
Hint Resolve sub_eq_id_extend_compose_sigma : mcpts.

Lemma sub_eq_sigma_compose_weak_id_extend {P : PtsSig} : forall {Γ : Ctx P} {M A s σ Δ},
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘(Wk∘σ) ≈ σ : Δ }}.
Proof with mautosolve.
  intros.
  assert {{ Γ ⊢s Id,,M : Γ, A::Sort@s }} by mauto.
  assert {{ Γ ⊢s (Id,,M)∘(Wk∘σ) ≈ ((Id,,M)∘Wk)∘σ : Δ }}.
  {
    eapply eq_sub_sym.
    eapply eq_sub_prop_assoc; mauto.
    econstructor; mauto.    
  }
  assert {{ Γ ⊢s (Id,,M)∘Wk ≈ Id : Γ }} by mauto.
  assert {{ Γ ⊢s ((Id,,M)∘Wk)∘σ ≈ Id∘σ : Δ }}.
  {
    eapply eq_sub_cong_comp; mauto.
    eapply eq_sub_refl; mauto.
  }
  eapply eq_sub_trans; mauto.
  eapply eq_sub_trans; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_eq_sigma_compose_weak_id_extend : mcpts.

Lemma sub_eq_wk_ext_sigma_id_extend {P : PtsSig} : forall {Γ : Ctx P} {M A s σ Δ},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : [σ]A }} ->
    {{ Γ ⊢s (Id,,M)∘((Wk∘σ),,#0) ≈ σ,,M : Δ, A::Sort@s }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ [σ]A : Sort@s }} by mauto.
  assert {{ Γ ⊢ M : [σ]A }} by mauto.
  assert {{ Γ ⊢s Id,,M : Γ, [σ]A::Sort@s }} by mauto.
  assert {{ Γ, [σ]A::Sort@s ⊢s Wk : Γ }} by (econstructor; mauto).
  assert {{ Γ, [σ]A::Sort@s ⊢ #0 : [Wk][σ]A }}.
  {
    econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ, [σ]A::Sort@s ⊢ #0 : [Wk∘σ]A }}.
  {
    eapply wf_exp_conv; mauto.
    eapply eq_typ_exp.
    econstructor; mauto.
    econstructor; mauto.
  }
  assert {{ Γ ⊢s (Id,,M)∘((Wk∘σ),,#0) ≈ ((Id,,M)∘(Wk∘Id)),,[Id,,M]#0 : Δ, A::Sort@s }}.
  {
    admit.
  }
  assert {{ Γ ⊢s (Id,,M)∘(Wk∘σ) ≈ σ : Δ }} by mauto.
  assert {{ Γ ⊢ M : [Id][σ]A }} by mauto 4.
  assert {{ Γ ⊢ [Id,,M]#0 ≈ M : [Id][σ]A }} by (econstructor; mauto 3).
  assert {{ Γ ⊢ [Id,,M]#0 ≈ M : [σ]A }}.
  {
    eapply eq_exp_conv; mauto.
    eapply eq_typ_exp.
    econstructor; mauto.
  }
  enough {{ Γ ⊢ [Id,,M]#0 ≈ M : [(Id,,M)∘(Wk∘σ)]A }}.
  {
    admit.
  }
  eapply wf_exp_eq_conv; mauto 3.
  eapply wf_exp_conv; mauto 3.
  eapply wf_exp_clo; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
  eapply eq_exp_sym.
  eapply eq_exp_conv; mauto 3.
  eapply eq_exp_cong_clo; mauto.
  eapply eq_exp_refl; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
Admitted.

#[export]
Hint Resolve sub_eq_wk_ext_sigma_id_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_wk_ext_sigma_id_extend using mauto 4 : mcpts.

Lemma sub_eq_p_wk_ext_sigma {P : PtsSig} : forall {Γ : Ctx P} {A s σ Δ},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, [σ]A::Sort@s ⊢s ((Wk∘σ),,#0)∘Wk ≈ Wk∘σ : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, [σ]A::Sort@s ⊢s Wk : Γ }} by (econstructor; mauto 4).
  assert {{ Γ, [σ]A::Sort@s ⊢ #0 : [Wk][σ]A }}.
  {
    econstructor; mauto 3.
    econstructor; mauto 3.
  }
  enough {{ Γ, [σ]A::Sort@s ⊢ #0 : [Wk∘σ]A }}.
  {
    econstructor; mauto.
    econstructor; mauto.
    econstructor; mauto.
  }
  eapply wf_conv; mauto 3.
  eapply wf_exp_conv; mauto.
  eapply wf_exp_clo; mauto.
  econstructor; mauto.
  econstructor; mauto.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve sub_eq_p_wk_ext_sigma : mcpts.


Lemma var_compose_subs {P : PtsSig} : forall {Γ : Ctx P} {τ Δ σ Ψ s A x},
    {{ Ψ ⊢ A : Sort@s }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ #x : [τ][σ]A :: Sort@s ∈ Γ }} ->
    {{ Γ ⊢ #x : [τ∘σ]A }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
  econstructor; mauto.
  eapply wf_exp_conv; mauto 3; econstructor; mauto 3; econstructor; mauto 3.
Qed.

#[export]
Hint Resolve var_compose_subs : mcpts.

Lemma sub_lookup_var0 {P : PtsSig} : forall (Δ : Ctx P) Γ σ M1 M2 A s,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ M1 : [σ]A }} ->
    {{ Δ ⊢ M2 : [σ]A }} ->
    {{ Δ ⊢ [σ,,M1,,M2]#0 ≈ M2 : [σ]A }}.
Proof.
  intros.
  assert {{ Γ, A::Sort@s ⊢ [Wk]A : Sort@s }}.
  {
    eapply presup_ctx_lookup_typ; mauto.
    econstructor; mauto.
  }
  assert {{ Δ ⊢s σ,,M1 : Γ, A::Sort@s }} by (econstructor; mauto 3).
  assert {{ Δ ⊢ [σ,,M1][Wk]A : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ [σ,,M1][Wk]A ≈ [σ]A : Sort@s }}.
  {
    transitivity {{{ [(σ,,M1)∘Wk]A }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
      econstructor; mauto 3.
    - eapply exp_eq_sub_cong_typ2'; mauto 4.
      econstructor; mauto 3.
      econstructor; mauto 3.
      econstructor; mauto 3.
      econstructor; mauto 3.
  }
  eapply wf_exp_eq_conv;
    [eapply eq_exp_prop_var_ze with (A := {{{ [Wk]A }}}) | |];
    mauto 4.
  econstructor; mauto.
  eapply wf_exp_conv; mauto.
  eapply eq_typ_sym.
  eapply eq_typ_exp.
  econstructor; mauto.
  econstructor; mauto.
Qed.

Lemma id_sub_lookup_var0 {P : PtsSig} : forall (Γ : Ctx P) M1 M2 A s,
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢ [Id,,M1,,M2]#0 ≈ M2 : A }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var0 | |];
    mauto 3;
    econstructor; mauto.
Qed.

Lemma sub_lookup_var1 {P : PtsSig} : forall (Δ : Ctx P) Γ σ M1 M2 A s,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Δ ⊢ M1 : [σ]A }} ->
    {{ Δ ⊢ M2 : [σ]A }} ->
    {{ Δ ⊢ [σ,,M1,,M2]#1 ≈ M1 : [σ]A }}.
Proof.
  intros.
  assert {{ Γ, A::Sort@s ⊢ [Wk]A : Sort@s }}.
  {
    econstructor; mauto 3; econstructor; mauto 3; econstructor; mauto 3.    
  }
  assert {{ Δ ⊢s σ,,M1 : Γ, A::Sort@s }} by (econstructor; mauto 3).
  assert {{ Δ ⊢ [σ,,M1][Wk]A : Sort@s }} by mauto 4.
  assert {{ Δ ⊢ [σ,,M1][Wk]A ≈ [σ]A : Sort@s }}.
  {
    transitivity {{{ [(σ,,M1)∘Wk]A }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
      econstructor; mauto.
    - eapply exp_eq_sub_cong_typ2'; mauto 4; econstructor; mauto; econstructor; mauto.
  }
  transitivity {{{ [σ,,M1]#0 }}}.
  - eapply wf_exp_eq_conv;
      [eapply eq_exp_prop_var_su | |];
      mauto 4;
      econstructor; mauto.
    eapply wf_exp_conv; mauto.
    eapply eq_typ_exp.
    econstructor; mauto.
  - eapply wf_exp_eq_conv;
    [eapply eq_exp_prop_var_ze | |];
    mauto 2.
    eapply eq_exp_refl; mauto.
Qed.

Lemma id_sub_lookup_var1 {P : PtsSig} : forall (Γ : Ctx P) M1 M2 A s,
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ ⊢ [Id,,M1,,M2]#1 ≈ M1 : A }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var1 | |];
    mauto 3;
    econstructor; mauto 3.  
Qed.

Lemma exp_eq_var_1_sub_wk_ext_sigma {P : PtsSig} : forall {Γ : Ctx P} {A s1 B s2 σ Δ},
    {{ Δ ⊢ B : Sort@s2 }} ->
    {{ Δ, B::Sort@s2 ⊢ A : Sort@s1 }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [(Wk∘((Wk∘σ),,#0)),,#0]#1 ≈ #1 : [Wk∘Wk][σ]B }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Γ, [σ]B::Sort@s2 ⊢s (Wk∘σ),,#0 : Δ, B::Sort@s2 }} by mauto 2.
  assert {{ ⊢ Γ, [σ]B::Sort@s2 }} by mauto 3.
  assert {{ ⊢ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 }} by mauto 3.
  assert {{ Δ, B::Sort@s2 ⊢ [Wk]B : Sort@s2 }}.
  {
    eapply presup_ctx_lookup_typ; mauto 3.
    econstructor; mauto.
  }
  assert {{ Δ, B::Sort@s2 ⊢ #0 : [Wk]B }} by (econstructor; mauto 3; econstructor; mauto 3).
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ #0 : [Wk][(Wk∘σ),,#0]A }} by (econstructor; mauto 2; econstructor; mauto 2).
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk∘((Wk∘σ),,#0)]A ≈ [Wk][(Wk∘σ),,#0]A : Sort@s1 }}.
  {
    eapply eq_exp_conv; mauto 3.
    eapply eq_exp_prop_comp; mauto.
    econstructor; mauto 3.
    econstructor; mauto 3.
    econstructor; mauto 3.
    econstructor; mauto 3.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢s Wk∘((Wk∘σ),,#0) : Δ, B::Sort@s2 }}.
  {
    econstructor; mauto 3.
    econstructor; mauto 3.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ #0 : [Wk∘((Wk∘σ),,#0)]A }}.
  {
    eapply wf_exp_conv; mauto 3.
    eapply eq_typ_exp.
    econstructor; mauto 3.
  }
  assert {{ Γ ⊢ [σ]B : Sort@s2 }} by mauto 2.
  assert {{ Γ, [σ]B::Sort@s2 ⊢s Wk : Γ }} by (econstructor; mauto 2).
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢s Wk : Γ, [σ]B::Sort@s2 }} by (econstructor; mauto 2).
  assert {{ Γ, [σ]B::Sort@s2 ⊢ [Wk][σ]B : Sort@s2 }} by mauto 2.
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk][Wk][σ]B : Sort@s2 }} by mauto 2.
  assert {{ Γ, [σ]B::Sort@s2 ⊢ [(Wk∘σ),,#0][Wk]B ≈ [Wk][σ]B : Sort@s2 }}.
  {
    eapply exp_eq_sub_sub_compose_cong_typ; mauto 3.
    econstructor; mauto.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk∘((Wk∘σ),,#0)][Wk]B ≈ [Wk][Wk][σ]B : Sort@s2 }}.
  {
    transitivity {{{ [Wk][(Wk∘σ),,#0][Wk]B }}}; mauto 3.
    econstructor; mauto.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [(Wk∘((Wk∘σ),,#0)),,#0]#1 ≈ [Wk∘((Wk∘σ),,#0)]#0 : [Wk][Wk][σ]B }}.
  {
    admit.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk∘((Wk∘σ),,#0)]#0 ≈ [Wk][(Wk∘σ),,#0]#0 : [Wk][Wk][σ]B }}.
  {
    admit.
  }
  assert {{ Γ, [σ]B::Sort@s2 ⊢s Wk∘σ : Δ }}.
  {
    econstructor; mauto.
  }
  assert {{ Γ, [σ]B::Sort@s2 ⊢ #0 : [Wk∘σ]B }}.
  {
    eapply wf_exp_conv; mauto 3.
    econstructor; mauto 3.
    econstructor; mauto 3.
    eapply eq_typ_exp.
    econstructor; mauto 3.
    econstructor; mauto 2.
  }
  assert {{ Γ, [σ]B::Sort@s2 ⊢ [(Wk∘σ),,#0]#0 ≈ #0 : [Wk∘σ]B }}.
  {
    econstructor; mauto.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk][(Wk∘σ),,#0]#0 ≈ [Wk]#0 : [Wk][Wk∘σ]B }}.
  {
    econstructor; mauto 3.
    eapply eq_sub_refl; mauto.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk][Wk∘σ]B ≈ [Wk][Wk][σ]B : Sort@s2 }}.
  {
    econstructor; mauto 3.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk][(Wk∘σ),,#0]#0 ≈ [Wk]#0 : [Wk][Wk][σ]B }} by mauto 2.
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [(Wk∘((Wk∘σ),,#0)),,#0]#1 ≈ #1 : [Wk][Wk][σ]B }}.
  {
    etransitivity; mauto 2.
    etransitivity; mauto 2.
    admit.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢s Wk∘Wk : Γ }}.
  {
    econstructor; mauto 2.
  }
  assert {{ Γ, [σ]B::Sort@s2, [(Wk∘σ),,#0]A::Sort@s1 ⊢ [Wk∘Wk][σ]B : Sort@s2 }} by mauto 2.
  eapply wf_exp_eq_conv; mauto 2.
Admitted.

(** *** Type Presuppositions *)
    
Lemma presup_exp_typ {P : PtsSig} : forall {Γ : Ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A }}.
Proof.
  induction 1; assert {{ ⊢ Γ }} by mauto 3; destruct_conjs; mauto 3.
  - econstructor; mauto 2.
  - econstructor; mauto 2.
  - econstructor; mauto 2.
  - econstructor; mauto 2.
  - inversion H; subst.
    + econstructor; mauto 2.
      econstructor; mauto 2.      
    + admit.
  - inversion IHwf_exp; subst; eapply wf_typ_clo; mauto 2.
  - admit.
Admitted.
    

Lemma presup_exp {P : PtsSig} : forall {Γ : Ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ {{ Γ ⊢ A }}.
Proof.
  mauto 4 using presup_exp_typ.
Qed.

(** *** Consistency Helper *)

Lemma no_closed_neutral {P : PtsSig} : forall {A : Exp P} {W : Ne P},
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
