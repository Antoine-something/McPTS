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
  intros * Hx Hx'; gen s' A'.
  induction Hx as [|* ? IHHx]; intros; inversion_clear Hx'.  
  - admit.
  - eapply IHHx; mauto.
Admitted.


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
  induction 1; split; destruct_pairs; mauto; try econstructor; mauto.
  admit.
Admitted.

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


(* I suspect the lemmas with double weaken are only used for equality types *)
Lemma exp_eq_sub_compose_double_weaken_double_extend_typ {P : PtsSig} : forall {Γ : Ctx P} {σ Δ s1 A s2 B M s3 C N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : [σ]B }} ->
    {{ Δ, B :: Sort@s2 ⊢ C : Sort@s3 }} ->
    {{ Γ ⊢ N : [σ,,M]C }} ->
    {{ Γ ⊢ [σ,,M,,N][Wk∘Wk]A ≈ [σ]A : Sort@s1 }}.
Proof with mautosolve 4.
  
Admitted.

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
Admitted.

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
Admitted.

#[export]
Hint Resolve exp_eq_var_0_sub_typ exp_eq_var_1_sub_typ : mcpts.
#[export]
Hint Rewrite -> @exp_eq_var_0_sub_typ @exp_eq_var_1_sub_typ : mcpts.

Lemma exp_eq_var_0_weaken_typ {P : PtsSig} : forall {Γ : Ctx P} {A s1 s2 s3},
    {{ ⊢ Γ, A :: Sort@s1 }} ->
    {{ #0 : [Wk]Sort@s2 :: Sort@s3 ∈ Γ }} ->
    {{ Γ, A :: Sort@s1 ⊢ [Wk]#0 ≈ #1 : Sort@s2 }}.
Proof with mautosolve 3.
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


Lemma exp_eq_sub_sub_compose_cong_typ : forall {Γ Δ Δ' Ψ σ τ σ' τ' A i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] : Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }} by mauto.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Type@i }} by mauto.
  enough {{ Γ ⊢ A[σ'∘τ'] ≈ A[σ'][τ'] : Type@i }}...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mcpts.


(** *** Other Tedious Lemmas *)

Lemma sub_eq_weaken_var0_id : forall {Γ A i},
    {{ Γ ⊢ A : Type@i }} ->
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

Lemma exp_eq_sub_sub_compose_cong : forall {Γ Δ Δ' Ψ σ τ σ' τ' M A i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Ψ ⊢ M : A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof with mautosolve 4.
  intros.
  assert {{ Γ ⊢ A[σ∘τ] ≈ A[σ'∘τ'] : Type@i }} by mauto.
  assert {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ∘τ] ≈ M[σ'∘τ'] : A[σ∘τ] }} by mauto.
  assert {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ'∘τ'] }} by mauto.
  enough {{ Γ ⊢ M[σ'∘τ'] ≈ M[σ'][τ'] : A[σ∘τ] }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mcpts.

Lemma ctxeq_ctx_lookup : forall {Γ Δ A x},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ #x : A ∈ Γ }} ->
    exists B i,
      {{ #x : B ∈ Δ }} /\
        {{ Γ ⊢ A ≈ B : Type@i }} /\
        {{ Δ ⊢ A ≈ B : Type@i }}.
Proof with mautosolve.
  intros * HΓΔ Hx; gen Δ.
  induction Hx as [|* ? IHHx]; inversion_clear 1 as [|? ? ? ? ? HΓΔ'];
    [|specialize (IHHx _ HΓΔ')]; destruct_conjs; repeat eexists...
Qed.

#[export]
Hint Resolve ctxeq_ctx_lookup : mcpts.

Lemma sub_id_on_typ : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve sub_id_on_typ : mcpts.

Lemma sub_id_extend : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor...
Qed.

#[export]
Hint Resolve sub_id_extend : mcpts.

Lemma sub_eq_id_on_typ : forall {Γ M M' A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof with mautosolve 4.
  intros.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve sub_eq_id_on_typ : mcpts.

Lemma sub_eq_id_extend_cong : forall {Γ M M' A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof with mautosolve 4.
  intros.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_id_extend_cong : mcpts.

Lemma sub_eq_p_id_extend : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
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

Lemma sub_q : forall {Γ A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s q σ : Δ, A }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto 4.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 4.
  econstructor; mauto 3.
  eapply wf_conv...
Qed.

Lemma sub_q_typ : forall {Γ σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, Type@i ⊢s q σ : Δ, Type@i }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ, Type@i ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, Type@i ⊢s σ∘Wk : Δ }} by mauto 4.
  assert {{ Γ, Type@i ⊢ #0 : Type@i }}...
Qed.


#[export]
Hint Resolve sub_q sub_q_typ : mcpts.

Lemma sub_eq_id_extend_compose_sigma : forall {Γ M A σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ Δ ⊢s Id : Δ }} by mauto.
  assert {{ Δ ⊢ M : A[Id] }} by mauto.
  assert {{ Γ ⊢s (Id,,M)∘σ ≈ (Id∘σ),,M[σ] : Δ, A }} by mauto 3.
  assert {{ Γ ⊢ M[σ] : A[Id][σ] }} by mauto.
  assert {{ Γ ⊢ A[Id][σ] ≈ A[Id∘σ] : Type@i }} by mauto.
  assert {{ Γ ⊢ M[σ] : A[Id∘σ] }} by mauto 4.
  enough {{ Γ ⊢ M[σ] ≈ M[σ] : A[Id∘σ] }}...
Qed.

#[export]
Hint Resolve sub_eq_id_extend_compose_sigma : mcpts.

Lemma sub_eq_sigma_compose_weak_id_extend : forall {Γ M A i σ Δ},
    {{ Γ ⊢ A : Type@i }} ->
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

Lemma sub_eq_q_sigma_id_extend : forall {Γ M A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Δ, A }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Γ }} by mauto 3.
  assert {{ Γ ⊢ A[σ] : Type@i }} by mauto.
  assert {{ Γ ⊢ M : A[σ] }} by mauto.
  assert {{ Γ ⊢s Id,,M : Γ, A[σ] }} by mauto.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by (eapply wf_conv; mauto 3).
  assert {{ Γ ⊢s q σ∘(Id,,M) ≈ ((σ∘Wk)∘(Id,,M)),,#0[Id,,M] : Δ, A }} by mauto.
  assert {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }} by mauto.
  assert {{ Γ ⊢ M : A[σ][Id] }} by mauto 4.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ][Id] }} by mauto 3.
  assert {{ Γ ⊢ #0[Id,,M] ≈ M : A[σ] }} by mauto.
  enough {{ Γ ⊢ #0[Id,,M] ≈ M : A[(σ∘Wk)∘(Id,,M)] }} by mauto.
  eapply wf_exp_eq_conv...
Qed.

#[export]
Hint Resolve sub_eq_q_sigma_id_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_id_extend using mauto 4 : mcpts.

Lemma sub_eq_p_q_sigma : forall {Γ A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof with mautosolve 3.
  intros.
  assert {{ Γ, A[σ] ⊢s Wk : Γ }} by mauto 4.
  assert {{ Γ, A[σ] ⊢ #0 : A[σ][Wk] }} by mauto 3.
  enough {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }} by mauto.
  eapply wf_conv...
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma : mcpts.


Lemma var_compose_subs : forall {Γ τ Δ σ Ψ i A x},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ #x : A[σ][τ] ∈ Γ }} ->
    {{ Γ ⊢ #x : A[σ∘τ] }}.
Proof.
  intros.
  eapply wf_conv; mauto 3.
Qed.

#[export]
Hint Resolve var_compose_subs : mcpts.

Lemma sub_lookup_var0 : forall Δ Γ σ M1 M2 B i,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #0[σ,,M1,,M2] ≈ M2 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] : Type @ i }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] : Type @ i }}.
  {
    transitivity {{{ B[Wk∘(σ,,M1)] }}}.
    - eapply exp_eq_sub_compose_typ; mauto 4.
    - eapply exp_eq_sub_cong_typ2'; mauto 4.
  }
  eapply wf_exp_eq_conv;
    [eapply wf_exp_eq_var_0_sub with (A := {{{ B[Wk] }}}) | |];
    mauto 4.
Qed.

Lemma id_sub_lookup_var0 : forall Γ M1 M2 B i,
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #0[Id,,M1,,M2] ≈ M2 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var0 | |];
    mauto 3.
Qed.

Lemma sub_lookup_var1 : forall Δ Γ σ M1 M2 B i,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #1[σ,,M1,,M2] ≈ M1 : B[σ] }}.
Proof.
  intros.
  assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto.
  assert {{ Δ ⊢s σ,,M1 : Γ, B }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] : Type @ i }} by mauto 4.
  assert {{ Δ ⊢ B[Wk][σ,,M1] ≈ B[σ] : Type @ i }}.
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
    mauto 2.
    mauto.
Qed.

Lemma id_sub_lookup_var1 : forall Γ M1 M2 B i,
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #1[Id,,M1,,M2] ≈ M1 : B }}.
Proof.
  intros.
  eapply wf_exp_eq_conv;
    [eapply sub_lookup_var1 | |];
    mauto 3.
Qed.

Lemma exp_eq_var_1_sub_q_sigma : forall {Γ A i B j σ Δ},
    {{ Δ ⊢ B : Type@j }} ->
    {{ Δ, B ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof with mautosolve 4.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s q σ : Δ, B }} by mauto 2.
  assert {{ ⊢ Γ, B[σ] }} by mauto 3.
  assert {{ ⊢ Γ, B[σ], A[q σ] }} by mauto 3.
  assert {{ Δ, B ⊢ B[Wk] : Type@j }} by mauto 4.
  assert {{ Δ, B ⊢ #0 : B[Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ][Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ A[q σ∘Wk] ≈ A[q σ][Wk] : Type@i }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢s q σ∘Wk : Δ, B }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0 : A[q σ∘Wk] }} by mauto 3.
  assert {{ Γ ⊢ B[σ] : Type@j }} by mauto 2.
  assert {{ Γ, B[σ] ⊢s Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk : Γ, B[σ] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[σ][Wk] : Type@j }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk][Wk] : Type@j }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ B[Wk][q σ] ≈ B[σ][Wk] : Type@j }} by (eapply exp_eq_sub_sub_compose_cong_typ; mauto 3).
  assert {{ Γ, B[σ],A[q σ] ⊢ B[Wk][q σ∘Wk] ≈ B[σ][Wk][Wk] : Type@j }} by (transitivity {{{ B[Wk][q σ][Wk] }}}; mauto 3).
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #0[q σ∘Wk] : B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ∘Wk] ≈ #0[q σ][Wk] : B[σ][Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ] ⊢s σ∘Wk : Δ }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Γ, B[σ] ⊢ #0[q σ] ≈ #0 : B[σ∘Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ∘Wk][Wk] }} by mauto 3.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ∘Wk][Wk] ≈ B[σ][Wk][Wk] : Type@j }} by mauto 4.
  assert {{ Γ, B[σ], A[q σ] ⊢ #0[q σ][Wk] ≈ #0[Wk] : B[σ][Wk][Wk] }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk][Wk] }} by (do 2 etransitivity; mauto 2).
  assert {{ Γ, B[σ], A[q σ] ⊢s Wk∘Wk : Γ }} by mauto 2.
  assert {{ Γ, B[σ], A[q σ] ⊢ B[σ][Wk∘Wk] : Type@j }} by mauto 2.
  eapply wf_exp_eq_conv; mauto 2.
Qed.

(** *** Type Presuppositions *)

Lemma presup_exp_typ : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  induction 1; assert {{ ⊢ Γ }} by mauto 3; destruct_conjs; mauto 3.

  - enough {{ Γ ⊢s Id,,M : Γ, ℕ }}; mauto 3.

  - eexists; mauto 4 using lift_exp_max_left, lift_exp_max_right.

  - enough {{ Γ ⊢s Id,,N : Γ, A }}; mauto 3.

  - enough {{ Γ ⊢s Id,,M1,,M2,,N : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }} by mauto 3.
    assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A ⊢ A[Wk] : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }} by mauto 4.
    assert {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }} by mauto 3.
    assert {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4).

    assert {{ Γ ⊢s Id,,M1 : Γ, A }} by mauto 3.
    assert {{ Γ ⊢ M2 : A[Wk][Id,,M1] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
    assert {{ Γ ⊢s Id,,M1,,M2 : Γ, A, A[Wk] }} by mauto 3.
    econstructor; [mautosolve 3 | mautosolve 3 |].
    eapply wf_conv; [| | symmetry]; mauto 3.
    transitivity {{{ Eq A[Wk∘Wk][Id,,M1,,M2] #1[Id,,M1,,M2] #0[Id,,M1,,M2] }}}.
    + econstructor; mauto 3 using id_sub_lookup_var0, id_sub_lookup_var1; eapply wf_conv; mauto 4.
    + assert {{ Γ ⊢ M2 : A }} by eassumption. (* re-assert to help search process *)
      assert {{ Γ ⊢ M1 : A[Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
      assert {{ Γ ⊢ M2 : A[Wk∘Wk][Id,,M1,,M2] }} by (eapply wf_conv; [| | symmetry]; mauto 2).
      econstructor; mauto 3 using id_sub_lookup_var0, id_sub_lookup_var1.
Qed.

Lemma presup_exp : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  mauto 4 using presup_exp_typ.
Qed.

(** *** Consistency Helper *)

Lemma no_closed_neutral : forall {A} {W : ne},
    ~ {{ ⋅ ⊢ W : A }}.
Proof.
  intros * H.
  dependent induction H; destruct W;
    try (simpl in *; congruence);
    autoinjections;
    intuition.
  inversion_by_head ctx_lookup.
Qed.
#[export]
Hint Resolve no_closed_neutral : mcpts.
