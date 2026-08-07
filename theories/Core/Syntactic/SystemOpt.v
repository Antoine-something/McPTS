From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CoreInversions Presup.
Import Syntax_Notations.

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.

(** * Optimized rules related to context *)


(** ** For global contexts *)
Corollary wf_gctx_eq_extend' {P} : forall {Δ Δ' : gctx P} {A A' x},
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ Δ ; ⋅ ⊢ A ≈ A' }} ->
    {{ `#x ∉ Δ }} ->
    {{ ⊢ Δ, x:A ≈ Δ', x:A' }}.
Proof.
  intros; gen_presups.
  econstructor; mauto 2.
Qed.

Corollary wf_gctx_subtyp_extend' {P} : forall {Δ Δ' : gctx P} {A A' x},
    {{ ⊢ Δ ⊆ Δ' }} ->
    {{ Δ ; ⋅ ⊢ A ⊆ A' }} ->
    {{ Δ' ; ⋅ ⊢ A' }} ->
    {{ `#x ∉ Δ }} ->
    {{ ⊢ Δ, x:A ⊆ Δ', x:A' }}.
Proof.
  intros; gen_presups.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_gctx_eq_extend' wf_gctx_subtyp_extend' : mcpts.
#[export]
Remove Hints wf_gctx_eq_extend wf_gctx_subtyp_extend : mcpts.
 
(** ** For local contexts *)  
Corollary wf_ctx_eq_extend' {P} : forall {Δ : gctx P} {Γ Γ' A A'},
    {{ Δ ⊢ Γ ≈ Γ' }} ->
    {{ Δ ; Γ ⊢ A ≈ A' }} ->
    {{ Δ ⊢ Γ, A ≈ Γ', A' }}.    
Proof.
  intros; gen_presups.
  econstructor; mauto 3.
Qed.

Corollary wf_ctx_subtyp_extend' {P} : forall {Δ : gctx P} {Γ Γ' A A'},
    {{ Δ ⊢ Γ ⊆ Γ' }} ->
    {{ Δ ; Γ' ⊢ A' }} ->
    {{ Δ ; Γ ⊢ A ⊆ A' }} ->
    {{ Δ ⊢ Γ, A ⊆ Γ', A' }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_ctx_eq_extend' wf_ctx_subtyp_extend' : mcpts.
#[export]
Remove Hints wf_ctx_eq_extend wf_ctx_subtyp_extend : mcpts.

(** * Optimized rules for expressions *)

(** ** Conversion rules for [wf_exp] *)
Corollary wf_exp_conv' {P} : forall {Δ : gctx P} {Γ A B M},
    {{ Δ ; Γ ⊢ M : A }} ->
    {{ Δ ; Γ ⊢ A ⊆ B }} ->
    {{ Δ ; Γ ⊢ M : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_conv_exp_eq' {P} : forall {Δ : gctx P} {Γ A B M s},
    {{ Δ ; Γ ⊢ M : A }} ->
    {{ Δ ; Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Δ ; Γ ⊢ M : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_conv_typ_eq' {P} : forall {Δ : gctx P} {Γ A B M},
    {{ Δ ; Γ ⊢ M : A }} ->
    {{ Δ ; Γ ⊢ A ≈ B }} ->
    {{ Δ ; Γ ⊢ M : B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_conv' wf_exp_conv_exp_eq' wf_exp_conv_typ_eq' : mcpts.
#[export]
Remove Hints wf_exp_conv wf_exp_conv_exp_eq wf_exp_conv_typ_eq : mcpts.

(** Rewrite rules associated to optimized conversions *)
Add Parametric Morphism {P} (Δ : gctx P) Γ : (wf_exp Δ Γ)
  with signature wf_typ_subtyp Δ Γ ==> eq ==> Basics.impl as wf_exp_morphism_iff3_subtyp.
Proof.
  intros A B Hsub M HM.
  gen_presups.
  mauto 2.
Qed.

Add Parametric Morphism {P} (Δ : gctx P) Γ s : (wf_exp Δ Γ)
  with signature wf_exp_eq Δ Γ {{{ Sort@s }}} ==> eq ==> iff as wf_exp_morphism_iff3_exp_eq.
Proof.
  split; impl_opt_constructor.
Qed.

Add Parametric Morphism {P} (Δ : gctx P) Γ : (wf_exp Δ Γ)
  with signature wf_typ_eq Δ Γ ==> eq ==> iff as wf_exp_morphism_iff3_typ_eq.
Proof.
  split; impl_opt_constructor.
Qed.

(** ** Conversion rules for [wf_exp_eq] *)
Corollary wf_exp_eq_conv' {P} : forall {Δ : gctx P} {Γ A B M M'},
    {{ Δ ; Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ; Γ ⊢ A ⊆ B }} ->
    {{ Δ ; Γ ⊢ M ≈ M' : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_eq_conv_exp_eq' {P} : forall {Δ : gctx P} {Γ A B M M' s},
    {{ Δ ; Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ; Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Δ ; Γ ⊢ M ≈ M' : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_eq_conv_typ_eq' {P} : forall {Δ : gctx P} {Γ A B M M'},
    {{ Δ ; Γ ⊢ M ≈ M' : A }} ->
    {{ Δ ; Γ ⊢ A ≈ B }} ->
    {{ Δ ; Γ ⊢ M ≈ M' : B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_conv' wf_exp_eq_conv_exp_eq' wf_exp_eq_conv_typ_eq' : mcpts.
#[export]
Remove Hints wf_exp_eq_conv wf_exp_eq_conv_exp_eq wf_exp_eq_conv_typ_eq : mcpts.

(** Rewrite rules associated to optimized conversions *)
Add Parametric Morphism {P} (Δ : gctx P) Γ : (wf_exp_eq Δ Γ)
  with signature wf_typ_subtyp Δ Γ ==> eq ==> eq ==> Basics.impl as wf_exp_eq_morphism_iff3_subtyp.
Proof.
  intros A B Hsub M M' HM.
  gen_presups.
  mauto 2.
Qed.

Add Parametric Morphism {P} (Δ : gctx P) Γ s : (wf_exp_eq Δ Γ)
  with signature wf_exp_eq Δ Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3_exp_eq.
Proof.
  split; impl_opt_constructor.
Qed.

Add Parametric Morphism {P} (Δ : gctx P) Γ : (wf_exp_eq Δ Γ)
  with signature wf_typ_eq Δ Γ ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3_typ_eq.
Proof.
  split; impl_opt_constructor.
Qed.


(** ** Rules for sorts *)
Lemma wf_exp_eq_sort_sub' {P : PtsSig} : forall (Δ : gctx P) Γ Γ' σ s s',
    {{ Δ ; Γ' ⊢ Sort@s : Sort@s' }} ->
    {{ Δ ; Γ ⊢ Sort@s : Sort@s' }} ->
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s' }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_sort_sub' : mcpts.
#[export]
Hint Rewrite -> @wf_exp_eq_sort_sub' using solve [lia | mauto 3] : mcpts.
#[export]
Remove Hints wf_exp_eq_typ_sub : mcpts.

Lemma wf_typ_eq_sort_sub' {P} : forall (Δ : gctx P) Γ Γ' σ s,
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ ⊢ Sort@s[σ] ≈ Sort@s }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_typ_eq_sort_sub' : mcpts.
#[export]
Hint Rewrite -> @wf_typ_eq_sort_sub' using solve [lia | mauto 3] : mcpts.
#[export]
Remove Hints wf_typ_eq_sub_sort : mcpts.


(** ** Rules for functions *)
Corollary wf_exp_pi' {P : PtsSig} : forall {Δ : gctx P} {Γ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
    {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ Π r A B : Sort@s3 }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_pi' : mcpts.
#[export]
Remove Hints wf_exp_pi : mcpts.

Corollary wf_exp_fn' {P : PtsSig} : forall {Δ : gctx P} {Γ A M B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
    {{ Δ ; Γ, A ⊢ M : B }} ->
    {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ λ r A B M : Π r A B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_fn' : mcpts.
#[export]
Remove Hints wf_exp_fn : mcpts.

Corollary wf_exp_app' {P : PtsSig} : forall {Δ : gctx P} {Γ M N A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ M : Π r A B }} ->
    {{ Δ ; Γ ⊢ N : A }} ->
    {{ Δ ; Γ ⊢ M N : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  inversion_clear HAwf0.
  assert ({{ Δ ; Γ ⊢ A : Sort@s1 }} /\ {{ Δ ; Γ, A ⊢ B : Sort@s2 }} /\ {{ Δ ; Γ ⊢ Sort@s3 ⊆ Sort@s }}) as [] by (eapply wf_exp_pi_inversion; mauto 2).
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_app' : mcpts.
#[export]
Remove Hints wf_exp_app : mcpts.


Corollary wf_exp_eq_pi_cong' {P} : forall {Δ Γ A A' s1 s2 s3 B B'} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Δ ; Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_cong : mcpts.

Corollary wf_exp_eq_fn_cong' {P : PtsSig} : forall {Δ Γ A A' s1 s2 s3 B B' M M'} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Δ ; Γ, A ⊢ M ≈ M' : B }} ->
    {{ Δ ; Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ λ r A B M ≈ λ r A' B' M' : Π r A B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_cong : mcpts.

Corollary wf_exp_eq_fn_sub' {P : PtsSig} : forall {Δ Γ Γ' σ A M B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ' ⊢ A : Sort@s1 }} ->
    {{ Δ ; Γ', A ⊢ M : B }} ->
    {{ Δ ; Γ', A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ (λ r A B M)[σ] ≈ λ r A[σ] B[q σ] M[q σ] : (Π r A B)[σ] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_fn_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_sub : mcpts.

Corollary wf_exp_eq_app_cong' {P : PtsSig} : forall {Δ Γ A B M M' N N' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ M ≈ M' : Π r A B }} ->
    {{ Δ ; Γ ⊢ N ≈ N' : A }} ->
    {{ Δ ; Γ ⊢ M N ≈ M' N' : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Δ ; Γ ⊢ A : Sort@s1 }} /\ {{ Δ ; Γ, A ⊢ B : Sort@s2 }}) as [] by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_cong : mcpts.

Corollary wf_exp_eq_app_sub' {P : PtsSig} : forall {Δ Γ Γ' σ A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ' ⊢ M : Π r A B }} ->
    {{ Δ ; Γ' ⊢ N : A }} ->
    {{ Δ ; Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Δ ; Γ' ⊢ A : Sort@s1 }} /\ {{ Δ ; Γ', A ⊢ B : Sort@s2 }}) as [] by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_sub : mcpts.

Corollary wf_exp_eq_pi_beta' {P : PtsSig} : forall {Δ Γ A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ A : Sort@s1 }} ->
    {{ Δ ; Γ, A ⊢ M : B }} ->
    {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ ⊢ N : A }} ->
    {{ Δ ; Γ ⊢ (λ r A B M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_beta : mcpts.

Corollary wf_exp_eq_pi_eta' {P : PtsSig} : forall {Δ Γ A B M s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ M : Π r A B }} ->
    {{ Δ ; Γ ⊢ M ≈ λ r A B (M[Wk] #0) : Π r A B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Δ ; Γ ⊢ A : Sort@s1 }} /\ {{ Δ ; Γ, A ⊢ B : Sort@s2 }}) as [] by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_eta' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_eta : mcpts.


(** ** Rules for natural numbers *)
Corollary wf_exp_eq_nat_sub' {P} : forall {Δ Γ s} {r : Ru_nat P s}  σ Γ',
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ ⊢ ℕ[σ] ≈ ℕ : Sort@s }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_sub : mcpts.

Corollary wf_exp_eq_natrec_cong' {P} : forall {Δ : gctx P} {Γ A A' MZ MZ' MS MS' M M' s} {r : Ru_nat P s},
    {{ Δ ; Γ, ℕ ⊢ A }} ->
    {{ Δ ; Γ, ℕ ⊢ A' }} ->
    {{ Δ ; Γ, ℕ ⊢ A ≈ A' }} ->
    {{ Δ ; Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Δ ; Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Δ ; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mcpts.

Corollary wf_exp_eq_natrec_sub' {P} : forall {Δ : gctx P} {Γ Γ' σ A MZ MS M s} {r : Ru_nat P s},
    {{ Δ ; Γ ⊢s σ : Γ' }} ->
    {{ Δ ; Γ', ℕ ⊢ A }} ->
    {{ Δ ; Γ' ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ ; Γ', ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ' ⊢ M : ℕ }} ->
    {{ Δ ; Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_natrec_sub : mcpts.

Corollary wf_exp_eq_nat_beta_zero' {P} : forall {Δ : gctx P} {Γ A MZ MS s} {r : Ru_nat P s},
    {{ Δ ; Γ, ℕ ⊢ A }} ->
    {{ Δ ; Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ ; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mcpts.

Corollary wf_exp_eq_nat_beta_succ' {P} : forall {Δ : gctx P} {Γ A MZ MS M s} {r : Ru_nat P s},
    {{ Δ ; Γ, ℕ ⊢ A }} ->
    {{ Δ ; Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ ; Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ; Γ ⊢ M : ℕ }} ->
    {{ Δ ; Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mcpts.

(** ** Optimized constructors for wf_subtyp *)
Corollary wf_typ_subtyp_refl' {P} : forall {Δ : gctx P} {Γ A B},
    {{ Δ ; Γ ⊢ A ≈ B }} ->
    {{ Δ ; Γ ⊢ A ⊆ B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_typ_subtyp_refl' : mcpts.
#[export]
Remove Hints wf_typ_subtyp_refl : mcpts.

Corollary wf_typ_subtyp_pi' {P} : forall {Δ Γ A A' B B' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Δ ; Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Δ ; Γ, A ⊢ B : Sort@s2 }} ->
    {{ Δ ; Γ, A' ⊢ B' : Sort@s2 }} ->
    {{ Δ ; Γ, A' ⊢ B ⊆ B' }} ->
    {{ Δ ; Γ ⊢ Π r A B ⊆ Π r A' B' }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_typ_subtyp_pi' : mcpts.
#[export]
Remove Hints wf_typ_subtyp_pi : mcpts.
