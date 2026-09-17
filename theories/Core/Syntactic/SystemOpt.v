From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export CoreInversions Presup.
Import Syntax_Notations.

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.

(** * Optimized rules related to context *) 
Corollary wf_ctx_eq_extend' {P} : forall {Γ : ctx P} {Γ' A A'},
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ ⊢ Γ, A ≈ Γ', A' }}.    
Proof.
  intros; gen_presups.
  econstructor; mauto 3.
Qed.

Corollary wf_ctx_subtyp_extend' {P} : forall {Γ : ctx P} {Γ' A A'},
    {{ ⊢ Γ ⊆ Γ' }} ->
    {{ Γ' ⊢ A' }} ->
    {{ Γ ⊢ A ⊆ A' }} ->
    {{ ⊢ Γ, A ⊆ Γ', A' }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_ctx_eq_extend' wf_ctx_subtyp_extend' : mcpts.
#[export]
Remove Hints wf_ctx_eq_extend wf_ctx_subtyp_extend : mcpts.

(** * Optimized rules for expressions *)

(** ** Conversion rules for [wf_exp] *)
Corollary wf_exp_conv' {P} : forall {Γ : ctx P} {A B M},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ⊆ B }} ->
    {{ Γ ⊢ M : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_conv_exp_eq' {P} : forall {Γ : ctx P} {A B M s},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Γ ⊢ M : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_conv_typ_eq' {P} : forall {Γ : ctx P} {A B M},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ M : B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_conv' wf_exp_conv_exp_eq' wf_exp_conv_typ_eq' : mcpts.
#[export]
Remove Hints wf_exp_conv wf_exp_conv_exp_eq wf_exp_conv_typ_eq : mcpts.

(** Rewrite rules associated to optimized conversions *)
Add Parametric Morphism {P} (Γ : ctx P) : (wf_exp Γ)
  with signature wf_typ_subtyp Γ ==> eq ==> Basics.impl as wf_exp_morphism_iff3_subtyp.
Proof.
  intros A B Hsub M HM.
  gen_presups.
  mauto 2.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) s : (wf_exp Γ)
  with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> iff as wf_exp_morphism_iff3_exp_eq.
Proof.
  split; impl_opt_constructor.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) : (wf_exp Γ)
  with signature wf_typ_eq Γ ==> eq ==> iff as wf_exp_morphism_iff3_typ_eq.
Proof.
  split; impl_opt_constructor.
Qed.

(** ** Conversion rules for [wf_exp_eq] *)
Corollary wf_exp_eq_conv' {P} : forall {Γ : ctx P} {A B M M'},
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ⊆ B }} ->
    {{ Γ ⊢ M ≈ M' : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_eq_conv_exp_eq' {P} : forall {Γ : ctx P} {A B M M' s},
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : B }}.
Proof. impl_opt_constructor. Qed.

Corollary wf_exp_eq_conv_typ_eq' {P} : forall {Γ : ctx P} {A B M M'},
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ M ≈ M' : B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_conv' wf_exp_eq_conv_exp_eq' wf_exp_eq_conv_typ_eq' : mcpts.
#[export]
Remove Hints wf_exp_eq_conv wf_exp_eq_conv_exp_eq wf_exp_eq_conv_typ_eq : mcpts.

(** Rewrite rules associated to optimized conversions *)
Add Parametric Morphism {P} (Γ : ctx P) : (wf_exp_eq Γ)
  with signature wf_typ_subtyp Γ ==> eq ==> eq ==> Basics.impl as wf_exp_eq_morphism_iff3_subtyp.
Proof.
  intros A B Hsub M M' HM.
  gen_presups.
  mauto 2.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) s : (wf_exp_eq Γ)
  with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3_exp_eq.
Proof.
  split; impl_opt_constructor.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) : (wf_exp_eq Γ)
  with signature wf_typ_eq Γ ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3_typ_eq.
Proof.
  split; impl_opt_constructor.
Qed.


(** ** Rules for sorts *)
Lemma wf_exp_eq_sort_sub' {P : PtsSig} : forall {Γ : ctx P} {Γ' σ s s'},
    {{ Γ' ⊢ Sort@s : Sort@s' }} ->
    {{ Γ ⊢ Sort@s : Sort@s' }} ->
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s' }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_sort_sub' : mcpts.
#[export]
Hint Rewrite -> @wf_exp_eq_sort_sub' using solve [lia | mauto 3] : mcpts.
#[export]
Remove Hints wf_exp_eq_typ_sub : mcpts.

Lemma wf_typ_eq_sort_sub' {P} : forall {Γ : ctx P} {Γ' σ s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ Sort@s[σ] ≈ Sort@s }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_typ_eq_sort_sub' : mcpts.
#[export]
Hint Rewrite -> @wf_typ_eq_sort_sub' using solve [lia | mauto 3] : mcpts.
#[export]
Remove Hints wf_typ_eq_sub_sort : mcpts.


(** ** Rules for functions *)
Corollary wf_exp_pi' {P : PtsSig} : forall {Γ A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ, A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ Π r A B : Sort@s3 }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_pi' : mcpts.
#[export]
Remove Hints wf_exp_pi : mcpts.

Corollary wf_exp_fn' {P : PtsSig} : forall {Γ A M B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ, A ⊢ M : B }} ->
    {{ Γ, A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ λ r A B M : Π r A B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_fn' : mcpts.
#[export]
Remove Hints wf_exp_fn : mcpts.

Corollary wf_exp_app' {P : PtsSig} : forall {Γ M N A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M N : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  inversion_clear HAwf0.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ Sort@s }}) as [] by (eapply wf_exp_pi_inversion; mauto 2).
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_app' : mcpts.
#[export]
Remove Hints wf_exp_app : mcpts.


Corollary wf_exp_eq_pi_cong' {P} : forall {Γ A A' s1 s2 s3 B B'} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
    {{ Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_cong : mcpts.

Corollary wf_exp_eq_fn_cong' {P : PtsSig} : forall {Γ A A' s1 s2 s3 B B' M M'} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Γ, A ⊢ M ≈ M' : B }} ->
    {{ Γ, A ⊢ B ≈ B' : Sort@s2 }} ->
    {{ Γ ⊢ λ r A B M ≈ λ r A' B' M' : Π r A B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_cong : mcpts.

Corollary wf_exp_eq_fn_sub' {P : PtsSig} : forall {Γ Γ' σ A M B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ A : Sort@s1 }} ->
    {{ Γ', A ⊢ M : B }} ->
    {{ Γ', A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ (λ r A B M)[σ] ≈ λ r A[σ] B[q σ] M[q σ] : (Π r A B)[σ] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_fn_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_sub : mcpts.

Corollary wf_exp_eq_app_cong' {P : PtsSig} : forall {Γ A B M M' N N' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M ≈ M' : Π r A B }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}) as [] by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_cong : mcpts.

Corollary wf_exp_eq_app_sub' {P : PtsSig} : forall {Γ Γ' σ A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ' ⊢ M : Π r A B }} ->
    {{ Γ' ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ' ⊢ A : Sort@s1 }} /\ {{ Γ', A ⊢ B : Sort@s2 }}) as [] by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_sub : mcpts.

Corollary wf_exp_eq_pi_beta' {P : PtsSig} : forall {Γ A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ, A ⊢ M : B }} ->
    {{ Γ, A ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ (λ r A B M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_beta : mcpts.

Corollary wf_exp_eq_pi_eta' {P : PtsSig} : forall {Γ A B M s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ M ≈ λ r A B (M[Wk] #0) : Π r A B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A ⊢ B : Sort@s2 }}) as [] by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_eta' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_eta : mcpts.


(** ** Rules for natural numbers *)
Corollary wf_exp_eq_nat_sub' {P} : forall {Γ s} {r : Ru_nat P s}  σ Γ',
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢ ℕ[σ] ≈ ℕ : Sort@s }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_sub : mcpts.

Corollary wf_exp_eq_natrec_cong' {P} : forall {Γ : ctx P} {A A' MZ MZ' MS MS' M M' s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ, ℕ ⊢ A' }} ->
    {{ Γ, ℕ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mcpts.

Corollary wf_exp_eq_natrec_sub' {P} : forall {Γ : ctx P} {Γ' σ A MZ MS M s} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ', ℕ ⊢ A }} ->
    {{ Γ' ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ', ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_natrec_sub : mcpts.

Corollary wf_exp_eq_nat_beta_zero' {P} : forall {Γ : ctx P} {A MZ MS s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mcpts.

Corollary wf_exp_eq_nat_beta_succ' {P} : forall {Γ : ctx P} {A MZ MS M s} {r : Ru_nat P s},
    {{ Γ, ℕ ⊢ A }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mcpts.

(** ** Optimized constructors for wf_subtyp *)
Corollary wf_typ_subtyp_refl' {P} : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ A ⊆ B }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_typ_subtyp_refl' : mcpts.
#[export]
Remove Hints wf_typ_subtyp_refl : mcpts.

Corollary wf_typ_subtyp_pi' {P} : forall {Γ A A' B B' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Γ, A ⊢ B : Sort@s2 }} ->
    {{ Γ, A' ⊢ B' : Sort@s2 }} ->
    {{ Γ, A' ⊢ B ⊆ B' }} ->
    {{ Γ ⊢ Π r A B ⊆ Π r A' B' }}.
Proof. impl_opt_constructor. Qed.

#[export]
Hint Resolve wf_typ_subtyp_pi' : mcpts.
#[export]
Remove Hints wf_typ_subtyp_pi : mcpts.
