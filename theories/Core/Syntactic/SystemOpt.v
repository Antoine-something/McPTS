From Coq Require Import Setoid.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export CoreInversions Presup.
Import Syntax_Notations.

Add Parametric Morphism {P : PtsSig} (s : P) Γ : (wf_exp Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> iff as wf_exp_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups;
    eapply wf_conv; mauto 3.
Qed.

Add Parametric Morphism {P : PtsSig} (s : P) Γ : (wf_exp_eq Γ)
    with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3.
Proof with mautosolve.
  split; intros; gen_presups;
    eapply wf_eq_conv; mauto 3.
Qed.

#[local]
Ltac impl_opt_constructor :=
  intros;
  gen_presups;
  mautosolve 4.


Corollary wf_exp_conv' {P} : forall {Γ : ctx P} {A B M},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ⊆ B }} ->
    {{ Γ ⊢ M : B }}.
Proof.
  impl_opt_constructor.
Qed.

Corollary wf_exp_eq_conv' {P} : forall {Γ : ctx P} {A B M M'},
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ M ≈ M' : B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_conv' wf_exp_eq_conv' : mcpts.
#[export]
Remove Hints wf_exp_conv wf_exp_eq_conv : mcpts.

Add Parametric Morphism {P} Γ : (@wf_exp P Γ)
  with signature wf_typ_eq Γ ==> eq ==> iff as wf_exp_morphism_iff3_typ.
Proof with mautosolve.
  split; intros; gen_presups;
  eapply wf_exp_conv'; mauto 3.
Qed.

Add Parametric Morphism {P} Γ : (@wf_exp_eq P Γ)
    with signature wf_typ_eq Γ ==> eq ==> eq ==> iff as wf_exp_eq_morphism_iff3_typ.
Proof with mautosolve.
  split; intros; gen_presups;
    eapply wf_exp_eq_conv'; mauto 3.
Qed.


Corollary wf_vlookup' {P} : forall {Γ : ctx P} {x A s},
    {{ ⊢ Γ }} ->
    {{ #x : A@s ∈ Γ }} ->
    {{ Γ ⊢ #x : A }}.
Proof.
  intros.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_vlookup' : mcpts.
#[export]
Remove Hints wf_vlookup : mcpts.


Corollary wf_conv' {P : PtsSig} : forall (Γ : ctx P) M A A' s,
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv' : mcpts.
#[export]
Remove Hints wf_conv : mcpts.

Corollary eq_conv' {P : PtsSig} : forall (Γ : ctx P) M M' A A' s,
   {{ Γ ⊢ M ≈ M' : A }} ->
   {{ Γ ⊢ A ≈ A' : Sort@s }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve eq_conv' : mcpts.
#[export]
Remove Hints wf_eq_conv : mcpts.

Corollary wf_conv_typ {P} : forall {Γ : ctx P} {M A A'},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  impl_opt_constructor.
Qed.

Corollary eq_conv_typ {P} : forall {Γ : ctx P} {M M' A A'},
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_conv_typ eq_conv_typ : mcpts.
#[export]
Remove Hints wf_conv_unsorted wf_eq_conv_unsorted : mcpts. 

Corollary wf_ctx_eq_extend' {P : PtsSig} : forall {Γ : ctx P} {Δ A A' s},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ ⊢ Γ, A@s ≈ Δ, A'@s }}.
Proof.
  intros.
  gen_presups.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve wf_ctx_eq_extend' : mcpts.
#[export]
Remove Hints wf_ctx_eq_extend : mcpts.


Corollary wf_pi {P : PtsSig} : forall {Γ : ctx P} {A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ Π r A B : Sort@s3 }}.
Proof.
  intros; mauto 2.
Qed.

#[export]
Hint Resolve wf_pi : mcpts.

Corollary wf_fn' {P : PtsSig} : forall {Γ : ctx P} {A M B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ, A@s1 ⊢ M : B }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ λ r A M : Π r A B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_fn' : mcpts.
#[export]
Remove Hints wf_fn : mcpts.

Corollary wf_app' {P : PtsSig} : forall {Γ : ctx P} {M N A B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ M N : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  inversion_clear HAwf0.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }} /\ {{ Γ ⊢ Sort@s3 ⊆ Sort@s }}) as [] by (eapply wf_pi_inversion; mauto 2).
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_app' : mcpts.
#[export]
Remove Hints wf_app : mcpts.

Lemma wf_exp_eq_sort_sub' {P : PtsSig} : forall (Γ : ctx P) σ Δ s s',
    {{ Δ ⊢ Sort@s : Sort@s' }} ->
    {{ Γ ⊢ Sort@s : Sort@s' }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_sort_sub' : mcpts.
#[export]
Hint Rewrite -> @wf_exp_eq_sort_sub' using solve [lia | mauto 3] : mcpts.

Lemma wf_typ_eq_sort_sub' {P} : forall (Γ : ctx P) σ Δ s,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s[σ] ≈ Sort@s }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_typ_eq_sort_sub' : mcpts.

#[export]
Hint Rewrite -> @wf_typ_eq_sort_sub' using solve [lia | mauto 3] : mcpts.

Corollary wf_exp_eq_pi_cong' {P} : forall {Γ A A' s1 s2 s3 B B'} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Γ, A@s1 ⊢ B ≈ B' : Sort@s2 }} ->
    {{ Γ ⊢ Π r A B ≈ Π r A' B' : Sort@s3 }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_cong : mcpts.

Corollary wf_exp_eq_fn_cong' {P : PtsSig} : forall {Γ : ctx P} {A A' s1 s2 s3 B M M'} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Γ, A@s1 ⊢ M ≈ M' : B }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ λ r A M ≈ λ r A' M' : Π r A B }}.
Proof.
  intros.
  econstructor; mauto 2.
  assert ({{ ⊢ Γ }} /\ {{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ ⊢ A' : Sort@s1 }} /\ {{ Γ ⊢ Sort@s1 }}) by (eapply presup_exp_eq; mauto 2).
  destruct_conjs.
  gen_presups.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_cong : mcpts.

Corollary wf_exp_eq_fn_sub' {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M B s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ, A@s1 ⊢ M : B }} ->
    {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ (λ r A M)[σ] ≈ λ r A[σ] M[q σ] : (Π r A B)[σ] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_fn_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_fn_sub : mcpts.

Corollary wf_exp_eq_app_cong' {P : PtsSig} : forall {Γ : ctx P} {A B M M' N N' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M ≈ M' : Π r A B }} ->
    {{ Γ ⊢ N ≈ N' : A }} ->
    {{ Γ ⊢ M N ≈ M' N' : B[Id,,N] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }}) by mauto 2.
  destruct_conjs.
  econstructor; mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_cong : mcpts.

Corollary wf_exp_eq_app_sub' {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : Π r A B }} ->
    {{ Δ ⊢ N : A }} ->
    {{ Γ ⊢ (M N)[σ] ≈ M[σ] N[σ] : B[σ,,N[σ]] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Δ ⊢ A : Sort@s1 }} /\ {{ Δ, A@s1 ⊢ B : Sort@s2 }}) by mauto 2.
  destruct_conjs.
  econstructor; mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_app_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_app_sub : mcpts.

Corollary wf_exp_eq_pi_beta' {P : PtsSig} : forall {Γ : ctx P} {A B M N s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A : Sort@s1 }} ->
    {{ Γ, A@s1 ⊢ M : B }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ N : A }} ->
    {{ Γ ⊢ (λ r A M) N ≈ M[Id,,N] : B[Id,,N] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_pi_beta' : mcpts.
#[export]
Remove Hints wf_exp_eq_pi_beta : mcpts.

Corollary wf_exp_eq_pi_eta' {P : PtsSig} : forall {Γ : ctx P} {A B M s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ ⊢ M ≈ λ r A (M[Wk] #0) : Π r A B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }}) by mauto 2.
  destruct_conjs.
  econstructor; mauto 2.
Qed.


Corollary wf_exp_eq_nat_sub' {P} : forall {Γ : ctx P} {s} {r : Ru_nat P s}  σ Δ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ ℕ[σ] ≈ ℕ : Sort@s }}.
Proof.
  intros.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_sub : mcpts.


Corollary wf_exp_eq_natrec_cong' {P} : forall {Γ : ctx P} {A A' MZ MZ' MS MS' M M' s s'} {r : Ru_nat P s},
    {{ Γ, ℕ@s ⊢ A : Sort@s' }} ->
    {{ Γ, ℕ@s ⊢ A' : Sort@s' }} ->
    {{ Γ, ℕ@s ⊢ A ≈ A' : Sort@s' }} ->
    {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
    {{ Γ, ℕ@s, A@s' ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  try impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_cong' : mcpts.
#[export]
Remove Hints wf_exp_eq_natrec_cong : mcpts.

Corollary wf_exp_eq_natrec_sub' {P} : forall {Γ : ctx P} {σ Δ A MZ MS M s s'} {r : Ru_nat P s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, ℕ@s ⊢ A : Sort@s' }} ->
    {{ Δ ⊢ MZ : A[Id,,zero] }} ->
    {{ Δ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end[σ] ≈ rec M[σ] return A[q σ] | zero -> MZ[σ] | succ -> MS[q (q σ)] end : A[σ,,M[σ]] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_natrec_sub' : mcpts.
#[export]
Remove Hints wf_exp_eq_natrec_sub : mcpts.

Corollary wf_exp_eq_nat_beta_zero' {P} : forall {Γ : ctx P} {A MZ MS s s'} {r : Ru_nat P s},
    {{ Γ, ℕ@s ⊢ A : Sort@s' }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ rec zero return A | zero -> MZ | succ -> MS end ≈ MZ : A[Id,,zero] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_zero' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_beta_zero : mcpts.


Corollary wf_exp_eq_nat_beta_succ' {P} : forall {Γ : ctx P} {A MZ MS M s s'} {r : Ru_nat P s},
    {{ Γ, ℕ@s ⊢ A : Sort@s' }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ rec (succ M) return A | zero -> MZ | succ -> MS end ≈ MS[Id,,M,,rec M return A | zero -> MZ | succ -> MS end] : A[Id,,succ M] }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_exp_eq_nat_beta_succ' : mcpts.
#[export]
Remove Hints wf_exp_eq_nat_beta_succ : mcpts.

(** Optimized constructors for wf_subtyp *)
Corollary wf_subtyp_refl' {P} : forall {Γ : ctx P} {A B},
    {{ Γ ⊢ A ≈ B }} ->
    {{ Γ ⊢ A ⊆ B }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_refl' : mcpts.
#[export]
Remove Hints wf_subtyp_refl : mcpts.

Corollary wf_subtyp_pi' {P} : forall {Γ : ctx P} {A A' B B' s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    {{ Γ ⊢ A ≈ A' : Sort@s1 }} ->
    {{ Γ, A@s1 ⊢ B : Sort@s2 }} ->
        {{ Γ, A'@s1 ⊢ B' : Sort@s2 }} ->
        {{ Γ, A'@s1 ⊢ B ⊆ B' }} ->
        {{ Γ ⊢ Π r A B ⊆ Π r A' B' }}.
Proof.
  impl_opt_constructor.
Qed.

#[export]
Hint Resolve wf_subtyp_pi' : mcpts.
#[export]
Remove Hints wf_subtyp_pi : mcpts.
