From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.


Corollary sub_id_typ {P : PtsSig} : forall (Γ : ctx P) M A s,
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof.
  intros.
  gen_presups.
  mauto 4.
Qed.

#[export]
Hint Resolve sub_id_typ : mcpts.

Corollary invert_sub_id {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M[Id] : A }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros * [? [? [? [?%wf_sub_id_inversion []]]]]%wf_exp_sub_inversion.
  rename x into Δ, x0 into B, x1 into s.
  destruct H1; destruct_conjs.
  - assert {{ Γ ⊢ M : B }} by mauto 3.
    assert {{ Γ ⊢ B[Id] ≈ B : Sort@s }} by mauto 4.
    assert {{ Γ ⊢ A ≈ B }} by mauto 4.    
    eapply wf_exp_conv_typ; mauto 2.
  - assert {{ Γ ⊢ M : B }} by mauto 3.
    mauto 3.
Qed.

#[export]
Hint Resolve invert_sub_id : mcpts.

Corollary invert_typ_id {P : PtsSig} : forall (Γ : ctx P) A,
    {{ Γ ⊢ A[Id] }} ->
    {{ Γ ⊢ A }}.
Proof.
  intros * H.
  inversion_clear H.
  assert {{ Γ ⊢ A : Sort@s }} by mauto 2.
  mauto 2.
Qed.

Hint Resolve invert_typ_id : mcpts.

    
Corollary invert_sub_id_typ {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  inversion_clear H;
    gen_presups.
  - inversion H2.
  - assert {{ Γ ⊢ A : Sort@s }} by mauto 3.
    assert {{ Γ ⊢ A[Id] ≈ A : Sort@s }} by mauto 3.
    mauto 3.
  - assert {{ Γ ⊢ A[Id] ≈ A : Sort@s }} by mauto 4.
    mauto 4.
Qed.

#[export]
Hint Resolve invert_sub_id_typ : mcpts.

Lemma invert_compose_id {P : PtsSig} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ∘Id : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof.
  intros * [? []]%wf_sub_compose_inversion.
  mauto 4.
Qed.

#[export]
Hint Resolve invert_compose_id : mcpts.

Add Parametric Morphism {P : PtsSig} (s : P) Γ Δ : a_sub
    with signature wf_exp_eq Δ {{{ Sort@s }}} ==> wf_sub_eq Γ Δ ==> wf_exp_eq Γ {{{ Sort@s }}} as sub_typ_cong.
Proof.
  intros.
  gen_presups.
  mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ1 : ctx P) Γ2 Γ3 : a_compose
    with signature wf_sub_eq Γ2 Γ3 ==> wf_sub_eq Γ1 Γ2 ==> wf_sub_eq Γ1 Γ3 as sub_compose_cong.
Proof. mauto. Qed.

Lemma wf_ctx_sub_length {P : PtsSig} : forall (Γ : ctx P) Δ,
    {{ ⊢ Γ ≈ Δ }} ->
    length Γ = length Δ.
Proof. induction 1; simpl; auto. Qed.

Open Scope list_scope.

Lemma app_ctx_lookup {P : PtsSig} : forall (Δ : ctx P) T Γ n s,
    length Δ = n ->
    {{ #n : ^(iter (S n) (fun T => {{{ T[Wk] }}}) T)@s ∈ ^(Δ ++ (T, s) :: Γ) }}.
Proof.
  induction Δ; intros; simpl in *; subst; mauto.
  assert {{ # (length Δ) : ^ (iter (length Δ) (fun T0 => {{{ T0[Wk] }}}) T)[Wk]@s ∈ ^ (app Δ {{{ Γ, T@s }}}) }} by mauto.
  destruct_conjs.
  mauto.    
Qed.  

Lemma ctx_lookup_functional {P : PtsSig} : forall n (T : exp P) Γ s,
    {{ #n : T@s ∈ Γ }} ->
    forall T',
      {{ #n : T'@s ∈ Γ }} ->
      T = T'.
Proof.
  induction 1; intros; progressive_inversion; eauto.
  assert (A = A0) by mauto.
  subst.
  mauto.
Qed.

Lemma app_ctx_vlookup {P : PtsSig} : forall (Δ : ctx P) T Γ n s,
    {{ ⊢ ^(Δ ++ (T, s) :: Γ) }} ->
    length Δ = n ->
    {{ ^(Δ ++ (T, s) :: Γ) ⊢ #n : ^(iter (S n) (fun T => {{{ T[Wk] }}}) T) }}.
Proof.
  intros.
  assert {{ #n : ^(iter (S n) (fun T' => {{{ T'[Wk] }}}) T)@s ∈ ^(Δ ++ (T, s) :: Γ) }} by (eapply app_ctx_lookup; mauto).
  subst.
  eapply wf_vlookup'; mauto.
Qed.

Lemma sub_q_eq {P : PtsSig} : forall (Δ : ctx P) A Γ σ σ' s,
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ, A[σ]@s ⊢s q σ ≈ q σ' : Δ, A@s }}.
Proof.
  intros. gen_presup H0.
  econstructor; mauto 3.
  - econstructor; mauto 4.
  - assert {{ #0 : A[σ][Wk]@s ∈ Γ, A[σ]@s }} by mauto.
    assert {{ Γ, A[σ]@s ⊢ #0 ≈ #0 : A[σ][Wk] }} by mauto.
    eapply wf_exp_eq_conv'; mauto.
Qed.
#[export]
Hint Resolve sub_q_eq : mcpts.

(* Lemma wf_subtyp_subst_eq {P : PtsSig} : forall (Δ : ctx P) A B s, *)
(*     {{ Δ ⊢ A ≈ B : Sort@s }} -> *)
(*     forall Γ σ σ', *)
(*       {{ Γ ⊢s σ ≈ σ' : Δ }} -> *)
(*       {{ Γ ⊢ A[σ] ≈ B[σ'] : Sort@s }}. *)
(* Proof. *)
(*   mauto. *)
(* Qed. *)

(* Lemma wf_subtyp_subst {P : PtsSig} : forall (Δ : ctx P) A B, *)
(*     {{ Δ ⊢ A ≈ B }} -> *)
(*     forall Γ σ, *)
(*       {{ Γ ⊢s σ : Δ }} -> *)
(*       {{ Γ ⊢ A[σ] ≈ B[σ] }}. *)
(* Proof. *)
(*   mauto. *)
(* Qed. *)
(* #[export] *)
(* Hint Resolve wf_subtyp_subst_eq wf_subtyp_subst : mcpts. *)

Lemma exp_typ_sub_lhs {P : PtsSig} : forall {Γ σ Δ s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s1[σ] : Sort@s2 }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_typ_sub_lhs : mcpts.

Lemma sub_decompose_q {P : PtsSig} : forall (Γ : ctx P) A σ Δ Δ' τ M s,
  {{ Γ ⊢ A : Sort@s }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ M : A[σ][τ] }} ->
  {{ Δ' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A@s }}.
Proof.
  intros. gen_presups.
  simpl.
  rewrite wf_sub_eq_extend_compose; mauto 3.
  - assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘(Wk∘(τ,,M)) : Γ }}.
    {
      eapply wf_sub_eq_compose_assoc; mauto 3.
      econstructor; mauto 3.
    }
    assert {{ Δ' ⊢s σ∘(Wk∘(τ,,M)) ≈ σ∘τ : Γ }} by (eapply wf_sub_eq_compose_cong; mauto).
    assert {{ Δ' ⊢s (σ∘Wk)∘(τ,,M) ≈ σ∘τ : Γ}} by (etransitivity; mauto).
    assert {{ Δ' ⊢ #0[τ,,M] ≈ M : A[σ][τ] }} by (eapply wf_exp_eq_var_0_sub; mauto).
    eapply wf_sub_eq_extend_cong; mauto 2.
    assert {{ Γ ⊢ A ≈ A : Sort@s }} by mauto.
    assert {{ Δ' ⊢ A[σ][τ] ≈ A[σ∘τ] : Sort@s }} by mauto.
    assert {{ Δ' ⊢ A[σ∘τ] ≈ A[(σ∘Wk)∘(τ,,M)] : Sort@s }} by mauto 4.
    assert {{ Δ' ⊢ A[σ][τ] ≈ A[(σ∘Wk)∘(τ,,M)] : Sort@s }} by (etransitivity; mauto).
    eapply wf_exp_eq_conv; mauto 4.
  - mauto 5.
  - assert {{ Δ, A[σ]@s ⊢ A[σ][Wk] ≈ A[σ∘Wk] : Sort@s }} by (symmetry; mauto).
    assert {{ #0 : A[σ][Wk]@s ∈ Δ, A[σ]@s }} by mauto.
    gen_presup H3.
    eapply wf_exp_conv with (A := {{{ A[σ][Wk] }}}); mauto.
Qed.

#[local]
Hint Rewrite -> @sub_decompose_q using mauto : mcpts.


Lemma sub_decompose_q_typ {P : PtsSig} : forall (Γ : ctx P) A B σ Δ Δ' τ M s s',
  {{ Γ, A@s ⊢ B : Sort@s' }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ M : A[σ][τ] }} ->
  {{ Δ' ⊢ B[σ∘τ,,M] ≈ B[q σ][τ,,M] : Sort@s' }}.
Proof.
  intros. gen_presups.
  assert {{ Δ' ⊢s q σ ∘ (τ ,, M) ≈ σ ∘ τ ,, M : Γ, A@s }} by (eapply sub_decompose_q; mauto 2).
  transitivity {{{ B[(q σ)∘(τ,,M)] }}}; mauto 4.
  eapply wf_exp_eq_sub_compose_sort; mauto 3.
  econstructor; mauto 3.
Qed.

Lemma sub_eq_p_q_sigma_compose_tau_extend {P : PtsSig} : forall {Δ' : ctx P} {τ Δ M A σ Γ s},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ' ⊢s τ : Δ }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Δ' ⊢ M : A[σ][τ] }} ->
    {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ σ∘τ : Γ }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A@s }} by mauto 3.
  assert {{ Δ, A[σ]@s ⊢s q σ : Γ, A@s }} by mauto 2.
  assert {{ Δ' ⊢s τ,,M : Δ, A[σ]@s }} by mauto 3.
  transitivity {{{ Wk∘((σ∘τ),,M) }}}; [| autorewrite with mcpts; mauto 3].
  eapply wf_sub_eq_compose_cong; [| mauto 2].
  autorewrite with mcpts.
  econstructor; mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] : Sort@s }} by mauto.
  eapply wf_exp_eq_conv; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_compose_tau_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_p_q_sigma_compose_tau_extend using mauto 4 : mcpts.


(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_lhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B s s'},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A@s ⊢ B : Sort@s' }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] : Sort@s' }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  
  assert {{ Δ ⊢s Id,,M : Δ, A@s }} by mauto 4.
  autorewrite with mcpts.
  assert {{ Γ ⊢ M[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s σ,,M[σ] ≈ (Id,,M)∘σ : Δ, A@s }} by mauto.
  transitivity {{{ B[(Id,,M)∘σ] }}}; mauto 3.
  eapply wf_exp_eq_sub_cong_sort; mauto 2.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_lhs_typ_gen : mcpts.

(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_rhs_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B s s'},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A@s ⊢ B : Sort@s' }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] : Sort@s' }}.
Proof.
  intros.
  assert {{ Δ ⊢ A : Sort@s }} by mauto 3.
  transitivity {{{ B[(σ∘Id),,M] }}}.
  - symmetry.
    eapply sub_decompose_q_typ; mauto 3.
  - eapply wf_exp_eq_sub_cong_sort; mauto 2.
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_rhs_typ : mcpts.

Lemma exp_eq_sub_cong_typ2 {P : PtsSig} : forall {Δ : ctx P} {Γ A σ τ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof with mautosolve 3.
  mauto.
Qed.

#[export]
Hint Resolve exp_eq_sub_cong_typ2 : mcpts.

Lemma exp_pi_sub_lhs {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ (Π r A B)[σ] : Sort@s3 }}.
Proof.
  intros.
  mauto 4.
Qed.

#[export]
Hint Resolve exp_pi_sub_lhs : mcpts.

Lemma exp_pi_sub_rhs {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ, A@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }}.
Proof.
  intros.
  econstructor; mauto 4.  
Qed.

#[export]
Hint Resolve exp_pi_sub_rhs : mcpts.

Lemma exp_pi_eta_rhs_body {P : PtsSig} : forall {Γ : ctx P} {A B M s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ, A@s1 ⊢ M[Wk] #0 : B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A@s1 ⊢ B : Sort@s2 }}) as [] by mauto 2.
  assert {{ Γ, A@s1 ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A@s1, A[Wk]@s1 ⊢s q Wk : Γ, A@s1 }} by mauto 3.
  assert {{ Γ, A@s1 ⊢ M[Wk] : (Π r A B)[Wk] }} by mauto 3.
  assert {{ Γ, A@s1 ⊢ Π r A[Wk] B[q Wk] ≈ (Π r A B)[Wk] : Sort@s3 }} by mauto 3.
  assert {{ Γ, A@s1 ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by mauto 4.
  eapply wf_conv'; [ econstructor; revgoals; mauto 3 |]; mauto 3.
  
  (* assert {{ Γ,A:Sort@s1 ⊢ B[q Wk][Id,,#0] : Sort@s2 }}. *)
  (* { *)
  (*   admit. *)
  (* } *)
  (* eapply wf_exp *)
  (* econstructor; [econstructor; revgoals; mauto 3 | mauto 3 | mauto 3 |].  *)
  (* eapply wf_typ_eq_exp. *)
  transitivity {{{ B[Wk∘Id,,#0] }}}.
  { 
    symmetry.
    eapply sub_decompose_q_typ; mauto 4.
    eapply wf_conv' with (A := {{{ A[Wk] }}}); mauto 3.
    symmetry.
    assert {{ Γ, A@s1 ⊢ A[Wk] : Sort@s1 }} by mauto 3.
    mauto 2.
  }
  transitivity {{{ B[Wk,,#0] }}}.
  - eapply wf_exp_eq_sub_cong_sort with (Δ := {{{ Γ, A@s1 }}}); [mauto 3 |].
    eapply wf_sub_eq_extend_cong; mauto 2.
    eapply wf_exp_eq_conv'; mauto 3.
    eapply wf_exp_eq_sub_cong_sort; mauto 3.
  - assert {{ Γ, A@s1 ⊢s Wk,,#0 ≈ Id : Γ, A@s1 }} by mauto 3.
    transitivity {{{ B[Id] }}}; mauto.
Qed.
#[export]
Hint Resolve exp_pi_eta_rhs_body : mcpts.

(** This works for both var_0 and var_S cases *)
Lemma exp_eq_var_sub_rhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {σ Δ A M s},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M : Δ, A@s }} by mauto 3.
  assert {{ Δ, A@s ⊢s Wk : Δ }} by mauto 3.
  assert {{ Γ ⊢ A[Wk][σ,,M] ≈ A[Wk∘(σ,,M)] : Sort@s }} by (symmetry; mauto 4).
  assert {{ Γ ⊢s Wk∘(σ,,M) ≈ σ : Δ }} by mauto 2.
  assert {{ Γ ⊢ A[Wk∘(σ,,M)] ≈ A[σ] : Sort@s }} by mauto 3.
  transitivity {{{ A[Wk∘(σ,,M)] }}}; mauto 2.
Qed.
#[export]
Hint Resolve exp_eq_var_sub_rhs_typ_gen : mcpts.

Lemma exp_sub_decompose_double_q_with_id_double_extend {P : PtsSig} : forall (Γ : ctx P) A B C σ Δ M N L sa sb sc,
    {{ Γ, B@sb, C@sc ⊢ A : Sort@sa }} ->
    {{ Γ, B@sb, C@sc ⊢ M : A }} ->
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ ⊢ N : B[σ] }} ->
    {{ Δ ⊢ L : C[σ,,N] }} ->
    {{ Δ ⊢ M[σ,,N,,L] ≈ M[q (q σ)][Id,,N,,L] : A[σ,,N,,L] }}.
Proof.
  intros.
  gen_presups.
  assert {{ Γ ⊢ B : Sort@sb }} by mauto 3.
  
  assert {{ Δ, B[σ]@sb ⊢s q σ : Γ, B@sb }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, B[σ]@sb }} by mauto 3.
  assert {{ Δ ⊢ L : C[q σ][Id,,N] }} by mauto.
  assert {{ Δ ⊢ L : C[q σ∘(Id,,N)] }} by mauto 4.
  assert {{ Δ ⊢s Id,,N,,L : Δ, B[σ]@sb, C[q σ]@sc }} by mauto 4.
  assert {{ Δ ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B@sb }} by mauto 3.
  assert {{ Δ ⊢ C[q σ][Id,,N] ≈ C[σ,,N] : Sort@sc }} by mauto.
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ (q σ∘(Id,,N)),,L : Γ, B@sb, C@sc }} by (eapply sub_decompose_q; mauto 3).
  assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B@sb, C@sc }} by (bulky_rewrite; mauto 4).
  assert {{ Δ ⊢ A[q (q σ)][Id,,N,,L] ≈ A[q (q σ)∘(Id,,N,,L)] : Sort@sa }} by mauto.
  assert {{ Δ ⊢ A[q (q σ)∘(Id,,N,,L)] ≈ A[σ,,N,,L] : Sort@sa }} by mauto.
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[q (q σ)∘(Id,,N,,L)] : A[q (q σ)∘(Id,,N,,L)] }} by mauto. 
  assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[σ,,N,,L] : A[q (q σ)∘(Id,,N,,L)] }} by (bulky_rewrite; mauto 4).  
  symmetry; mauto 3.
Qed.

#[export]
Hint Resolve exp_sub_decompose_double_q_with_id_double_extend : mcpts.


Lemma sub_eq_q_compose {P : PtsSig} : forall {Γ : ctx P} {A σ Δ τ Δ' s},
  {{ Γ ⊢ A : Sort@s }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ', A[σ∘τ]@s ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, A@s }}.
Proof.
  intros.
  assert {{ ⊢ Δ' }} by mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] : Sort@s }} by mauto.
  assert {{ ⊢ Δ', A[σ][τ]@s }} by mauto 4.
  assert {{ ⊢ Δ', A[σ∘τ]@s ≈ Δ', A[σ][τ]@s }} as -> by mauto.
  assert {{ ⊢ Δ }} by mauto 3.
  assert {{ ⊢ Δ, A[σ]@s }} by mauto 3.
  assert {{ Δ, A[σ]@s ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, A[σ]@s ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Δ, A[σ]@s ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  transitivity {{{ ((σ∘Wk)∘q τ),,#0[q τ] }}}; [econstructor; mauto 3 |].
  symmetry; econstructor; mauto 3; symmetry.
  - transitivity {{{ σ∘(Wk∘q τ) }}}; [mauto 4 |].
    assert {{ Δ' ⊢ A[σ][τ] : Sort@s }} by mauto 4.
    assert {{ Δ', A[σ][τ]@s ⊢s Wk : Δ' }} by mauto 3.
    transitivity {{{ σ∘(τ∘Wk) }}}; [| mauto 3].
    econstructor; mauto 3.
  - assert {{ Δ', A[σ][τ]@s ⊢s (σ∘τ)∘Wk ≈ σ∘(τ∘Wk) : Γ }} by mauto 3.
    gen_presup H10.
    assert {{ Δ', A[σ][τ]@s ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘(τ∘Wk)] : Sort@s }} by mauto 3.
    assert {{ Δ', A[σ][τ]@s ⊢ A[σ∘(τ∘Wk)] ≈ A[σ][τ∘Wk] : Sort@s }} by mauto 4.
    assert {{ Δ', A[σ][τ]@s ⊢ A[(σ∘τ)∘Wk] ≈ A[σ][τ∘Wk] : Sort@s }} by mauto 3.
    assert {{ Δ', A[σ][τ]@s ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘τ][Wk] : Sort@s }} by mauto 4.
    assert {{ Δ', A[σ][τ]@s ⊢ A[σ∘τ][Wk] ≈ A[σ][τ][Wk] : Sort@s }} by mauto 3.
    eapply wf_exp_eq_conv' with (A := {{{ A[σ][τ∘Wk] }}}); mauto 4.
    eapply wf_exp_eq_var_0_sub; mauto 3.
    eapply wf_conv' with (A := {{{ A[σ][τ][Wk] }}}); mauto 3.
    symmetry.
    transitivity {{{ A[σ∘τ][Wk] }}}; mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_q_compose : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_compose using mauto 4 : mcpts.

(* Not sure if this is provable, but I am also unsure if it is every used. (note it is not part of the hints) *)  
Lemma wf_exp_sort_sub_eq_sort {P} : forall {Γ : ctx P} {s σ K},
    {{ Γ ⊢ Sort@s[σ] : K }} ->
    {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : K }}.
Proof.
Admitted.
(*   intros. *)
(*   assert (exists Δ K' s', {{ Γ ⊢s σ : Δ }} /\ {{ Δ ⊢ Sort@s : K' }} /\ *)
(*                        (({{ Γ ⊢ K'[σ] ≈ K }} /\ {{ Δ ⊢ K' : Sort@s' }}) \/ ({{ Γ ⊢ K' ≈ K }} /\ {{ Δ ⊢ K' ≈ Sort@s' }}))) as [Δ [K' [s']]] by mauto 2. *)
(*   destruct_conjs. *)
(*   assert (exists s'', Ax P s s'' /\ {{ Δ ⊢ Sort@s'' ≈ K' }}) as [s'' []] by mauto 2. *)
(*   destruct H2; destruct_conjs. *)
(*   -  *)
    
  
(*   assert (exists s', {{ Δ ⊢ Sort@s' ≈ K' }} /\ Ax P s s') as [s' []] by (eapply wf_exp_sort_sort; mauto 2). *)
(*   assert {{ Γ ⊢ Sort@s' ≈ K }}. *)
(*   { *)
(*     transitivity {{{ K'[σ] }}}; mauto 2. *)
(*     transitivity {{{ Sort@s'[σ] }}}; mauto 2. *)
(*     symmetry; mauto 2. *)
(*   } *)
(*   enough {{ Γ ⊢ Sort@s[σ] ≈ Sort@s : Sort@s' }} by mauto 2. *)
(*   mauto 2. *)
(* Qed. *)



(** There lemmas seem to only be needed for equality types *)
(* Lemma wf_exp_eq_eqrec_Aσwkwk_Aσwkwk {P} : forall {Γ : ctx P} {σ Δ A s s'} {r : Ru_nat P s}, *)
(*   {{ Γ ⊢s σ : Δ }} -> *)
(*   {{ Δ ⊢ A : Sort@s' }} -> *)
(*   {{ Γ, A[σ], A[σ][Wk] ⊢ A[σ][Wk∘Wk] ≈ A[σ][Wk][Wk] }}. *)
(* Proof. *)
(*   intros. *)
(*   assert {{ ⊢ Γ, A[σ] }} by mauto 3. *)
(*   assert {{ Γ, A[σ] ⊢ A[σ][Wk] : Sort@s' }} by mauto 4. *)
(*   assert {{ ⊢ Γ, A[σ], A[σ][Wk] }} by mauto 3. *)
(*   assert {{ Γ ⊢ A[σ] : Sort@s' }} by mauto 3. *)
(*   assert {{ Γ ⊢ A[σ] }} by mauto 2. *)
(*   mauto 4. *)
(* Qed. *)

(* Lemma wf_exp_eq_eqrec_Aσwkwkwkτ1 {P} : forall {Γ : ctx P} {Δ Ψ σ τ A B s s'} {r : Ru_nat P s}, *)
(*   {{ Γ ⊢s σ : Δ }} -> *)
(*   {{ Δ ⊢ A : Sort@s' }} -> *)
(*   {{ Ψ ⊢s τ : Γ, A[σ], A[σ][Wk], B }} -> *)
(*   {{ Ψ ⊢ A[σ][Wk][Wk][Wk][τ] ≈ A[σ][Wk][Wk][Wk∘τ] }}. *)
(* Proof. *)
(*   intros. symmetry. *)
(*   gen_presups. *)
(*   assert {{ Γ ⊢ A[σ] : Sort@s' }} by mauto 2. *)
(*   assert {{ Γ, A[σ] ⊢ A[σ][Wk] : Sort@s' }} by mauto 4. *)
(*   assert {{ Γ, A[σ], A[σ][Wk] ⊢ A[σ][Wk][Wk] : Sort@s' }} by mauto 4. *)
(*   mauto. *)
(* Qed. *)

(* Lemma wf_exp_eq_eqrec_Aσwkwkwkτ2 {P} : forall {Γ : ctx P} {Δ Ψ σ τ A B s s'} {r : Ru_nat P s}, *)
(*   {{ Γ ⊢s σ : Δ }} -> *)
(*   {{ Δ ⊢ A : Sort@s' }} -> *)
(*   {{ Ψ ⊢s τ : Γ, A[σ], A[σ][Wk], B }} -> *)
(*   {{ Ψ ⊢ A[σ][Wk][Wk][Wk][τ] ≈ A[σ][Wk][Wk∘Wk∘τ] }}. *)
(* Proof. *)
(*   intros. symmetry. *)
(*   gen_presups. *)
(*   erewrite @wf_exp_eq_eqrec_Aσwkwkwkτ1 with (r := r); mauto 3. *)
(*   assert {{ Γ ⊢ A[σ] : Sort@s' }} by mauto 2. *)
(*   assert {{ Γ, A[σ] ⊢ A[σ][Wk] : Sort@s' }} by mauto 4. *)
(*   eapply wf_typ_eq_sub_compose; mauto 3. *)
(* Qed. *)

(* Lemma wf_exp_eq_eqrec_Aσwkwkwkτ3 {P} : forall {Γ : ctx P} {Δ Ψ σ τ A B s s'} {r : Ru_nat P s}, *)
(*   {{ Γ ⊢s σ : Δ }} -> *)
(*   {{ Δ ⊢ A : Sort@s' }} -> *)
(*   {{ Ψ ⊢s τ : Γ, A[σ], A[σ][Wk], B }} -> *)
(*   {{ Ψ ⊢ A[σ][Wk][Wk][Wk][τ] ≈ A[σ][Wk∘Wk∘Wk∘τ] }}. *)
(* Proof. *)
(*   intros. symmetry. *)
(*   gen_presups. *)
(*   assert {{ Ψ ⊢s Wk∘Wk∘τ : Γ, A[σ] }} by mauto. *)
(*   erewrite @wf_exp_eq_eqrec_Aσwkwkwkτ2 with (P := P); mauto 3. *)
(*   eapply wf_typ_eq_sub_compose; mauto 3. *)
(* Qed. *)

(* #[export] *)
(* Hint Resolve exp_eq_typ_q_sigma_then_weak_weak_extend_succ_var_1 : mcpts. *)    
    
