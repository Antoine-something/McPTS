From Coq Require Import Setoid Nat.
From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.


Corollary sub_id_typ {P : PtsSig} : forall (Γ : ctx P) M A,
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
  intros * [? [? [?%wf_sub_id_inversion []]]]%wf_exp_sub_inversion.
  assert {{ x ⊢ M : x0[Id] }} by (eapply sub_id_typ; mauto).
  assert {{ Γ ⊢ M : x0[Id] }} by mauto.
  eapply wf_conv'; mauto 4.
Qed.

#[export]
Hint Resolve invert_sub_id : mcpts.
    
Corollary invert_sub_id_typ {P : PtsSig} : forall (Γ : ctx P) M A,
    {{ Γ ⊢ M : A[Id] }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros.
  gen_presups.
  
  (* assert {{ Γ ⊢ A }} by mauto. *)
  (* autorewrite with mcpts in *; eassumption.   *)
Admitted.

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

Add Parametric Morphism {P : PtsSig} (s : St P) Γ Δ : a_sub
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

Lemma app_ctx_lookup {P : PtsSig} : forall (Δ : ctx P) T Γ n,
    length Δ = n ->
    exists K, {{ #n : ^(iter (S n) (fun T => {{{ T[Wk] }}}) T) :: K ∈ ^(Δ ++ (T, K) :: Γ) }}.
Proof.
  (* induction Δ; intros; simpl in *; subst; mauto. *)
Admitted.

Lemma ctx_lookup_functional {P : PtsSig} : forall n (T : exp P) K Γ,
    {{ #n : T :: K ∈ Γ }} ->
    forall T' K',
      {{ #n : T' :: K' ∈ Γ }} ->
      T = T' /\ K = K'.
Proof.
  induction 1; intros; progressive_inversion; eauto.
  (* erewrite IHctx_lookup; eauto. *)
Admitted.

Lemma app_ctx_vlookup {P : PtsSig} : forall (Δ : ctx P) T Γ n K,
    {{ ⊢ ^(Δ ++ (T, K) :: Γ) }} ->
    length Δ = n ->
    {{ ^(Δ ++ (T, K) :: Γ) ⊢ #n : ^(iter (S n) (fun T => {{{ T[Wk] }}}) T) }}.
Proof.
  intros. econstructor; auto using app_ctx_lookup.
Admitted.

Lemma sub_q_eq {P : PtsSig} : forall (Δ : ctx P) A s Γ σ σ',
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ, A[σ]::Sort@s ⊢s q σ ≈ q σ' : Δ, A::Sort@s }}.
Proof.
  intros. gen_presup H0.
  econstructor; mauto 3.
  - econstructor; mauto 4.
  - assert {{ #0 : A[σ][Wk] :: Sort@s ∈ Γ, A[σ]::Sort@s }} by mauto.
    assert {{ Γ, A[σ]::Sort@s ⊢ #0 ≈ #0 : A[σ][Wk] }} by mauto.
    eapply wf_exp_eq_conv'; mauto.
Qed.
#[export]
Hint Resolve sub_q_eq : mcpts.

Lemma wf_subtyp_subst_eq {P : PtsSig} : forall (Δ : ctx P) A B,
    {{ Δ ⊢ A ≈ B }} ->
    forall Γ σ σ',
      {{ Γ ⊢s σ ≈ σ' : Δ }} ->
      {{ Γ ⊢ A[σ] ≈ B[σ'] }}.
Proof.
  mauto.
Qed.

Lemma wf_subtyp_subst {P : PtsSig} : forall (Δ : ctx P) A B,
    {{ Δ ⊢ A ≈ B }} ->
    forall Γ σ,
      {{ Γ ⊢s σ : Δ }} ->
      {{ Γ ⊢ A[σ] ≈ B[σ] }}.
Proof.
  mauto.
Qed.
#[export]
Hint Resolve wf_subtyp_subst_eq wf_subtyp_subst : mcpts.

Lemma exp_typ_sub_lhs {P : PtsSig} : forall {Γ σ Δ s1 s2},
    Ax P s1 s2 ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ Sort@s1[σ] : Sort@s2 }}.
Proof.
  intros; mauto 4.
Qed.
#[export]
Hint Resolve exp_typ_sub_lhs : mcpts.

Lemma sub_decompose_q {P : PtsSig} : forall (Γ : ctx P) S s σ Δ Δ' τ t,
  {{ Γ ⊢ S : Sort@s }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ t : S[σ][τ] }} ->
  {{ Δ' ⊢s q σ ∘ (τ ,, t) ≈ σ ∘ τ ,, t : Γ, S::Sort@s }}.
Proof.
  intros. gen_presups.
  simpl.
  (* autorewrite with mcpts. *)
  (* symmetry. *)
  (* rewrite wf_sub_eq_extend_compose; mauto 3; *)
  (*   [| mauto *)
  (*   | rewrite <- @exp_eq_sub_compose_typ; mauto 4]. *)
  (* eapply wf_sub_eq_extend_cong; eauto. *)
  (* - rewrite wf_sub_eq_compose_assoc; mauto 3; mauto 4. *)
  (*   rewrite wf_sub_eq_p_extend; eauto; mauto 4. *)
  (* - rewrite <- @exp_eq_sub_compose_typ; mauto 4. *)
Admitted.

#[local]
Hint Rewrite -> @sub_decompose_q using mauto 4 : mcpts.

Lemma sub_decompose_q_typ {P : PtsSig} : forall (Γ : ctx P) S T s1 s2 σ Δ Δ' τ t,
  {{ Γ, S::Sort@s1 ⊢ T : Sort@s2 }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ' ⊢ t : S[σ][τ] }} ->
  {{ Δ' ⊢ T[σ∘τ,,t] ≈ T[q σ][τ,,t] : Sort@s2 }}.
Proof.
  intros. gen_presups.
  (* autorewrite with mcpts. *)
  (* eapply exp_eq_sub_cong_typ2'; [mauto 2 | econstructor; mauto 4 |]. *)
  (* eapply sub_eq_refl; econstructor; mauto 3. *)
Admitted.

Lemma sub_eq_p_q_sigma_compose_tau_extend {P : PtsSig} : forall {Δ' : ctx P} {τ Δ M A s σ Γ},
    {{ Δ ⊢s σ : Γ }} ->
    {{ Δ' ⊢s τ : Δ }} ->
    {{ Γ ⊢ A : Sort@s }} ->
    {{ Δ' ⊢ M : A[σ][τ] }} ->
    {{ Δ' ⊢s Wk∘(q σ∘(τ,,M)) ≈ σ∘τ : Γ }}.
Proof.
  intros.
  assert {{ ⊢ Γ, A::Sort@s }} by mauto 3.
  assert {{ Δ, A[σ]::Sort@s ⊢s q σ : Γ, A::Sort@s }} by mauto 2.
  assert {{ Δ' ⊢s τ,,M : Δ, A[σ]::Sort@s }} by mauto 3.
  transitivity {{{ Wk∘((σ∘τ),,M) }}}; [| autorewrite with mcpts; mauto 3].
  eapply wf_sub_eq_compose_cong; [| mauto 2].
  autorewrite with mcpts. econstructor; mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] : Sort@s }} as -> by mauto.
  mauto 3.
Qed.

#[export]
Hint Resolve sub_eq_p_q_sigma_compose_tau_extend : mcpts.
#[export]
Hint Rewrite -> @sub_eq_p_q_sigma_compose_tau_extend using mauto 4 : mcpts.


(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_lhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B s1 s2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] : Sort@s2 }}.
Proof.
  intros.
  assert {{ ⊢ Δ }} by mauto 2.
  assert ({{ Δ ⊢ A : Sort@s1 }}) by mauto 3.
  assert {{ Δ ⊢s Id,,M : Δ, A::Sort@s1 }} by mauto 4.
  autorewrite with mcpts.
  assert {{ Γ ⊢ M[σ] : A[σ] }} by mauto 2.
  assert {{ Γ ⊢s σ,,M[σ] ≈ (Id,,M)∘σ : Δ, A::Sort@s1 }} as -> by mauto.
  eapply wf_exp_eq_conv'; mauto 4.
Qed.
#[export]
Hint Resolve exp_eq_elim_sub_lhs_typ_gen : mcpts.

(** This works for both natrec_sub and app_sub cases *)
Lemma exp_eq_elim_sub_rhs_typ {P : PtsSig} : forall {Γ : ctx P} {σ Δ M A B s1 s2},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] : Sort@s2 }}.
Proof.
  intros.
  assert ({{ Δ ⊢ A : Sort@s1 }}) by mauto 3.
  autorewrite with mcpts.
  assert {{ Γ ⊢s σ∘Id ≈ σ : Δ }} by mauto 3.
  (* assert {{ Γ ⊢s σ,,M ≈ (σ∘Id),,M : Δ, A::Sort@s1 }} as <-; mauto 4. *)
Admitted.
#[export]
Hint Resolve exp_eq_elim_sub_rhs_typ : mcpts.

Lemma exp_eq_sub_cong_typ2 {P : PtsSig} : forall {Δ : ctx P} {Γ A σ τ s},
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Sort@s }}.
Proof with mautosolve 3.
  intros.
  gen_presups.
  mauto.
Qed.
#[export]
Hint Resolve exp_eq_sub_cong_typ2 : mcpts.
#[export]
Remove Hints exp_eq_sub_cong_typ2' : mcpts.

Lemma exp_pi_sub_lhs {P : PtsSig} : forall {Γ : ctx P} {σ Δ A B s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s1 }} ->
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
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
    {{ Δ, A::Sort@s1 ⊢ B : Sort@s2 }} ->
    {{ Γ ⊢ Π r A[σ] B[q σ] : Sort@s3 }}.
Proof.
  intros.
  econstructor; mauto 3.
Qed.
#[export]
Hint Resolve exp_pi_sub_rhs : mcpts.

Lemma exp_pi_eta_rhs_body {P : PtsSig} : forall {Γ : ctx P} {A B M s1 s2 s3} {r : Ru P s1 s2 s3},
    {{ Γ ⊢ M : Π r A B }} ->
    {{ Γ, A::Sort@s1 ⊢ M[Wk] #0 : B }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ A : Sort@s1 }} /\ {{ Γ, A::Sort@s1 ⊢ B : Sort@s2 }}) as [] by mauto 2.
  assert {{ Γ, A::Sort@s1 ⊢s Wk : Γ }} by mauto 3.
  assert {{ Γ, A::Sort@s1, A[Wk]::Sort@s1 ⊢s q Wk : Γ, A::Sort@s1 }} by mauto 3.
  assert {{ Γ, A::Sort@s1 ⊢ M[Wk] : (Π r A B)[Wk] }} by mauto 3.
  assert {{ Γ, A::Sort@s1 ⊢ Π r A[Wk] B[q Wk] ≈ (Π r A B)[Wk] : Sort@s3 }} by mauto 3.
  assert {{ Γ, A::Sort@s1 ⊢ M[Wk] : Π r A[Wk] B[q Wk] }} by mauto 4.
  econstructor; [econstructor; revgoals; mauto 3 | mauto 3 |]. 
  eapply wf_typ_eq_exp.
  (* autorewrite with mcpts. *)
  (* - transitivity {{{ B[Id] }}}; [| mauto 3]. *)
  (*   eapply exp_eq_sub_cong_typ2; mauto 4. *)
  (*   transitivity {{{ Wk,,#0 }}}; [| mauto 3]. *)
  (*   econstructor; mauto 3. *)
  (*   autorewrite with mcpts. *)
  (*   mauto 3. *)
  (* - econstructor; mauto 3. *)
  (*   autorewrite with mcpts. *)
  (*   mauto 3. *)
Admitted.
#[export]
Hint Resolve exp_pi_eta_rhs_body : mcpts.

(** This works for both var_0 and var_S cases *)
Lemma exp_eq_var_sub_rhs_typ_gen {P : PtsSig} : forall {Γ : ctx P} {σ Δ s A M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Sort@s }}.
Proof.
  intros.
  assert {{ Γ ⊢s σ,,M : Δ, A::Sort@s }} by mauto 3.
  (* autorewrite with mcpts. *)
  (* mauto 3. *)
Admitted.
#[export]
Hint Resolve exp_eq_var_sub_rhs_typ_gen : mcpts.

Lemma exp_sub_decompose_double_q_with_id_double_extend {P : PtsSig} : forall (Γ : ctx P) A B C σ Δ M N L s1 s2,
  {{ Γ, B::Sort@s1, C::Sort@s2 ⊢ M : A }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ ⊢ N : B[σ] }} ->
  {{ Δ ⊢ L : C[σ,,N] }} ->
  {{ Δ ⊢ M[σ,,N,,L] ≈ M[q (q σ)][Id,,N,,L] : A[σ,,N,,L] }}.
Proof.
  intros.
  gen_presups.
  assert ({{ Γ ⊢ B : Sort@s1 }}) by mauto 3.
  assert {{ Δ, B[σ]::Sort@s1 ⊢s q σ : Γ, B::Sort@s1 }} by mauto 3.
  assert {{ Δ ⊢s Id,,N : Δ, B[σ]::Sort@s1 }} by mauto 3.
  assert {{ Δ ⊢ L : C[q σ][Id,,N] }} by (rewrite -> @exp_eq_elim_sub_rhs_typ; mauto 3).
  assert {{ Δ ⊢ L : C[q σ∘(Id,,N)] }} by mauto.
  assert {{ Δ ⊢s Id,,N,,L : Δ, B[σ]::Sort@s1, C[q σ]::Sort@s2 }} by mauto 4.
  assert {{ Δ ⊢s q σ∘(Id,,N) ≈ σ,,N : Γ, B::Sort@s1 }} by mauto 3.
  (* exvar (St P) ltac:(fun s => assert {{ Δ ⊢ C[q σ][Id,,N] ≈ C[σ,,N] : Sort@s }} by mauto). *)
  (* assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ (q σ∘(Id,,N)),,L : Γ, B, C }} by (eapply sub_decompose_q; mauto 3). *)
  (* assert {{ Δ ⊢s q (q σ)∘(Id,,N,,L) ≈ σ,,N,,L : Γ, B, C }} by (bulky_rewrite; mauto 3). *)
  (* exvar nat ltac:(fun i => assert {{ Δ ⊢ A[q (q σ)][Id,,N,,L] ≈ A[q (q σ)∘(Id,,N,,L)] : Type@i }} by mauto 3). *)
  (* exvar nat ltac:(fun i => assert {{ Δ ⊢ A[q (q σ)∘(Id,,N,,L)] ≈ A[σ,,N,,L] : Type@i }} as <- by mauto 3). *)
  (* assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[q (q σ)∘(Id,,N,,L)] : A[q (q σ)∘(Id,,N,,L)] }} by mauto 4. *)
  (* assert {{ Δ ⊢ M[q (q σ)][Id,,N,,L] ≈ M[σ,,N,,L] : A[q (q σ)∘(Id,,N,,L)] }} by (bulky_rewrite; mauto 3). *)
  (* symmetry; mauto 3. *)
Admitted.

#[export]
Hint Resolve exp_sub_decompose_double_q_with_id_double_extend : mcpts.

Lemma sub_eq_q_compose {P : PtsSig} : forall {Γ : ctx P} {A s σ Δ τ Δ'},
  {{ Γ ⊢ A : Sort@s }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ' ⊢s τ : Δ }} ->
  {{ Δ', A[σ∘τ]::Sort@s ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, A::Sort@s }}.
Proof.
  intros.
  assert {{ ⊢ Δ' }} by mauto 3.
  assert {{ Δ' ⊢ A[σ∘τ] ≈ A[σ][τ] : Sort@s }} by mauto.
  assert {{ ⊢ Δ', A[σ][τ]::Sort@s }} by mauto 4.
  assert {{ ⊢ Δ', A[σ∘τ]::Sort@s ≈ Δ', A[σ][τ]::Sort@s }} as -> by mauto.
  assert {{ ⊢ Δ }} by mauto 3.
  assert {{ ⊢ Δ, A[σ]::Sort@s }} by mauto 3.
  assert {{ Δ, A[σ]::Sort@s ⊢s Wk : Δ }} by mauto 3.
  assert {{ Δ, A[σ]::Sort@s ⊢ #0 : A[σ][Wk] }} by mauto 3.
  assert {{ Δ, A[σ]::Sort@s ⊢ #0 : A[σ∘Wk] }} by mauto 3.
  transitivity {{{ ((σ∘Wk)∘q τ),,#0[q τ] }}}; [econstructor; mauto 3 |].
  symmetry; econstructor; mauto 3; symmetry.
  - transitivity {{{ σ∘(Wk∘q τ) }}}; [mauto 4 |].
    assert {{ Δ' ⊢ A[σ][τ] : Sort@s }} by mauto 3.
    assert {{ Δ', A[σ][τ]::Sort@s ⊢s Wk : Δ' }} by mauto 3.
    transitivity {{{ σ∘(τ∘Wk) }}}; [| mauto 3].
    econstructor; mauto 3.
  - assert {{ Δ', A[σ][τ]::Sort@s ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘(τ∘Wk)] : Sort@s }} by mauto 4.
    assert {{ Δ', A[σ][τ]::Sort@s ⊢ A[σ∘(τ∘Wk)] ≈ A[σ][τ∘Wk] : Sort@s }} by (eapply wf_exp_eq_conv'; mauto).
    bulky_rewrite.
    econstructor; mauto 3.
    assert {{ Δ', A[σ][τ]::Sort@s ⊢ A[(σ∘τ)∘Wk] ≈ A[σ][τ∘Wk] : Sort@s }} as <- by mauto 3.
    assert {{ Δ', A[σ][τ]::Sort@s ⊢ A[(σ∘τ)∘Wk] ≈ A[σ∘τ][Wk] : Sort@s }} as -> by (eapply wf_exp_eq_conv'; mauto).
    assert {{ Δ', A[σ][τ]::Sort@s ⊢ A[σ∘τ][Wk] ≈ A[σ][τ][Wk] : Sort@s }} as -> by (eapply wf_exp_eq_conv'; mauto 3).
    mauto 4.
Qed.

#[export]
Hint Resolve sub_eq_q_compose : mcpts.
#[export]
Hint Rewrite -> @sub_eq_q_compose using mauto 4 : mcpts.
