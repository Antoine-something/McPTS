From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Corollaries.
Import Syntax_Notations.

Generalizable All Variables.

Reserved Notation "⊢t Γ ≜ Γ'" (in custom judg at level 80, Γ custom exp, Γ' custom exp).
Reserved Notation "Γ ⊢t M ≜ M' : A" (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp).
Reserved Notation "Γ ⊢t A ≜ A'" (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp).
Reserved Notation "Γ ⊢ts σ ≜ σ' : Δ" (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp).

Section Translation.
  Context (P : PtsSig).
  (* (pred_P : PredicativeSig P). *)

  Definition eSig : PtsSig := eP P.
  (* Definition ePred : PredicativeSig eSig := epred_P P pred_P. *)

  Inductive tr_exp : ctx P -> typ P -> exp P -> exp eSig -> Prop :=
  | tr_st :
    `( forall {s1 s2},
          Ax P s1 s2 ->
          {{ ⊢ Γ }} ->
          {{ Γ ⊢t Sort@s1 ≜ ^(@a_st eSig (st_P s1)) : Sort@s2 }} )
  | tr_pi :
    `( forall {s1 s2 s3} (r : Ru P s1 s2 s3),
          {{ Γ ⊢t A ≜ A' : Sort@s1 }} ->
          {{ Γ, A@s1 ⊢t B ≜ B' : Sort@s2 }} ->
          {{ Γ ⊢t Π r A B ≜ ^(@a_pi eSig _ _ _ (ru_P r) A' B') : Sort@s3 }} )
  | tr_lam :
    `( forall {s1 s2 s3} (r : Ru P s1 s2 s3),
          {{ Γ ⊢t A ≜ A' : Sort@s1 }} ->
          {{ Γ, A@s1 ⊢t B ≜ B' : Sort@s2 }} ->
          {{ Γ, A@s1 ⊢t M ≜ M' : B }} ->
          {{ Γ ⊢t λ r A M ≜ ^(@a_fn eSig _ _ _ (ru_P r) A' M') : Π r A B }} )
  | tr_app :
    `( forall {s1 s2 s3} (r : Ru P s1 s2 s3),
          {{ Γ ⊢t A ≜ A' : Sort@s1 }} ->
          {{ Γ, A@s1 ⊢t B ≜ B' : Sort@s2 }} ->
          {{ Γ ⊢t M ≜ M' : Π r A B }} ->
          {{ Γ ⊢t N ≜ N' : A }} ->
          {{ Γ ⊢t M N ≜ M' N' : B[Id ,, N] }} )
  | tr_var : 
    `( {{ ⊢ Γ }} ->
       {{ # x : A@s ∈ Γ }} ->
       {{ Γ ⊢t #x ≜ #x : A }} )
  | tr_sub_typ :
    `( {{ Δ ⊢t M ≜ M' : A }} ->
       {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
       {{ Δ ⊢ A : Sort@s }} ->
       {{ Γ ⊢t M[σ] ≜ M'[σ'] : A[σ] }} )
  | tr_sub_sort :
    `( {{ Δ ⊢t M ≜ M' : Sort@s }} ->
       {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
       {{ Γ ⊢t M[σ] ≜ M'[σ'] : Sort@s }} )

  | tr_conv :
    `( {{ Γ ⊢t M ≜ M' : A }} ->
       {{ Γ ⊢ A ≈ A' : Sort@s }} ->
       {{ Γ ⊢t M ≜ M' : A' }} )
  where "Γ ⊢t M ≜ M' : A" := (tr_exp Γ A M M') (in custom judg) : type_scope

  with tr_sub : ctx P -> ctx P -> sub P -> sub eSig -> Prop :=
  | tr_id :
    `( {{ ⊢ Γ }} ->
       {{ Γ ⊢ts Id ≜ Id : Γ }} )
  | tr_weaken :
    `( {{ ⊢ Γ, A@s }} ->
       {{ Γ, A@s ⊢ts Wk ≜ Wk : Γ }} )
  | tr_compose :
    `( {{ Γ1 ⊢ts σ2 ≜ σ2' : Γ2 }} ->
       {{ Γ2 ⊢ts σ1 ≜ σ1' : Γ3 }} ->
       {{ Γ1 ⊢ts σ1∘σ2 ≜ σ1'∘σ2' : Γ3 }} )
  | tr_extend :
    `( {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
       {{ Δ ⊢ A : Sort@s }} ->
       {{ Γ ⊢t M ≜ M' : A[σ] }} ->
       {{ Γ ⊢ts σ,,M ≜ σ',,M' : Δ, A@s }} )
  | tr_sub_conv :
    `( {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
       {{ ⊢ Δ ≈ Δ' }} ->
       {{ Γ ⊢ts σ ≜ σ' : Δ' }} )
  where "Γ ⊢ts σ ≜ σ' : Δ" := (tr_sub Γ Δ σ σ') (in custom judg) : type_scope.

  Inductive tr_typ : ctx P -> typ P -> typ eSig -> Prop :=
  | tr_typ_st :
    `( {{ ⊢ Γ }} ->
       {{ Γ ⊢t Sort@s ≜ ^(@a_st eSig (st_P s)) }} )
  | tr_typ_exp :
    `( {{ Γ ⊢t A ≜ A' : Sort@s }} ->
       {{ Γ ⊢t A ≜ A' }} )
  where "Γ ⊢t A ≜ A'" := (tr_typ Γ A A') (in custom judg) : type_scope.

  Inductive tr_ctx : ctx P -> ctx eSig -> Prop :=
  | tr_nil : {{ ⊢t ⋅ ≜ ⋅ }}
  | tr_cons :
    `( {{ ⊢t Γ ≜ Γ' }} ->
       {{ Γ ⊢t A ≜ A' : Sort@s }} ->
       {{ ⊢t Γ, A@s ≜ Γ', A'@^(st_P s) }} )
  where "⊢t Γ ≜ Γ'" := (tr_ctx Γ Γ') (in custom judg) : type_scope.

  #[local]
  Hint Constructors tr_exp tr_sub tr_typ tr_ctx : mcpts.

  Scheme tr_exp_mut_ind := Induction for tr_exp Sort Prop
  with tr_sub_mut_ind := Induction for tr_sub Sort Prop.
  Combined Scheme syntactic_tr_mut_ind from
    tr_exp_mut_ind,
    tr_sub_mut_ind.

  #[local]
  Ltac functional_injective_auto M H :=
    let D := fresh "D" in
    let HD := fresh "HD" in
    remember M as D eqn:HD;
    induction H; directed inversion HD; subst; clear_refl_eqs; mauto 3;
    f_equal; intuition.

  Lemma tr_functional :
    (forall Γ A M M1, {{ Γ ⊢t M ≜ M1 : A }} -> forall Γ' B M2, {{ Γ' ⊢t M ≜ M2 : B }} -> M1 = M2) /\
      (forall Γ Δ σ σ1, {{ Γ ⊢ts σ ≜ σ1 : Δ }} -> forall Γ' Ψ σ2, {{ Γ' ⊢ts σ ≜ σ2 : Ψ }} -> σ1 = σ2).
  Proof using Type.
    apply syntactic_tr_mut_ind;
      intros;
      try (directed inversion H; subst; reflexivity);
      try (directed inversion H1; subst; f_equal; solve [intuition]).
    - functional_injective_auto {{{ Sort@s1 }}} H.
    - functional_injective_auto {{{ Π r A B }}} H1.
      (** UIP *)
      dependent destruction H5; reflexivity.
    - functional_injective_auto {{{ λ r A M }}} H2.
      (** UIP *)
      dependent destruction H6; reflexivity.
    - functional_injective_auto {{{ M N }}} H3.
    - functional_injective_auto (@a_var P x) H.
    - functional_injective_auto {{{ M[σ] }}} H1.
    - functional_injective_auto {{{ M[σ] }}} H1.
    - intuition.
    - functional_injective_auto (@a_id P) H.
    - functional_injective_auto (@a_weaken P) H.
    - functional_injective_auto {{{ σ1∘σ2 }}} H1.
    - functional_injective_auto {{{ σ,,M }}} H1.
    - intuition.
  Qed.
  
  Corollary tr_exp_functional : forall Γ Γ' A B M M1 M2, {{ Γ ⊢t M ≜ M1 : A }} -> {{ Γ' ⊢t M ≜ M2 : B }} -> M1 = M2.
  Proof using Type. intros; eapply tr_functional; eauto. Qed.
  
  Corollary tr_sub_functional : forall Γ Γ' Δ Ψ σ σ1 σ2, {{ Γ ⊢ts σ ≜ σ1 : Δ }} -> {{ Γ' ⊢ts σ ≜ σ2 : Ψ }} -> σ1 = σ2.
  Proof using Type. intros; eapply tr_functional; eauto. Qed.

  Lemma tr_typ_functional : forall Γ Γ' A A1 A2, {{ Γ ⊢t A ≜ A1 }} -> {{ Γ' ⊢t A ≜ A2 }} -> A1 = A2.
  Proof using Type.
    intros; gen A2 Γ'.
    induction H; inversion 1; intros; subst; mauto 2.
    - functional_injective_auto {{{ Sort@s }}} H1.
    - functional_injective_auto {{{ Sort@s0 }}} H.
    - eapply tr_exp_functional; eassumption.
  Qed.

  Lemma tr_ctx_functional : forall Γ Γ1 Γ2, {{ ⊢t Γ ≜ Γ1 }} -> {{ ⊢t Γ ≜ Γ2 }} -> Γ1 = Γ2.
  Proof using Type.
    intros; gen Γ2.
    induction H; inversion_clear 1; [reflexivity | ].
    assert (Γ' = Γ'0) by auto.
    assert (A' = A'0) by (eapply tr_exp_functional; mauto 2).
    subst.
    reflexivity.
  Qed.
    
  Lemma tr_injective :
    (forall Γ A M1 M, {{ Γ ⊢t M1 ≜ M : A }} -> forall Γ' B M2, {{ Γ' ⊢t M2 ≜ M : B }} -> M1 = M2) /\
      (forall Γ Δ σ1 σ, {{ Γ ⊢ts σ1 ≜ σ : Δ }} -> forall Γ' Ψ σ2, {{ Γ' ⊢ts σ2 ≜ σ : Ψ }} -> σ1 = σ2).
  Proof using Type.
    apply syntactic_tr_mut_ind;
      intros;
      try (directed inversion H; subst; reflexivity);
      try (directed inversion H1; subst; f_equal; solve [intuition]).
    - functional_injective_auto (@a_st eSig (st_P s1)) H.
    - functional_injective_auto (@a_pi eSig _ _ _ (ru_P r) A' B') H1.
      (** UIP *)
      dependent destruction H8; reflexivity.
    - functional_injective_auto (@a_fn eSig _ _ _ (ru_P r) A' M') H2.
      (** UIP *)
      dependent destruction H9; reflexivity.
    - functional_injective_auto {{{ M' N' }}} H3.
    - functional_injective_auto (@a_var eSig x) H.
    - functional_injective_auto {{{ M'[σ'] }}} H1.
    - functional_injective_auto {{{ M'[σ'] }}} H1.
    - intuition.
    - functional_injective_auto (@a_id eSig) H.
    - functional_injective_auto (@a_weaken eSig) H.
    - functional_injective_auto {{{ σ1'∘σ2' }}} H1.
    - functional_injective_auto {{{ σ',,M' }}} H1.
    - intuition.
  Qed.

  Corollary tr_exp_injective : forall Γ Γ' A B M1 M2 M, {{ Γ ⊢t M1 ≜ M : A }} -> {{ Γ' ⊢t M2 ≜ M : B }} -> M1 = M2.
  Proof using Type. intros; eapply tr_injective; eauto. Qed.
  Corollary tr_sub_injective : forall Γ Γ' Δ Ψ σ1 σ2 σ, {{ Γ ⊢ts σ1 ≜ σ : Δ }} -> {{ Γ' ⊢ts σ2 ≜ σ : Ψ }} -> σ1 = σ2.
  Proof using Type. intros; eapply tr_injective; eauto. Qed.

  Lemma tr_typ_injective : forall Γ Γ' A1 A2 A, {{ Γ ⊢t A1 ≜ A }} -> {{ Γ' ⊢t A2 ≜ A }} -> A1 = A2.
  Proof using Type.
    intros; gen A2 Γ'.
    induction H; inversion 1; intros; subst; mauto 2.
    - functional_injective_auto (@a_st eSig (st_P s)) H1.
    - functional_injective_auto (@a_st eSig (st_P s0)) H.
    - eapply tr_exp_injective; eassumption.
  Qed.

  Lemma tr_ctx_injective : forall Γ1 Γ2 Γ, {{ ⊢t Γ1 ≜ Γ }} -> {{ ⊢t Γ2 ≜ Γ }} -> Γ1 = Γ2.
  Proof using Type.
    intros; gen Γ2.
    induction H; inversion_clear 1; [reflexivity |].
    assert (Γ = Γ0) by auto.
    assert (A = A0) by (eapply tr_exp_injective; mauto 2).
    subst.
    reflexivity.
  Qed.
End Translation.

Arguments tr_exp {P}.
Arguments tr_st {P}.
Arguments tr_pi {P}.
Arguments tr_lam {P}.
Arguments tr_app {P}.
Arguments tr_var {P}.
Arguments tr_sub_typ {P}.
Arguments tr_sub_sort {P}.
Arguments tr_conv {P}.

Arguments tr_sub {P}.
Arguments tr_id {P}.
Arguments tr_weaken {P}.
Arguments tr_compose {P}.
Arguments tr_extend {P}.
Arguments tr_sub_conv {P}.

Arguments tr_typ {P}.
Arguments tr_typ_st {P}.
Arguments tr_typ_exp {P}.

Arguments tr_ctx {P}.
Arguments tr_nil {P}.
Arguments tr_cons {P}.

Notation "⊢t Γ ≜ Γ'" := (tr_ctx Γ Γ') (in custom judg at level 80, Γ custom exp, Γ' custom exp) : type_scope.
Notation "Γ ⊢t M ≜ M' : A" := (tr_exp Γ A M M') (in custom judg at level 80, Γ custom exp, M custom exp, M' custom exp, A custom exp) : type_scope.
Notation "Γ ⊢t A ≜ A'" := (tr_typ Γ A A') (in custom judg at level 80, Γ custom exp, A custom exp, A' custom exp) : type_scope.
Notation "Γ ⊢ts σ ≜ σ' : Δ" := (tr_sub Γ Δ σ σ') (in custom judg at level 80, Γ custom exp, σ custom exp, σ' custom exp, Δ custom exp) : type_scope.

#[local]
Hint Constructors tr_exp tr_sub tr_typ tr_ctx : mcpts.

#[export]
Hint Resolve tr_exp_functional tr_sub_functional tr_typ_functional tr_ctx_functional : mcpts.

Ltac functional_tr_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "tr_functional equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ ^_ ⊢t ^?M ≜ ^?M1 : ^_ }},
      H2 : {{ ^_ ⊢t ^?M ≜ ^?M2 : ^_ }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : {{ ^_ ⊢ts ^?σ ≜ ^?σ1 : ^_ }},
      H2 : {{ ^_ ⊢ts ^?σ ≜ ^?σ2 : ^_ }} |- _ =>
      clean replace σ2 with σ1 by first [solve [mauto 2] | tactic_error σ2 σ1]; clear H2
  | H1 : {{ ^_ ⊢t ^?A ≜ ^?A1 }},
      H2 : {{ ^_ ⊢t ^?A ≜ ^?A2 }} |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2] | tactic_error A2 A1]; clear H2
  | H1 : {{ ^_ ⊢t ^?M ≜ ^?M1 : ^_ }},
      H2 : {{ ^_ ⊢t ^?M ≜ ^?M2 }} |- _ =>
      let H := fresh "H" in
      assert {{ ^_ ⊢t M ≜ M1 }} as H by mauto 3;
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H H2
  | H1 : {{ ⊢t ^?Γ ≜ ^?Γ1 }},
      H2 : {{ ⊢t ^?Γ ≜ ^?Γ2 }} |- _ =>
      clean replace Γ2 with Γ1 by first [solve [mauto 2] | tactic_error Γ2 Γ1]; clear H2
  end.
Ltac functional_tr_rewrite_clear := repeat functional_tr_rewrite_clear1.

#[export]
Hint Resolve tr_exp_injective tr_sub_injective tr_typ_injective tr_ctx_injective : mcpts.

Ltac injective_tr_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "tr_functional equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : {{ ^_ ⊢t ^?M1 ≜ ^?M : ^_ }},
      H2 : {{ ^_ ⊢t ^?M2 ≜ ^?M : ^_ }} |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : {{ ^_ ⊢ts ^?σ1 ≜ ^?σ : ^_ }},
      H2 : {{ ^_ ⊢ts ^?σ2 ≜ ^?σ : ^_ }} |- _ =>
      clean replace σ2 with σ1 by first [solve [mauto 2] | tactic_error σ2 σ1]; clear H2
  | H1 : {{ ^_ ⊢t ^?A1 ≜ ^?A }},
      H2 : {{ ^_ ⊢t ^?A2 ≜ ^?A }} |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2] | tactic_error A2 A1]; clear H2
  | H1 : {{ ^_ ⊢t ^?M1 ≜ ^?M : ^_ }},
      H2 : {{ ^_ ⊢t ^?M2 ≜ ^?M }} |- _ =>
      let H := fresh "H" in
      assert {{ ^_ ⊢t M1 ≜ M }} as H by mauto 3;
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H H2
  | H1 : {{ ⊢t ^?Γ1 ≜ ^?Γ }},
      H2 : {{ ⊢t ^?Γ2 ≜ ^?Γ }} |- _ =>
      clean replace Γ2 with Γ1 by first [solve [mauto 2] | tactic_error Γ2 Γ1]; clear H2
  end.
Ltac injective_tr_rewrite_clear := repeat injective_tr_rewrite_clear1.

Ltac destruct_tr H :=
  match type of H with
  | {{ ^_ ⊢t Sort@?s ≜ ^?M' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢t Π ?r ^?A ^?B ≜ ^?M' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢t λ ?r ^?A ^?M ≜ ^?M' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢t ^?M ^?N ≜ ^?M' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢t #?n ≜ ^?M' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢t ^?M[^?σ] ≜ ^?M' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢ts Id ≜ ^?σ' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢ts Wk ≜ ^?σ' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢ts ^?σ∘^?τ ≜ ^?σ' : ^_ }} => dependent destruction H
  | {{ ^_ ⊢ts ^?σ,,^?M ≜ ^?σ' : ^_ }} => dependent destruction H
  | {{ ⊢t ⋅ ≜ ^?Γ' }} => dependent destruction H
  | {{ ⊢t ^?Γ, ^?A@^?K ≜ ^?Γ' }} => dependent destruction H
  end;
  functional_tr_rewrite_clear.

Ltac invert_tr P H :=
  match type of H with
  | {{ ^?Γ ⊢t Sort@?s ≜ ^?M' : ^_ }} =>
      assert {{ Γ ⊢t Sort@s ≜ ^(@a_st (eSig P) (st_P s)) : A }} by mauto 3;
      functional_tr_rewrite_clear
  | {{ ^_ ⊢t Π ?r ^?A ^?B ≜ ^?M' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t λ ?r ^?A ^?M ≜ ^?M' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t ^?M ^?N ≜ ^?M' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t #?n ≜ ^?M' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t ^?M[^?σ] ≜ ^?M' : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts Id ≜ ^?σ' : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts Wk ≜ ^?σ' : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts ^?σ∘^?τ ≜ ^?σ' : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts ^?σ,,^?M ≜ ^?σ' : ^_ }} => directed inversion H
  | {{ ^?Γ ⊢t Sort@?s ≜ ^?M' }} =>
      assert {{ Γ ⊢t Sort@s ≜ ^(@a_st (eSig P) (st_P s)) }} by mauto 3;
      functional_tr_rewrite_clear
  | {{ ⊢t ⋅ ≜ ^?Γ' }} => directed inversion H
  | {{ ⊢t ^?Γ, ^?A@^?K ≜ ^?Γ' }} => directed inversion H
  end;
  subst.

Ltac invert_inv_tr P H :=
  match type of H with
  | {{ ^_ ⊢t ^?M ≜ ^(@a_st (eSig P) (st_P ?s)) : ^_ }} =>
      assert {{ Γ ⊢t Sort@s ≜ ^(@a_st (eSig P) (st_P s)) }} by mauto 3;
      injective_tr_rewrite_clear
  | {{ ^_ ⊢t ^?M ≜ Sort@?s' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t ^?M ≜ Π ?r' ^?A' ^?B' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t ^?M ≜ λ ?r' ^?A' ^?M' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t ^?M ≜ ^?M' ^?N' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t ^?M ≜ #?n' : ^_ }} => directed inversion H
  | {{ ^_ ⊢t ^?M ≜ ^?M'[^?σ'] : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts ^?σ ≜ Id : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts ^?σ ≜ Wk : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts ^?σ ≜ ^?σ'∘^?τ' : ^_ }} => directed inversion H
  | {{ ^_ ⊢ts ^?σ ≜ ^?σ',,^?M' : ^_ }} => directed inversion H
  | {{ ^?Γ ⊢t ^?M ≜ Sort@?s' }} => directed inversion H
  | {{ ^?Γ ⊢t ^?M ≜ ^(@a_st (eSig P) (st_P ?s)) }} =>
      assert {{ Γ ⊢t Sort@s ≜ ^(@a_st (eSig P) (st_P s)) }} by mauto 3;
      injective_tr_rewrite_clear
  | {{ ⊢t ^?Γ ≜ ⋅ }} => directed inversion H
  | {{ ⊢t ^?Γ ≜ ^?Γ', ^?A'@^?K' }} => directed inversion H
  end;
  subst.

(* Ltac apply_tr_IH := *)
(*   match goal with *)
(*   (* Cases for contexts *) *)
(*   | H1 : forall Γ', tr_ctx ?Γ Γ' -> {{ ⊢ Γ' }}, *)
(*     H2 : {{ ⊢ ^?Γ }} |- {{ ⊢ ^?Γ' }} => (eapply H1; try econstructor; mauto 2) *)
(*   | H1 : forall Γ' Δ', tr_ctx ?Γ Γ' -> tr_ctx ?Δ Δ' -> {{ ⊢ Γ' ≈ Δ' }}, *)
(*     H2 : {{ ⊢ ^?Γ ≈ ^?Δ }} |- {{ ⊢ ^?Γ' ≈ ^?Δ' }} => eapply H1; try econstructor; mauto 2 *)
(*   (* Cases for terms *) *)
(*   | H1 : forall Γ' A' M', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?A A' -> {{ Γ' ⊢ M' : A' }}, *)
(*     H2 : {{ ^?Γ ⊢ ^?M : ^?A }}, *)
(*     H3 : tr_ctx ?Γ ?Γ', H4 : tr_exp ?M ?M', H5 : tr_exp ?A ?A' *)
(*     |- {{ ^?Γ' ⊢ ^?M' : ^?A' }} => eapply H1; try econstructor; mauto 2 *)
(* | H1 : forall Γ' A' M' N', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?N N' -> tr_exp ?A A' -> {{ Γ' ⊢ M' ≈ N' : A' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} |- {{ ^?Γ' ⊢ ^?M' ≈ ^?N' : ^?A' }} => eapply H1; try econstructor; mauto 2 *)
(*     (* Cases for types *) *)
(*      | H1 : forall Γ' A', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> {{ Γ' ⊢ A' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?A }} |- {{ ^?Γ' ⊢ ^?A' }} => eapply H1; try econstructor; mauto 2 *)
(*      | H1 : forall Γ' A' B', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> tr_exp ?B B' -> {{ Γ' ⊢ A' ≈ B' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?A ≈ ^?B }} |- {{ ^?Γ' ⊢ ^?A' ≈ ^?B' }} => eapply H1; try econstructor; mauto 2 *)
(*     (* Cases for substitutions *) *)
(*      | H1 : forall Γ' Δ' σ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' : Δ' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?σ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2 *)
(*      | H1 : forall Γ' Δ' σ' τ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_sub ?τ τ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' ≈ τ' : Δ' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?σ ≈ ^?τ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' ≈ ^?τ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2 *)
(*      | _ => idtac *)
(*      end. *)

(* Ltac apply_tr_IH' := *)
(*   match goal with *)
(*   (* Cases for contexts *) *)
(*   | H1 : forall Γ', tr_ctx ?Γ Γ' -> {{ ⊢ Γ' }}, *)
(*     H2 : {{ ⊢ ^?Γ }} |- {{ ⊢ ^?Γ' }} => (eapply H1; try econstructor; mauto 2) *)
(*   | H1 : forall Γ' Δ', tr_ctx ?Γ Γ' -> tr_ctx ?Δ Δ' -> {{ ⊢ Γ' ≈ Δ' }}, *)
(*     H2 : {{ ⊢ ^?Γ ≈ ^?Δ }} |- {{ ⊢ ^?Γ' ≈ ^?Δ' }} => eapply H1; try econstructor; mauto 2 *)
(*   (* Cases for terms *) *)
(*   | H1 : forall Γ' A' M', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?A A' -> {{ Γ' ⊢ M' : A' }}, *)
(*     H2 : {{ ^?Γ ⊢ ^?M : ^?A }}, *)
(*     H3 : tr_ctx ?Γ ?Γ', H4 : tr_exp ?M ?M', H5 : tr_exp ?A ?A' *)
(*                                             |- _ => try (assert {{ ^?Γ' ⊢ ^?M' : ^?A' }} by (eapply H1; mauto 2)) *)
(* | H1 : forall Γ' A' M' N', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?N N' -> tr_exp ?A A' -> {{ Γ' ⊢ M' ≈ N' : A' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} |- {{ ^?Γ' ⊢ ^?M' ≈ ^?N' : ^?A' }} => eapply H1; try econstructor; mauto 2 *)
(*     (* Cases for types *) *)
(*      | H1 : forall Γ' A', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> {{ Γ' ⊢ A' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?A }} |- {{ ^?Γ' ⊢ ^?A' }} => eapply H1; try econstructor; mauto 2 *)
(*      | H1 : forall Γ' A' B', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> tr_exp ?B B' -> {{ Γ' ⊢ A' ≈ B' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?A ≈ ^?B }} |- {{ ^?Γ' ⊢ ^?A' ≈ ^?B' }} => eapply H1; try econstructor; mauto 2 *)
(*     (* Cases for substitutions *) *)
(*      | H1 : forall Γ' Δ' σ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' : Δ' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?σ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2 *)
(*      | H1 : forall Γ' Δ' σ' τ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_sub ?τ τ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' ≈ τ' : Δ' }}, *)
(*        H2 : {{ ^?Γ ⊢ ^?σ ≈ ^?τ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' ≈ ^?τ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2 *)
(*      | _ => idtac *)
(*      end. *)

Lemma extract_tr {P} :
  (forall (Γ : ctx P) A M M',
      {{ Γ ⊢t M ≜ M' : A }} ->
      {{ Γ ⊢ M : A }}) /\
    (forall (Γ : ctx P) Δ σ σ',
        {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
        {{ Γ ⊢s σ : Δ }}).
Proof.
  apply syntactic_tr_mut_ind; intros; mauto 2.
Qed.    

Lemma extract_tr1 {P} : forall (Γ : ctx P) A M M',
    {{ Γ ⊢t M ≜ M' : A }} ->
    {{ Γ ⊢ M : A }}.
Proof. pose proof (@extract_tr P); intuition. Qed.

Lemma extract_tr2 {P} : forall (Γ : ctx P) Δ σ σ',
    {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
    {{ Γ ⊢s σ : Δ }}.
Proof. pose proof (@extract_tr P); intuition. Qed.

#[local]
Hint Resolve extract_tr1 extract_tr2 : mcpts.

Lemma extract_tr3 {P} : forall (Γ : ctx P) A A',
    {{ Γ ⊢t A ≜ A' }} ->
    {{ Γ ⊢ A }}.
Proof. induction 1; mauto 3. Qed.

#[local]
Hint Resolve extract_tr3 : mcpts.

Lemma extract_tr4 {P} : forall (Γ : ctx P) Γ',
    {{ ⊢t Γ ≜ Γ' }} ->
    {{ ⊢ Γ }}.
Proof. induction 1; mauto 3. Qed.

#[local]
Hint Resolve extract_tr4 : mcpts.

#[local]
Ltac tr_judg_auto := try solve [mauto 2 | econstructor; mauto 2 | timeout 1 (do 5 (econstructor; mauto 2))].

Lemma tr_lookup {P} : forall {Γ : ctx P} {Γ'},
    tr_ctx Γ Γ' ->
    forall {s A x},
      {{ # x : A@s ∈ Γ }} ->
      exists A', {{ Γ ⊢t A ≜ A' : Sort@s }} /\ {{ # x : A'@^(st_P s) ∈ Γ' }}.
Proof.
  induction 1; inversion 1; subst.
  - eexists.
    do 3 (econstructor; mauto 3).
  - specialize (IHtr_ctx _ _ _ H6).
    destruct_conjs.
    eexists.
    do 3 (econstructor; mauto 3).
Qed.

#[local]
Hint Resolve tr_lookup : mcpts.

Lemma tr_ctx_eq {P} :
  (forall (Γ : ctx P) A M M',
      {{ Γ ⊢t M ≜ M' : A }} ->
      forall Γ',
        {{ ⊢ Γ ≈ Γ' }} ->
        {{ Γ' ⊢t M ≜ M' : A }}) /\
    (forall (Γ : ctx P) Δ σ σ',
        {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
        forall Γ',
          {{ ⊢ Γ ≈ Γ' }} ->
          {{ Γ' ⊢ts σ ≜ σ' : Δ }}).
Proof.
  apply syntactic_tr_mut_ind; intros; mauto 3.
  - econstructor; mauto 3.
    eapply H0; mauto 4.
  - econstructor; mauto 2.
    + eapply H0; mauto 4.
    + eapply H1; mauto 4.
  - econstructor; mauto 2.
    eapply H0; mauto 4.
  - epose proof (@ctxeq_lookup_helper P _ _ _ _ ltac:(eassumption) _ ltac:(symmetry; eassumption)).
    destruct_conjs.
    eapply tr_conv; [| symmetry]; mauto 3.
  - econstructor; mauto 2.
  - econstructor; mauto 3.
  - inversion H; subst.
    econstructor; mauto 3.
  - econstructor; mauto 3.
Qed.

Corollary tr_exp_ctx_eq {P} : forall (Γ : ctx P) Γ' A M M',
    {{ Γ ⊢t M ≜ M' : A }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ Γ' ⊢t M ≜ M' : A }}.
Proof. intros; eapply tr_ctx_eq; mauto 2. Qed.

Corollary tr_sub_ctx_eq {P} : forall (Γ : ctx P) Γ' Δ σ σ',
    {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ Γ' ⊢ts σ ≜ σ' : Δ }}.
Proof. intros; eapply tr_ctx_eq; mauto 2. Qed.

#[local]
Hint Resolve tr_exp_ctx_eq tr_sub_ctx_eq : mcpts.

#[local]
Lemma tr_judg_helper {P} : forall (Γ : ctx P) Δ s A σ,
    {{ Δ ⊢ A : Sort@s }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ]@s ⊢t #0 ≜ #0 : A[σ∘Wk] }}.
Proof.
  intros.
  eapply tr_conv; mauto 4.
  eapply exp_eq_sub_compose_typ_sorted; mauto 4.
Qed.

#[local]
Hint Resolve tr_judg_helper : mcpts.

Lemma tr_judg {P} :
  (forall (Γ : ctx P), {{ ⊢ Γ }} ->
                    exists Γ', {{ ⊢t Γ ≜ Γ' }} /\ {{ ⊢ Γ' }}) /\
    (forall (Γ : ctx P) Δ, {{ ⊢ Γ ≈ Δ }} ->
                         exists Γ' Δ', {{ ⊢t Γ ≜ Γ' }} /\ {{ ⊢t Δ ≜ Δ' }} /\ {{ ⊢ Γ' ≈ Δ' }}) /\
    (forall (Γ : ctx P) A M, {{ Γ ⊢ M : A }} ->
                          exists Γ' A' M', {{ ⊢t Γ ≜ Γ' }} /\ {{ Γ ⊢t M ≜ M' : A }} /\ {{ Γ ⊢t A ≜ A' }} /\ {{ Γ' ⊢ M' : A' }}) /\
    (forall (Γ : ctx P) A M N, {{ Γ ⊢ M ≈ N : A }} ->
                            exists Γ' A' M' N', {{ ⊢t Γ ≜ Γ' }} /\ {{ Γ ⊢t M ≜ M' : A }} /\ {{ Γ ⊢t N ≜ N' : A }} /\ {{ Γ ⊢t A ≜ A' }} /\ {{ Γ' ⊢ M' ≈ N' : A' }}) /\
    (forall (Γ : ctx P) Δ σ, {{ Γ ⊢s σ : Δ }} ->
                            exists Γ' Δ' σ', {{ ⊢t Γ ≜ Γ' }} /\ {{ Γ ⊢ts σ ≜ σ' : Δ }} /\ {{ ⊢t Δ ≜ Δ' }} /\ {{ Γ' ⊢s σ' : Δ' }}) /\
    (forall (Γ : ctx P) Δ σ τ, {{ Γ ⊢s σ ≈ τ : Δ }} ->
                               exists Γ' Δ' σ' τ', {{ ⊢t Γ ≜ Γ' }} /\ {{ Γ ⊢ts σ ≜ σ' : Δ }} /\ {{ Γ ⊢ts τ ≜ τ' : Δ }} /\ {{ ⊢t Δ ≜ Δ' }} /\ {{ Γ' ⊢s σ' ≈ τ' : Δ' }}).
Proof.
  apply syntactic_wf_mut_ind.
  all: intros;
    destruct_conjs;
    functional_tr_rewrite_clear;
    (on_all_hyp: invert_tr P);
    functional_tr_rewrite_clear;
    try match goal with
      | H : {{ # _ : ^_@^_ ∈ ^_ }} |- _ =>
          pose proof (tr_lookup ltac:(eassumption) H);
          destruct_conjs
      end;
    functional_tr_rewrite_clear;
    try (repeat eexists; mautosolve 3).
  - repeat eexists; mauto 3.
    do 2 (econstructor; mauto 2).
  - assert {{ Γ ⊢t Π r A B ≜ ^(@a_pi (eSig P) _ _ _ (ru_P r) H22 H16) }} by mauto 3.
    functional_tr_rewrite_clear.
    repeat eexists; mauto 3.
    do 4 (econstructor; mauto 3).
  - repeat eexists; mauto 3.
    assert {{ ⊢ Δ }} by mauto 2.
    + econstructor; mauto 3.
    + do 2 (econstructor; mauto 3).
  - repeat eexists; [mautosolve 3 | mautosolve 4 | | mautosolve 3 |].
    + do 5 (econstructor; mauto 3).
    + mauto 3.
  - repeat eexists; mauto 3.
    assert {{ ⊢ Γ, A@s1 ≈ Γ, A'@s1 }} by (eapply wf_ctx_eq_extend'; mauto 3).
    do 2 (econstructor; mauto 3).
  - repeat eexists; mauto 3.
    assert {{ ⊢ Γ, A@s1 ≈ Γ, A'@s1 }} by (eapply wf_ctx_eq_extend'; mauto 3).
    econstructor; do 2 (econstructor; mauto 3).
  - repeat eexists; [mautosolve 3 | mautosolve 4 | | mautosolve 4 | mautosolve 4].
    eapply tr_conv.
    + econstructor; mauto 3; revgoals.
      * do 4 (econstructor; mauto 3).
      * do 4 (econstructor; mauto 3).
    + mauto 3.
  - assert {{ Γ ⊢t Π r A B ≜ ^(@a_pi (eSig P) _ _ _ (ru_P r) H26 H20) }} by mauto 3.
    functional_tr_rewrite_clear.
    repeat eexists; mauto 3;
      do 4 (econstructor; mauto 3).
  - assert {{ Δ ⊢t Π r A B ≜ ^(@a_pi (eSig P) _ _ _ (ru_P r) H23 H17) }} by mauto 3.
    functional_tr_rewrite_clear.
    repeat eexists; [mautosolve 3 | | | econstructor; mautosolve 4 |].
    + eapply tr_conv; [econstructor |]; mautosolve 3.
    + eapply tr_conv; [econstructor | mautosolve 3]; revgoals.
      * econstructor; mauto 3.
      * econstructor; mauto 3.
      * do 4 (econstructor; mauto 3).
      * econstructor; mauto 3.
    + mauto 3.
  - repeat eexists; mauto 3; do 4 (econstructor; mauto 3).
  - assert {{ Γ ⊢t Π r A B ≜ ^(@a_pi (eSig P) _ _ _ (ru_P r) H15 H9) }} by mauto 3.
    functional_tr_rewrite_clear.
    repeat eexists; [mautosolve 3 | mautosolve 3 | | mautosolve 3 |].
    + do 2 (econstructor; mauto 3).
      eapply tr_conv.
      * econstructor; [| | | mautosolve 3];
          [econstructor; mautosolve 3 | | econstructor; mauto 3; econstructor; mautosolve 3].
        do 2 (econstructor; mauto 3); [do 2 (econstructor; mauto 3) |].
        eapply tr_conv; mauto 4.
        eapply exp_eq_refl; econstructor; mauto 2.
        econstructor; mauto 4.
      * transitivity {{{ B[Id] }}}; [| mautosolve 3].
        transitivity {{{ B[Wk,,#0] }}}; [eapply exp_eq_elim_sub_rhs_typ; mautosolve 3 |].
        econstructor; mauto 3.
    + mauto 3.
  - repeat eexists; [mautosolve 3 | | mautosolve 3 | mautosolve 3 |].
    + econstructor; [econstructor |]; [| mautosolve 3 | | mautosolve 3].
      * econstructor; mauto 3.
      * do 2 (econstructor; mauto 3).
    + assert {{ Γ ⊢t A[σ] ≜ H9[H15] }} by (econstructor; mauto 3).
      functional_tr_rewrite_clear.
      econstructor; mauto 3.
  - repeat eexists; [mautosolve 3 | | econstructor; mautosolve 3 | mautosolve 3 |].
    * do 4 (econstructor; mauto 3).
    * assert {{ Γ ⊢t A[σ] ≜ H9[H15] }} by (econstructor; mauto 3).
      functional_tr_rewrite_clear.
      econstructor; mauto 3.
  - repeat eexists; [mautosolve 3 | | | |];
      econstructor; mautosolve 3.
  - repeat eexists; [| | econstructor; mautosolve 3 | |]; mautosolve 3.
  - gen_presup w.
    inversion HAwf; subst.
    + repeat eexists; mautosolve 3.
    + repeat eexists; [mautosolve 3 | econstructor; mautosolve 3 | | |]; mautosolve 3.
  - repeat eexists; mauto 3;
      do 2 (econstructor; mauto 3).
  - repeat eexists; mauto 3.
    assert {{ Γ ⊢t A[σ] ≜ H9[H15] }} by (econstructor; mauto 3).
    functional_tr_rewrite_clear.
    econstructor; mauto 3.
  - assert {{ Γ ⊢t A[σ] ≜ H11[H17] }} by (econstructor; mauto 3).
    functional_tr_rewrite_clear.
    repeat eexists; mauto 3.
    econstructor; mauto 3.
  - repeat eexists; [mautosolve 3 | econstructor; mautosolve 3 | | |]; mautosolve 3.
  - repeat eexists; [mautosolve 3 | econstructor; mautosolve 3 | | |]; mautosolve 3.
  - assert {{ Γ' ⊢t A[σ] ≜ H16[H22] }} by (econstructor; mauto 3).
    functional_tr_rewrite_clear.
    repeat eexists; [mautosolve 3 | econstructor; [econstructor |]; mautosolve 3 | | mautosolve 3 |];
      do 2 (econstructor; mauto 3).
  - assert {{ Γ' ⊢t A[σ] ≜ H9[H15] }} by (econstructor; mauto 3).
    functional_tr_rewrite_clear.
    repeat eexists; [mautosolve 3 | | mautosolve 3 | mautosolve 3 |].
    + do 2 (econstructor; mauto 3).
    + mauto 3.
  - repeat eexists; [mautosolve 3 | mautosolve 3 | | mautosolve 3 |].
    + do 2 (econstructor; mauto 3).
      * econstructor; mauto 3.
      * eapply exp_eq_sub_compose_typ_sorted; mauto 3.
    + econstructor; mauto 3.
Qed.


Scheme wf_ctx_eq_mut_ind'' := Induction for wf_ctx_eq Sort Prop
with wf_exp_eq_mut_ind'' := Induction for wf_exp_eq Sort Prop
with wf_sub_eq_mut_ind'' := Induction for wf_sub_eq Sort Prop.
Combined Scheme syntactic_wf_eq_mut_ind'' from
  wf_ctx_eq_mut_ind'',
  wf_exp_eq_mut_ind'',
  wf_sub_eq_mut_ind''.

Lemma inv_tr_exp_no_exotic_sort {P} : forall Γ n B A,
    ~ {{ Γ ⊢t A ≜ ^(@a_st (eSig P) (st_ext n)) : B }}.
Proof.
  intros ** ?.
  remember (@a_st (eSig P) (st_ext n)) as D eqn:HD.
  induction H; inversion HD; subst.
  mauto 3.
Qed.

Lemma inv_tr_typ_no_exotic_sort {P} : forall Γ n A,
    ~ {{ Γ ⊢t A ≜ ^(@a_st (eSig P) (st_ext n)) }}.
Proof.
  intros ** ?.
  remember (@a_st (eSig P) (st_ext n)) as D eqn:HD.
  induction H; inversion HD; subst.
  eapply inv_tr_exp_no_exotic_sort; eassumption.
Qed.

Lemma inv_tr_exp_sort {P} : forall Γ s' B A,
    {{ Γ ⊢t A ≜ ^(@a_st (eSig P) s') : B }} ->
    exists s, A = {{{ Sort@s }}} /\ s' = st_P s.
Proof.
  intros.
  remember (@a_st (eSig P) s') as D eqn:HD.
  induction H; inversion HD; subst; mauto 3.
Qed.

Lemma inv_tr_typ_sort {P} : forall Γ s' A,
    {{ Γ ⊢t A ≜ ^(@a_st (eSig P) s') }} ->
    exists s, A = {{{ Sort@s }}} /\ s' = st_P s.
Proof.
  intros.
  remember (@a_st (eSig P) s') as D eqn:HD.
  induction H; inversion HD; subst; mauto 3.
  eapply inv_tr_exp_sort; mauto 3.
Qed.

Lemma inv_tr_exp_sub {P} : forall (Γ : ctx P) A M N' σ',
    {{ Γ ⊢t M ≜ N'[σ'] : A }} ->
    exists Δ B N σ, ({{ Γ ⊢ A ≈ B[σ] }} \/ (exists s, {{ Γ ⊢ A ≈ Sort@s }} /\ B = {{{ Sort@s }}})) /\ M = {{{ N[σ] }}} /\ {{ Δ ⊢t N ≜ N' : B }} /\ {{ Γ ⊢ts σ ≜ σ' : Δ }}.
Proof.
  intros.
  remember {{{ N'[σ'] }}} as D eqn:HD.
  induction H; inversion HD; subst.
  - repeat eexists; mauto 3.
    left.
    do 2 (econstructor; mauto 3).
  - repeat eexists; mauto 3.
    right; eexists; mauto 3.
    do 3 (econstructor; mauto 3).
  - specialize (IHtr_exp ltac:(reflexivity)).
    destruct_conjs; subst.
    destruct H5; repeat eexists; mauto 3.
    + left.
      eapply wf_typ_eq_trans; mauto 3.
    + destruct_conjs; subst.
      right.
      repeat eexists; mauto 3.
      eapply wf_typ_eq_trans; mauto 3.
Qed.

Lemma inv_tr_exp_pi {P} : forall {s1 s2 s3} (r' : Ru (eSig P) (st_P s1) (st_P s2) (st_P s3)) (Γ : ctx P) D A B' C',
    {{ Γ ⊢t A ≜ Π r' B' C' : D }} ->
    exists r B C, r' = ru_P r /\ A = {{{ Π r B C }}} /\ {{ Γ ⊢t B ≜ B' : Sort@s1 }} /\ {{ Γ, B@s1 ⊢t C ≜ C' : Sort@s2 }}.
Proof.
  intros.
  remember {{{ Π r' B' C' }}} as E eqn:HE.
  induction H; inversion HE; subst.
  - (** UIP *)
    dependent destruction H5.
    repeat eexists; mauto 3.
  - specialize (IHtr_exp ltac:(reflexivity)).
    destruct_conjs; subst.
    repeat eexists; mauto 3.
Qed.

Lemma inv_tr_exp_lam {P} : forall {s1 s2 s3} (r' : Ru (eSig P) (st_P s1) (st_P s2) (st_P s3)) (Γ : ctx P) C M A' N',
    {{ Γ ⊢t M ≜ λ r' A' N' : C }} ->
    exists r A B N, r' = ru_P r /\ M = {{{ λ r A N }}} /\ {{ Γ ⊢t A ≜ A' : Sort@s1 }} /\ {{ Γ, A@s1 ⊢t N ≜ N' : B }} /\ {{ Γ ⊢ Π r A B ≈ C }}.
Proof.
  intros.
  remember {{{ λ r' A' N' }}} as D eqn:HD.
  induction H; inversion HD; subst.
  - (** UIP *)
    dependent destruction H6.
    repeat eexists; mauto 3.
    do 2 (econstructor; mauto 3).
  - specialize (IHtr_exp ltac:(reflexivity)).
    destruct_conjs; subst.
    repeat eexists; mauto 3.
Qed.

Lemma inv_tr_wf_exp {P} : forall Γ' M' A',
    {{ Γ' ⊢ M' : A' }} ->
    forall (Γ : ctx P) M A,
      {{ ⊢t Γ ≜ Γ' }} ->
      {{ Γ ⊢t A ≜ A' }} ->
      {{ Γ ⊢t M ≜ M' : A }} ->
      {{ Γ ⊢ M : A }}.
Proof.
  intros.
  inversion H; subst; mauto 3.
Qed.

  
Lemma inv_tr_judg {P} :
  (forall Γ' Δ',
      {{ ⊢ Γ' ≈ Δ' }} ->
      forall (Γ : ctx P) Δ,
        {{ ⊢t Γ ≜ Γ' }} ->
        {{ ⊢t Δ ≜ Δ' }} ->
        {{ ⊢ Γ ≈ Δ }}) /\
    (forall Γ' A' M' N',
        {{ Γ' ⊢ M' ≈ N' : A' }} ->
        forall (Γ : ctx P) A M N,
          {{ ⊢t Γ ≜ Γ' }} ->
          {{ Γ ⊢t A ≜ A' }} ->
          {{ Γ ⊢t M ≜ M' : A }} ->
          {{ Γ ⊢t N ≜ N' : A }} ->
          {{ Γ ⊢ M ≈ N : A }}) /\
    (forall Γ' Δ' σ' τ',
        {{ Γ' ⊢s σ' ≈ τ' : Δ' }} ->
        forall (Γ : ctx P) Δ σ τ,
          {{ ⊢t Γ ≜ Γ' }} ->
          {{ ⊢t Δ ≜ Δ' }} ->
          {{ Γ ⊢ts σ ≜ σ' : Δ }} ->
          {{ Γ ⊢ts τ ≜ τ' : Δ }} ->
          {{ Γ ⊢s σ ≈ τ : Δ }}).
Proof.
  apply syntactic_wf_eq_mut_ind'';
    intros;
    destruct_conjs;
    clear_dups;
    (on_all_hyp: fun H => pose proof (inv_tr_typ_sort _ _ _ H));
    destruct_conjs; subst;
    (on_all_hyp: invert_inv_tr P);
    injective_tr_rewrite_clear;
    autoinjections;
    clear_dups;
    mauto 3.
  - eapply wf_ctx_eq_extend'; mauto 3.
    assert {{ ⊢ Γ2 ≈ Γ1 }} by mauto 3.
    enough {{ Γ1 ⊢ A1 ≈ A0 : ^_ }} by mauto 3.
    eapply H1; mauto 3.
  - pose proof (inv_tr_exp_sub _ _ _ _ _ H1).
    pose proof (inv_tr_exp_sort _ _ _ _ H2).
    destruct_conjs; subst.
    inversion a; subst.
    (on_all_hyp: invert_inv_tr P).
    assert {{ Γ0 ⊢t Sort@H3 ≜ ^(@a_st (eSig P) (st_P H3)) }} by mauto 3.
    injective_tr_rewrite_clear.
    destruct H8; mauto 3.
  - inversion r; subst.
    pose proof (inv_tr_exp_sub _ _ _ _ _ H1).
    destruct_conjs; subst.
    pose proof (inv_tr_exp_pi _ _ _ _ _ _ H11).
    destruct_conjs; subst.
    assert {{ ^_ ⊢ H13 : Sort@s0 }} by mauto 2.
    assert {{ Γ0 ⊢s H8 : ^_ }} by mauto 2.
    assert {{ Γ0, H13[H8]@s0 ⊢ts H8∘Wk ≜ σ∘Wk : ^_ }} by do 2 (econstructor; mauto 3).
    assert {{ Γ0, H13[H8]@s0 ⊢ts q H8 ≜ q σ : ^_, ^_@s0 }} by mauto 3.
    assert {{ Γ0, H13[H8]@s0 ⊢t H14[q H8] ≜ B[q σ] : Sort@s3 }} by mauto 3.
    assert {{ Γ0 ⊢t Π H10 H13[H8] H14[q H8] ≜ ^(@a_pi (eSig P) _ _ _ (ru_P H10) {{{ A[σ] }}} {{{ B[q σ] }}}) : Sort@H3 }} by mauto 3.
    injective_tr_rewrite_clear.
    mauto 3.
  - inversion r; subst.
    pose proof (inv_tr_exp_pi _ _ _ _ _ _ H3).
    pose proof (inv_tr_exp_pi _ _ _ _ _ _ H4).
    destruct_conjs; subst.
    autoinjections.
    (** UIP *)
    dependent destruction H12.
    assert {{ Γ0 ⊢ H15 ≈ H8 : Sort@_ }} by (apply H; mauto 3).
    econstructor; mauto 3.
    eapply H0; mauto 3.
    + econstructor; mauto 3.
    + eapply tr_exp_ctx_eq; mauto 3.
      econstructor; mauto 3.
  - inversion r; subst.
    inversion H2; subst.
    pose proof (inv_tr_exp_pi _ _ _ _ _ _ H6).
    destruct_conjs; subst.
    pose proof (inv_tr_exp_lam _ _ _ _ _ _ H3).
    destruct_conjs; subst.
    autoinjections.
    injective_tr_rewrite_clear.
    (** UIP *)
    dependent destruction H17.
    pose proof (inv_tr_exp_lam _ _ _ _ _ _ H4).
    destruct_conjs; subst.
    autoinjections.
    (** UIP *)
    dependent destruction H24.
    assert {{ Γ0 ⊢ H8 ≈ H7 : Sort@_ }} by (apply H; mauto 3).
    
    econstructor; mauto 3.
    eapply H0; mauto 3.
    + eapply tr_conv; mauto 3.
      admit. (** This part requires soundness; circular *)
    + eapply tr_conv; mauto 3.
      admit. (** This part requires soundness; circular *)
Admitted.
