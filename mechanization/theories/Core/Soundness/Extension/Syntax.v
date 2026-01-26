From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Generalizable All Variables.


Section Translation.
  Context (P : PtsSig).
  (* (pred_P : PredicativeSig P). *)

  Definition eSig : PtsSig := eP P.
  (* Definition ePred : PredicativeSig eSig := epred_P P pred_P. *)

  Inductive tr_exp : exp P -> exp eSig -> Prop :=
  | tr_st : forall s, tr_exp {{{ Sort@s }}} (@a_st eSig (st_P s))
  | tr_pi : forall {s1 s2 s3} (r : Ru P s1 s2 s3) A A' B B',
      tr_exp A A' -> tr_exp B B' ->
      tr_exp {{{ Π r A B }}} (@a_pi eSig (st_P s1) (st_P s2) (st_P s3) (ru_P r) A' B')
  | tr_lam : forall {s1 s2 s3} (r : Ru P s1 s2 s3) A A' M M',
      tr_exp A A' -> tr_exp M M' ->
      tr_exp {{{ λ r A M }}} (@a_fn eSig (st_P s1) (st_P s2) (st_P s3) (ru_P r) A' M')
  | tr_app : forall M M' N N',
      tr_exp M M' -> tr_exp N N' ->
      tr_exp {{{ M N }}} {{{ M' N' }}}
  | tr_var : forall n, tr_exp {{{ #n }}} {{{ #n }}}
  | tr_clo : forall M M' σ σ',
      tr_exp M M' -> tr_sub σ σ' ->
      tr_exp {{{ M[σ] }}} {{{ M'[σ'] }}}

  with tr_sub : sub P -> sub eSig -> Prop :=
  | tr_id : tr_sub {{{ Id }}} {{{ Id }}}
  | tr_weaken : tr_sub {{{ Wk }}} {{{ Wk }}}
  | tr_compose : forall σ σ' τ τ',
      tr_sub σ σ' -> tr_sub τ τ' ->
      tr_sub {{{ σ∘τ }}} {{{ σ'∘τ' }}}
  | tr_extend : forall σ σ' M M',
      tr_sub σ σ' -> tr_exp M M' ->
      tr_sub {{{ σ,,M }}} {{{ σ',,M' }}}.

  Inductive tr_ctx : ctx P -> ctx eSig -> Prop :=
  | tr_nil : tr_ctx {{{ ⋅ }}} {{{ ⋅ }}}
  | tr_cons : forall Γ Γ' s A A',
      tr_ctx Γ Γ' -> tr_exp A A' ->
      tr_ctx {{{ Γ, A@s }}} {{{ Γ', A'@^(st_P s) }}}.

  #[local]
  Hint Constructors tr_exp tr_sub tr_ctx : mcpts.

  Scheme tr_exp_mut_ind := Induction for tr_exp Sort Prop
  with tr_sub_mut_ind := Induction for tr_sub Sort Prop.
  Combined Scheme syntactic_tr_mut_ind from
    tr_exp_mut_ind,
    tr_sub_mut_ind.

  Lemma tr_functional :
    (forall M M1, tr_exp M M1 -> forall M2, tr_exp M M2 -> M1 = M2) /\
      (forall σ σ1, tr_sub σ σ1 -> forall σ2, tr_sub σ σ2 -> σ1 = σ2).
  Proof using Type.
  Admitted.
    (* apply syntax_mut_ind. *)
  (*   1,5,7,8: intros; dependent destruction H; dependent destruction H0; reflexivity. *)
  (*   all: intros; dependent destruction H2; dependent destruction H1. *)
    
  (*   - assert (A' = A'0) by mauto 2. *)
  (*     assert (B' = B'0) by mauto 2. *)
  (*     subst. *)
  (*     reflexivity. *)

  (*   - assert (A' = A'0) by mauto 2. *)
  (*     assert (M' = M'0) by mauto 2. *)
  (*     subst. *)
  (*     reflexivity. *)

  (*   - assert (M' = M'0) by mauto 2. *)
  (*     assert (N' = N'0) by mauto 2. *)
  (*     subst. *)
  (*     reflexivity. *)

  (*   - assert (M' = M'0) by mauto 2. *)
  (*     assert (σ' = σ'0) by mauto 2. *)
  (*     subst. *)
  (*     reflexivity. *)

  (*   - assert (σ' = σ'0) by mauto 2. *)
  (*     assert (τ' = τ'0) by mauto 2. *)
  (*     subst. *)
  (*     reflexivity. *)

  (*   - assert (σ' = σ'0) by mauto 2. *)
  (*     assert (M' = M'0) by mauto 2. *)
  (*     subst. *)
  (*     reflexivity. *)
  (* Qed. *)
  Lemma tr_functional_ctx : forall Γ Γ1, tr_ctx Γ Γ1 -> forall Γ2, tr_ctx Γ Γ2 -> Γ1 = Γ2.
  Proof using Type.
    induction 1; inversion_clear 1; [reflexivity | ].
    assert (Γ' = Γ'0) by auto.
    assert (A' = A'0) by (eapply tr_functional; mauto 2).
    subst.
    reflexivity.
  Qed.
  
  Corollary tr_exp_functional : forall M M1 M2, tr_exp M M1 -> tr_exp M M2 -> M1 = M2.
  Proof using Type. intros; eapply tr_functional; eauto. Qed.
  
  Corollary tr_sub_functional : forall σ σ1 σ2, tr_sub σ σ1 -> tr_sub σ σ2 -> σ1 = σ2.
  Proof using Type. intros; eapply tr_functional; eauto. Qed.

  Corollary tr_ctx_functional : forall Γ Γ1 Γ2, tr_ctx Γ Γ1 -> tr_ctx Γ Γ2 -> Γ1 = Γ2.
  Proof using Type. intros; eapply tr_functional_ctx; eauto. Qed.
    

  Lemma tr_injective :
    (forall M1 M, tr_exp M1 M -> forall M2, tr_exp M2 M -> M1 = M2) /\
      (forall σ1 σ, tr_sub σ1 σ -> forall σ2, tr_sub σ2 σ -> σ1 = σ2).
  Proof using Type.
  Admitted.
  (*   apply syntax_mut_ind. *)
  (*   1,5,7,8: intros; dependent destruction H; dependent destruction H0; reflexivity. *)
  (*   all: intros; dependent destruction H2; dependent destruction H1; (on_all_hyp: fun H => erewrite H in *; eauto).   *)
  (* Qed. *)
  Lemma tr_injective_ctx : forall Γ1 Γ, tr_ctx Γ1 Γ -> forall Γ2, tr_ctx Γ2 Γ -> Γ1 = Γ2.
  Proof using Type.
    induction 1; inversion_clear 1; [reflexivity |].
    assert (Γ = Γ0) by auto.
    assert (A = A0) by (eapply tr_injective; mauto 2).
    subst.
    reflexivity.
  Qed.    

  Corollary tr_exp_injective : forall M1 M2 M, tr_exp M1 M -> tr_exp M2 M -> M1 = M2.
  Proof using Type. intros; eapply tr_injective; eauto. Qed.
  Corollary tr_sub_injective : forall σ1 σ2 σ, tr_sub σ1 σ -> tr_sub σ2 σ -> σ1 = σ2.
  Proof using Type. intros; eapply tr_injective; eauto. Qed.
  Corollary tr_ctx_injective : forall Γ1 Γ2 Γ, tr_ctx Γ1 Γ -> tr_ctx Γ2 Γ -> Γ1 = Γ2.
  Proof using Type. intros; eapply tr_injective_ctx; eauto. Qed.

  Scheme exp_mut_ind := Induction for exp Sort Prop
  with sub_mut_ind := Induction for sub Sort Prop.
  Combined Scheme syntax_mut_ind from
    exp_mut_ind,
    sub_mut_ind.

  
  Lemma tr_total :
    (forall M, exists M', tr_exp M M') /\
      (forall σ, exists σ', tr_sub σ σ').
  Proof using Type.
  Admitted.
  (*   apply syntax_mut_ind. *)
  (*   all: intros; destruct_conjs; eexists; econstructor; mauto 2. *)
  (* Qed. *)

  Corollary tr_exp_total : forall M, exists M', tr_exp M M'.
  Proof using Type. eapply tr_total. Qed.
  Corollary tr_sub_total : forall σ, exists σ', tr_sub σ σ'.
  Proof using Type. eapply tr_total. Qed.
  Corollary tr_total_ctx : forall Γ, exists Γ', tr_ctx Γ Γ'.
  Proof using Type.
    intros Γ; induction Γ.
    - eexists; econstructor; mauto 2.
    - destruct_conjs.
      destruct (tr_exp_total a).
      eexists; econstructor; mauto 2.
  Qed.
    
  
  (* Fixpoint translate_exp (M : exp P) : exp eSig := *)
  (*   match M with *)
  (*   | a_st s => @a_st eSig (st_P s) *)
  (*   | a_pi r A B => @a_pi eSig _ _ _ (ru_P r) (translate_exp A) (translate_exp B) *)
  (*   | a_fn r A M => @a_fn eSig _ _ _ (ru_P r) (translate_exp A) (translate_exp M) *)
  (*   | a_app M N => a_app (translate_exp M) (translate_exp N) *)
  (*   | a_var n => a_var n *)
  (*   | a_sub M σ => a_sub (translate_exp M) (translate_sub σ) *)
  (*   end *)
      
  (* with translate_sub (σ : sub P) : sub eSig := *)
  (*   match σ with *)
  (*   | a_id => a_id *)
  (*   | a_weaken => a_weaken *)
  (*   | a_compose σ τ => a_compose (translate_sub σ) (translate_sub τ) *)
  (*   | a_extend σ M => a_extend (translate_sub σ) (translate_exp M) *)
  (*   end. *)

  (* Definition translate_ctx (Γ : ctx P) : ctx eSig := List.map (translate_exp) Γ. *)

  
End Translation.

Arguments tr_exp {P}.
Arguments tr_st {P}.
Arguments tr_pi {P} {s1} {s2} {s3}.
Arguments tr_lam {P} {s1} {s2} {s3}.
Arguments tr_app {P}.
Arguments tr_var {P}.
Arguments tr_clo {P}.

Arguments tr_sub {P}.
Arguments tr_id {P}.
Arguments tr_weaken {P}.
Arguments tr_compose {P}.
Arguments tr_extend {P}.

Arguments tr_ctx {P}.
Arguments tr_nil {P}.
Arguments tr_cons {P}.


#[export]
Hint Resolve tr_exp_functional tr_sub_functional tr_ctx_functional : mcpts.

Ltac functional_tr_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "tr_functional equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : tr_exp ?M ?M1,
      H2 : tr_exp ?M ?M2 |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : tr_sub ?σ ?σ1,
      H2 : tr_sub ?σ ?σ2 |- _ =>
      clean replace σ2 with σ1 by first [solve [mauto 2] | tactic_error σ2 σ1]; clear H2
  | H1 : tr_ctx ?Γ ?Γ1,
      H2 : tr_ctx ?Γ ?Γ2 |- _ =>
      clean replace Γ2 with Γ1 by first [solve [mauto 2] | tactic_error Γ2 Γ1]; clear H2
  end.
Ltac functional_tr_rewrite_clear := repeat functional_tr_rewrite_clear1.

#[export]
Hint Resolve tr_exp_injective tr_sub_injective tr_ctx_injective : mcpts.

Ltac injective_tr_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "tr_functional equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : tr_exp ?M1 ?M,
      H2 : tr_exp ?M2 ?M |- _ =>
      clean replace M2 with M1 by first [solve [mauto 2] | tactic_error M2 M1]; clear H2
  | H1 : tr_sub ?σ1 ?σ,
      H2 : tr_sub ?σ2 ?σ |- _ =>
      clean replace σ2 with σ1 by first [solve [mauto 2] | tactic_error σ2 σ1]; clear H2
  | H1 : tr_ctx ?Γ1 ?Γ,
      H2 : tr_ctx ?Γ2 ?Γ |- _ =>
      clean replace Γ2 with Γ1 by first [solve [mauto 2] | tactic_error Γ2 Γ1]; clear H2
  end.
Ltac injective_tr_rewrite_clear := repeat injective_tr_rewrite_clear1.


Ltac destruct_tr H :=
  match type of H with
  | tr_exp {{{ Sort@?s }}} ?M' => dependent destruction H
  | tr_exp {{{ Π ?r ^?A ^?B }}} ?M' => dependent destruction H
  | tr_exp {{{ λ ?r ^?A ^?M }}} ?M' => dependent destruction H
  | tr_exp {{{ ^?M ^?N }}} ?M' => dependent destruction H
  | tr_exp {{{ #?n }}} ?M' => dependent destruction H
  | tr_exp {{{ ^?M[^?σ] }}} ?M' => dependent destruction H
  | tr_sub {{{ Id }}} ?σ' => dependent destruction H
  | tr_sub {{{ Wk }}} ?σ' => dependent destruction H
  | tr_sub {{{ ^?σ ∘ ^?τ }}} ?σ' => dependent destruction H
  | tr_sub {{{ ^?σ,,^?M }}} ?M' => dependent destruction H
  | tr_ctx {{{ ⋅ }}} ?Γ' => dependent destruction H
  | tr_ctx {{{ ^?Γ, ^?A@^?K }}} ?Γ' => dependent destruction H
  end;
  functional_tr_rewrite_clear.

Ltac invert_tr H :=
  match type of H with
  | tr_exp {{{ Sort@?s }}} ?M' => directed inversion H
  | tr_exp {{{ Π ?r ^?A ^?B }}} ?M' => directed inversion H
  | tr_exp {{{ λ ?r ^?A ^?M }}} ?M' => directed inversion H
  | tr_exp {{{ ^?M ^?N }}} ?M' => directed inversion H
  | tr_exp {{{ #?n }}} ?M' => directed inversion H
  | tr_exp {{{ ^?M[^?σ] }}} ?M' => directed inversion H
  | tr_sub {{{ Id }}} ?σ' => directed inversion H
  | tr_sub {{{ Wk }}} ?σ' => directed inversion H
  | tr_sub {{{ ^?σ ∘ ^?τ }}} ?σ' => directed inversion H
  | tr_sub {{{ ^?σ,,^?M }}} ?M' => directed inversion H
  | tr_ctx {{{ ⋅ }}} ?Γ' => directed inversion H
  | tr_ctx {{{ ^?Γ, ^?A@^?K }}} ?Γ' => directed inversion H
  end;
  subst.


Lemma tr_wf_ctx_lookup {P} : forall {A : typ P} {n Γ s A' Γ'},
    tr_exp A A' ->
    tr_ctx Γ Γ' ->
    {{ #n : A@s ∈ Γ }} ->
    {{ #n : A'@^(st_P s) ∈ Γ' }}.
Proof.
  intros.
  gen H H0 A' Γ'.
  induction H1; simpl;
    intros * HAA' HΓΓ';
    inversion_clear HAA'; inversion_clear HΓΓ'.
  - inversion_clear H2.
    functional_tr_rewrite_clear.
    mauto.
  - inversion_clear H3.
    econstructor.
    eapply IHctx_lookup; mauto.
Qed.

#[export]
Hint Resolve tr_wf_ctx_lookup : mcpts.

Ltac apply_tr_IH :=
  match goal with
  (* Cases for contexts *)
  | H1 : forall Γ', tr_ctx ?Γ Γ' -> {{ ⊢ Γ' }},
    H2 : {{ ⊢ ^?Γ }} |- {{ ⊢ ^?Γ' }} => (eapply H1; try econstructor; mauto 2)
  | H1 : forall Γ' Δ', tr_ctx ?Γ Γ' -> tr_ctx ?Δ Δ' -> {{ ⊢ Γ' ≈ Δ' }},
    H2 : {{ ⊢ ^?Γ ≈ ^?Δ }} |- {{ ⊢ ^?Γ' ≈ ^?Δ' }} => eapply H1; try econstructor; mauto 2
  (* Cases for terms *)
  | H1 : forall Γ' A' M', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?A A' -> {{ Γ' ⊢ M' : A' }},
    H2 : {{ ^?Γ ⊢ ^?M : ^?A }},
    H3 : tr_ctx ?Γ ?Γ', H4 : tr_exp ?M ?M', H5 : tr_exp ?A ?A'
    |- {{ ^?Γ' ⊢ ^?M' : ^?A' }} => eapply H1; try econstructor; mauto 2
| H1 : forall Γ' A' M' N', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?N N' -> tr_exp ?A A' -> {{ Γ' ⊢ M' ≈ N' : A' }},
       H2 : {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} |- {{ ^?Γ' ⊢ ^?M' ≈ ^?N' : ^?A' }} => eapply H1; try econstructor; mauto 2
    (* Cases for types *)
     | H1 : forall Γ' A', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> {{ Γ' ⊢ A' }},
       H2 : {{ ^?Γ ⊢ ^?A }} |- {{ ^?Γ' ⊢ ^?A' }} => eapply H1; try econstructor; mauto 2
     | H1 : forall Γ' A' B', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> tr_exp ?B B' -> {{ Γ' ⊢ A' ≈ B' }},
       H2 : {{ ^?Γ ⊢ ^?A ≈ ^?B }} |- {{ ^?Γ' ⊢ ^?A' ≈ ^?B' }} => eapply H1; try econstructor; mauto 2
    (* Cases for substitutions *)
     | H1 : forall Γ' Δ' σ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' : Δ' }},
       H2 : {{ ^?Γ ⊢ ^?σ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2
     | H1 : forall Γ' Δ' σ' τ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_sub ?τ τ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' ≈ τ' : Δ' }},
       H2 : {{ ^?Γ ⊢ ^?σ ≈ ^?τ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' ≈ ^?τ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2
     | _ => idtac
     end.

Ltac apply_tr_IH' :=
  match goal with
  (* Cases for contexts *)
  | H1 : forall Γ', tr_ctx ?Γ Γ' -> {{ ⊢ Γ' }},
    H2 : {{ ⊢ ^?Γ }} |- {{ ⊢ ^?Γ' }} => (eapply H1; try econstructor; mauto 2)
  | H1 : forall Γ' Δ', tr_ctx ?Γ Γ' -> tr_ctx ?Δ Δ' -> {{ ⊢ Γ' ≈ Δ' }},
    H2 : {{ ⊢ ^?Γ ≈ ^?Δ }} |- {{ ⊢ ^?Γ' ≈ ^?Δ' }} => eapply H1; try econstructor; mauto 2
  (* Cases for terms *)
  | H1 : forall Γ' A' M', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?A A' -> {{ Γ' ⊢ M' : A' }},
    H2 : {{ ^?Γ ⊢ ^?M : ^?A }},
    H3 : tr_ctx ?Γ ?Γ', H4 : tr_exp ?M ?M', H5 : tr_exp ?A ?A'
                                            |- _ => try (assert {{ ^?Γ' ⊢ ^?M' : ^?A' }} by (eapply H1; mauto 2))
| H1 : forall Γ' A' M' N', tr_ctx ?Γ Γ' -> tr_exp ?M M' -> tr_exp ?N N' -> tr_exp ?A A' -> {{ Γ' ⊢ M' ≈ N' : A' }},
       H2 : {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} |- {{ ^?Γ' ⊢ ^?M' ≈ ^?N' : ^?A' }} => eapply H1; try econstructor; mauto 2
    (* Cases for types *)
     | H1 : forall Γ' A', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> {{ Γ' ⊢ A' }},
       H2 : {{ ^?Γ ⊢ ^?A }} |- {{ ^?Γ' ⊢ ^?A' }} => eapply H1; try econstructor; mauto 2
     | H1 : forall Γ' A' B', tr_ctx ?Γ Γ' -> tr_exp ?A A' -> tr_exp ?B B' -> {{ Γ' ⊢ A' ≈ B' }},
       H2 : {{ ^?Γ ⊢ ^?A ≈ ^?B }} |- {{ ^?Γ' ⊢ ^?A' ≈ ^?B' }} => eapply H1; try econstructor; mauto 2
    (* Cases for substitutions *)
     | H1 : forall Γ' Δ' σ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' : Δ' }},
       H2 : {{ ^?Γ ⊢ ^?σ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2
     | H1 : forall Γ' Δ' σ' τ',  tr_ctx ?Γ Γ' -> tr_sub ?σ σ' -> tr_sub ?τ τ' -> tr_ctx ?Δ Δ' -> {{ Γ' ⊢s σ' ≈ τ' : Δ' }},
       H2 : {{ ^?Γ ⊢ ^?σ ≈ ^?τ : ^?Δ }} |- {{ ^?Γ' ⊢s ^?σ' ≈ ^?τ' : ^?Δ' }} => eapply H1; try econstructor; mauto 2
     | _ => idtac
     end.


Lemma tr_judg {P} :
  (forall (Γ : ctx P), {{ ⊢ Γ }} ->
                  forall Γ',
                    tr_ctx Γ Γ' ->
                    {{ ⊢ Γ' }}) /\
    (forall (Γ : ctx P) Δ, {{ ⊢ Γ ≈ Δ }} ->
                  forall Γ' Δ',
                    tr_ctx Γ Γ' -> tr_ctx Δ Δ' ->
                    {{ ⊢ Γ' ≈ Δ' }}) /\
    (forall (Γ : ctx P) A M, {{ Γ ⊢ M : A }} ->
                        forall Γ' A' M',
                          tr_ctx Γ Γ' -> tr_exp M M' -> tr_exp A A' ->
                          {{ Γ' ⊢ M' : A' }}) /\
    (forall (Γ : ctx P) A M N, {{ Γ ⊢ M ≈ N : A }} ->
                        forall Γ' A' M' N',
                          tr_ctx Γ Γ' -> tr_exp M M' -> tr_exp N N' -> tr_exp A A' ->
                          {{ Γ' ⊢ M' ≈ N' : A' }}) /\
    (forall (Γ : ctx P) A, {{ Γ ⊢ A }} ->
                      forall Γ' A',
                        tr_ctx Γ Γ' -> tr_exp A A' ->
                        {{ Γ' ⊢ A' }}) /\
    (forall (Γ : ctx P) A B, {{ Γ ⊢ A ≈ B }} ->
                      forall Γ' A' B',
                        tr_ctx Γ Γ' -> tr_exp A A' -> tr_exp B B' ->
                        {{ Γ' ⊢ A' ≈ B' }}) /\
    (forall (Γ : ctx P) Δ σ, {{ Γ ⊢s σ : Δ }} ->
                        forall Γ' Δ' σ',
                          tr_ctx Γ Γ' -> tr_sub σ σ' -> tr_ctx Δ Δ' ->
                          {{ Γ' ⊢s σ' : Δ' }}) /\
    (forall (Γ : ctx P) Δ σ τ, {{ Γ ⊢s σ ≈ τ : Δ }} ->
                        forall Γ' Δ' σ' τ',
                          tr_ctx Γ Γ' -> tr_sub σ σ' -> tr_sub τ τ' -> tr_ctx Δ Δ' ->
                          {{ Γ' ⊢s σ' ≈ τ' : Δ' }}).
Proof.
  apply syntactic_wf_mut_ind.
  all: intros;
    (on_all_hyp: invert_tr);
    econstructor; mauto 2.  
  
  - eapply H0;
    try econstructor; mauto 2.

    
  - eapply H0; mauto 2.
    econstructor; mauto 2.

  - eapply H1; mauto 2.
    econstructor; mauto 2.

  - eapply H2; mauto 2.
    econstructor; mauto 2.

  - eapply H3; mauto 2.
    econstructor; mauto 2.

  - econstructor; mauto 2.

    
Admitted.






    
(* Arguments translate_exp {P}. *)
(* Arguments translate_sub {P}. *)
(* Arguments translate_ctx {P}. *)

Lemma translate_wf_ctx_lookup {P} : forall {A : typ P} {n Γ},
    {{ #n : A ∈ Γ }} ->
    {{ #n : ^(translate_exp A) ∈ ^(translate_ctx Γ) }}.
Proof.
  intros * H.
  induction H; simpl; mauto.
Qed.

#[export]
Hint Resolve translate_wf_ctx_lookup : mcpts.
 
#[local]
Ltac gen_translate_IH translate_wf_ctx translate_wf_exp translate_wf_typ translate_wf_sub translate_wf_ctx_eq translate_wf_exp_eq translate_wf_typ_eq translate_wf_sub_eq H :=
  match type of H with
  | {{ ⊢ ^?Γ }} =>
      pose proof translate_wf_ctx _ _ H
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      pose proof translate_wf_exp _ _ _ _ H
  | {{ ^?Γ ⊢ ^?A }} =>
      pose proof translate_wf_typ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      pose proof translate_wf_sub _ _ _ _ H
  | {{ ⊢ ^?Γ ≈ ^?Δ }} =>
      pose proof translate_wf_ctx_eq _ _ _ H
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      pose proof translate_wf_exp_eq _ _ _ _ _ H
  | {{ ^?Γ ⊢ ^?A ≈ ^?B }} =>
      pose proof translate_wf_typ_eq _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} =>
      pose proof translate_wf_sub_eq _ _ _ _ _ H
  end.

Lemma translate_wf_ctx {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ ^(translate_ctx Γ) }}
with translate_wf_exp {P} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp M) : ^(translate_exp A) }}
with translate_wf_typ {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp A) }}
with translate_wf_sub {P} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ ^(translate_ctx Γ) ⊢s ^(translate_sub σ) : ^(translate_ctx Δ) }}
with translate_wf_ctx_eq {P} : forall {Γ : ctx P} {Δ},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ ⊢ ^(translate_ctx Γ) ≈ ^(translate_ctx Δ) }}
with translate_wf_exp_eq {P} : forall {Γ : ctx P} {M M' A},
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp M) ≈ ^(translate_exp M') : ^(translate_exp A) }}
with translate_wf_typ_eq {P} : forall {Γ : ctx P} {A A'},
    {{ Γ ⊢ A ≈ A' }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp A) ≈ ^(translate_exp A') }}      
with translate_wf_sub_eq {P} : forall {Γ : ctx P} {σ σ' Δ},
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ^(translate_ctx Γ) ⊢s ^(translate_sub σ) ≈ ^(translate_sub σ') : ^(translate_ctx Δ) }}.
Proof.
  all: inversion_clear 1;
    (on_all_hyp: gen_translate_IH translate_wf_ctx translate_wf_exp translate_wf_typ translate_wf_sub translate_wf_ctx_eq translate_wf_exp_eq translate_wf_typ_eq translate_wf_sub_eq);
    clear translate_wf_ctx translate_wf_exp translate_wf_typ translate_wf_sub translate_wf_ctx_eq translate_wf_exp_eq translate_wf_typ_eq translate_wf_sub_eq;
    try mautosolve 3.

  all: try (econstructor; mautosolve 4).
  all: econstructor; [econstructor|]; eauto.
Qed.
