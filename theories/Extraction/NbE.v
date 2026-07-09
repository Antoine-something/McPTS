From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Extraction Require Import Evaluation Readback.
Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env_order {P : PtsSig} : (ctx P) -> Prop :=
| ie_nil : initial_env_order nil
| ie_cons :
  `( initial_env_order Γ ->
     (forall ρ, initial_env Γ ρ ->
           eval_exp_order A ρ) ->
     initial_env_order {{{ Γ, A }}}).

#[local]
Hint Constructors initial_env_order : mcpts.

Lemma initial_env_order_sound {P : PtsSig} : forall (Γ : ctx P) ρ,
    initial_env Γ ρ ->
    initial_env_order Γ.
Proof with (econstructor; intros; functional_initial_env_rewrite_clear; functional_eval_rewrite_clear; mauto).
  induction 1...
Qed.

#[local]
Hint Resolve initial_env_order_sound : mcpts.

Section InitialEnvImpl.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : initial_env_order _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations initial_env_impl {P : PtsSig} (Γ : ctx P) (H : initial_env_order Γ) : { ρ | initial_env Γ ρ } by struct H :=
  | nil, H => exist _ empty_env _
  | {{{ Γ, A }}}, H =>
      let (ρ, Hρ) := initial_env_impl Γ _ in
      let (a, Ha) := eval_exp_impl A ρ _ in
      exist _ d{{{ ρ ↦ ⇑! a (length Γ) }}} _.

End InitialEnvImpl.

(** The definitions of [initial_env_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of initial_env. *)

Lemma initial_env_impl_complete {P : PtsSig} : forall (Γ : ctx P) ρ,
    initial_env Γ ρ ->
    exists H H', initial_env_impl Γ H = exist _ ρ H'.
Proof.
  intros.
  assert (Horder : initial_env_order Γ) by mauto.
  exists Horder.
  destruct (initial_env_impl Γ Horder).
  functional_initial_env_rewrite_clear.
  eexists; reflexivity.
Qed.

(** A similar approach works for nbe implementations.
    However, as we have 2 implementations (each for [nbe] and [nbe_ty]),
    We define a tactic to deal with both cases. *)

Ltac functional_nbe_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_nbe_rewrite_clear;
          eexists; reflexivity
      end
  end.

Inductive nbe_order {P : PtsSig} (Γ : ctx P) M A : Prop :=
| nbe_order_run :
  `( initial_env_order Γ ->
     (forall ρ, initial_env Γ ρ ->
           eval_exp_order A ρ) ->
     (forall ρ, initial_env Γ ρ ->
           eval_exp_order M ρ) ->
     (forall ρ a m,
         initial_env Γ ρ ->
         {{ ⟦ A ⟧ ρ ↘ a }} ->
         {{ ⟦ M ⟧ ρ ↘ m }} ->
         read_nf_order (length Γ) d{{{ ⇓ a m }}}) ->
     nbe_order Γ M A ).

#[local]
Hint Constructors nbe_order : mcpts.

Lemma nbe_order_sound {P : PtsSig} : forall (Γ : ctx P) M A w,
    nbe Γ M A w ->
    nbe_order Γ M A.
Proof with (econstructor; intros;
            functional_initial_env_rewrite_clear;
            functional_eval_rewrite_clear;
            functional_read_rewrite_clear;
            mauto).
  induction 1...
Qed.

#[local]
Hint Resolve nbe_order_sound : mcpts.

Section NbEDef.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : nbe_order _ _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_impl {P : PtsSig} (Γ : ctx P) M A (H : nbe_order Γ M A) : { w | nbe Γ M A w } by struct H :=
  | Γ, M, A, H =>
      let (ρ, Hρ) := initial_env_impl Γ _ in
      let (a, Ha) := eval_exp_impl A ρ _ in
      let (m, Hm) := eval_exp_impl M ρ _ in
      let (w, Hw) := read_nf_impl (length Γ) d{{{ ⇓ a m }}} _ in
      exist _ w _.

End NbEDef.

Lemma nbe_impl_complete {P : PtsSig} : forall (Γ : ctx P) M A w,
    nbe Γ M A w ->
    exists H H', nbe_impl Γ M A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.

Inductive nbe_ty_order {P : PtsSig} (Γ : ctx P) A : Prop :=
| nbe_ty_order_run :
  `( initial_env_order Γ ->
     (forall ρ, initial_env Γ ρ ->
           eval_exp_order A ρ) ->
     (forall ρ a,
         initial_env Γ ρ ->
         {{ ⟦ A ⟧ ρ ↘ a }} ->
         read_typ_order (length Γ) a) ->
     nbe_ty_order Γ A ).

#[local]
Hint Constructors nbe_ty_order : mcpts.

Lemma nbe_ty_order_sound {P : PtsSig} : forall (Γ : ctx P) A w,
    nbe_ty Γ A w ->
    nbe_ty_order Γ A.
Proof with (econstructor; intros;
            functional_initial_env_rewrite_clear;
            functional_eval_rewrite_clear;
            functional_read_rewrite_clear;
            mauto).
  induction 1...
Qed.

#[local]
Hint Resolve nbe_ty_order_sound : mcpts.

Section NbETyDef.

  #[local]
  Ltac impl_obl_tac1 :=
  match goal with
  | H : nbe_ty_order _ _ |- _ => progressive_invert H
  end.

  #[local]
  Ltac impl_obl_tac :=
    repeat impl_obl_tac1; try econstructor; mauto.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations nbe_ty_impl {P : PtsSig} (Γ : ctx P) A (H : nbe_ty_order Γ A) : { w | nbe_ty Γ A w } by struct H :=
  | Γ, A, H =>
      let (ρ, Hρ) := initial_env_impl Γ _ in
      let (a, Ha) := eval_exp_impl A ρ _ in
      let (w, Hw) := read_typ_impl (length Γ) a _ in
      exist _ w _.

End NbETyDef.

Lemma nbe_ty_impl_complete {P : PtsSig} : forall (Γ : ctx P) A w,
    nbe_ty Γ A w ->
    exists H H', nbe_ty_impl Γ A H = exist _ w H'.
Proof.
  intros; functional_nbe_complete.
Qed.
