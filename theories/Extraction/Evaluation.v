From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

Inductive eval_env_lookup_order {P : PtsSig} : env P -> nat -> Prop :=
| eelo_here : `( eval_env_lookup_order d{{{ ρ ↦ m }}} 0 )
| eelo_there : `( eval_env_lookup_order ρ i ->
                  eval_env_lookup_order d{{{ ρ ↦ n }}} (S i)).

Inductive eval_exp_order {P : PtsSig} : exp P -> env P -> Prop :=
| eeo_sort :
  `( eval_exp_order {{{ Sort@s }}} ρ )
| eeo_var :
  `( eval_env_lookup_order ρ x ->
     eval_exp_order {{{ #x }}} ρ )
| eeo_pi :
  `( forall r : Ru_pi P s1 s2 s3,
        eval_exp_order A ρ ->
        eval_exp_order {{{ Π r A B }}} ρ )
| eeo_fn :
  `( forall r : Ru_pi P s1 s2 s3,
        eval_exp_order {{{ λ r A B M }}} ρ )
| eeo_app :
  `( eval_exp_order M ρ ->
     eval_exp_order N ρ ->
     (forall m n, {{ ⟦ M ⟧ ρ ↘ m }} -> {{ ⟦ N ⟧ ρ ↘ n }} -> eval_app_order m n) ->
     eval_exp_order {{{ M N }}} ρ )
| eeo_nat :
  `( eval_exp_order {{{ ℕ }}} ρ )
| eeo_zero :
  `( eval_exp_order {{{ zero }}} ρ )
| eeo_succ :
  `( eval_exp_order {{{ M }}} ρ ->
     eval_exp_order {{{ succ M }}} ρ )
| eeo_natrec :
  `( eval_exp_order M ρ ->
     (forall m, {{ ⟦ M ⟧ ρ ↘ m }} -> eval_natrec_order A MZ MS m ρ) ->
     eval_exp_order {{{ rec M return A | zero -> MZ | succ -> MS end }}} ρ )
| eeo_sub :
  `( eval_sub_order σ ρ ->
     (forall ρ', {{ ⟦ σ ⟧s ρ ↘ ρ' }} -> eval_exp_order M ρ') ->
     eval_exp_order {{{ M[σ] }}} ρ )

with eval_app_order {P : PtsSig} : domain P -> domain P -> Prop :=
| eao_fn :
  `( forall r : Ru_pi P s1 s2 s3,
        eval_exp_order M d{{{ ρ ↦ n }}} ->
        eval_app_order d{{{ λ r ρ M }}} n )
| eao_neut :
  `( forall r : Ru_pi P s1 s2 s3,
        eval_exp_order B d{{{ ρ ↦ n }}} ->
        eval_app_order d{{{ ⇑ (Π r a ρ B) m }}} n )

with eval_natrec_order {P : PtsSig} : exp P -> exp P -> exp P -> domain P -> env P -> Prop :=
| eno_zero :
  `( eval_exp_order MZ ρ ->
     eval_natrec_order A MZ MS d{{{ zero }}} ρ )
| eno_succ :
  `( eval_natrec_order A MZ MS b ρ ->
     (forall r, {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} -> eval_exp_order {{{ MS }}} d{{{ (ρ ↦ b) ↦ r }}}) ->
     eval_natrec_order A MZ MS d{{{ succ b }}} ρ )
| eno_neut :
  `( eval_exp_order MZ ρ ->
     eval_exp_order A d{{{ ρ ↦ ⇑ a m }}} ->
     eval_natrec_order A MZ MS d{{{ ⇑ a m }}} ρ )

with eval_sub_order {P : PtsSig} : sub P -> env P -> Prop :=
| eso_id :
  `( eval_sub_order {{{ Id }}} ρ )
| eso_weaken :
  `( eval_sub_order {{{ Wk }}} ρ )
| eso_extend :
  `( eval_sub_order σ ρ ->
     eval_exp_order M ρ ->
     eval_sub_order {{{ σ ,, M }}} ρ )
| eso_compose :
  `( eval_sub_order τ ρ ->
     (forall ρ', {{ ⟦ τ ⟧s ρ ↘ ρ' }} -> eval_sub_order σ ρ') ->
     eval_sub_order {{{ σ ∘ τ }}} ρ ).

#[local]
Hint Constructors eval_exp_order eval_env_lookup_order eval_natrec_order eval_app_order eval_sub_order : mcpts.

Lemma eval_env_lookup_order_sound {P : PtsSig} : forall {ρ : env P} x m,
    {{ #| ρ[x] |↘ m }} ->
    eval_env_lookup_order ρ x.
Proof.
  induction 1; mauto.
Qed.

#[export]
Hint Resolve eval_env_lookup_order_sound : mcpts.

Lemma eval_exp_order_sound {P : PtsSig} : forall {m : exp P} ρ a,
    {{ ⟦ m ⟧ ρ ↘ a }} ->
    eval_exp_order m ρ
with eval_app_order_sound {P : PtsSig} : forall {m : domain P} n r,
    {{ $| m & n |↘ r }} ->
    eval_app_order m n
with eval_natrec_order_sound {P : PtsSig} : forall {A : exp P} MZ MS m ρ r,
    {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
    eval_natrec_order A MZ MS m ρ
with eval_sub_order_sound {P : PtsSig}: forall {σ : sub P} ρ ρ',
    {{ ⟦ σ ⟧s ρ ↘ ρ' }} ->
    eval_sub_order σ ρ.
Proof with (econstructor; intros; functional_eval_rewrite_clear; mauto 3).
  - clear eval_exp_order_sound; induction 1...
  - clear eval_app_order_sound; induction 1...
  - clear eval_natrec_order_sound.
    induction 1; mauto.
    econstructor; mauto.
    intros.
    assert (r = r0) by mauto 2 using functional_eval_natrec.
    subst.
    mauto.
  - clear eval_sub_order_sound. induction 1...
Qed.

#[export]
Hint Resolve eval_exp_order_sound eval_app_order_sound eval_natrec_order_sound eval_sub_order_sound : mcpts.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : eval_exp_order _ _ |- _ => progressive_invert H
  | H : eval_app_order _ _ |- _ => progressive_invert H
  | H : eval_natrec_order _ _ _ _ _ |- _ => progressive_invert H
  | H : eval_env_lookup_order {{{ ⋅ }}} _ |- _ => exfalso; inversion H
  | H : eval_env_lookup_order _ _ |- _ => progressive_invert H
  | H : eval_sub_order _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; eauto.

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations eval_env_lookup_impl {P : PtsSig} (ρ : env P) x (H : eval_env_lookup_order ρ x) : { m | env_lookup ρ x m } by struct H :=
| {{{ ⋅ }}}, _, _ => _
| (cons m ρ), 0, H  => exist _ m _
| (cons n ρ), (S i), H => let (r, Hr) := eval_env_lookup_impl ρ i _ in exist _ r _.


#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations eval_exp_impl {P : PtsSig} (m : exp P) ρ (H : eval_exp_order m ρ) : { d | eval_exp m ρ d } by struct H :=
| {{{ Sort@s }}}, ρ, H => exist _ d{{{ Sort@s }}} _
| {{{ #x }}}, ρ, H =>
    let (r, Hr) := eval_env_lookup_impl ρ x _ in
    exist _ r _
| {{{ Π r A B }}}, ρ, H =>
    let (a, Ha) := eval_exp_impl A ρ _ in
    exist _ d{{{ Π r a ρ B }}} _
| {{{ λ r A B M }}}, ρ, H => exist _ d{{{ λ r ρ M }}} _
| {{{ M N }}}  , ρ, H =>
    let (m, Hm) := eval_exp_impl M ρ _ in
    let (n, Hn) := eval_exp_impl N ρ _ in
    let (a, Ha) := eval_app_impl m n _ in
    exist _ a _
| {{{ ℕ }}}                                         , ρ, H => exist _ d{{{ ℕ }}} _
| {{{ zero }}}                                      , ρ, H => exist _ d{{{ zero }}} _
| {{{ succ m }}}                                    , ρ, H =>
    let (r, Hr) := eval_exp_impl m ρ _ in
    exist _ d{{{ succ r }}} _
| {{{ rec M return A | zero -> MZ | succ -> MS end }}}, ρ, H =>
    let (m, Hm) := eval_exp_impl M ρ _ in
    let (r, Hr)  := eval_natrec_impl A MZ MS m ρ _ in
    exist _ r _
| {{{ M[σ] }}}  , ρ, H =>
    let (ρ', Hρ') := eval_sub_impl σ ρ _ in
    let (m, Hm) := eval_exp_impl M ρ' _ in
    exist _ m _

with eval_app_impl {P : PtsSig} (m : domain P) n (H : eval_app_order m n) : { d | eval_app m n d } by struct H :=
| d{{{ λ r ρ M }}}        , n, H =>
    let (m, Hm) := eval_exp_impl M d{{{ ρ ↦ n }}} _ in
    exist _ m _
| d{{{ ⇑ (Π r a ρ B) m }}}, n, H =>
    let (b, Hb) := eval_exp_impl B d{{{ ρ ↦ n }}} _ in
    exist _ d{{{ ⇑ b (m (⇓ a n)) }}} _

with eval_natrec_impl {P : PtsSig} (A : exp P) MZ MS m ρ (H : eval_natrec_order A MZ MS m ρ) : { d | eval_natrec A MZ MS m ρ d } by struct H :=
| A, MZ, MS, d{{{ zero }}}  , ρ, H =>
    let (mz, Hmz) := eval_exp_impl MZ ρ _ in
    exist _ mz _
| A, MZ, MS, d{{{ succ m }}}, ρ, H =>
    let (mr, Hmr) := eval_natrec_impl A MZ MS m ρ _ in
    let (r, Hr) := eval_exp_impl MS d{{{ (ρ ↦ m) ↦ mr }}} _ in
    exist _ r _
| A, MZ, MS, d{{{ ⇑ a m }}} , ρ, H =>
    let (mz, Hmz) := eval_exp_impl MZ ρ _ in
    let (mA, HmA) := eval_exp_impl A d{{{ ρ ↦ ⇑ a m }}} _ in
    exist _ d{{{ ⇑ mA (rec m under ρ return A | zero -> mz | succ -> MS end) }}} _

with eval_sub_impl {P : PtsSig} (s : sub P) ρ (H : eval_sub_order s ρ) : { ρ' | eval_sub s ρ ρ' } by struct H :=
| {{{ Id }}}, ρ, H => exist _ ρ _
| {{{ Wk }}}, ρ, H => exist _ d{{{ ρ↯ }}} _
| {{{ s ,, M }}}, ρ, H =>
    let (ρ', Hρ') := eval_sub_impl s ρ _ in
    let (m, Hm) := eval_exp_impl M ρ _ in
    exist _ d{{{ ρ' ↦ m }}} _
| {{{ s ∘ τ }}}, ρ, H =>
    let (ρ', Hρ') := eval_sub_impl τ ρ _ in
    let (ρ'', Hρ'') := eval_sub_impl s ρ' _ in
    exist _ ρ'' _.

Extraction Inline eval_exp_impl_functional
  eval_app_impl_functional
  eval_natrec_impl_functional
  eval_sub_impl_functional.

(** The definitions of [eval_*_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of eval. *)

#[local]
Ltac functional_eval_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_eval_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma eval_exp_impl_complete {P : PtsSig} : forall (M : exp P) ρ m,
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    exists H H', eval_exp_impl M ρ H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_natrec_impl_complete {P : PtsSig} : forall (A : exp P) MZ MS m ρ r,
    {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
    exists H H', eval_natrec_impl A MZ MS m ρ H = exist _ r H'.
Proof.
  intros.
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          assert (x = r) by mauto 2 using functional_eval_natrec; subst; 
          eexists; reflexivity
      end
  end.
Qed.

Lemma eval_app_impl_complete {P : PtsSig} : forall (m : domain P) n r,
    {{ $| m & n |↘ r }} ->
    exists H H', eval_app_impl m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_env_lookup_impl_complete {P : PtsSig} : forall (ρ : env P) x m,
    {{ #| ρ[x] |↘ m }} ->
    exists H H', eval_env_lookup_impl ρ x H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_sub_impl_complete {P : PtsSig} : forall (σ : sub P) ρ ρ',
    {{ ⟦ σ ⟧s ρ ↘ ρ' }} ->
    exists H H', eval_sub_impl σ ρ H = exist _ ρ' H'.
Proof.
  intros; functional_eval_complete.
Qed.
