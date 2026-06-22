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
     (forall r, {{ rec b ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} -> eval_exp_order {{{ MS }}} d{{{ (p ↦ b) ↦ r }}}) ->
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
  | H : eval_env_lookup_order _ _ |- _ => progressive_invert H
  | H : eval_sub_order _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; eauto.

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations eval_env_lookup_impl {P : PtsSig} (ρ : env P) x (H : eval_env_lookup_order ρ x) : { m | env_lookup ρ x m } by struct H :=
| nil, _, _ => _
| (cons m ρ), 0, H  => exist _ m _
| (cons n ρ), (S i), H => let (r, Hr) := eval_env_lookup_impl ρ i _ in exist _ r _.

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations eval_exp_impl m ρ (H : eval_exp_order m ρ) : { d | eval_exp m ρ d } by struct H :=
| {{{ Sort@s }}}, ρ, H => exist _ d{{{ Sort@s }}} _
| {{{ #x }}}, ρ, H => exist _ (p x) _
| {{{ ℕ }}}                                         , ρ, H => exist _ d{{{ ℕ }}} _
| {{{ zero }}}                                      , ρ, H => exist _ d{{{ zero }}} _
| {{{ succ m }}}                                    , ρ, H =>
    let (r, Hr) := eval_exp_impl m ρ _ in
    exist _ d{{{ succ r }}} _
| {{{ rec M return A | zero -> MZ | succ -> MS end }}}, ρ, H =>
    let (m, Hm) := eval_exp_impl M ρ _ in
    let (r, Hr)  := eval_natrec_impl A MZ MS m ρ _ in
    exist _ r _
| {{{ Π A B }}}, ρ, H =>
    let (r, Hr) := eval_exp_impl A ρ _ in
    exist _ d{{{ Π r ρ B }}} _
| {{{ λ A M }}}, ρ, H => exist _ d{{{ λ ρ M }}} _
| {{{ M N }}}  , ρ, H =>
    let (m, Hm) := eval_exp_impl M ρ _ in
    let (n, Hn) := eval_exp_impl N ρ _ in
    let (a, Ha) := eval_app_impl m n _ in
    exist _ a _
| {{{ Σ A B }}}, ρ, H =>
    let (r, Hr) := eval_exp_impl A ρ _ in
    exist _ d{{{ Σ r ρ B }}} _
| {{{ ⟨ M1 : A ; M2 : B ⟩ }}}, ρ, H =>
    let (m1, Hm1) := eval_exp_impl M1 ρ _ in
    let (m2, Hm2) := eval_exp_impl M2 ρ _ in
    exist _ d{{{ ⟨ m1 ; m2 ⟩ }}} _
| {{{ fst M }}}                                      , ρ, H =>
    let (m, Hm) := eval_exp_impl M ρ _ in
    let (a, Ha) := eval_fst_impl m _ in
    exist _ a _
| {{{ snd M }}}                                      , ρ, H =>
    let (m, Hm) := eval_exp_impl M ρ _ in
    let (b, Hb) := eval_snd_impl m _ in
    exist _ b _
| {{{ Eq A M1 M2 }}}                                    , ρ, H =>
    let (a, Ha) := eval_exp_impl A ρ _ in
    let (m1, Hm1) := eval_exp_impl M1 ρ _ in
    let (m2, Hm2) := eval_exp_impl M2 ρ _ in
    exist _ d{{{ Eq a m1 m2 }}} _
| {{{ refl A M }}}                                      , ρ, H =>
    let (m, Hm) := eval_exp_impl M ρ _ in
    exist _ d{{{ refl m }}} _
| {{{ eqrec N as Eq A M1 M2 return B | refl -> BR end }}}, ρ, H =>
    let (a, Ha) := eval_exp_impl A ρ _ in
    let (m1, Hm1) := eval_exp_impl M1 ρ _ in
    let (m2, Hm2) := eval_exp_impl M2 ρ _ in
    let (n, Hn) := eval_exp_impl N ρ _ in
    let (r, Hr) := eval_eqrec_impl a B BR m1 m2 n ρ _ in
    exist _ r _
| {{{ M[σ] }}}  , ρ, H =>
    let (p', Hp') := eval_sub_impl σ ρ _ in
    let (m, Hm) := eval_exp_impl M ρ' _ in
    exist _ m _

with eval_natrec_impl A MZ MS m ρ (H : eval_natrec_order A MZ MS m ρ) : { d | eval_natrec A MZ MS m ρ d } by struct H :=
| A, MZ, MS, d{{{ zero }}}  , ρ, H =>
    let (mz, Hmz) := eval_exp_impl MZ ρ _ in
    exist _ mz _
| A, MZ, MS, d{{{ succ m }}}, ρ, H =>
    let (mr, Hmr) := eval_natrec_impl A MZ MS m ρ _ in
    let (r, Hr) := eval_exp_impl MS d{{{ ρ ↦ m ↦ mr }}} _ in
    exist _ r _
| A, MZ, MS, d{{{ ⇑ a m }}} , ρ, H =>
    let (mz, Hmz) := eval_exp_impl MZ ρ _ in
    let (mA, HmA) := eval_exp_impl A d{{{ ρ ↦ ⇑ a m }}} _ in
    exist _ d{{{ ⇑ mA (rec m under ρ return A | zero -> mz | succ -> MS end) }}} _

with eval_app_impl m n (H : eval_app_order m n) : { d | eval_app m n d } by struct H :=
| d{{{ λ ρ M }}}        , n, H =>
    let (m, Hm) := eval_exp_impl M d{{{ ρ ↦ n }}} _ in
    exist _ m _
| d{{{ ⇑ (Π a ρ B) m }}}, n, H =>
    let (b, Hb) := eval_exp_impl B d{{{ ρ ↦ n }}} _ in
    exist _ d{{{ ⇑ b (m (⇓ a n)) }}} _

with eval_snd_impl m (H : eval_snd_order m) : { d | eval_snd m d } by struct H :=
| d{{{ ⟨ a ; b ⟩ }}}, H => exist _ b _
| d{{{ ⇑ (Σ a ρ B) m }}}, H =>
    let (b, Hb) := eval_exp_impl B d{{{ ρ ↦ ⇑ a (fst m) }}} _ in
    exist _ d{{{ ⇑ b (snd m) }}} _

with eval_eqrec_impl a B BR m1 m2 n ρ (H : eval_eqrec_order a B BR m1 m2 n ρ) : { d | eval_eqrec a B BR m1 m2 n ρ d } by struct H :=
| a, B, BR, m1, m2, d{{{ refl n }}}, ρ, H =>
    let (r, Hr) := eval_exp_impl BR d{{{ ρ ↦ n }}} _ in
    exist _ r _
| a, B, BR, m1, m2, d{{{ ⇑ c n }}} , ρ, H =>
    let (b, Hb) := eval_exp_impl B d{{{ ρ ↦ m1 ↦ m2 ↦ ⇑ c n }}} _ in
    exist _ d{{{ ⇑ b (eqrec n under ρ as Eq a m1 m2 return B | refl -> BR end) }}} _

with eval_sub_impl s ρ (H : eval_sub_order s ρ) : { ρ' | eval_sub s ρ ρ' } by struct H :=
| {{{ Id }}}, ρ, H => exist _ ρ _
| {{{ Wk }}}, ρ, H => exist _ d{{{ ρ↯ }}} _
| {{{ s ,, M }}}, ρ, H =>
    let (p', Hp') := eval_sub_impl s ρ _ in
    let (m, Hm) := eval_exp_impl M ρ _ in
    exist _ d{{{ ρ' ↦ m }}} _
| {{{ s ∘ τ }}}, ρ, H =>
    let (p', Hp') := eval_sub_impl τ ρ _ in
    let (p'', Hp'') := eval_sub_impl s ρ' _ in
    exist _ ρ'' _.

Extraction Inline eval_exp_impl_functional
  eval_natrec_impl_functional
  eval_app_impl_functional
  eval_snd_impl_functional
  eval_eqrec_impl_functional
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

Lemma eval_exp_impl_complete : forall M ρ m,
    {{ ⟦ M ⟧ ρ ↘ m }} ->
    exists H H', eval_exp_impl M ρ H = exist _ m H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_natrec_impl_complete : forall A MZ MS m ρ r,
    {{ rec m ⟦return A | zero -> MZ | succ -> MS end⟧ ρ ↘ r }} ->
    exists H H', eval_natrec_impl A MZ MS m ρ H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_app_impl_complete : forall m n r,
    {{ $| m & n |↘ r }} ->
    exists H H', eval_app_impl m n H = exist _ r H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_fst_impl_complete : forall m a,
    {{ π₁ m ↘ a }} ->
    exists H H', eval_fst_impl m H = exist _ a H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_snd_impl_complete : forall n b,
    {{ π₂ n ↘ b }} ->
    exists H H', eval_snd_impl n H = exist _ b H'.
Proof.
  intros; functional_eval_complete.
Qed.

Lemma eval_sub_impl_complete : forall σ ρ ρ',
    {{ ⟦ σ ⟧s ρ ↘ ρ' }} ->
    exists H H', eval_sub_impl σ ρ H = exist _ ρ' H'.
Proof.
  intros; functional_eval_complete.
Qed.
