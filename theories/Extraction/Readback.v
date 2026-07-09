From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Readback Evaluation.
From McPTS.Extraction Require Import Evaluation.
Import Domain_Notations.

Generalizable All Variables.

Inductive read_nf_order {P : PtsSig} : nat -> domain_nf P -> Prop :=
| rnf_type :
  `( read_typ_order i a ->
    read_nf_order i d{{{ ⇓ Sort@s a }}} )
| rnf_fn :
  `( forall (r : Ru_pi P s1 s2 s3),
        read_typ_order i a ->
        eval_app_order m d{{{ ⇑! a i }}} ->
        eval_exp_order B d{{{ p ↦ ⇑! a i }}} ->
        (forall b,
            {{ ⟦ B ⟧ p ↦ ⇑! a i ↘ b }} ->
            read_typ_order (S i) b) ->
        (forall m' b,
            {{ $| m & ⇑! a i |↘ m' }} ->
            {{ ⟦ B ⟧ p ↦ ⇑! a i ↘ b }} ->
            read_nf_order (S i) d{{{ ⇓ b m' }}}) ->
        read_nf_order i d{{{ ⇓ (Π r a p B) m }}} )
| rnf_zero :
  `( read_nf_order i d{{{ ⇓ ℕ zero }}} )
| rnf_succ :
  `( read_nf_order i d{{{ ⇓ ℕ m }}} ->
     read_nf_order i d{{{ ⇓ ℕ (succ m) }}} )
| rnf_nat_neut :
  `( read_ne_order i m ->
     read_nf_order i d{{{ ⇓ ℕ (⇑ a m) }}} )
| rnf_neut :
  `( read_ne_order i m ->
     read_nf_order i d{{{ ⇓ (⇑ a b) (⇑ c m) }}} )

with read_ne_order {P : PtsSig} : nat -> domain_ne P -> Prop :=
| rne_var :
  `( read_ne_order i d{{{ !x }}} )
| rne_app :
  `( read_ne_order i m ->
     read_nf_order i n ->
     read_ne_order i d{{{ m n }}} )
| rne_natrec :
  `( eval_exp_order B d{{{ p ↦ ⇑! ℕ i }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ i ↘ b }} ->
         read_typ_order (S i) b) ->
     eval_exp_order B d{{{ p ↦ zero }}} ->
     (forall bz,
         {{ ⟦ B ⟧ p ↦ zero ↘ bz }} ->
         read_nf_order i d{{{ ⇓ bz mz }}}) ->
     eval_exp_order B d{{{ p ↦ succ (⇑! ℕ i) }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ i ↘ b }} ->
         eval_exp_order MS d{{{ (p ↦ ⇑! ℕ i) ↦ ⇑! b (S i) }}}) ->
     (forall b bs ms,
         {{ ⟦ B ⟧ p ↦ ⇑! ℕ i ↘ b }} ->
         {{ ⟦ B ⟧ p ↦ succ (⇑! ℕ i) ↘ bs }} ->
         {{ ⟦ MS ⟧ (p ↦ ⇑! ℕ i) ↦ ⇑! b (S i) ↘ ms }} ->
         read_nf_order (S (S i)) d{{{ ⇓ bs ms }}}) ->
     read_ne_order i m ->
     read_ne_order i d{{{ rec m under p return B | zero -> mz | succ -> MS end }}} )

with read_typ_order {P : PtsSig} : nat -> domain P -> Prop :=
| rtyp_sort :
  `( read_typ_order i d{{{ Sort@s }}} )
| rtyp_nat :
  `( read_typ_order i d{{{ ℕ }}} )
| rtyp_pi :
  `( forall (r : Ru_pi P s1 s2 s3),
      read_typ_order i a ->
     eval_exp_order B d{{{ p ↦ ⇑! a i }}} ->
     (forall b,
         {{ ⟦ B ⟧ p ↦ ⇑! a i ↘ b }} ->
         read_typ_order (S i) b) ->
     read_typ_order i d{{{ Π r a p B }}})
| rtyp_neut :
  `( read_ne_order i b ->
     read_typ_order i d{{{ ⇑ a b }}} ).

#[local]
Hint Constructors read_nf_order read_ne_order read_typ_order : mcpts.

Lemma read_nf_order_sound {P : PtsSig} : forall i (d : domain_nf P) m,
    {{ Rnf d in i ↘ m }} ->
    read_nf_order i d
with read_ne_order_sound {P : PtsSig} : forall i (d : domain_ne P) m,
    {{ Rne d in i ↘ m }} ->
    read_ne_order i d
with read_typ_order_sound {P : PtsSig} : forall i (d : domain P) m,
    {{ Rtyp d in i ↘ m }} ->
    read_typ_order i d.
Proof with (econstructor; intros; functional_eval_rewrite_clear; mauto).
  - clear read_nf_order_sound; induction 1...
  - clear read_ne_order_sound; induction 1...
  - clear read_typ_order_sound; induction 1...
Qed.

#[export]
Hint Resolve read_nf_order_sound read_ne_order_sound read_typ_order_sound : mcpts.

#[local]
Ltac impl_obl_tac1 :=
  match goal with
  | H : read_nf_order _ _ |- _ => progressive_invert H
  | H : read_ne_order _ _ |- _ => progressive_invert H
  | H : read_typ_order _ _ |- _ => progressive_invert H
  end.

#[local]
Ltac impl_obl_tac :=
  repeat impl_obl_tac1; try econstructor; mauto.

#[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
Equations read_nf_impl {P : PtsSig} i (d : domain_nf P) (H : read_nf_order i d) : { m | {{ Rnf d in i ↘ m }} } by struct H :=
| i, d{{{ ⇓ Sort@s a }}}, H =>
    let (A, HA) := read_typ_impl i a _ in
    exist _ A _
| i, d{{{ ⇓ (Π r a p B) m }}}, H =>
    let (A, HA) := read_typ_impl i a _ in
    let (m', Hm') := eval_app_impl m d{{{ ⇑! a i }}} _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a i }}} _ in
    let (B', HB') := read_typ_impl (S i) b _ in
    let (M, HM) := read_nf_impl (S i) d{{{ ⇓ b m' }}} _ in
    exist _ n{{{ λ r A B' M }}} _
| i, d{{{ ⇓ ℕ zero }}}    , H => exist _ n{{{ zero }}} _
| i, d{{{ ⇓ ℕ (succ m) }}}, H =>
    let (M, HM) := read_nf_impl i d{{{ ⇓ ℕ m }}} _ in
    exist _ n{{{ succ M }}} _
| i, d{{{ ⇓ ℕ (⇑ ^_ m) }}}, H =>
    let (M, HM) := read_ne_impl i m _ in
    exist _ n{{{ ⇑ M }}} _
| i, d{{{ ⇓ (⇑ a b) (⇑ c m) }}}, H =>
    let (M, HM) := read_ne_impl i m _ in
    exist _ n{{{ ⇑ M }}} _

with read_ne_impl {P : PtsSig} i (d : domain_ne P) (H : read_ne_order i d) : { m | {{ Rne d in i ↘ m }} } by struct H :=
| i, d{{{ !x }}}, H => exist _ n{{{ #(i - x - 1) }}} _
| i, d{{{ m n }}}, H =>
    let (M, HM) := read_ne_impl i m _ in
    let (N, HN) := read_nf_impl i n _ in
    exist _ n{{{ M N }}} _
| i, d{{{ rec m under p return B | zero -> mz | succ -> MS end }}}, H =>
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! ℕ i }}} _ in
    let (B', HB') := read_typ_impl (S i) b _ in
    let (bz, Hbz) := eval_exp_impl B d{{{ p ↦ zero }}} _ in
    let (MZ, HMZ) := read_nf_impl i d{{{ ⇓ bz mz }}} _ in
    let (bs, Hbs) := eval_exp_impl B d{{{ p ↦ succ (⇑! ℕ i) }}} _ in
    let (ms, Hms) := eval_exp_impl MS d{{{ (p ↦ ⇑! ℕ i) ↦ ⇑! b (S i) }}} _ in
    let (MS', HMS') := read_nf_impl (S (S i)) d{{{ ⇓ bs ms }}} _ in
    let (M, HM) := read_ne_impl i m _ in
    exist _ n{{{ rec M return B' | zero -> MZ | succ -> MS' end }}} _

with read_typ_impl {P : PtsSig} i (d : domain P) (H : read_typ_order i d) : { m | {{ Rtyp d in i ↘ m }} } by struct H :=
| i, d{{{ Sort@s }}}, H => exist _ n{{{ Sort@s }}} _
| i, d{{{ ℕ }}}, H => exist _ n{{{ ℕ }}} _
| i, d{{{ Π r a p B }}}, H =>
    let (A, HA) := read_typ_impl i a _ in
    let (b, Hb) := eval_exp_impl B d{{{ p ↦ ⇑! a i }}} _ in
    let (B', HB') := read_typ_impl (S i) b _ in
    exist _ n{{{ Π r A B' }}} _
| i, d{{{ ⇑ a b }}}, H =>
    let (B, HB) := read_ne_impl i b _ in
    exist _ n{{{ ⇑ B }}} _.

Extraction Inline read_nf_impl_functional
  read_ne_impl_functional
  read_typ_impl_functional.

(** The definitions of [read_*_impl] already come with soundness proofs,
    so we only need to prove completeness. However, the completeness
    is also obvious from the soundness of eval orders and functional
    nature of readback. *)

#[local]
Ltac functional_read_complete :=
  lazymatch goal with
  | |- exists (_ : ?T), _ =>
      let Horder := fresh "Horder" in
      assert T as Horder by mauto 3;
      eexists Horder;
      lazymatch goal with
      | |- exists _, ?L = _ =>
          destruct L;
          functional_read_rewrite_clear;
          eexists; reflexivity
      end
  end.

Lemma read_nf_impl_complete {P : PtsSig} : forall i (d : domain_nf P) m,
    {{ Rnf d in i ↘ m }} ->
    exists H H', read_nf_impl i d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_ne_impl_complete {P : PtsSig} : forall i (d : domain_ne P) m,
    {{ Rne d in i ↘ m }} ->
    exists H H', read_ne_impl i d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.

Lemma read_typ_impl_complete {P : PtsSig} : forall s (d : domain P) m,
    {{ Rtyp d in s ↘ m }} ->
    exists H H', read_typ_impl s d H = exist _ m H'.
Proof.
  intros; functional_read_complete.
Qed.
