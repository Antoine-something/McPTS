From Coq Require Import Lia Orders PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export Domain Evaluation Readback.
Import Domain_Notations.

Notation "'Dom' a ≈ b ∈ R" := ((R a b : Prop) : Prop) (in custom judg at level 90, a custom domain, b custom domain, R constr).
Notation "'DF' a ≈ b ∈ R ↘ R'" := ((R R' a b : Prop) : Prop) (in custom judg at level 90, a custom domain, b custom domain, R constr, R' constr).
Notation "'Exp' a ≈ b ∈ R" := (R a b : (Prop : Type)) (in custom judg at level 90, a custom exp, b custom exp, R constr).
Notation "'EF' a ≈ b ∈ R ↘ R'" := (R R' a b : (Prop : Type)) (in custom judg at level 90, a custom exp, b custom exp, R constr, R' constr).


(** Precedences of the next notations follow the ones in the standard library.
    However, we do not use the ones in the standard library so that we can change
    the relation if necessary in the future. *)
Notation "R ~> R'" := (subrelation R R') (at level 70, right associativity).
Notation "R <~> R'" := (relation_equivalence R R') (at level 95, no associativity).

Generalizable All Variables.

(** *** Helper Bundles *)
(** Related modulo evaluation *)
Variant rel_mod_eval `(R : relation (domain P) -> domain P -> domain P -> Prop) A ρ A' ρ' R' : Prop := mk_rel_mod_eval : forall a a', {{ ⟦ A ⟧ ρ ↘ a }} -> {{ ⟦ A' ⟧ ρ' ↘ a' }} -> {{ DF a ≈ a' ∈ R ↘ R' }} -> rel_mod_eval R A ρ A' ρ' R'.
#[global]
Arguments mk_rel_mod_eval {_ _ _ _ _ _ _}.
#[export]
Hint Constructors rel_mod_eval : mcpts.

(** Related modulo application *)
Variant rel_mod_app {P : PtsSig} f a f' a' (R : relation (domain P)) : Prop := mk_rel_mod_app : forall fa f'a', {{ $| f & a |↘ fa }} -> {{ $| f' & a' |↘ f'a' }} -> {{ Dom fa ≈ f'a' ∈ R }} -> rel_mod_app f a f' a' R.
#[global]
Arguments mk_rel_mod_app {_ _ _ _ _ _}.
#[export]
Hint Constructors rel_mod_app : mcpts.

(** *** (Some Elements of) PER Lattice *)

Definition per_bot {P : PtsSig} : relation (domain_ne P) := fun m m' => (forall s, exists L, {{ Rne m in s ↘ L }} /\ {{ Rne m' in s ↘ L }}).
#[global]
Arguments per_bot /.
#[export]
Hint Transparent per_bot : mcpts.
#[export]
Hint Unfold per_bot : mcpts.

Definition per_top {P : PtsSig} : relation (domain_nf P) := fun m m' => (forall s, exists L, {{ Rnf m in s ↘ L }} /\ {{ Rnf m' in s ↘ L }}).
#[global]
Arguments per_top /.
#[export]
Hint Transparent per_top : mcpts.
#[export]
Hint Unfold per_top : mcpts.

Definition per_top_typ {P : PtsSig} : relation (domain P) := fun a a' => (forall s, exists C, {{ Rtyp a in s ↘ C }} /\ {{ Rtyp a' in s ↘ C }}).
#[global]
Arguments per_top_typ /.
#[export]
Hint Transparent per_top_typ : mcpts.
#[export]
Hint Unfold per_top_typ : mcpts.

Inductive per_nat {P : PtsSig} : relation (domain P):=
| per_nat_zero : {{ Dom zero ≈ zero ∈ per_nat }}
| per_nat_succ :
  `{ {{ Dom m ≈ m' ∈ per_nat }} ->
     {{ Dom succ m ≈ succ m' ∈ per_nat }} }
| per_nat_neut :
  `{ {{ Dom m ≈ m' ∈ per_bot }} ->
     {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_nat }} }
.
#[export]
Hint Constructors per_nat : mcpts.

Variant per_ne {P : PtsSig} : relation (domain P) :=
| per_ne_neut :
  `{ {{ Dom m ≈ m' ∈ @per_bot P }} ->
     {{ Dom ⇑ a m ≈ ⇑ a' m' ∈ per_ne }} }
.
#[export]
Hint Constructors per_ne : mcpts.

(** * Sort/Element PER *)
(** ** Sort/Element PER Definition *)

Section Per_sort_elem_core_def.
  Context
    `(pred_P : PredicativeSig P)
      (s_elem : P).

  Let dom := domain P.

  Context (per_sort_elem_rec : forall s', pred_rel pred_P s' s_elem -> relation dom -> relation dom).
  Arguments per_sort_elem_rec {_}.

  Definition per_sort_rec {s'} (ord : pred_rel pred_P s' s_elem) : relation dom :=
    fun a a' => exists R, per_sort_elem_rec ord R a a'.

  (** Defines 'a = b ∈ Sort_s ↘ R' in the paper *)
  Inductive per_sort_elem_core : relation dom -> dom -> dom -> Prop :=
  | per_sort_elem_core_sort :
    `{ forall (s2 : P)
         (ax : Ax_typ P s1 s2)
         (sub : st_subtyp s2 s_elem)
         (elem_rel : relation dom),
          s1 = s1' ->
          (elem_rel <~> per_sort_rec (ord_ax_typ_sub pred_P ax sub)) ->
          {{ DF Sort@s1 ≈ Sort@s1' ∈ per_sort_elem_core ↘ elem_rel }} }
  | per_sort_elem_core_pi :
    `{ forall (r : Ru_pi P s_in s_out s_pi)
         (sub : st_subtyp s_pi s_elem)
         (in_rel : relation dom)
         (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation dom)
         (elem_rel : relation dom)
         (equiv_a_a' : (s_in = s_elem -> {{ DF a ≈ a' ∈ per_sort_elem_core ↘ in_rel }}) /\ (forall (lt_in_elem : pred_rel pred_P s_in s_elem), {{ DF a ≈ a' ∈ per_sort_elem_rec lt_in_elem ↘ in_rel }})),
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (fun R b b' => (s_out = s_elem -> {{ DF b ≈ b' ∈ per_sort_elem_core ↘ R }}) /\ (forall (lt_out_elem : pred_rel pred_P s_out s_elem), {{ DF b ≈ b' ∈ per_sort_elem_rec lt_out_elem ↘ R }})) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem_core ↘ elem_rel }} }
  | per_sort_elem_core_nat :
    `{ forall (r : Ru_nat P s)
         (sub : st_subtyp s s_elem)
         (elem_rel : relation dom),
          (elem_rel <~> per_nat) ->
          {{ DF ℕ ≈ ℕ ∈ per_sort_elem_core ↘ elem_rel }} }
  | per_sort_elem_core_neut :
    `{ forall (elem_rel : relation dom),
          {{ Dom e ≈ e' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          {{ DF ⇑ a e ≈ ⇑ a' e' ∈ per_sort_elem_core ↘ elem_rel }} }
  .

  Hypothesis
    (motive : relation dom -> dom -> dom -> Prop)
      (case_sort :
        forall {s1 s1' s2 : P}
          (ax : Ax_typ P s1 s2)
          (sub : st_subtyp s2 s_elem)
            {elem_rel : relation dom},
          s1 = s1' ->
          (elem_rel <~> per_sort_rec (ord_ax_typ_sub pred_P ax sub)) ->
          motive elem_rel d{{{ Sort@s1 }}} d{{{ Sort@s1' }}})
      (case_Pi :
        forall {s_in s_out s_pi : P} (r : Ru_pi P s_in s_out s_pi)
          (sub : st_subtyp s_pi s_elem)
          {a ρ B a' ρ' B' in_rel}
          (out_rel : forall {n n'} (equiv_n_n' : (in_rel n n')), relation dom)
          {elem_rel : relation dom},
          (s_in = s_elem -> {{ DF a ≈ a' ∈ per_sort_elem_core ↘ in_rel }} /\ motive in_rel a a') /\ (forall (lt_in_elem : pred_rel pred_P s_in s_elem), {{ DF a ≈ a' ∈ per_sort_elem_rec lt_in_elem ↘ in_rel }}) ->
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : (in_rel n n')),
              rel_mod_eval (fun R b b' => (s_out = s_elem -> {{ DF b ≈ b' ∈ per_sort_elem_core ↘ R }} /\ motive R b b') /\ (forall (lt_out_elem : pred_rel pred_P s_out s_elem), {{ DF b ≈ b' ∈ per_sort_elem_rec lt_out_elem ↘ R }})) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : (in_rel n n')), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          motive elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a' ρ' B' }}})
      (case_nat :
        forall {s} (r : Ru_nat P s)
          (sub : st_subtyp s s_elem)
          {elem_rel : relation dom},
          (elem_rel <~> per_nat) ->
          motive elem_rel d{{{ ℕ }}} d{{{ ℕ }}})
      (case_ne :
        forall {a a' b b'}
          {elem_rel : relation dom},
          (per_bot b b') ->
          (elem_rel <~> per_ne) ->
          motive elem_rel (d_neut a b) (d_neut a' b'))
  .

  #[derive(equations=no, eliminator=no)]
  Equations per_sort_elem_core_strong_ind R a b (H : {{ DF a ≈ b ∈ per_sort_elem_core ↘ R }})
    : {{ DF a ≈ b ∈ motive ↘ R }} :=
  | R, a, b, (per_sort_elem_core_sort s2 ax sub _ HE eq) => case_sort ax sub HE eq;
  | R, a, b, (per_sort_elem_core_pi r sub _ out_rel _ equiv_a_a' per HT HE) =>
      case_Pi r sub out_rel
        (let 'conj HA _ := equiv_a_a' in
         conj (fun eq => conj _ (per_sort_elem_core_strong_ind _ _ _ (HA eq))) _)
        per
        (fun _ _ equiv_n_n' =>
           let 'mk_rel_mod_eval b b' evb evb' (conj HB _) := HT _ _ equiv_n_n' in
           mk_rel_mod_eval b b' evb evb' (conj (fun eq => conj _ (per_sort_elem_core_strong_ind _ _ _ (HB eq))) _))
        HE;
  | R, a, b, (per_sort_elem_core_nat _ sub _ HE) => case_nat _ sub HE;
  | R, a, b, (per_sort_elem_core_neut _ equiv_e_e' HE) => case_ne equiv_e_e' HE
  .    
End Per_sort_elem_core_def.

#[export]
Hint Constructors per_sort_elem_core : mcpts.

Section Per_sort_elem_def.
  Context `(pred_P : PredicativeSig P).

  Let dom := domain P.

  Instance Per_sort_elem_def_wf : WellFounded (pred_rel pred_P) := (wf_rel pred_P).

  Equations per_sort_elem (s : P) : relation dom -> dom -> dom -> Prop by wf s :=
  | s => per_sort_elem_core pred_P s (fun s' lt_s'_s R' a a' => {{ DF a ≈ a' ∈ per_sort_elem s' ↘ R' }}).
End Per_sort_elem_def.

Arguments per_sort_elem {_} _.

Definition per_sort `(pred_P : PredicativeSig P) (s : P) : relation (domain P) :=
  fun a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem pred_P s ↘ R' }}.

#[global]
Arguments per_sort _ _ _ _ _ /.
#[export]
Hint Transparent per_sort : mcpts.
#[export]
Hint Unfold per_sort : mcpts.

Lemma per_sort_elem_core_sort' `{pred_P : PredicativeSig P} : forall s1 s2 s_elem elem_rel,
    Ax_typ P s1 s2 ->
    st_subtyp s2 s_elem ->
    (elem_rel <~> per_sort pred_P s1) ->
    {{ DF Sort@s1 ≈ Sort@s1 ∈ per_sort_elem pred_P s_elem ↘ elem_rel }}.
Proof.
  intros.
  simp per_sort_elem.
  eapply per_sort_elem_core_sort with (ax := H) (sub := H0); mauto.
Qed.

#[export]
Hint Resolve per_sort_elem_core_sort' : mcpts.

(** ** Sort/Element PER Induction Principle *)

Section Per_sort_elem_ind_def.
  Context
    (P : PtsSig)
      (pred_P : PredicativeSig P).

  Let dom := domain P.

  Hypothesis
    (motive : P -> relation dom -> dom -> dom -> Prop)
      (case_sort :
        forall s_elem {s1 s1' s2 elem_rel}
          (ax : Ax_typ P s1 s2)
          (sub : st_subtyp s2 s_elem),
          s1 = s1' ->
          (elem_rel <~> per_sort pred_P s1) ->
          (forall a b R, {{ DF a ≈ b ∈ per_sort_elem pred_P s1 ↘ R }} -> motive s1 R a b) ->
          motive s_elem elem_rel d{{{ Sort@s1 }}} d{{{ Sort@s1' }}})
      (case_Pi :
        forall s_elem {s_in s_out s_pi} (r : Ru_pi P s_in s_out s_pi)
          (sub : st_subtyp s_pi s_elem)
          {a ρ B a' ρ' B' in_rel}
          (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation dom)
          {elem_rel},
          {{ DF a ≈ a' ∈ per_sort_elem pred_P s_in ↘ in_rel }} ->
          motive s_in in_rel a a' ->
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (fun R x y => {{ DF x ≈ y ∈ per_sort_elem pred_P s_out ↘ R }} /\ motive s_out R x y) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          motive s_elem elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a' ρ' B' }}})
      (case_N : forall s s_elem (r : Ru_nat P s) (sub : st_subtyp s s_elem) {elem_rel},
          (elem_rel <~> per_nat) ->
          motive s_elem elem_rel d{{{ ℕ }}} d{{{ ℕ }}})
      (case_ne :
        forall s_elem {a a' b b' elem_rel},
          {{ Dom b ≈ b' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          motive s_elem elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}}).

  #[local]
  Ltac def_simp := simp per_sort_elem in *; solve [mauto 3 using ord_ax_typ, ord_ax_sub, ord_ru_pi].

  Instance Per_sort_elem_ind_def_wf : WellFounded (pred_rel pred_P) := (wf_rel pred_P).

  #[local]
  Ltac impl_tac := simpl in *; program_simplify; CoreTactics.equations_simpl; try program_solve_wf; try def_simp.

  #[derive(equations=no, eliminator=no), tactic="impl_tac"]
  Equations per_sort_elem_ind' (s : P) (R : relation dom) (a b : dom)
  (H : {{ DF a ≈ b ∈ per_sort_elem_core pred_P s (fun s' lt_s'_s R' a a' => {{ DF a ≈ a' ∈ per_sort_elem pred_P s' ↘ R' }}) ↘ R }}) : {{ DF a ≈ b ∈ motive s ↘ R }} by wf s :=
  | s, R, a, b =>
      per_sort_elem_core_strong_ind pred_P s _ (motive s)
        (fun _ _ _ ax_typ sub _ eq HE => case_sort  _ ax_typ sub eq HE (fun a' b' R' H' => per_sort_elem_ind' _ R' a' b' _))
        (fun _ _ _ r sub _ _ _ _ _ _ _ out_rel _ HA per HB =>
           let 'conj Heq Hlt := HA in
           case_Pi _ r sub out_rel
             (match proj1 (ord_ru_pi_sub pred_P r sub) with
              | or_introl _ => _
              | or_intror eq => let 'conj _ _ := Heq eq in _
              end)
             (match proj1 (ord_ru_pi_sub pred_P r sub) with
              | or_introl _ => _
              | or_intror eq => let 'conj _ _ := Heq eq in _
              end)
             per
             (fun _ _ equiv =>
                let 'mk_rel_mod_eval _ _ evb evb' (conj Heq _) := HB _ _ equiv in
                match proj2 (ord_ru_pi_sub pred_P r sub) with
                | or_introl lt_out_s => mk_rel_mod_eval _ _ evb evb' (conj _ _)
                | or_intror eq => let 'conj _ _ := Heq eq in _
                end))
        (fun _ _ sub _ => case_N _ _ _ sub)
        (fun _ _ _ _ _ _ _ => case_ne _ _ _)
        R a b.
  Next Obligation.
    eapply ord_ax_typ_sub; mauto 2.
  Qed.
  Next Obligation.
    unfold pointwise_lifting.
    rewrite -> r0.
    reflexivity.
  Qed.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_sort_elem_ind s a b R (H : per_sort_elem pred_P s a b R) : motive s a b R :=
  | s, a, b, R, _ := per_sort_elem_ind' s a b R _.
End Per_sort_elem_ind_def.

(** Subtyping PER *)
Reserved Notation "⟪ pred_P ⟫ 'Subs' a <: b 'at' s" (in custom judg at level 80, pred_P constr, a custom domain, b custom domain, s constr).
Reserved Notation "⟪ pred_P ⟫ 'Sub' a <: b" (in custom judg at level 80, pred_P constr, a custom domain, b custom domain).

(* Not sure if we want this or just the unsorted version (like for syntactic judgments) *)
Inductive per_subtyp_sorted `(pred_P : PredicativeSig P) : P -> domain P -> domain P -> Prop :=
| per_subtyp_sorted_sort :
  `( st_subtyp s1 s2 ->
     {{ Dom Sort@s1 ≈ Sort@s1 ∈ per_sort pred_P s }} ->
     {{ Dom Sort@s2 ≈ Sort@s2 ∈ per_sort pred_P s }} ->
     {{ ⟪ pred_P ⟫ Subs Sort@s1 <: Sort@s2 at s }} )
| per_subtyp_sorted_nat :
  `( {{ Dom ℕ ≈ ℕ ∈ per_sort pred_P s }} ->
     {{ ⟪ pred_P ⟫ Subs ℕ <: ℕ at s }} )
| per_subtyp_sorted_pi :
  `( forall {r : Ru_pi P s1 s2 s3}
       {sub : st_subtyp s3 s}
       (in_rel : relation (domain P)) elem_rel elem_rel',
        {{ DF a ≈ a' ∈ per_sort_elem pred_P s1 ↘ in_rel }} ->
        (forall c c' b b',
            {{ Dom c ≈ c' ∈ in_rel }} ->
            {{ ⟦ B ⟧ (ρ ↦ c) ↘ b }} ->
            {{ ⟦ B' ⟧ (ρ' ↦ c') ↘ b' }} ->
            {{ ⟪ pred_P ⟫ Subs b <: b' at s2 }}) ->
        {{ DF Π r a ρ B ≈ Π r a ρ B ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
        {{ DF Π r a' ρ' B' ≈ Π r a' ρ' B' ∈ per_sort_elem pred_P s ↘ elem_rel' }} ->
        {{ ⟪ pred_P ⟫ Subs Π r a ρ B <: Π r a' ρ' B' at s }})
| per_subtyp_sorted_neut :
  `( {{ Dom e ≈ e' ∈ per_bot }} ->
     {{ ⟪ pred_P ⟫ Subs ⇑ a e <: ⇑ a' e' at s }} )
where "⟪ pred_P ⟫ 'Subs' a <: b 'at' s" := (per_subtyp_sorted pred_P s a b) (in custom judg) : type_scope.

Inductive per_subtyp `(pred_P : PredicativeSig P) : domain P -> domain P -> Prop :=
| per_subtyp_sort :
  `( st_subtyp s1 s2 ->
     {{ ⟪ pred_P ⟫ Sub Sort@s1 <: Sort@s2 }} )
| per_subtyp_from_sorted :
  `( {{ ⟪ pred_P ⟫ Subs a <: b at s }} ->
     {{ ⟪ pred_P ⟫ Sub a <: b }} )
where "⟪ pred_P ⟫ 'Sub' a <: b" := (per_subtyp pred_P a b) (in custom judg) : type_scope.

#[export]
Hint Constructors per_subtyp_sorted per_subtyp : mcpts.


Definition rel_typ `(pred_P : PredicativeSig P) s A ρ A' ρ' R' := rel_mod_eval (per_sort_elem pred_P s) A ρ A' ρ' R'.
Arguments rel_typ _ _ _ _ _ _ _ _ /.
#[export]
Hint Transparent rel_typ : mcpts.
#[export]
Hint Unfold rel_typ : mcpts.


(** * Unsorted type PER *)
Section Per_typ_def.
  Context
    `(pred_P : PredicativeSig P).

  Let dom := domain P.

  Inductive per_typ_elem : relation dom -> dom -> dom -> Prop :=
  | per_typ_sort :
    `{ R <~> per_sort pred_P s ->
       {{ DF Sort@s ≈ Sort@s ∈ per_typ_elem ↘ R }} }
  | per_typ_type :
    `{ {{ DF a ≈ b ∈ per_sort_elem pred_P s ↘ R }} ->
       {{ DF a ≈ b ∈ per_typ_elem ↘ R }} }.

End Per_typ_def.

#[export]
Hint Constructors per_typ_elem : mcpts.


Definition per_typ `(pred_P : PredicativeSig P) : relation (domain P) :=
  fun a a' => exists R', {{ DF a ≈ a' ∈ per_typ_elem pred_P ↘ R' }}.
#[global]
Arguments per_typ _ _ _ _ /.
#[export]
Hint Transparent per_typ : mcpts.
#[export]
Hint Unfold per_typ : mcpts.




Definition rel_typ_unsorted `(pred_P : PredicativeSig P) A ρ A' ρ' R' := rel_mod_eval (per_typ_elem pred_P) A ρ A' ρ' R'.
Arguments rel_typ_unsorted _ _ _ _ _ _ _ /.
#[export]
Hint Transparent rel_typ_unsorted : mcpts.
#[export]
Hint Unfold rel_typ_unsorted : mcpts.

(** * Context/Environment PER *)

Section Per_ctx_env_def.
  Context `(pred_P : PredicativeSig P).

  Let dom := domain P.

  Variant cons_per_ctx_env tail_rel (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation dom) : relation (env P) :=
    | mk_cons_per_ctx_env :
      `{ forall (equiv_ρ_drop_ρ'_drop : {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }}),
            {{ #| ρ[0] |↘ n }} -> {{ #| ρ'[0] |↘ n' }} ->
            {{ Dom n ≈ n' ∈ head_rel equiv_ρ_drop_ρ'_drop }} ->
            {{ Dom ρ ≈ ρ' ∈ cons_per_ctx_env tail_rel (@head_rel) }} }.

  Inductive per_ctx_env : relation (env P) -> ctx P -> ctx P -> Prop :=
  | per_ctx_env_nil :
    `{ forall env_rel,
          (env_rel <~> fun ρ ρ' => True) ->
          {{ EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ env_rel }} }
  | per_ctx_env_cons :
    `{ forall tail_rel
          (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation dom)
          env_rel
          (equiv_Γ_Γ' : {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }}),
          PER tail_rel ->
          (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
              rel_typ_unsorted pred_P A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
          (env_rel <~> cons_per_ctx_env tail_rel (@head_rel)) ->
          {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ env_rel }} }
  .
End Per_ctx_env_def.

#[export]
Hint Constructors cons_per_ctx_env per_ctx_env : mcpts.

Definition per_ctx `(pred_P : PredicativeSig P) : relation (ctx P) := fun Γ Γ' => exists R', @per_ctx_env P pred_P R' Γ Γ'.
Definition valid_ctx `(pred_P : PredicativeSig P) : ctx P -> Prop := fun Γ => @per_ctx P pred_P Γ Γ.
#[export]
Hint Transparent valid_ctx : mcpts.
#[export]
Hint Unfold valid_ctx : mcpts.


(** Context Subtyping PER *)
Reserved Notation "⟪ pred_P ⟫ 'SubE' Γ <: Δ" (in custom judg at level 80, pred_P constr, Γ custom exp, Δ custom exp).

Inductive per_ctx_subtyp `(pred_P : PredicativeSig P) : ctx P -> ctx P -> Prop :=
| per_ctx_subtyp_nil :
  {{ ⟪ pred_P ⟫ SubE ⋅ <: ⋅ }}
| per_ctx_subtyp_cons :
  `{ forall tail_rel env_rel env_rel',
        {{ ⟪ pred_P ⟫ SubE Γ <: Γ' }} ->
        {{ EF Γ ≈ Γ ∈ per_ctx_env pred_P ↘ tail_rel }} ->
        (forall ρ ρ' a a'
           (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
            {{ ⟦ A ⟧ ρ ↘ a }} ->
            {{ ⟦ A' ⟧ ρ' ↘ a' }} ->
            {{ ⟪ pred_P ⟫ Sub a <: a' }}) ->
        {{ EF Γ, A ≈ Γ, A ∈ per_ctx_env pred_P ↘ env_rel }} ->
        {{ EF Γ', A' ≈ Γ', A' ∈ per_ctx_env pred_P ↘ env_rel' }} ->
        {{ ⟪ pred_P ⟫ SubE Γ, A <: Γ', A' }} }
where "⟪ pred_P ⟫ 'SubE' Γ <: Δ" := (per_ctx_subtyp pred_P Γ Δ) (in custom judg) : type_scope.

#[export]
Hint Constructors per_ctx_subtyp : mcpts.
