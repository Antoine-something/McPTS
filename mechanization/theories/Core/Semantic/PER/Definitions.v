From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
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
Variant rel_mod_eval {P : PtsSig} (R : relation (domain P) -> domain P -> domain P -> Prop) A ρ A' ρ' R' : Prop := mk_rel_mod_eval : forall a a', {{ ⟦ A ⟧ ρ ↘ a }} -> {{ ⟦ A' ⟧ ρ' ↘ a' }} -> {{ DF a ≈ a' ∈ R ↘ R' }} -> rel_mod_eval R A ρ A' ρ' R'.
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
  Variable
    (P : PtsSig)
      (pred_P : PredicativeSig P)
      (s : St P)
      (per_sort_rec : forall {s'}, Ax P s' s -> relation (domain P)).

  (** Defines 'a = b ∈ Sort_s ↘ R' in the paper *)
  Inductive per_sort_elem_core : (St P) -> relation (domain P) -> domain P -> domain P -> Prop :=
  | per_sort_elem_core_sort :
    `{ forall (elem_rel : relation (domain P))
         (ax_s1_s : Ax P s1 s),
          s1 = s2 ->
          (elem_rel <~> per_sort_rec ax_s1_s) ->
          {{ DF Sort@s1 ≈ Sort@s2 ∈ per_sort_elem_core s ↘ elem_rel }} }
  | per_sort_elem_core_pi : 
    `{ forall (s_in s_out : St P) (r : Ru P s_in s_out s)
         (in_rel : relation (domain P))
         (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P))
         (elem_rel : relation (domain P))
         (equiv_a_a'  : {{ DF a ≈ a' ∈ (per_sort_elem_core s_in) ↘ in_rel }}),
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (per_sort_elem_core s_out) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ (per_sort_elem_core s) ↘ elem_rel }} }
  | per_sort_elem_core_neut :
    `{ forall (elem_rel : relation (domain P)),
         {{ Dom e ≈ e' ∈ @per_bot P }} ->
         (elem_rel <~> @per_ne P) ->
         {{ DF ⇑ a e ≈ ⇑ a' e' ∈ (per_sort_elem_core s) ↘ elem_rel }} }
  .

  Hypothesis
    (motive : St P -> relation (domain P) -> domain P -> domain P -> Prop)
      (case_sort :
        forall {s1 s2 elem_rel} (ax_s1_s : Ax P s1 s),
          s1 = s2 ->
          (elem_rel <~> per_sort_rec ax_s1_s) ->
          motive s elem_rel d{{{ Sort@s1 }}} d{{{ Sort@s2 }}})
      (case_Pi :
        forall (s_in s_out : St P) (r : Ru P s_in s_out s)
          {a ρ B a' ρ' B' in_rel}
          (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P))
          {elem_rel},
          {{ DF a ≈ a' ∈ per_sort_elem_core s_in ↘ in_rel }} ->
          motive s_in in_rel a a' ->
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (fun R x y => {{DF x ≈ y ∈ per_sort_elem_core s_out ↘ R }} /\ motive s_out R x y) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          motive s elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a' ρ' B' }}})
      (case_ne :
        forall {s a b a' b' elem_rel},
          {{ Dom b ≈ b' ∈ @per_bot P }} ->
          (elem_rel <~> per_ne) ->
          motive s elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}})
  .

  #[derive(equations=no, eliminator=no)]
  Equations per_sort_elem_core_strong_ind (s' : St P) R a b (H : {{ DF a ≈ b ∈ per_sort_elem_core s' ↘ R }}) : {{ DF a ≈ b ∈ motive s' ↘ R }} :=
  | s, R, a, b, (per_sort_elem_core_sort _ ax_s1_s HE eq)               => case_sort ax_s1_s HE eq;
  | s_elem, R, a, b, (per_sort_elem_core_pi s_in s_out r _ out_rel _ equiv_a_a' per HT HE) =>
      case_Pi s_in s_out r out_rel equiv_a_a' (per_sort_elem_core_strong_ind s_in _ _ _ equiv_a_a') per
        (fun _ _ equiv_n_n' => match HT _ _ equiv_n_n' with
                            | mk_rel_mod_eval b b' evb evb' Rel =>
                                mk_rel_mod_eval b b' evb evb' (conj _ (per_sort_elem_core_strong_ind s_out _ _ _ Rel))
                            end)
        HE;
  | s, R, a, b, (per_sort_elem_core_neut _ equiv_b_b' HE)                 => case_ne equiv_b_b' HE.
  
  (* #[derive(equations=no, eliminator=no)] *)
  (* Equations per_sort_elem_core_strong_ind (s' : St P) R a b (H : {{ DF a ≈ b ∈ per_sort_elem_core s' ↘ R }}) : {{ DF a ≈ b ∈ motive s ↘ R }} := *)
  (* | s, R, a, b, (per_sort_elem_core_sort _ ax_s1_s HE eq)               => case_sort ax_s1_s HE eq *)
  (* | s_elem, R, a, b, (per_sort_elem_core_pi s_in s_out r _ out_rel _ equiv_a_a' per HT HE) => *)
  (*     case_Pi s_in s_out r out_rel equiv_a_a' (per_sort_elem_core_strong_ind s_in _ _ _ equiv_a_a') per *)
  (*       (fun _ _ equiv_n_n' => match HT _ _ equiv_n_n' with *)
  (*                           | mk_rel_mod_eval b b' evb evb' Rel => *)
  (*                               mk_rel_mod_eval b b' evb evb' (conj _ (per_sort_elem_core_strong_ind s_out _ _ _ Rel)) *)
  (*                           end) *)
  (*       HE; *)
  (* | s, R, a, b, (per_sort_elem_core_neut _ equiv_b_b' HE)                 => case_ne equiv_b_b' HE. *)
End Per_sort_elem_core_def.

#[export]
Hint Constructors per_sort_elem_core : mcpts.

Section Per_sort_elem_def.
  Variable
    (P : PtsSig)
      (pred_P : PredicativeSig P).

  Instance Per_sort_elem_def_wf : WellFounded (pred_rel P pred_P) := (wf_rel P pred_P).

Equations? per_sort_elem (s : St P) : relation (domain P) -> domain P -> domain P -> Prop by wf s :=
| s => per_sort_elem_core P s (fun s' ax_s'_s a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem s' ↘ R' }}) s.
Proof.
  eapply (ord_ax P pred_P).
  auto.
Qed.
End Per_sort_elem_def.

Definition per_sort {P : PtsSig} (pred_P : PredicativeSig P) (s : St P) : relation (domain P) :=
  fun a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem P pred_P s ↘ R' }}.

#[global]
Arguments per_sort _ _ _ _ _ /.
#[export]
Hint Transparent per_sort : mcpts.
#[export]
Hint Unfold per_sort : mcpts.

Lemma per_sort_elem_core_sort' {P : PtsSig} {pred_P : PredicativeSig P} : forall s1 s2 elem_rel,
    Ax P s1 s2 ->
    (elem_rel <~> per_sort pred_P s1) ->
    {{ DF Sort@s1 ≈ Sort@s1 ∈ per_sort_elem P pred_P s2 ↘ elem_rel }}.
Proof.
  intros.
  simp per_sort_elem.
  econstructor; mauto 3.
Qed.

#[export]
Hint Resolve per_sort_elem_core_sort' : mcpts.

(** ** Sort/Element PER Induction Principle *)

Section Per_sort_elem_ind_def.
  Variable
    (P : PtsSig)
      (pred_P : PredicativeSig P).

  Hypothesis
    (motive : (St P) -> relation (domain P) -> domain P -> domain P -> Prop)
      (case_sort :
        forall s {s1 s2 elem_rel},
          Ax P s1 s -> s1 = s2 ->
          (elem_rel <~> per_sort pred_P s1) ->
          (forall A B R, {{ DF A ≈ B ∈ per_sort_elem P pred_P s1 ↘ R }} -> motive s1 R A B) ->
          motive s elem_rel d{{{ Sort@s1 }}} d{{{ Sort@s2 }}} )
      (case_Pi :
        forall s_in s_out s (r : Ru P s_in s_out s)
          {a ρ B a' ρ' B' in_rel}
          (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P))
          {elem_rel},
          {{ DF a ≈ a' ∈ per_sort_elem P pred_P s_in ↘ in_rel }} ->
          motive s_in in_rel a a' ->
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (fun R x y => {{ DF x ≈ y ∈ per_sort_elem P pred_P s_in ↘ R }} /\ motive s_in R x y) B d{{{ ρ ↦ n' }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          motive s elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a' ρ' B' }}})
      (case_ne :
        forall s {a b a' b' elem_rel},
          {{ Dom b ≈ b' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          motive s elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}}).

  #[local]
  Ltac def_simp := simp per_sort_elem in *; mauto 3.

  Instance Per_sort_elem_ind_def_wf : WellFounded (pred_rel P pred_P) := (wf_rel P pred_P).
  
  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations? per_sort_elem_ind' (s : St P) (R : relation (domain P)) (a b : domain P)
  (H : {{ DF a ≈ b ∈ per_sort_elem_core P s (fun s' ax_s'_s a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem P pred_P s' ↘ R' }}) s ↘ R }}) : {{ DF a ≈ b ∈ motive s ↘ R }} by wf s :=
  | s, R, a, b, H =>
      per_sort_elem_core_strong_ind P s _ motive
        (fun _ _ _ ax_s1_s eq HE => case_sort s ax_s1_s eq HE (fun A B R' H' => per_sort_elem_ind' _ R' A B _))
        (fun s_in s_out r _ _ _ _ _ _ _ out_rel _ _ IHA per _ => case_Pi s_in s_out s r out_rel _ IHA per _)
        (fun s' _ _ _ _ _ => case_ne s')
        s R a b H.
  Proof.
    - eapply ord_ax; mauto.
    - admit.
    - admit.
  Abort.
End Per_sort_elem_ind_def.


Section Per_univ_elem_ind_def.
  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_univ_elem_ind' (i : nat) (R : relation domain) (a b : domain)
    (H : {{ DF a ≈ b ∈ per_univ_elem_core i (fun j lt_j_i a a' => exists R', {{ DF a ≈ a' ∈ per_univ_elem j ↘ R' }}) ↘ R }}) : {{ DF a ≈ b ∈ motive i ↘ R }} by wf i :=
  | i, R, a, b, H =>
      per_univ_elem_core_strong_ind i _ (motive i)
        (fun _ _ _ j_lt_i eq HE => case_U i j_lt_i eq HE (fun A B R' H' => per_univ_elem_ind' _ R' A B _))
        (fun _ => case_N i)
        (fun _ _ _ _ _ _ _ out_rel _ _ IHA per _ => case_Pi i out_rel _ IHA per _)
        (fun _ _ _ _ _ _ _ _ _ IHA per _ _ _ => case_Eq i _ IHA per _ _ _)
        (fun _ _ _ _ _ => case_ne i)
        R a b H.

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_univ_elem_ind i a b R (H : per_univ_elem i a b R) : motive i a b R :=
  | i, a, b, R, H := per_univ_elem_ind' i a b R _.
End Per_univ_elem_ind_def.

Reserved Notation "'Sub' a <: b 'at' i" (in custom judg at level 90, a custom domain, b custom domain, i constr).

(** * Universe Subtyping *)

Inductive per_subtyp : nat -> domain -> domain -> Prop :=
| per_subtyp_univ :
  `( i <= j ->
     j < k ->
     {{ Sub 𝕌@i <: 𝕌@j at k }} )
| per_subtyp_nat :
  `( {{ Sub ℕ <: ℕ at i }} )
| per_subtyp_pi :
  `( forall (in_rel : relation domain) elem_rel elem_rel',
        {{ DF a ≈ a' ∈ per_univ_elem i ↘ in_rel }} ->
        (forall c c' b b',
            {{ Dom c ≈ c' ∈ in_rel }} ->
            {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
            {{ ⟦ B' ⟧ ρ' ↦ c' ↘ b' }} ->
            {{ Sub b <: b' at i }}) ->
        {{ DF Π a ρ B ≈ Π a ρ B ∈ per_univ_elem i ↘ elem_rel }} ->
        {{ DF Π a' ρ' B' ≈ Π a' ρ' B' ∈ per_univ_elem i ↘ elem_rel' }} ->
        {{ Sub Π a ρ B <: Π a' ρ' B' at i }} )
| per_subtyp_eq :
  `( forall elem_rel,
        {{ DF Eq a m1 m2 ≈ Eq a' m1' m2' ∈ per_univ_elem i ↘ elem_rel }} ->
        {{ Sub Eq a m1 m2 <: Eq a' m1' m2' at i }} )
| per_subtyp_neut :
  `( {{ Dom b ≈ b' ∈ per_bot }} ->
     {{ Sub ⇑ a b <: ⇑ a' b' at i }} )
where "'Sub' a <: b 'at' i" := (per_subtyp i a b) (in custom judg) : type_scope.

#[export]
 Hint Constructors per_subtyp : mcpts.

Definition rel_typ i A ρ A' ρ' R' := rel_mod_eval (per_univ_elem i) A ρ A' ρ' R'.
Arguments rel_typ _ _ _ _ _ _ /.
#[export]
Hint Transparent rel_typ : mcpts.
#[export]
Hint Unfold rel_typ : mcpts.

(** * Context/Environment PER *)

Variant cons_per_ctx_env tail_rel (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation domain) : relation env :=
| mk_cons_per_ctx_env :
  `{ forall (equiv_ρ_drop_ρ'_drop : {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }}),
        {{ Dom ^(ρ 0) ≈ ^(ρ' 0) ∈ head_rel equiv_ρ_drop_ρ'_drop }} ->
        {{ Dom ρ ≈ ρ' ∈ cons_per_ctx_env tail_rel (@head_rel) }} }.
#[export]
Hint Constructors cons_per_ctx_env : mcpts.

Inductive per_ctx_env : relation env -> ctx -> ctx -> Prop :=
| per_ctx_env_nil :
  `{ forall env_rel,
        (env_rel <~> fun ρ ρ' => True) ->
        {{ EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ env_rel }} }
| per_ctx_env_cons :
  `{ forall tail_rel
        (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation domain)
        env_rel
        (equiv_Γ_Γ' : {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }}),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
            rel_typ i A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
        (env_rel <~> cons_per_ctx_env tail_rel (@head_rel)) ->
        {{ EF Γ, A ≈ Γ', A' ∈ per_ctx_env ↘ env_rel }} }
.
#[export]
Hint Constructors per_ctx_env : mcpts.

Definition per_ctx : relation ctx := fun Γ Γ' => exists R', per_ctx_env R' Γ Γ'.
Definition valid_ctx : ctx -> Prop := fun Γ => per_ctx Γ Γ.
#[export]
Hint Transparent valid_ctx : mcpts.
#[export]
Hint Unfold valid_ctx : mcpts.

Reserved Notation "'SubE' Γ <: Δ" (in custom judg at level 90, Γ custom exp, Δ custom exp).

(** * Context Subtyping *)

Inductive per_ctx_subtyp : ctx -> ctx -> Prop :=
| per_ctx_subtyp_nil :
  {{ SubE ⋅ <: ⋅ }}
| per_ctx_subtyp_cons :
  `{ forall tail_rel env_rel env_rel',
        {{ SubE Γ <: Γ' }} ->
        {{ EF Γ ≈ Γ ∈ per_ctx_env ↘ tail_rel }} ->
        (forall ρ ρ' a a'
           (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
            {{ ⟦ A ⟧ ρ ↘ a }} ->
            {{ ⟦ A' ⟧ ρ' ↘ a' }} ->
            {{ Sub a <: a' at i }}) ->
        {{ EF Γ , A ≈ Γ , A ∈ per_ctx_env ↘ env_rel }} ->
        {{ EF Γ' , A' ≈ Γ' , A' ∈ per_ctx_env ↘ env_rel' }} ->
        {{ SubE Γ, A <: Γ', A' }} }
where "'SubE' Γ <: Δ" := (per_ctx_subtyp Γ Δ) (in custom judg) : type_scope.

#[export]
Hint Constructors per_ctx_subtyp : mcpts.
