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
      (s_elem : St P)
      (per_sort_elem_rec : forall {s'}, pred_rel pred_P s' s_elem -> relation (domain P) -> relation (domain P)).

  Definition per_sort_rec {s'} (ord : pred_rel pred_P s' s_elem) : relation (domain P) :=
    fun a a' => exists R, per_sort_elem_rec ord R a a'.

  (** Defines 'a = b ∈ Sort_s ↘ R' in the paper *)
  Inductive per_sort_elem_core : relation (domain P) -> domain P -> domain P -> Prop :=
  | per_sort_elem_core_sort :
    `{ forall (ax : Ax P s1 s_elem)
          (elem_rel : relation (domain P)),
          s1 = s2 ->
          (elem_rel <~> per_sort_rec (ord_ax pred_P ax)) ->
          {{ DF Sort@s1 ≈ Sort@s2 ∈ per_sort_elem_core ↘ elem_rel }} }
  | per_sort_elem_core_pi :
    `{ forall (r : Ru P s_in s_out s_elem)
          (in_rel : relation (domain P))
          (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P))
          (elem_rel : relation (domain P))
          (equiv_a_a' : (s_in = s_elem -> {{ DF a ≈ a' ∈ per_sort_elem_core ↘ in_rel }}) /\ (forall (lt_in_elem : pred_rel pred_P s_in s_elem), {{ DF a ≈ a' ∈ per_sort_elem_rec lt_in_elem ↘ in_rel }})),
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (fun R b b' => (s_out = s_elem -> {{ DF b ≈ b' ∈ per_sort_elem_core ↘ R }}) /\ (forall (lt_out_elem : pred_rel pred_P s_out s_elem), {{ DF b ≈ b' ∈ per_sort_elem_rec lt_out_elem ↘ R }})) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem_core ↘ elem_rel }} }
  | per_sort_elem_core_neut :
    `{ forall (elem_rel : relation (domain P)),
          {{ Dom e ≈ e' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          {{ DF ⇑ a e ≈ ⇑ a' e' ∈ per_sort_elem_core ↘ elem_rel }} }     
  .
    
  Hypothesis
    (motive : relation (domain P) -> domain P -> domain P -> Prop)
      (case_sort :
        forall {s1 s2 : St P}
           (ax : Ax P s1 s_elem)
           {elem_rel : relation (domain P)},
          s1 = s2 ->
          (elem_rel <~> per_sort_rec (ord_ax pred_P ax)) ->
          motive elem_rel d{{{ Sort@s1 }}} d{{{ Sort@s2 }}})
      (case_Pi :
        forall {s_in s_out : St P} (r : Ru P s_in s_out s_elem)
          {a ρ B a' ρ' B' in_rel}
          (out_rel : forall {n n'} (equiv_n_n' : (in_rel n n')), relation (domain P))
          {elem_rel : relation (domain P)},
          (s_in = s_elem -> {{ DF a ≈ a' ∈ per_sort_elem_core ↘ in_rel }} /\ motive in_rel a a') /\ (forall (lt_in_elem : pred_rel pred_P s_in s_elem), {{ DF a ≈ a' ∈ per_sort_elem_rec lt_in_elem ↘ in_rel }}) ->
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : (in_rel n n')),
              rel_mod_eval (fun R b b' => (s_out = s_elem -> {{ DF b ≈ b' ∈ per_sort_elem_core ↘ R }} /\ motive R b b') /\ (forall (lt_out_elem : pred_rel pred_P s_out s_elem), {{ DF b ≈ b' ∈ per_sort_elem_rec lt_out_elem ↘ R }})) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : (in_rel n n')), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          motive elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a' ρ' B' }}})
      (case_ne :
        forall {a b a' b'}
          {elem_rel : relation (domain P)},
          (per_bot b b') ->
          (elem_rel <~> per_ne) ->
          motive elem_rel (d_neut a b) (d_neut a' b'))
  .

  #[derive(equations=no, eliminator=no)]
  Equations per_sort_elem_core_strong_ind R a b (H : {{ DF a ≈ b ∈ per_sort_elem_core ↘ R }})
    : {{ DF a ≈ b ∈ motive ↘ R }} :=
  | R, a, b, (per_sort_elem_core_sort ax _ HE eq)
    => case_sort ax HE eq ;
  | R, a, b, (per_sort_elem_core_pi r _ out_rel _ equiv_a_a' per HT HE) =>
      case_Pi r out_rel
        (match equiv_a_a' with
         | conj HA _ => conj (fun eq => conj _ (per_sort_elem_core_strong_ind _ _ _ (HA eq))) _
         end)
        per
        (fun _ _ equiv_n_n' => match HT _ _ equiv_n_n' with
                              | mk_rel_mod_eval b b' evb evb' Rel =>
                                  mk_rel_mod_eval b b' evb evb'
                                    (match Rel with
                                     | conj HB _ => conj (fun eq => conj _ (per_sort_elem_core_strong_ind _ _ _ (HB eq))) _
                                     end)
                              end)
        HE;
  | R, a, b, (per_sort_elem_core_neut _ equiv_e_e' HE)
    => case_ne equiv_e_e' HE.
    
End Per_sort_elem_core_def.

#[export]
Hint Constructors per_sort_elem_core : mcpts.

Section Per_sort_elem_def.
  Variable
    (P : PtsSig)
      (pred_P : PredicativeSig P).
  
  Instance Per_sort_elem_def_wf : WellFounded (pred_rel pred_P) := (wf_rel pred_P).

  Equations per_sort_elem (s : St P) : relation (domain P) -> domain P -> domain P -> Prop by wf s :=
  | s => per_sort_elem_core P pred_P s (fun s' lt_s'_s R' a a' => {{ DF a ≈ a' ∈ per_sort_elem s' ↘ R' }}).
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
  unshelve econstructor; mauto.
Qed.  

#[export]
Hint Resolve per_sort_elem_core_sort' : mcpts.

(** ** Sort/Element PER Induction Principle *)

Section Per_sort_elem_ind_def.
  Variable
    (P : PtsSig)
      (pred_P : PredicativeSig P).

  Hypothesis
    (motive : St P -> relation (domain P) -> domain P -> domain P -> Prop)
      (case_sort :
        forall s_elem {s1 s2 elem_rel}
          (ax : Ax P s1 s_elem),
          s1 = s2 ->
          (elem_rel <~> per_sort pred_P s1) ->
          (forall a b R, {{ DF a ≈ b ∈ per_sort_elem P pred_P s1 ↘ R }} -> motive s1 R a b) ->
          motive s_elem elem_rel d{{{ Sort@s1 }}} d{{{ Sort@s2 }}})
      (case_Pi :
        forall s_elem {s_in s_out} (r : Ru P s_in s_out s_elem)
          {a ρ B a' ρ' B' in_rel}
          (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P))
          {elem_rel},
          {{ DF a ≈ a' ∈ per_sort_elem P pred_P s_in ↘ in_rel }} ->
          motive s_in in_rel a a' ->
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (fun R x y => {{ DF x ≈ y ∈ per_sort_elem P pred_P s_out ↘ R }} /\ motive s_out R x y) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          motive s_elem elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a' ρ' B' }}})
      (case_ne :
        forall s_elem {a b a' b' elem_rel},
          {{ Dom b ≈ b' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          motive s_elem elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}}).

  #[local]
  Ltac def_simp := simp per_sort_elem in *; mauto using ord_ax, ord_ru.

  Instance Per_sort_elem_ind_def_wf : WellFounded (pred_rel pred_P) := (wf_rel pred_P).
  
  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_sort_elem_ind' (s : St P) (R : relation (domain P)) (a b : domain P)
  (H : {{ DF a ≈ b ∈ per_sort_elem_core P pred_P s (fun s' lt_s'_s R' a a' => {{ DF a ≈ a' ∈ per_sort_elem P pred_P s' ↘ R' }}) ↘ R }}) : {{ DF a ≈ b ∈ motive s ↘ R }} by wf s :=
  | s, R, a, b, H =>
      per_sort_elem_core_strong_ind P pred_P s _ (motive s)
        (fun _ _ ax _ eq HE => case_sort s ax eq HE (fun a b R' H' => per_sort_elem_ind' _ R' a b _))
        (fun _ _ r _ _ _ _ _ _ _ out_rel _ HA per HB =>
           case_Pi s r out_rel
             (match HA with
              | conj Heq Hlt =>
                  match proj1 (ord_ru pred_P r) with
                  | or_introl _ => _
                  | or_intror eq =>
                      match Heq eq with
                      | conj _ _ => _
                      end
                  end
              end)
             (match HA with
              | conj Heq Hlt =>
                  match proj1 (ord_ru pred_P r) with
                  | or_introl _ => per_sort_elem_ind' _ _ _ _ _
                  | or_intror eq =>
                      match Heq eq with
                      | conj _ _ => _
                      end
                  end
              end)
             per
             (fun _ _ equiv =>
                match HB _ _ equiv with
                | mk_rel_mod_eval b b' evb evb' Rel =>
                    match Rel with
                    | conj Heq _ =>
                        match proj2 (ord_ru pred_P r) with
                        | or_introl lt_out_s => mk_rel_mod_eval b b' evb evb' (conj _ _)
                        | or_intror eq =>
                            match Heq eq with
                            | conj _ _ => mk_rel_mod_eval b b' evb evb' (conj _ _)
                            end
                        end
                    end
                end))
        (fun _ _ _ _ _ Hb HE => case_ne s Hb HE)
        R a b H.
  Next Obligation. Qed.
  Next Obligation. def_simp. Qed.
  Next Obligation. def_simp. Qed.
  Next Obligation. Qed.
  Next Obligation. Qed.
  Next Obligation. def_simp. Qed.
  Next Obligation. def_simp. Qed.
  Next Obligation. Qed.
  
  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations per_sort_elem_ind s a b R (H : per_sort_elem P pred_P s a b R) : motive s a b R :=
  | s, a, b, R, H := per_sort_elem_ind' s a b R _.
End Per_sort_elem_ind_def.


Definition rel_typ {P : PtsSig} (pred_P : PredicativeSig P) s A ρ A' ρ' R' := rel_mod_eval (per_sort_elem P pred_P s) A ρ A' ρ' R'.
Arguments rel_typ _ _ _ _ _ _ _ _ /.
#[export]
Hint Transparent rel_typ : mcpts.
#[export]
Hint Unfold rel_typ : mcpts.


(** * Context/Environment PER *)

Variant cons_per_ctx_env {P : PtsSig} tail_rel (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation (domain P)) : relation (env P) :=
| mk_cons_per_ctx_env :
  `{ forall (equiv_ρ_drop_ρ'_drop : {{ Dom ρ ↯ ≈ ρ' ↯ ∈ tail_rel }}),
        {{ ρ[0] ↘ n }} -> {{ ρ'[0] ↘ n' }} ->
        {{ Dom n ≈ n' ∈ head_rel equiv_ρ_drop_ρ'_drop }} ->
        {{ Dom ρ ≈ ρ' ∈ cons_per_ctx_env tail_rel (@head_rel) }} }.
#[export]
Hint Constructors cons_per_ctx_env : mcpts.

Inductive per_ctx_env {P : PtsSig} {pred_P : PredicativeSig P} : relation (env P) -> ctx P -> ctx P -> Prop :=
| per_ctx_env_nil :
  `{ forall env_rel,
        (env_rel <~> fun ρ ρ' => ρ = nil /\ ρ' = nil) ->
        {{ EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ env_rel }} }
| per_ctx_env_cons :
  `{ forall tail_rel
       (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation (domain P))
       env_rel
       (equiv_Γ_Γ' : {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }}),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
            rel_typ pred_P s A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
        (env_rel <~> cons_per_ctx_env tail_rel (@head_rel)) ->
        {{ EF Γ, A::Sort@s ≈ Γ', A'::Sort@s ∈ per_ctx_env ↘ env_rel }} }
.
#[export]
Hint Constructors per_ctx_env : mcpts.

Definition per_ctx {P : PtsSig} {pred_P : PredicativeSig P} : relation (ctx P) := fun Γ Γ' => exists R', @per_ctx_env P pred_P R' Γ Γ'.
Definition valid_ctx {P : PtsSig} {pred_P : PredicativeSig P} : ctx P -> Prop := fun Γ => @per_ctx P pred_P Γ Γ.
#[export]
Hint Transparent valid_ctx : mcpts.
#[export]
Hint Unfold valid_ctx : mcpts.

