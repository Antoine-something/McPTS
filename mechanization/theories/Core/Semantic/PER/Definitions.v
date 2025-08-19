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
      (pred_P : PredicativeSig P).

  (** Defines 'a = b ∈ Sort_s ↘ R' in the paper *)
  Inductive per_sort_elem_core (s_elem : St P) (per_sort_rec : forall s', pred_rel P pred_P s' s_elem -> relation (domain P)) : relation (domain P) -> domain P -> domain P -> Prop :=
  | per_sort_elem_core_sort :
    `{ forall (elem_rel : relation (domain P))
         (ax_s1_s_elem : Ax P s1 s_elem)
         (per_sort_rec_s1 : forall s', pred_rel P pred_P s' s1 -> relation (domain P))
         (psr_monotone : forall s' lt_s'_s1 lt_s'_s, per_sort_rec_s1 s' lt_s'_s1 <~> per_sort_rec s' lt_s'_s),
          s1 = s2 ->
          (elem_rel <~> per_sort_rec s1 (proj1 (ord_ax P pred_P s1 s_elem ax_s1_s_elem))) ->
          {{ DF Sort@s1 ≈ Sort@s2 ∈ per_sort_elem_core s_elem per_sort_rec ↘ elem_rel }} }
  | per_sort_elem_core_pi :
    `{ forall (s_in s_out : St P) (r : Ru P s_in s_out s_elem)
         (per_sort_rec_in : forall s', pred_rel P pred_P s' s_in -> relation (domain P))
         (psr_in_monotone : forall s' lt_s'_s_in lt_s'_s, per_sort_rec_in s' lt_s'_s_in <~> per_sort_rec s' lt_s'_s)
         (per_sort_rec_out : forall s', pred_rel P pred_P s' s_out -> relation (domain P))
         (psr_out_monotone : forall s' lt_s'_s_out lt_s'_s, per_sort_rec_out s' lt_s'_s_out <~> per_sort_rec s' lt_s'_s)
         (in_rel : relation (domain P))
         (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P))
         (elem_rel : relation (domain P))
         (equiv_a_a' : {{ DF a ≈ a' ∈ per_sort_elem_core s_in per_sort_rec_in ↘ in_rel }}),
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}),
              rel_mod_eval (per_sort_elem_core s_out per_sort_rec_out) B d{{{ ρ ↦ n }}} B' d{{{ρ' ↦ n' }}} (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          {{ DF Π r a ρ B ≈ Π r a' ρ' B' ∈ per_sort_elem_core s_elem per_sort_rec ↘ elem_rel }} }
  | per_sort_elem_core_neut :
    `{ forall (elem_rel : relation (domain P)),
          {{ Dom e ≈ e' ∈ per_bot }} ->
          (elem_rel <~> per_ne) ->
          {{ DF ⇑ a e ≈ ⇑ a' e' ∈ per_sort_elem_core s_elem per_sort_rec ↘ elem_rel }} }     
  .

  Hypothesis
    (motive : forall s (per_sort_rec : forall s', pred_rel P pred_P s' s -> relation (domain P)), relation (domain P) -> domain P -> domain P -> Prop)
      (case_sort :
        forall {s_elem s1 s2 : St P}
          (per_sort_rec : forall s', pred_rel P pred_P s' s_elem -> relation (domain P))
          (per_sort_rec_s1 : forall s', pred_rel P pred_P s' s1 -> relation (domain P))
          (psr_monotone : forall s' lt_s'_s1 lt_s'_s, per_sort_rec_s1 s' lt_s'_s1 <~> per_sort_rec s' lt_s'_s)
          {elem_rel : relation (domain P)}
          (ax_s1_s_elem : Ax P s1 s_elem),
          s1 = s2 ->
          (elem_rel <~> per_sort_rec s1 (proj1 (ord_ax P pred_P s1 s_elem ax_s1_s_elem))) ->
          (forall A B R, (per_sort_elem_core s1 per_sort_rec_s1 R A B) -> motive s1 per_sort_rec_s1 R A B) ->
          motive s_elem per_sort_rec elem_rel (d_sort s1) (d_sort s2))
      (case_Pi :
        forall (s_in s_out s_elem : St P) (r : Ru P s_in s_out s_elem)
          (per_sort_rec_elem : forall s', pred_rel P pred_P s' s_elem -> relation (domain P))
          (per_sort_rec_in : forall s', pred_rel P pred_P s' s_in -> relation (domain P))
          (psr_in_monotone : forall s' lt_s'_s_in lt_s'_s, per_sort_rec_in s' lt_s'_s_in <~> per_sort_rec_elem s' lt_s'_s)
          (per_sort_rec_out : forall s', pred_rel P pred_P s' s_out -> relation (domain P))
          (psr_out_monotone : forall s' lt_s'_s_out lt_s'_s, per_sort_rec_out s' lt_s'_s_out <~> per_sort_rec_elem s' lt_s'_s)
          {a ρ B a' ρ' B'}
          {in_rel : relation (domain P)}
          (out_rel : forall {n n'} (equiv_n_n' : (in_rel n n')), relation (domain P))
          {elem_rel : relation (domain P)},
          (per_sort_elem_core s_in per_sort_rec_in in_rel a a') ->
          motive s_in per_sort_rec_in in_rel a a' ->
          PER in_rel ->
          (forall {n n'} (equiv_n_n' : (in_rel n n')),
              rel_mod_eval (fun R x y => (per_sort_elem_core s_out per_sort_rec_out R x y) /\ motive s_out per_sort_rec_out R x y) B (extend_env ρ n) B' (extend_env ρ' n') (out_rel equiv_n_n')) ->
          (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : (in_rel n n')), rel_mod_app f n f' n' (out_rel equiv_n_n')) ->
          motive s_elem per_sort_rec_elem elem_rel (d_pi r a ρ B) (d_pi r a' ρ' B'))
      (case_ne :
        forall (s_elem : St P)
          (per_sort_rec : forall s', pred_rel P pred_P s' s_elem -> relation (domain P))
          {a b a' b'}
          {elem_rel : relation (domain P)},
          (per_bot b b') ->
          (elem_rel <~> per_ne) ->
          motive s_elem per_sort_rec elem_rel (d_neut a b) (d_neut a' b'))
  .

  Instance Per_sort_elem_core_def_wf : WellFounded (pred_rel P pred_P) := (wf_rel P pred_P).
  
  #[derive(equations=no, eliminator=no)]
  Equations? per_sort_elem_core_strong_ind (s : St P)
  (per_sort_rec_s : forall s', pred_rel P pred_P s' s -> relation (domain P))
  R a b
  (H : {{ DF a ≈ b ∈ per_sort_elem_core s per_sort_rec_s ↘ R }})
    : {{ DF a ≈ b ∈ motive s per_sort_rec_s ↘ R }} by wf s :=
  | s, per_sort_rec_s, R, a, b, (per_sort_elem_core_sort _ _ _ ax_s1_s per_sort_rec_s1 psr1_monotone HE eq)
    => case_sort per_sort_rec_s per_sort_rec_s1 psr1_monotone ax_s1_s HE eq (fun A B R H => per_sort_elem_core_strong_ind s1 per_sort_rec_s1 R A B H) ;
  | s, per_sort_rec_s, R, a, b, (per_sort_elem_core_pi _ _ s_in s_out r per_sort_rec_in psr_in_monotone per_sort_rec_out psr_out_monotone _ out_rel _ equiv_a_a' per HT HE) =>
      case_Pi s_in s_out s r per_sort_rec_s per_sort_rec_in psr_in_monotone per_sort_rec_out psr_out_monotone out_rel equiv_a_a' (per_sort_elem_core_strong_ind s_in _ _ _ _ equiv_a_a') per
        (fun _ _ equiv_n_n' => match HT _ _ equiv_n_n' with
                            | mk_rel_mod_eval b b' evb evb' Rel =>
                                mk_rel_mod_eval b b' evb evb' (conj _ (per_sort_elem_core_strong_ind s_out _ _ _ _ Rel))
                            end)
        HE;
  | s, per_sort_rec_s, R, a, b, (per_sort_elem_core_neut _ _ _ equiv_e_e' HE)
    => case_ne s per_sort_rec_s equiv_e_e' HE.
  Proof.
    - eapply ord_ax; mauto.
    - eapply (ord_ru P pred_P s_in s_out s r); mauto.
    - eapply (ord_ru P pred_P s_in s_out s r); mauto.
  Qed.

End Per_sort_elem_core_def.


#[export]
Hint Constructors per_sort_elem_core : mcpts.


Section Per_sort_elem_def.
  Variable
    (P : PtsSig)
      (pred_P : PredicativeSig P).
  
  Instance Per_sort_elem_def_wf : WellFounded (pred_rel P pred_P) := (wf_rel P pred_P).

  Equations per_sort_elem (s : St P) : relation (domain P) -> domain P -> domain P -> Prop by wf s :=
  | s => per_sort_elem_core P pred_P s (fun s' lt_s'_s a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem s' ↘ R' }}).
    
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
  econstructor; mauto.

Admitted.



#[export]
Hint Resolve per_sort_elem_core_sort' : mcpts.

(** ** Sort/Element PER Induction Principle *)

(* Section Per_sort_elem_ind_def. *)
(*   Variable *)
(*     (P : PtsSig) *)
(*       (pred_P : PredicativeSig P). *)

(*   Hypothesis *)
(*     (motive : St P -> relation (domain P) -> domain P -> domain P -> Prop) *)
(*       (case_sort : *)
(*         forall s_elem {s1 s2 elem_rel} *)
(*           (ax_s1_s_elem : Ax P s1 s_elem), *)
(*           s1 = s2 -> *)
(*           (elem_rel <~> per_sort pred_P s_elem) -> *)
(*           (forall a b R, {{ DF a ≈ b ∈ per_sort_elem P pred_P s1 ↘ R }} -> motive s1 R a b) -> *)
(*           motive s_elem elem_rel d{{{ Sort@s1 }}} d{{{ Sort@s2 }}} ) *)
(*       (case_Pi : *)
(*         forall s_in s_out s_elem (r : Ru P s_in s_out s_elem) *)
(*           {a ρ B a' ρ' B' in_rel} *)
(*           (out_rel : forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), relation (domain P)) *)
(*           {elem_rel}, *)
(*           {{ DF a ≈ a' ∈ per_sort_elem P pred_P s_in ↘ in_rel }} -> *)
(*           motive s_in in_rel a a' -> *)
(*           PER in_rel -> *)
(*           (forall {n n'} (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), *)
(*               rel_mod_eval (fun R x y => {{ DF x ≈ y ∈ per_sort_elem P pred_P s_out ↘ R }} /\ motive s_out R x y) B d{{{ ρ ↦ n }}} B' d{{{ ρ' ↦ n' }}} (out_rel equiv_n_n')) -> *)
(*           (elem_rel <~> fun f f' => forall n n' (equiv_n_n' : {{ Dom n ≈ n' ∈ in_rel }}), rel_mod_app f n f' n' (out_rel equiv_n_n')) -> *)
(*           motive s_elem elem_rel d{{{ Π r a ρ B }}} d{{{ Π r a' ρ' B' }}}) *)
(*       (case_ne : *)
(*         forall s_elem {a b a' b' elem_rel}, *)
(*           {{ Dom b ≈ b' ∈ per_bot }} -> *)
(*           (elem_rel <~> per_ne) -> *)
(*           motive s_elem elem_rel d{{{ ⇑ a b }}} d{{{ ⇑ a' b' }}}). *)

(*   #[local] *)
(*   Ltac def_simp := simp per_sort_elem in *; mauto. *)

(*   Instance Per_sort_elem_ind_def_wf : WellFounded (pred_rel P pred_P) := (wf_rel P pred_P). *)
  
(*   #[derive(equations=no, eliminator=no), tactic="def_simp"] *)
(*   Equations? per_sort_elem_ind' (s : St P) (R : relation (domain P)) (a b : domain P) *)
(*   (H : {{ DF a ≈ b ∈ per_sort_elem_core P pred_P s (fun s' lt_s'_s a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem P pred_P s' ↘ R' }}) ↘ R }}) : {{ DF a ≈ b ∈ motive s ↘ R }} by wf s := *)
(*   | s, R, a, b, H => *)
(*       per_sort_elem_core_strong_ind P pred_P (fun s prs => motive s) *)
(*         (fun s_elem s1 s2 _ _ _ ax_s1_s eq HE IH1 => case_sort s_elem ax_s1_s eq _ (fun a b R' H' => per_sort_elem_ind' s1 R' a b _)) *)
(*         (fun s_in s_out s_elem r per_sort_rec_in per_sort_rec_out per_sort_rec_out _ _ _ _ _ _ _ out_rel _ _ IHA per _ => case_Pi s_in s_out s_elem r out_rel _ IHA per _) *)
(*         (fun s_elem per_sort_rec _ _ _ _ _ Hb HE => case_ne s_elem Hb HE) *)
(*         s (fun s' lt_s'_s a a' => exists R', {{ DF a ≈ a' ∈ per_sort_elem P pred_P s' ↘ R' }}) R a b H. *)
(*   Proof. *)
(*     - subst. admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*   Abort. *)
  
(*   #[derive(equations=no, eliminator=no), tactic="def_simp"] *)
(*   Equations per_sort_elem_ind s a b R (H : per_sort_elem P pred_P s a b R) : motive s a b R := *)
(*   | s, a, b, R, H := per_sort_elem_core_strong_ind P pred_P (fun s per_sort_rec => motive s) *)
(*                        (fun s_elem s1 s2 _ elem_rel ax_s1_s_elem eq _ => case_sort s_elem ax_s1_s_elem eq _) *)
(*                        s a b R _. *)
(* End Per_sort_elem_ind_def. *)



Definition rel_typ {P : PtsSig} (pred_P : PredicativeSig P) s per_sort_rec A ρ A' ρ' R' := rel_mod_eval (per_sort_elem_core P pred_P s per_sort_rec) A ρ A' ρ' R'.
Arguments rel_typ _ _ _ _ _ _ _ _ _ /.
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
        (env_rel <~> fun ρ ρ' => True) ->
        {{ EF ⋅ ≈ ⋅ ∈ per_ctx_env ↘ env_rel }} }
| per_ctx_env_cons :
  `{ forall tail_rel
        (head_rel : forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}), relation (domain P))
        env_rel
        (equiv_Γ_Γ' : {{ EF Γ ≈ Γ' ∈ per_ctx_env ↘ tail_rel }}),
        PER tail_rel ->
        (forall {ρ ρ'} (equiv_ρ_ρ' : {{ Dom ρ ≈ ρ' ∈ tail_rel }}),
            rel_typ pred_P s per_sort_rec A ρ A' ρ' (head_rel equiv_ρ_ρ')) ->
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

