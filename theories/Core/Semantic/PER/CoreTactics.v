From Coq Require Import Lia PeanoNat Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import LibTactics PtsSignature Base.
From McPTS.Core.Semantic Require Import PER.Definitions.
Import Domain_Notations.

Ltac lazy_destruct H H' :=
  match type of H with
  | forall _ _ _, exists _, _ => pose proof (H _ _ H'); deex_once
  | _ => destruct (H _ _ H') as []
  end.

Ltac destruct_rel_by_assumption in_rel H :=
  repeat
    match goal with
    | H' : {{ Dom ^?c ≈ ^?c' ∈ ?in_rel0 }} |- _ =>
        unify in_rel0 in_rel;
        lazy_destruct H H';
        destruct_all;
        mark_with H' 1
    end;
  unmark_all_with 1.

Ltac destruct_rel_mod_eval :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_eval _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_eval _ _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
Ltac destruct_rel_mod_app :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_mod_app _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_mod_app _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.
(* Ltac destruct_rel_typ := *)
(*   repeat *)
(*     match goal with *)
(*     | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_typ _ _ _ _ _ _ _) |- _ => *)
(*         destruct_rel_by_assumption in_rel H; mark H *)
(*     | H : rel_typ _ _ _ _ _ _ _ |- _ => *)
(*         dependent destruction H *)
(*     end; *)
(*   unmark_all. *)
Ltac destruct_rel_typ_unsorted :=
  repeat
    match goal with
    | H : (forall c c' (equiv_c_c' : {{ Dom c ≈ c' ∈ ?in_rel }}), rel_typ_unsorted _ _ _ _ _ _) |- _ =>
        destruct_rel_by_assumption in_rel H; mark H
    | H : rel_typ_unsorted _ _ _ _ _ _ |- _ =>
        dependent destruction H
    end;
  unmark_all.


(** Sort/Element PER Helper Tactics *)
Ltac basic_invert_per_sort_elem H :=
  progress simp per_sort_elem in H;
  dependent destruction H;
  try rewrite <- per_sort_elem_equation_1 in *.

Ltac basic_per_sort_elem_econstructor :=
  progress simp per_sort_elem;
  econstructor;
  try rewrite <- per_sort_elem_equation_1 in *.



(** Tactics to apply relation equivalences *)
(* The tactics should do a deep rewrite (i.e. all occurences in all premises) and keep only one relation *)
(* Right now, it only works in some cases, but I don't know why *)
Ltac rewrite_relation_equivalence_left :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac rewrite_relation_equivalence_right :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        try setoid_rewrite <- H;
        (on_all_hyp: fun H' => assert_fails (unify H H'); unmark H; setoid_rewrite <- H in H');
        let T := type of H in
        fold (id T) in H
    end; unfold id in *.

Ltac clear_relation_equivalence :=
  repeat match goal with
    | H : ?R1 <~> ?R2 |- _ =>
        (unify R1 R2; clear H) + (is_var R1; clear R1 H) + (is_var R2; clear R2 H)
    end.

Ltac apply_relation_equivalence :=
  clear_relation_equivalence;
  rewrite_relation_equivalence_right;
  clear_relation_equivalence;
  rewrite_relation_equivalence_left;
  clear_relation_equivalence.


(** This tactic applies the predicativity condition on function spaces to get rid of the two possible cases *)
#[global]
Ltac clear_pi_sort_eq_and_pred_rel1 :=
  match goal with
  | [r : Ru_pi ?P ?s1 _ ?s3,
     sub : st_subtyp ?s3 ?s,
     H1 : ?s1 = ?s -> ?Ps,
     H2 : pred_rel ?pred_P ?s1 ?s -> ?Ps1 |- _] => 
      assert Ps1 by (pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2);
      clear H1 H2
  | [r : Ru_pi ?P ?s1 _ ?s3,
     sub : st_subtyp ?s3 ?s,
     H : (?s1 = ?s -> ?Ps) /\ (pred_rel ?pred_P ?s1 ?s -> ?Ps1) |- _] => 
      destruct H;
      assert Ps1 by (pose proof ord_ru_pi_sub pred_P r sub as [[] ?]; subst; mauto 2);
      clear H
  | [r : Ru_pi ?P _ ?s2 ?s3,
     sub : st_subtyp ?s3 ?s,
     H1 : ?s2 = ?s -> ?Ps,
     H2 : pred_rel ?pred_P ?s2 ?s -> ?Ps2 |- _] => 
      assert Ps2 by (pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2);
      clear H1 H2
  | [r : Ru_pi ?P _ ?s2 ?s3,
     sub : st_subtyp ?s3 ?s,
     H : (?s2 = ?s -> ?Ps) /\ (pred_rel ?pred_P ?s2 ?s -> ?Ps2) |- _] => 
      destruct H;
      assert Ps2 by (pose proof ord_ru_pi_sub pred_P r sub as [? []]; subst; mauto 2);
      clear H
  end.

#[global]
Ltac clear_pi_sort_eq_and_pred_rel := repeat clear_pi_sort_eq_and_pred_rel1.
