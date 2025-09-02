From McPTS Require Import LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import PER.
Import Domain_Notations.

Ltac eexists_rel_exp :=
  eexists;
  split; [eassumption |];
  eexists.

Ltac eexists_rel_exp_with s :=
  eexists;
  split; [eassumption |];
  exists s.

Ltac eexists_rel_sub :=
  eexists;
  split; [eassumption |];
  eexists;
  split; [eassumption |].

Ltac eexists_subtyp :=
  eexists;
  split; [eassumption |];
  eexists.

Ltac eexists_subtyp_with s :=
  eexists;
  split; [eassumption |];
  exists s.

Ltac invert_rel_typ_body :=
  simplify_evals;
  match_by_head per_sort_elem ltac:(fun H => directed invert_per_sort_elem H); subst;
  clear_dups;
  clear_refl_eqs;
  handle_per_sort_elem_irrel;
  clear_dups;
  try rewrite <- per_sort_elem_equation_1 in *.
