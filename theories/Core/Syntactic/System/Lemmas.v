From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Import Syntax.
From McPTS.Core.Syntactic.System Require Import Definitions.
From McPTS.Core.Syntactic.System.Lemmas Require Export Instances CorePresup SortLemmas NatLemmas SubstitutionLemmas TypeLemmas VariableLemmas.
Import Syntax_Notations.

  
(** *** Consistency Helper *)
Lemma no_closed_neutral {P : PtsSig} : forall {A : exp P} {W : ne P},
    ~ {{ ⋅ ⊢ W : A }}.
Proof.
  intros * H.
  dependent induction H; destruct W;
    try (simpl in *; congruence);
    autoinjections;
    intuition.
  inversion_by_head (@ctx_lookup P).
Qed.

#[export]
Hint Resolve no_closed_neutral : mcpts.
