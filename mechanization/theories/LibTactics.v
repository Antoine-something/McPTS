From Coq Require Export Equivalence Lia Morphisms Program.Equality Program.Tactics Relation_Definitions RelationClasses.
From Equations Require Export Equations.

Open Scope predicate_scope.

Create HintDb mctt discriminated.

(** Transparency setting for generalized rewriting *)
#[export]
Typeclasses Transparent arrows.
