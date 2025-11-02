From Coq Require Import List String.

From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.


(** * Concrete Syntax Tree *)
Module Cst.
  Inductive obj (P : PtsSig) : Set :=
  (** Sorts *)
  | st : P -> obj P
  (** Functions *)
  | pi : string -> obj P -> obj P -> obj P
  | fn : string -> obj P -> obj P -> obj P
  | app : obj P -> obj P -> obj P
  (** Variables *)
  | var : string -> obj P.

  Arguments st {_}.
  Arguments pi {_}.
  Arguments fn {_}.
  Arguments app {_}.
  Arguments var {_}.
End Cst.

(** * Abstract Syntax Tree *)
Inductive exp (P : PtsSig) : Set :=
(** Sorts *)
| a_st : P -> exp P
(** Functions *)
| a_pi : forall (s1 s2 s3 : P), Ru P s1 s2 s3 -> exp P -> exp P -> exp P
| a_fn : forall (s1 s2 s3 : P), Ru P s1 s2 s3 -> exp P -> exp P -> exp P
| a_app : exp P -> exp P -> exp P
(** Variable *)
| a_var : nat -> exp P
(** Substitution Application *)
| a_sub : exp P -> sub P -> exp P
with sub (P : PtsSig) : Set :=
| a_id : sub P
| a_weaken : sub P
| a_compose : sub P -> sub P -> sub P
| a_extend : sub P -> exp P -> sub P.

Arguments a_st {_}.
Arguments a_pi {_ _ _ _}.
Arguments a_fn {_ _ _ _}.
Arguments a_app {_}.
Arguments a_var {_}.
Arguments a_sub {_}.
Arguments a_id {_}.
Arguments a_weaken {_}.
Arguments a_compose {_}.
Arguments a_extend {_}.


Notation typ := (fun P => exp P).
Notation ctx := (fun P => list (typ P)).


(** ** Syntactic Normal/Neutral Form *)
Inductive nf (P : PtsSig) : Set :=
| nf_st : P -> nf P
| nf_pi : forall (s1 s2 s3 : P), Ru P s1 s2 s3 -> nf P -> nf P -> nf P
| nf_fn : forall (s1 s2 s3 : P), Ru P s1 s2 s3 -> nf P -> nf P -> nf P
| nf_neut : ne P -> nf P
with ne (P : PtsSig) : Set :=
| ne_app : ne P -> nf P -> ne P
| ne_var : nat -> ne P
.

Arguments nf_st {_}.
Arguments nf_pi {_ _ _ _}.
Arguments nf_fn {_ _ _ _}.
Arguments nf_neut {_}.

Arguments ne_app {_}.
Arguments ne_var {_}.

Fixpoint nf_to_exp {P : PtsSig} (M : nf P) : exp P :=
  match M with
  | nf_st s => a_st s
  | nf_pi r A B => a_pi r (nf_to_exp A) (nf_to_exp B)
  | nf_fn r A M => a_fn r (nf_to_exp A) (nf_to_exp M)
  | nf_neut M => ne_to_exp M
  end
with ne_to_exp {P : PtsSig} (M : ne P) : exp P :=
  match M with
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_var x => a_var x
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

(* I am not sure if this carries over to our setting *)
(* Fact nf_eq_dec : forall (M M' : nf), *)
(*     ({M = M'} + {M <> M'})%type *)
(* with ne_eq_dec : forall (M M' : ne), *)
(*     ({M = M'} + {M <> M'})%type. *)
(* Proof. *)
(*   all: intros; decide equality; *)
(*     apply PeanoNat.Nat.eq_dec. *)
(* Defined. *)

Definition q {P : PtsSig} (σ : sub P) := a_extend (a_compose σ a_weaken) (a_var 0).
Arguments q {_} σ/.


#[global] Declare Custom Entry exp.
#[global] Declare Custom Entry nf.

#[global] Bind Scope mcpts_scope with exp.
#[global] Bind Scope mcpts_scope with sub.
#[global] Bind Scope mcpts_scope with nf.
#[global] Bind Scope mcpts_scope with ne.
Open Scope mcpts_scope.

(** ** Syntactic Notations *)
Module Syntax_Notations.
  (** We need to define substitution notation first to assert [left associativity] of level 0. *)
  Notation "e [ s ]" := (a_sub e s) (in custom exp at level 0, e custom exp, s custom exp at level 60, left associativity, format "e [ s ]") : mcpts_scope.

  Notation "{{{ x }}}" := x (at level 0, x custom exp at level 99, format "'{{{'  x  '}}}'") : mcpts_scope.
  Notation "( x )" := x (in custom exp at level 0, x custom exp at level 60) : mcpts_scope.
  Notation "'^' x" := x (in custom exp at level 0, x constr at level 0) : mcpts_scope.
  Notation "x" := x (in custom exp at level 0, x ident) : mcpts_scope.

  Notation "'Sort' @ s" := (a_st s) (in custom exp at level 0, s constr at level 0, format "'Sort' @ s") : mcpts_scope.
  Notation "'Π' r A B" := (a_pi r A B) (in custom exp at level 1, r constr at level 0, A custom exp at level 0, B custom exp at level 60) : mcpts_scope.
  Notation "'λ' r A e" := (a_fn r A e) (in custom exp at level 1, r constr at level 0, A custom exp at level 0, e custom exp at level 60) : mcpts_scope.
  Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom exp at level 40, f custom exp, x custom exp at next level, y custom exp at next level) : mcpts_scope.
  Notation "'#' n" := (a_var n) (in custom exp at level 0, n constr at level 0, format "'#' n") : mcpts_scope.

  Notation "'Id'" := a_id (in custom exp at level 0) : mcpts_scope.
  Notation "'Wk'" := a_weaken (in custom exp at level 0) : mcpts_scope.
  Notation "σ ∘ τ" := (a_compose σ τ) (in custom exp at level 40, right associativity, format "σ ∘ τ") : mcpts_scope.
  Notation "σ ,, e" := (a_extend σ e) (in custom exp at level 50, left associativity, format "σ ,, e") : mcpts_scope.
  Notation "'q' σ" := (q σ) (in custom exp at level 30) : mcpts_scope.

  Notation "⋅" := nil (in custom exp at level 0) : mcpts_scope.
  Notation "Γ , A" := (cons A Γ) (in custom exp at level 50, left associativity, format "Γ , A") : mcpts_scope.

  Notation "n{{{ x }}}" := x (at level 0, x custom nf at level 99, format "'n{{{'  x  '}}}'") : mcpts_scope.
  Notation "( x )" := x (in custom nf at level 0, x custom nf at level 60) : mcpts_scope.
  Notation "'^' x" := x (in custom nf at level 0, x constr at level 0) : mcpts_scope.
  Notation "x" := x (in custom nf at level 0, x ident) : mcpts_scope.

  Notation "'Sort' @ s" := (nf_st s) (in custom nf at level 0, s constr at level 0, format "'Sort' @ s") : mcpts_scope.
  Notation "'Π' r A B" := (nf_pi r A B) (in custom nf at level 2, r constr at level 0, A custom nf at level 1, B custom nf at level 60) : mcpts_scope.
  Notation "'λ' r A e" := (nf_fn r A e) (in custom nf at level 2, r constr at level 0, A custom nf at level 1, e custom nf at level 60) : mcpts_scope.
  Notation "f x .. y" := (ne_app .. (ne_app f x) .. y) (in custom nf at level 40, f custom nf, x custom nf at next level, y custom nf at next level) : mcpts_scope.
  Notation "'#' n" := (ne_var n) (in custom nf at level 0, n constr at level 0, format "'#' n") : mcpts_scope.
  Notation "'⇑' M" := (nf_neut M) (in custom nf at level 0, M custom nf at level 99, format "'⇑'  M") : mcpts_scope.
End Syntax_Notations.
