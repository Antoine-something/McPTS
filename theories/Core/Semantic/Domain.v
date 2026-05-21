From Equations Require Import Equations.

From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax.

Reserved Notation "'env'".

Inductive domain (P : PtsSig) : Set :=
| d_sort : P -> domain P
| d_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> domain P -> env P -> exp P -> domain P
| d_fn : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 ->  env P -> exp P -> domain P
| d_nat : domain P
| d_zero : domain P
| d_succ : domain P -> domain P
| d_neut : domain P -> domain_ne P -> domain P
with domain_ne (P : PtsSig) : Set :=
(** Notice that the number x here is not a de Bruijn index but an absolute
    representation of names.  That is, this number does not change relative to the
    binding structure it currently exists in.
 *)
| d_var : forall (x : nat), domain_ne P
| d_app : domain_ne P -> domain_nf P -> domain_ne P
| d_natrec : env P -> exp P -> domain P -> exp P -> domain_ne P -> domain_ne P
with domain_nf (P : PtsSig) : Set :=
| d_dom : domain P -> domain P -> domain_nf P
(** Contrary to McTT, environments are lists instead of functions *)
where "'env'" := (fun P => (list (domain P))).

(* Make the signature implicit to all constructors *)
Arguments d_sort {_}.
Arguments d_pi {_ _ _ _}.
Arguments d_fn {_ _ _ _}.
Arguments d_nat {_}.
Arguments d_zero {_}.
Arguments d_succ {_}.
Arguments d_neut {_}.
Arguments d_var {_}.
Arguments d_app {_}.
Arguments d_natrec {_}.
Arguments d_dom {_}.

Derive NoConfusion for domain domain_ne domain_nf.

(** The main reason to use lists is that we do not have a clear way to define the empty env as a function since there is no d_zero to make a default value *)
Definition empty_env {P : PtsSig} : env P := nil.

Definition extend_env {P : PtsSig} (ρ : env P) (d : domain P) : env P := cons d ρ.
Arguments extend_env _ _ _ /.
Transparent extend_env.

Definition drop_env {P : PtsSig} (ρ : env P) : env P :=
  match ρ with
  | nil => nil
  | cons d ρ' => ρ'
  end.
Arguments drop_env _ _ /.
Transparent drop_env.

#[global] Declare Custom Entry domain.
#[global] Bind Scope mcpts_scope with domain.

Module Domain_Notations.
  Export Syntax_Notations.

  Notation "'d{{{' x '}}}'" := x (at level 0, x custom domain at level 99, format "'d{{{'  x  '}}}'") : mcpts_scope.
  Notation "( x )" := x (in custom domain at level 0, x custom domain at level 60) : mcpts_scope.
  Notation "'^' x" := x (in custom domain at level 0, x constr at level 0) : mcpts_scope.
  Notation "x" := x (in custom domain at level 0, x ident) : mcpts_scope.
  Notation "'Sort' @ s" := (d_sort s) (in custom domain at level 0, s constr at level 0) : mcpts_scope.
  Notation "'Π' r a ρ B" := (d_pi r a ρ B) (in custom domain at level 0, r constr at level 0, a custom domain at level 30, ρ custom domain at level 0, B custom exp at level 30) : mcpts_scope.
  Notation "'λ' r ρ M" := (d_fn r ρ M) (in custom domain at level 0, r constr at level 0, ρ custom domain at level 30, M custom exp at level 30) : mcpts_scope.
  Notation "f x .. y" := (d_app .. (d_app f x) .. y) (in custom domain at level 40, f custom domain, x custom domain at next level, y custom domain at next level) : mcpts_scope.
  Notation "'ℕ'" := d_nat (in custom domain) : mcpts_scope.
  Notation "'zero'" := d_zero (in custom domain at level 0) : mcpts_scope.
  Notation "'succ' m" := (d_succ m) (in custom domain at level 30, m custom domain at level 30) : mcpts_scope.
  Notation "'rec' m 'under' ρ 'return' A | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec ρ A mz MS m) (in custom domain at level 0, A custom exp at level 60, mz custom domain at level 60, MS custom exp at level 60, ρ custom domain at level 60, m custom domain at level 60) : mcpts_scope.
  Notation "'!' n" := (d_var n) (in custom domain at level 0, n constr at level 0) : mcpts_scope.
  Notation "'⇑' a m" := (d_neut a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : mcpts_scope.
  Notation "'⇓' a m" := (d_dom a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : mcpts_scope.
  Notation "'⇑!' a n" := (d_neut a (d_var n)) (in custom domain at level 0, a custom domain at level 30, n constr at level 0) : mcpts_scope.
  Notation "ρ ↦ m" := (extend_env ρ m) (in custom domain at level 20, left associativity, ρ custom domain, m custom domain at level 30) : mcpts_scope.
  Notation "ρ '↯'" := (drop_env ρ) (in custom domain at level 10, ρ custom domain) : mcpts_scope.
End Domain_Notations.

Import Domain_Notations.

Proposition drop_env_extend_env_cancel {P : PtsSig} : forall (ρ : env P) a,
    d{{{ (ρ ↦ a) ↯ }}} = ρ.
Proof.
  reflexivity.
Qed.
