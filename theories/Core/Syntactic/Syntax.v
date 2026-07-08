From Coq Require Import List String.
From Coq Require Import Program.Equality.
From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.

(** * Concrete Syntax Tree *)  
Module Cst.
  Inductive obj (P : PtsSig) : Set :=
  (** Sorts *)
  | st : P -> obj P
  (** Functions *)
  | pi : forall s1 s2 s3 (r : Ru_pi P s1 s2 s3), string -> obj P -> obj P -> obj P
  | fn : forall s1 s2 s3 (r : Ru_pi P s1 s2 s3), string -> obj P -> obj P -> obj P -> obj P
  | app : obj P -> obj P -> obj P
  (** Variables *)
  | var : string -> obj P
  (** Natural numbers *)
  | nat : obj P
  | zero : obj P
  | succ : obj P -> obj P
  | natrec : obj P -> string -> obj P -> obj P -> string -> string -> obj P -> obj P.

  Arguments st {_}.
  Arguments pi {_ _ _ _}.
  Arguments fn {_ _ _ _ _}.
  Arguments app {_}.
  Arguments var {_}.
  Arguments nat {_}.
  Arguments zero {_}.
  Arguments succ {_}.
  Arguments natrec {_}.
End Cst.


(** * Abstract Syntax Tree *)
Inductive exp (P : PtsSig) : Set :=
(** Sorts *)
| a_st : P -> exp P
(** Functions *)
| a_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> exp P -> exp P -> exp P
| a_fn : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> exp P -> exp P -> exp P -> exp P
| a_app : exp P -> exp P -> exp P
(** Variable *)
| a_var : nat -> exp P
(** Substitution Application *)
| a_sub : exp P -> sub P -> exp P
(** Naturals **)
| a_nat : exp P
| a_zero : exp P
| a_succ : exp P -> exp P
| a_natrec : exp P -> exp P -> exp P -> exp P -> exp P
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
Arguments a_nat {_}.
Arguments a_zero {_}.
Arguments a_succ {_}.
Arguments a_natrec {_}.
Arguments a_id {_}.
Arguments a_weaken {_}.
Arguments a_compose {_}.
Arguments a_extend {_}.


Notation typ := (fun P => exp P).
Notation ctx := (fun (P : PtsSig) => list (typ P)%type).

Fixpoint nat_to_exp {P : PtsSig} (n : nat) : exp P :=
  match n with
  | 0 => a_zero
  | S m => a_succ (nat_to_exp m)
  end.

Definition num_to_exp {P : PtsSig} (n : Number.uint) : exp P :=
  nat_to_exp (Nat.of_num_uint n).

Fixpoint exp_to_nat {P : PtsSig} (e : exp P) : option nat :=
  match e with
  | a_zero => Some 0
  | a_succ e' =>
      match exp_to_nat e' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.

Definition exp_to_num {P : PtsSig} (e : exp P) :=
  match exp_to_nat e with
  | Some n => Some (Nat.to_num_uint n)
  | None => None
  end.


Scheme exp_mut_ind := Induction for exp Sort Prop
with sub_mut_ind := Induction for sub Sort Prop.
Combined Scheme syntax_mut_ind from
  exp_mut_ind,
  sub_mut_ind.

(** ** Syntactic Normal/Neutral Form *)
Inductive nf (P : PtsSig) : Set :=
| nf_st : P -> nf P
| nf_pi : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> nf P -> nf P -> nf P
| nf_fn : forall (s1 s2 s3 : P), Ru_pi P s1 s2 s3 -> nf P -> nf P -> nf P -> nf P
| nf_nat : nf P
| nf_zero : nf P
| nf_succ : nf P -> nf P
| nf_neut : ne P -> nf P
with ne (P : PtsSig) : Set :=
| ne_app : ne P -> nf P -> ne P
| ne_var : nat -> ne P
| ne_natrec : nf P -> nf P -> nf P -> ne P -> ne P
.

Arguments nf_st {_}.
Arguments nf_pi {_ _ _ _}.
Arguments nf_fn {_ _ _ _}.
Arguments nf_nat {_}.
Arguments nf_zero {_}.
Arguments nf_succ {_}.
Arguments nf_neut {_}.

Arguments ne_app {_}.
Arguments ne_var {_}.
Arguments ne_natrec {_}.

Fixpoint nf_to_exp {P : PtsSig} (M : nf P) : exp P :=
  match M with
  | nf_st s => a_st s
  | nf_pi r A B => a_pi r (nf_to_exp A) (nf_to_exp B)
  | nf_fn r A B M => a_fn r (nf_to_exp A) (nf_to_exp B) (nf_to_exp M)
  | nf_nat => a_nat
  | nf_zero => a_zero
  | nf_succ M => a_succ (nf_to_exp M)
  | nf_neut M => ne_to_exp M
  end
with ne_to_exp {P : PtsSig} (M : ne P) : exp P :=
  match M with
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_var x => a_var x
  | ne_natrec A MZ MS M => a_natrec (nf_to_exp A) (nf_to_exp MZ) (nf_to_exp MS) (ne_to_exp M)
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.
  
Fact nf_eq_dec {P : PtsSig} (dec_P : DecidableSig P) : forall (M M' : nf P),
    ({M = M'} + {M <> M'})%type
with ne_eq_dec {P : PtsSig} (dec_P : DecidableSig P): forall (M M' : ne P),
    ({M = M'} + {M <> M'})%type.
Proof.
  - intros.
    destruct M; destruct M';
      try solve [right; intros H; inversion H];
      try solve [left; reflexivity].
    + destruct (dec_st_eq dec_P s s0).
      * subst.
        left.
        reflexivity.
      * right.
        injection.
        eassumption.
    + destruct (dec_st_eq dec_P s1 s0); [| right; injection; intros; auto].
      destruct (dec_st_eq dec_P s2 s4); [| right; injection; intros; auto].
      destruct (dec_st_eq dec_P s3 s5); [| right; injection; intros; auto].
      subst.
      pose proof (dec_ru_pi_eq dec_P _ _ _ r r0).
      destruct H; [| right; injection; intros; simpl_existTs; auto].
      subst.
      destruct (nf_eq_dec P dec_P M1 M'1); [| right; injection; auto].
      destruct (nf_eq_dec P dec_P M2 M'2); [| right; injection; auto].
      subst.
      left.
      reflexivity.
    + destruct (dec_st_eq dec_P s1 s0); [| right; injection; intros; auto].
      destruct (dec_st_eq dec_P s2 s4); [| right; injection; intros; auto].
      destruct (dec_st_eq dec_P s3 s5); [| right; injection; intros; auto].
      subst.
      pose proof (dec_ru_pi_eq dec_P _ _ _ r r0).
      destruct H; [| right; injection; intros; simpl_existTs; auto].
      subst.
      destruct (nf_eq_dec P dec_P M1 M'1); [| right; injection; auto].
      destruct (nf_eq_dec P dec_P M2 M'2); [| right; injection; auto].
      destruct (nf_eq_dec P dec_P M3 M'3); [| right; injection; auto].
      subst.
      left.
      reflexivity.
    + destruct (nf_eq_dec P dec_P M M').
      * subst.
        left.
        reflexivity.
      * right.
        injection.
        eassumption.
    + destruct (ne_eq_dec P dec_P n n0).
      * subst.
        left.
        reflexivity.
      * right.
        injection.
        eassumption.
  - intros; decide equality; try apply PeanoNat.Nat.eq_dec.
Defined.

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
  Notation "'ℕ'" := a_nat (in custom exp at level 0) : mcpts_scope.
  Notation "'zero'" := a_zero (in custom exp at level 0) : mcpts_scope.
  Notation "'succ' e" := (a_succ e) (in custom exp at level 1, e custom exp at level 0) : mcpts_scope.
  Notation "'rec' e 'return' A | 'zero' -> ez | 'succ' -> es 'end'" := (a_natrec A ez es e) (in custom exp at level 0, A custom exp at level 60, ez custom exp at level 60, es custom exp at level 60, e custom exp at level 60) : mcpts_scope.
  Notation "'Π' r A B" := (a_pi r A B) (in custom exp at level 1, r constr at level 0, A custom exp at level 0, B custom exp at level 60) : mcpts_scope.
  Notation "'Π' r A B" := (a_pi r A B) (in custom exp at level 1, r constr at level 0, A custom exp at level 0, B custom exp at level 60) : mcpts_scope.
  Notation "'λ' r A B e" := (a_fn r A B e) (in custom exp at level 1, r constr at level 0, A custom exp at level 0, B custom exp at level 0, e custom exp at level 60) : mcpts_scope.
  Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom exp at level 40, f custom exp, x custom exp at next level, y custom exp at next level) : mcpts_scope.
  Notation "'#' n" := (a_var n) (in custom exp at level 0, n constr at level 0, format "'#' n") : mcpts_scope.

  Notation "'Id'" := a_id (in custom exp at level 0) : mcpts_scope.
  Notation "'Wk'" := a_weaken (in custom exp at level 0) : mcpts_scope.
  Notation "σ ∘ τ" := (a_compose σ τ) (in custom exp at level 40, right associativity, format "σ ∘ τ") : mcpts_scope.
  Notation "σ ,, e" := (a_extend σ e) (in custom exp at level 50, left associativity, format "σ ,, e") : mcpts_scope.
  Notation "'q' σ" := (q σ) (in custom exp at level 30) : mcpts_scope.

  Notation "⋅" := nil (in custom exp at level 0) : mcpts_scope.
  Notation "Γ , A" := (cons A Γ) (in custom exp at level 50, left associativity, format "Γ ,  A") : mcpts_scope.

  Notation "n{{{ x }}}" := x (at level 0, x custom nf at level 99, format "'n{{{'  x  '}}}'") : mcpts_scope.
  Notation "( x )" := x (in custom nf at level 0, x custom nf at level 60) : mcpts_scope.
  Notation "'^' x" := x (in custom nf at level 0, x constr at level 0) : mcpts_scope.
  Notation "x" := x (in custom nf at level 0, x ident) : mcpts_scope.

  Notation "'Sort' @ s" := (nf_st s) (in custom nf at level 0, s constr at level 0, format "'Sort' @ s") : mcpts_scope.
  Notation "'ℕ'" := nf_nat (in custom nf at level 0) : mcpts_scope.
  Notation "'zero'" := nf_zero (in custom nf at level 0) : mcpts_scope.
  Notation "'succ' M" := (nf_succ M) (in custom nf at level 2, M custom nf at level 1) : mcpts_scope.
  Notation "'rec' M 'return' A | 'zero' -> MZ | 'succ' -> MS 'end'" := (ne_natrec A MZ MS M) (in custom nf at level 0, A custom nf at level 60, MZ custom nf at level 60, MS custom nf at level 60, M custom nf at level 60) : mcpts_scope.
  Notation "'Π' r A B" := (nf_pi r A B) (in custom nf at level 2, r constr at level 0, A custom nf at level 1, B custom nf at level 60) : mcpts_scope.
  Notation "'λ' r A B e" := (nf_fn r A B e) (in custom nf at level 2, r constr at level 0, A custom nf at level 1, B custom nf at level 1, e custom nf at level 60) : mcpts_scope.
  Notation "f x .. y" := (ne_app .. (ne_app f x) .. y) (in custom nf at level 40, f custom nf, x custom nf at next level, y custom nf at next level) : mcpts_scope.
  Notation "'#' n" := (ne_var n) (in custom nf at level 0, n constr at level 0, format "'#' n") : mcpts_scope.
  Notation "'⇑' M" := (nf_neut M) (in custom nf at level 0, M custom nf at level 99, format "'⇑'  M") : mcpts_scope.
End Syntax_Notations.
