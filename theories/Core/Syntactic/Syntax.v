From Coq Require Import List String.
From Coq Require Import Program.Equality Logic.PropExtensionality.
From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.


(** * Abstract Syntax Tree *)  
Inductive exp (P : AdjSig) : Modes P -> Set :=
(** Sorts *)
| a_st : forall (m : Modes P), St m -> exp P m
(** Functions *)
| a_pi : forall (m : Modes P) (s1 s2 s3 : m), Ru_pi m s1 s2 s3 -> exp P m -> exp P m -> exp P m
| a_fn : forall (m : Modes P) (s1 s2 s3 : m), Ru_pi m s1 s2 s3 -> exp P m -> exp P m -> exp P m -> exp P m
| a_app : forall m, exp P m -> exp P m -> exp P m
(** Variable *)
| a_var : forall m, nat -> exp P m
(** Substitution Application *)
| a_sub : forall m, exp P m -> sub P -> exp P m
(** Naturals **)
| a_nat : forall m, exp P m
| a_zero : forall m, exp P m
| a_succ : forall m, exp P m -> exp P m
| a_natrec : forall m, exp P m -> exp P m -> exp P m -> exp P m -> exp P m
(** Upshift *)
| a_upshift : forall l h (leq : {{ l ⪯ h ∈ P }}) sl sh, Ru_upshift P l h leq sl sh -> exp P l -> exp P h
| a_susp : forall l h (leq : {{ l ⪯ h ∈ P }}) sl sh, Ru_upshift P l h leq sl sh -> exp P l -> exp P h
| a_force : forall l h (leq : {{ l ⪯ h ∈ P }}) sl sh, Ru_upshift P l h leq sl sh -> exp P h -> exp P l 

with sub (P : AdjSig) : Set :=
| a_id : sub P
| a_weaken : sub P
| a_compose : sub P -> sub P -> sub P
| a_extend : forall m, sub P -> exp P m -> sub P.


(* Make the adjoint signature implicit to all constructors *)
Arguments a_st {_ _}.
Arguments a_pi {_ _ _ _ _}.
Arguments a_fn {_ _ _ _ _}.
Arguments a_app {_ _}.
Arguments a_var {_ _}.
Arguments a_sub {_ _}.
Arguments a_nat {_ _}.
Arguments a_zero {_ _}.
Arguments a_succ {_ _}.
Arguments a_natrec {_ _}.
Arguments a_upshift {_ _ _ _ _ _}.
Arguments a_susp {_ _ _ _ _ _}.
Arguments a_force {_ _ _ _ _ _}.
Arguments a_id {_}.
Arguments a_weaken {_}.
Arguments a_compose {_}.
Arguments a_extend {_ _}.


Notation typ := (fun P m => exp P m).
Notation ctx := (fun P m => list (typ P m)).

Fixpoint nat_to_exp {P : AdjSig} {m : Modes P} (n : nat) : exp P m :=
  match n with
  | 0 => a_zero
  | S m => a_succ (nat_to_exp m)
  end.

Definition num_to_exp {P : AdjSig} {m : Modes P} (n : Number.uint) : exp P m :=
  nat_to_exp (Nat.of_num_uint n).

Fixpoint exp_to_nat {P : AdjSig} {m : Modes P} (e : exp P m) : option nat :=
  match e with
  | a_zero => Some 0
  | a_succ e' =>
      match exp_to_nat e' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
  end.

Definition exp_to_num {P : AdjSig} {m : Modes P} (e : exp P m) :=
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
Inductive nf (P : AdjSig) : Modes P -> Set :=
| nf_st : forall (m : Modes P), St m -> nf P m
| nf_pi : forall (m : Modes P) (s1 s2 s3 : m), Ru_pi m s1 s2 s3 -> nf P m -> nf P m -> nf P m
| nf_fn : forall (m : Modes P) (s1 s2 s3 : m), Ru_pi m s1 s2 s3 -> nf P m -> nf P m -> nf P m -> nf P m
| nf_nat : forall m, nf P m
| nf_zero : forall m, nf P m
| nf_succ : forall m, nf P m -> nf P m
| nf_neut : forall m, ne P m -> nf P m
| nf_upshift : forall l h (leq : {{ l ⪯ h ∈ P }}) sl sh, Ru_upshift P l h leq sl sh -> nf P l -> nf P h
| nf_susp : forall l h (leq : {{ l ⪯ h ∈ P }}) sl sh, Ru_upshift P l h leq sl sh -> nf P l -> nf P h
with ne (P : AdjSig) : Modes P -> Set :=
| ne_app : forall m, ne P m -> nf P m -> ne P m
| ne_var : forall m, nat -> ne P m
| ne_natrec : forall m, nf P m -> nf P m -> nf P m -> ne P m -> ne P m
| ne_force : forall l h (leq : {{ l ⪯ h ∈ P }}) sl sh, Ru_upshift P l h leq sl sh -> ne P h -> ne P l
.

Arguments nf_st {_ _}.
Arguments nf_pi {_ _ _ _ _}.
Arguments nf_fn {_ _ _ _ _}.
Arguments nf_nat {_ _}.
Arguments nf_zero {_ _}.
Arguments nf_succ {_ _}.
Arguments nf_neut {_ _}.
Arguments nf_upshift {_ _ _ _ _ _}.
Arguments nf_susp {_ _ _ _ _ _}.

Arguments ne_app {_ _}.
Arguments ne_var {_ _}.
Arguments ne_natrec {_ _}.
Arguments ne_force {_ _ _ _ _ _}.

Fixpoint nf_to_exp {P : AdjSig} {m : Modes P} (M : nf P m) : exp P m :=
  match M with
  | nf_st s => a_st s
  | nf_pi r A B => a_pi r (nf_to_exp A) (nf_to_exp B)
  | nf_fn r A B M => a_fn r (nf_to_exp A) (nf_to_exp B) (nf_to_exp M)
  | nf_nat => a_nat
  | nf_zero => a_zero
  | nf_succ M => a_succ (nf_to_exp M)
  | nf_neut M => ne_to_exp M
  | nf_upshift r A => a_upshift r (nf_to_exp A)
  | nf_susp r M => a_susp r (nf_to_exp M)
  end
with ne_to_exp {P : AdjSig} {m : Modes P} (M : ne P m) : exp P m :=
  match M with
  | ne_app M N => a_app (ne_to_exp M) (nf_to_exp N)
  | ne_var x => a_var x
  | ne_natrec A MZ MS M => a_natrec (nf_to_exp A) (nf_to_exp MZ) (nf_to_exp MS) (ne_to_exp M)
  | ne_force r M => a_force r (ne_to_exp M)
  end
.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.

Section DecideNfEq.
  Lemma eq_upshift_implies_strong_ru_upshift_eq {P : AdjSig} (dec_P : DecidableAdjSig P) :
    forall l l' h (leq : Mode_preorder P l h) (leq' : Mode_preorder P l' h) sl sl' sh sh' (r : Ru_upshift P l h leq sl sh) (r' : Ru_upshift P l' h leq' sl' sh') A A',
      (nf_upshift r A = nf_upshift r' A') ->
      strong_ru_upshift_eq l l' h h leq leq' sl sl' sh sh' r r'.
  Proof.
    intros.
    inversion H; subst.
    assert (leq = leq') as -> by (apply proof_irrelevance).
    simpl_existTs; subst.
    simpl_existTs; subst.
    repeat split; reflexivity.
  Qed.

  Lemma eq_susp_implies_strong_ru_upshift_eq {P : AdjSig} (dec_P : DecidableAdjSig P) :
    forall l l' h (leq : Mode_preorder P l h) (leq' : Mode_preorder P l' h) sl sl' sh sh' (r : Ru_upshift P l h leq sl sh) (r' : Ru_upshift P l' h leq' sl' sh') M M',
      (nf_susp r M = nf_susp r' M') ->
      strong_ru_upshift_eq l l' h h leq leq' sl sl' sh sh' r r'.
  Proof.
    intros.
    inversion H; subst.
    assert (leq = leq') as -> by (apply proof_irrelevance).
    simpl_existTs; subst.
    simpl_existTs; subst.
    repeat split; reflexivity.
  Qed.

  Lemma eq_force_implies_strong_ru_upshift_eq {P : AdjSig} (dec_P : DecidableAdjSig P) :
    forall l h h' (leq : Mode_preorder P l h) (leq' : Mode_preorder P l h') sl sl' sh sh' (r : Ru_upshift P l h leq sl sh) (r' : Ru_upshift P l h' leq' sl' sh') M M',
      (ne_force r M = ne_force r' M') ->
      strong_ru_upshift_eq l l h h' leq leq' sl sl' sh sh' r r'.
  Proof.
    intros.
    inversion H; subst.
    assert (leq = leq') as -> by (apply proof_irrelevance).
    simpl_existTs; subst.
    simpl_existTs; subst.
    repeat split; reflexivity.
  Qed.
  
  Fact nf_eq_dec {P : AdjSig} (dec_P : DecidableAdjSig P) : forall (m : Modes P) (M M' : nf P m),
      ({M = M'} + {M <> M'})%type
      with ne_eq_dec {P : AdjSig} (dec_P : DecidableAdjSig P): forall (m : Modes P) (M M' : ne P m),
          ({M = M'} + {M <> M'})%type.
  Proof.
    - intros.
      pose proof (dec_sigs dec_P m) as dec_m.
      destruct M; destruct M';
        try solve [right; intros H; inversion H];
        try solve [left; reflexivity].
      + destruct (dec_st_eq dec_m s s0).
        * subst.
          left.
          reflexivity.
        * right.
          injection.
          intros.
          simpl_existTs.
          intuition.
      + destruct (dec_st_eq dec_m s1 s0); [| right; injection; intros; simpl_existTs; auto].
        destruct (dec_st_eq dec_m s2 s4); [| right; injection; intros; simpl_existTs; auto].
        destruct (dec_st_eq dec_m s3 s5); [| right; injection; intros; simpl_existTs; auto].
        subst.
        destruct (dec_ru_pi_eq dec_m _ _ _ r r0); [| right; injection; intros; simpl_existTs; auto].
        subst.
        destruct (nf_eq_dec P dec_P m M1 M'1); [| right; injection; intros; simpl_existTs; auto].
        destruct (nf_eq_dec P dec_P m M2 M'2); [| right; injection; intros; simpl_existTs; auto].
        subst.
        left.
        reflexivity.
      + destruct (dec_st_eq dec_m s1 s0); [| right; injection; intros; simpl_existTs; auto].
        destruct (dec_st_eq dec_m s2 s4); [| right; injection; intros; simpl_existTs; auto].
        destruct (dec_st_eq dec_m s3 s5); [| right; injection; intros; simpl_existTs; auto].
        subst.
        destruct (dec_ru_pi_eq dec_m _ _ _ r r0); [| right; injection; intros; simpl_existTs; auto].
        subst.
        destruct (nf_eq_dec P dec_P m M1 M'1); [| right; injection; intros; simpl_existTs; auto].
        destruct (nf_eq_dec P dec_P m M2 M'2); [| right; injection; intros; simpl_existTs; auto].
        destruct (nf_eq_dec P dec_P m M3 M'3); [| right; injection; intros; simpl_existTs; auto].
        subst.
        left.
        reflexivity.
      + destruct (nf_eq_dec P dec_P m M M').
        * subst.
          left.
          reflexivity.
        * right.
          injection.
          intros.
          simpl_existTs.
          auto.
      + destruct (ne_eq_dec P dec_P m n n0).
        * subst.
          left.
          reflexivity.
        * right.
          injection.
          intros.
          simpl_existTs.
          auto.
      + destruct (strong_dec_ru_upshift dec_P l l0 h h leq leq0 sl sl0 sh sh0 r r0).
        * destruct s as [Hl [Hh [Hleq [Hsl [Hsh Hr]]]]]; subst.
          destruct (nf_eq_dec P dec_P l0 M M'); [| right; injection; intros; simpl_existTs; auto].
          left; subst; reflexivity.
        * right; injection.
          assert (strong_ru_upshift_eq l l0 h h leq leq0 sl sl0 sh sh0 r r0) by (eapply eq_upshift_implies_strong_ru_upshift_eq; eauto).
          auto.
      + destruct (strong_dec_ru_upshift dec_P l l0 h h leq leq0 sl sl0 sh sh0 r r0).
        * destruct s as [Hl [Hh [Hleq [Hsl [Hsh Hr]]]]]; subst.
          destruct (nf_eq_dec P dec_P l0 M M'); [| right; injection; intros; simpl_existTs; auto].
          left; subst; reflexivity.
        * right; injection.
          assert (strong_ru_upshift_eq l l0 h h leq leq0 sl sl0 sh sh0 r r0) by (eapply eq_susp_implies_strong_ru_upshift_eq; eauto).
          auto.
          
    - intros.
      pose proof (dec_sigs dec_P m) as dec_m.
      destruct M; destruct M';
        try solve [right; intros H; inversion H];
        try solve [left; reflexivity].
      + destruct (ne_eq_dec P dec_P m M M'); [| right; injection; intros; simpl_existTs; auto].
        destruct (nf_eq_dec P dec_P m n n0); [| right; injection; intros; simpl_existTs; auto].
        left; subst; reflexivity.
      + destruct (PeanoNat.Nat.eq_dec n n0); [| right; injection; intros; auto].
        left; subst; reflexivity.
      + destruct (ne_eq_dec P dec_P m M M'); [| right; injection; intros; simpl_existTs; auto].
        destruct (nf_eq_dec P dec_P m n n2); [| right; injection; intros; simpl_existTs; auto].
        destruct (nf_eq_dec P dec_P m n0 n3); [| right; injection; intros; simpl_existTs; auto].
        destruct (nf_eq_dec P dec_P m n1 n4); [| right; injection; intros; simpl_existTs; auto].
        left; subst; reflexivity.
      + destruct (strong_dec_ru_upshift dec_P l l h h0 leq leq0 sl sl0 sh sh0 r r0).
        * destruct s as [Hl [Hh [Hleq [Hsl [Hsh Hr]]]]]; subst.
          destruct (ne_eq_dec P dec_P h0 M M'); [| right; injection; intros; simpl_existTs; auto].
          left; subst; reflexivity.
        * right; injection.
          assert (strong_ru_upshift_eq l l h h0 leq leq0 sl sl0 sh sh0 r r0) by (eapply eq_force_implies_strong_ru_upshift_eq; eauto).
          auto.
  Defined.
End DecideNfEq.


Definition q {P : AdjSig} {m : Modes P} (σ : sub P) := a_extend (a_compose σ a_weaken) (@a_var P m 0).
Arguments q {_} {_} σ/.


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
  Notation "'↑' r A" := (a_upshift r A) (in custom exp at level 1, r constr at level 0, A custom exp at level 60) : mcpts_scope.
  Notation "'susp' r M" := (a_susp r M) (in custom exp at level 1, r constr at level 0, M custom exp at level 60) : mcpts_scope.
  Notation "'force' r M" := (a_force r M) (in custom exp at level 1, r constr at level 0, M custom exp at level 60) : mcpts_scope.
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
  Notation "'↑' r A" := (nf_upshift r A) (in custom exp at level 1, r constr at level 0, A custom exp at level 60) : mcpts_scope.
  Notation "'susp' r M" := (nf_susp r M) (in custom exp at level 1, r constr at level 0, M custom exp at level 60) : mcpts_scope.
  Notation "'force' r M" := (ne_force r M) (in custom exp at level 1, r constr at level 0, M custom exp at level 60) : mcpts_scope.
  Notation "'#' n" := (a_var n) (in custom exp at level 0, n constr at level 0, format "'#' n") : mcpts_scope.
  Notation "'#' n" := (ne_var n) (in custom nf at level 0, n constr at level 0, format "'#' n") : mcpts_scope.
  Notation "'⇑' M" := (nf_neut M) (in custom nf at level 0, M custom nf at level 99, format "'⇑'  M") : mcpts_scope.
End Syntax_Notations.
