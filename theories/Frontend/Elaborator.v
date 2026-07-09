From Coq Require Import Lia List MSets PeanoNat String FunInd.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax.

Open Scope string_scope.

Module StrSet := Make String_as_OT.
Module StrSProp := MSetProperties.Properties StrSet.

(** One cannot import notation from module type without
    restricting a module to that exact type.
    Thus, here we repeat the notation from [WSetsOn]. *)
Notation "s [<=] t" := (StrSet.Subset s t) (at level 70, no associativity).

(** De-monadify with pattern matching for now *)
Fixpoint lookup (s : string) (ctx : list string) : option nat :=
  match ctx with
  | nil => None
  | c::cs =>
      if string_dec c s
      then Some 0
      else
        match lookup s cs with
        | Some n => Some (n + 1)%nat
        | None => None
        end
  end
.

(** * Concrete Syntax Tree *)
Module CstAnn.
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
  Arguments fn {_ _ _ _}.
  Arguments app {_}.
  Arguments var {_}.
  Arguments nat {_}.
  Arguments zero {_}.
  Arguments succ {_}.
  Arguments natrec {_}.
End CstAnn.


Fixpoint elaborate {P} (cst : CstAnn.obj P) (ctx : list string) : option (exp P) :=
  match cst with
  | CstAnn.var s =>
      match lookup s ctx with
      | Some n => Some (a_var n)
      | None => None
      end
  | CstAnn.st s => Some (a_st s)
  | CstAnn.nat => Some a_nat
  | CstAnn.zero => Some a_zero
  | CstAnn.succ c =>
      match elaborate c ctx with
      | Some a => Some (a_succ a)
      | None => None
      end
  | CstAnn.natrec n mx m z sx sr s =>
      match elaborate m (mx :: ctx), elaborate z ctx, elaborate s (sr :: sx :: ctx), elaborate n ctx with
      | Some m, Some z, Some s, Some n => Some (a_natrec m z s n)
      | _, _, _, _ => None
      end
  | CstAnn.pi r s t c =>
      match elaborate c (s :: ctx), elaborate t ctx with
      | Some a, Some t => Some (a_pi r t a)
      | _, _ => None
      end
  | CstAnn.fn r s t b c =>
      match elaborate c (s :: ctx), elaborate b (s :: ctx), elaborate t ctx with
      | Some a, Some b, Some t => Some (a_fn r t b a)
      | _, _, _ => None
      end
  | CstAnn.app c1 c2 =>
      match elaborate c1 ctx, elaborate c2 ctx with
      | None, _ => None
      | _, None => None
      | Some a1, Some a2 => Some (a_app a1 a2)
      end
  end
.

Functional Scheme elaborate_fun_ind := Induction for elaborate Sort Prop.

Generalizable All Variables.

Inductive user_exp (P : PtsSig) : exp P -> Prop :=
(** Sorts *)
| user_exp_st :
  `( user_exp P (a_st s) )
(** Functions *)
| user_exp_pi :
  `( forall (r : Ru_pi P s1 s2 s3),
        user_exp P A ->
        user_exp P B ->
        user_exp P (a_pi r A B) )
| user_exp_fn :
  `( forall (r : Ru_pi P s1 s2 s3),
        user_exp P A ->
        user_exp P B ->
        user_exp P M ->
        user_exp P (a_fn r A B M) )
| user_exp_app :
  `( user_exp P M ->
     user_exp P N ->
     user_exp P (a_app M N) )
(** Variables *)
| user_exp_vlookup :
  `( user_exp P (a_var x) )
(** Natural numbers *)
| user_exp_nat :
  `( user_exp P a_nat )
| user_exp_zero :
  `( user_exp P a_zero )
| user_exp_succ :
  `( user_exp P M ->
     user_exp P (a_succ M) )
| user_exp_natrec :
  `( user_exp P A ->
     user_exp P MZ ->
     user_exp P MS ->
     user_exp P M ->
     user_exp P (a_natrec A MZ MS M) ).


Arguments user_exp_st {_}.
Arguments user_exp_pi {_ _ _ _}.
Arguments user_exp_fn {_ _ _ _}.
Arguments user_exp_app {_}.
Arguments user_exp_vlookup {_}.
Arguments user_exp_nat {_}.
Arguments user_exp_zero {_}.
Arguments user_exp_succ {_}.
Arguments user_exp_natrec {_}.

#[export]
Hint Constructors user_exp : mcpts.

Lemma user_exp_nf {P} : forall M, user_exp P (nf_to_exp M)
with user_exp_ne {P} : forall M, user_exp P (ne_to_exp M).
Proof.
  - clear user_exp_nf; induction M; mauto 3.
  - clear user_exp_ne; induction M; mauto 3.
Qed.

Lemma elaborator_gives_user_exp {P} : forall O vs M,
    elaborate O vs = Some M ->
    user_exp P M.
Proof.
  intros * Heq. gen M.
  functional induction (elaborate O vs) using elaborate_fun_ind;
    intros; inversion_clear Heq; mauto 4.

  - econstructor; mauto 3.
  - econstructor; mauto 3.
Qed.

(** This function finds all the variables in an object *)
Fixpoint cst_variables {P} (cst : CstAnn.obj P) : StrSet.t :=
 match cst with
 (** Sorts *)
 | CstAnn.st s => StrSet.empty
 (** Functions *)   
 | CstAnn.pi r s t c => StrSet.union (cst_variables t) (StrSet.remove s (cst_variables c))
 | CstAnn.fn r s t b c => StrSet.union (StrSet.union (cst_variables t) (StrSet.remove s (cst_variables b))) (StrSet.remove s (cst_variables c))
 | CstAnn.app c1 c2 => StrSet.union (cst_variables c1) (cst_variables c2)
 (** Variables *)
 | CstAnn.var s => StrSet.singleton s
 (** Natural numbers *)               
 | CstAnn.nat => StrSet.empty
 | CstAnn.zero => StrSet.empty
 | CstAnn.succ c => cst_variables c
 | CstAnn.natrec n mx m z sx sy s => StrSet.union (StrSet.union (cst_variables n) (StrSet.remove mx (cst_variables m))) (StrSet.union (cst_variables z) (StrSet.remove sx (StrSet.remove sy (cst_variables s))))
 end
.

(** 'closeq_at M n' specificies that an expression is closed in context of size n *)
Inductive closed_at {P} : exp P -> nat -> Prop :=
(** Sorts *)
| ca_sort : `( closed_at (a_st m) n )
(** Functions *)
| ca_pi : `( forall (r : Ru_pi P s1 s2 s3), closed_at t n -> closed_at b (1+n) -> closed_at (a_pi r t b) n )
| ca_lam : `( forall (r : Ru_pi P s1 s2 s3),  closed_at t n -> closed_at b (1+n) -> closed_at c (1+n) -> closed_at (a_fn r t b c) n )
| ca_app : `( closed_at a1 n -> closed_at a2 n -> closed_at (a_app a1 a2) n )
(** Variables *)
| ca_var : `( x < n -> closed_at (a_var x) n )
(** Natural numbers *)
| ca_nat : `( closed_at (a_nat) n )
| ca_zero : `( closed_at (a_zero) n )
| ca_succ : `( closed_at a n -> closed_at (a_succ a) n )
| ca_natrec : `( closed_at n l -> closed_at m (1+l) -> closed_at z l -> closed_at s (2+l) -> closed_at (a_natrec m z s n) l )

.
#[local]
Hint Constructors closed_at: mcpts.

(** Lemma for the well_scoped proof, lookup succeeds if var is in context *)
Lemma lookup_known (s : string) (ctx : list string) (H_in : List.In s ctx) : exists n : nat, (lookup s ctx = Some n /\ n < List.length ctx).
Proof.
  induction ctx as [| c ctx' IHctx]; simpl in *.
  - contradiction.
  - destruct (string_dec c s); subst.
    + eexists; split; auto. lia.
    + destruct H_in; try contradiction.
      destruct IHctx as [? [? ?]]; [assumption |].
      rewrite H0.
      eexists; split; auto. lia.
Qed.

(** Lemma for the well_scoped proof, lookup result always less than context length *)
Lemma lookup_bound s : forall ctx m, lookup s ctx = Some m -> m < (List.length ctx).
  induction ctx.
  - intros. discriminate H.
  - intros. destruct (string_dec a s).
    + rewrite e in H.
      simpl in H.
      destruct string_dec in H.
      * inversion H.
        unfold Datatypes.length.
        apply (Nat.lt_0_succ).
      * contradiction n. reflexivity.
    + simpl in H.
      destruct string_dec in H.
      * contradiction n.
      * destruct (lookup s ctx);
          try discriminate.
        inversion H.
        rewrite H1.
        simpl.
        pose (IHctx (m-1)).
        rewrite <- H1 in l.
        rewrite (Nat.add_sub n1 1) in l.
        rewrite <- H1.
        specialize (l eq_refl).
        lia.
Qed.

Import StrSProp.Dec.

Lemma Subset_to_In : forall xs x, StrSet.singleton x [<=] StrSProp.of_list xs -> In x xs.
Proof.
  intro xs; induction xs; simpl; intros.
  - rewrite <- F.empty_iff.
    apply (H x).
    fsetdec.
  - specialize (H x).
    rewrite F.add_iff in H.
    destruct H; [fsetdec | auto |].
    right. eapply IHxs.
    intros y Hy.
    assert (y = x); fsetdec.
Qed.

(** *** Well scopedness lemma *)

(** If the set of free variables in a cst are contained in a context
    then elaboration succeeds with that context, and the result is a closed term *)
Lemma well_scoped {P} (cst : CstAnn.obj P) : forall ctx,  cst_variables cst [<=] StrSProp.of_list ctx  ->
exists a : exp P, (elaborate cst ctx = Some a) /\ (closed_at a (List.length ctx)).
Proof.
  induction cst; intros; simpl in *; mauto.
  - (* pi *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.
  - (* fn *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    assert (cst_variables cst3 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; 
      destruct (IHcst3 _ H2) as [ast'' [-> ?]]; mauto.
  - (* app *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list ctx) by fsetdec.
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]]; mauto.

  - (* var *)
    apply Subset_to_In in H.
    edestruct lookup_known as [? [-> ?]]; [auto |].
    apply (In_nth _ _ s)  in H.
    destruct H as [? [? ?]].
    mauto.
    
  - (* succ *)
    destruct (IHcst _ H) as [ast [-> ?]]; mauto.
  - (* natrec *)
    assert (cst_variables cst1 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst2 [<=] StrSProp.of_list (s :: ctx)) by (simpl; fsetdec).
    assert (cst_variables cst3 [<=] StrSProp.of_list ctx) by fsetdec.
    assert (cst_variables cst4 [<=] StrSProp.of_list (s1 :: s0 :: ctx)) by (simpl; fsetdec).
    destruct (IHcst1 _ H0) as [ast [-> ?]];
      destruct (IHcst2 _ H1) as [ast' [-> ?]];
      destruct (IHcst3 _ H2) as [ast'' [-> ?]];
      destruct (IHcst4 _ H3) as [ast''' [-> ?]]; mauto.
Qed.

Example test_elab {P} : @elaborate P CstAnn.nat nil = Some a_nat.
Proof. reflexivity. Qed.

Example test_elab2 {P} : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3},
    @elaborate P (CstAnn.fn r "s" CstAnn.nat CstAnn.nat (CstAnn.fn r "x" CstAnn.nat CstAnn.nat (CstAnn.fn r "s" CstAnn.nat CstAnn.nat (CstAnn.var "q")))) nil = None.
Proof. reflexivity. Qed.
