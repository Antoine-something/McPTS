From Stdlib Require Import List String PeanoNat MSets FunInd.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax.
From McPTS.Frontend Require Import Elaborator.
From McPTS.CaseStudies.MLTTNonCumul Require Import Signature.

(** * Concrete Syntax Tree *)
Module Cst.
  Inductive obj : Set :=
  (** Universes *)
  | s_univ : nat -> obj
  (** Functions, max universe level *)
  | pi : string -> nat -> nat -> obj -> obj -> obj
  | fn : string -> nat -> nat -> obj -> obj -> obj -> obj
  | app : obj -> obj -> obj
  (** Variables *)
  | var : string -> obj
  (** Natural numbers *)
  | nat : obj
  | zero : obj
  | succ : obj -> obj
  | natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj.
End Cst.


Fixpoint annotate' (cst : Cst.obj) : CstAnn.obj MLTTNonCumul_Sig :=
  match cst with
  (* Sorts *)
  | Cst.s_univ n => @CstAnn.st MLTTNonCumul_Sig (s_univ n)
  (* Functions *)
  | Cst.pi s i j t c => @CstAnn.pi MLTTNonCumul_Sig _ _ _ (f_max i j) s (annotate' t) (annotate' c)
  | Cst.fn s i j t b c => @CstAnn.fn MLTTNonCumul_Sig _ _ _ (f_max i j) s (annotate' t) (annotate' b) (annotate' c)
  | Cst.app c1 c2 =>  @CstAnn.app MLTTNonCumul_Sig (annotate' c1) (annotate' c2)
  (* Variables *)
  | Cst.var x => @CstAnn.var MLTTNonCumul_Sig x
  (* Natural numbers *)
  | Cst.nat => @CstAnn.nat MLTTNonCumul_Sig
  | Cst.zero => @CstAnn.zero MLTTNonCumul_Sig
  | Cst.succ c => @CstAnn.succ MLTTNonCumul_Sig (annotate' c)
  | Cst.natrec n mx m z sx sr s => @CstAnn.natrec MLTTNonCumul_Sig (annotate' n) mx (annotate' m) (annotate' z) sx sr (annotate' s)
  end.

Definition elaborate' (cst : Cst.obj) (ctx : list string) : option (exp MLTTNonCumul_Sig) :=
  elaborate (annotate' cst) ctx.
