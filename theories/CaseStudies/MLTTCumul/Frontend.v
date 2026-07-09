From Coq Require Import List String PeanoNat MSets FunInd.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax.
From McPTS.Frontend Require Import Elaborator.
From McPTS.CaseStudies.MLTTCumul Require Import Signature.

(** * Concrete Syntax Tree *)
Module Cst.
  Inductive obj : Set :=
  (** Universes *)
  | s_univ : nat -> obj
  (** Functions, max universe level *)
  | pi : string -> nat -> obj -> obj -> obj
  | fn : string -> nat -> obj -> obj -> obj -> obj
  | app : obj -> obj -> obj
  (** Variables *)
  | var : string -> obj
  (** Natural numbers *)
  | nat : obj
  | zero : obj
  | succ : obj -> obj
  | natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj.
End Cst.


Fixpoint annotate' (cst : Cst.obj) : CstAnn.obj MLTTCumul_Sig :=
  match cst with
  (* Sorts *)
  | Cst.s_univ n => @CstAnn.st MLTTCumul_Sig (s_univ n)
  (* Functions *)
  | Cst.pi s i t c => @CstAnn.pi MLTTCumul_Sig _ _ _ (f_max i i) s (annotate' t) (annotate' c)
  | Cst.fn s i t b c => @CstAnn.fn MLTTCumul_Sig _ _ _ (f_max i i) s (annotate' t) (annotate' b) (annotate' c)
  | Cst.app c1 c2 =>  @CstAnn.app MLTTCumul_Sig (annotate' c1) (annotate' c2)
  (* Variables *)
  | Cst.var x => @CstAnn.var MLTTCumul_Sig x
  (* Natural numbers *)
  | Cst.nat => @CstAnn.nat MLTTCumul_Sig
  | Cst.zero => @CstAnn.zero MLTTCumul_Sig
  | Cst.succ c => @CstAnn.succ MLTTCumul_Sig (annotate' c)
  | Cst.natrec n mx m z sx sr s => @CstAnn.natrec MLTTCumul_Sig (annotate' n) mx (annotate' m) (annotate' z) sx sr (annotate' s)
  end.

Definition elaborate' (cst : Cst.obj) (ctx : list string) : option (exp MLTTCumul_Sig) :=
  elaborate (annotate' cst) ctx.
