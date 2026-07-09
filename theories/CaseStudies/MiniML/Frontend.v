From Coq Require Import List String PeanoNat MSets FunInd.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax.
From McPTS.Frontend Require Import Elaborator.
From McPTS.CaseStudies.MiniML Require Import Signature.

(** * Concrete Syntax Tree *)
Module Cst.
  Inductive obj : Set :=
  (** Sorts *)
  | st : obj
  (** Functions, without rule annotations (it can be inferred since there is only one possible rule) *)
  | pi : string -> obj -> obj -> obj
  | fn : string -> obj -> obj -> obj -> obj
  | app : obj -> obj -> obj
  (** Variables *)
  | var : string -> obj
  (** Natural numbers *)
  | nat : obj
  | zero : obj
  | succ : obj -> obj
  | natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj.  
End Cst.

Fixpoint annotate' (cst : Cst.obj) : CstAnn.obj MiniML_Sig :=
  match cst with
  (* Sort *)
  | Cst.st => @CstAnn.st MiniML_Sig s_typ
  (* Functions *)
  | Cst.pi s t c =>
      @CstAnn.pi MiniML_Sig _ _ _ f_simple s (annotate' t) (annotate' c)
  | Cst.fn s t b c =>
      @CstAnn.fn MiniML_Sig _ _ _ f_simple s (annotate' t) (annotate' b) (annotate' c)
  | Cst.app c1 c2 => @CstAnn.app MiniML_Sig (annotate' c1) (annotate' c2)
  (* Variables *)
  | Cst.var x => @CstAnn.var MiniML_Sig x
  (* Natural numbers *)
  | Cst.nat => @CstAnn.nat MiniML_Sig
  | Cst.zero => @CstAnn.zero MiniML_Sig
  | Cst.succ c => @CstAnn.succ MiniML_Sig (annotate' c)
  | Cst.natrec n mx m z sx sr s =>
      @CstAnn.natrec MiniML_Sig (annotate' n) mx (annotate' m) (annotate' z) sx sr (annotate' s)
  end.

Definition elaborate' (cst : Cst.obj) (ctx : list string) : option (exp MiniML_Sig) :=
  elaborate (annotate' cst) ctx.
