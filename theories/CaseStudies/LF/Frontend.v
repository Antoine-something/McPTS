From Stdlib Require Import List String PeanoNat MSets FunInd.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax.
From McPTS.Frontend Require Import Elaborator.
From McPTS.CaseStudies.LF Require Import Signature.

(** * Concrete Syntax Tree *)
Module Cst.
  Inductive obj : Set :=
  (** Sorts *)
  | s_typ : obj
  | s_knd : obj
  (** Functions, with codomain sort annotation *)
  | pi : string -> obj -> obj -> obj -> obj -> obj
  | fn : string -> obj -> obj -> obj -> obj -> obj -> obj
  | app : obj -> obj -> obj
  (** Variables *)
  | var : string -> obj
  (** Natural numbers *)
  | nat : obj
  | zero : obj
  | succ : obj -> obj
  | natrec : obj -> string -> obj -> obj -> string -> string -> obj -> obj.
End Cst.


Fixpoint annotate' (cst : Cst.obj) : option (CstAnn.obj LF_Sig) :=
  match cst with
  (* Sorts *)
  | Cst.s_typ => Some (@CstAnn.st LF_Sig s_typ)
  | Cst.s_knd => Some (@CstAnn.st LF_Sig s_knd)
  (* Functions *)
  | Cst.pi s s1 s2 t c =>
      match (annotate' t), (annotate' c) with
      | Some t, Some c =>
          match s1, s2 with
          | Cst.s_typ, Cst.s_typ => Some (@CstAnn.pi LF_Sig _ _ _ f_simple s t c)
          | Cst.s_typ, Cst.s_knd => Some (@CstAnn.pi LF_Sig _ _ _ f_dep s t c)
          | Cst.s_knd, Cst.s_knd => Some (@CstAnn.pi LF_Sig _ _ _ f_def s t c)
          | _, _ => None
          end
      | _, _ => None
      end
  | Cst.fn s s1 s2 t b c =>
      match (annotate' t), (annotate' b), (annotate' c) with
      | Some t, Some b, Some c =>
          match s1, s2 with
          | Cst.s_typ, Cst.s_typ => Some (@CstAnn.fn LF_Sig _ _ _ f_simple s t b c)
          | Cst.s_typ, Cst.s_knd => Some (@CstAnn.fn LF_Sig _ _ _ f_dep s t b c)
          | Cst.s_knd, Cst.s_knd => Some (@CstAnn.fn LF_Sig _ _ _ f_def s t b c)
          | _, _ => None
          end
      | _, _, _ => None
      end
  | Cst.app c1 c2 =>
      match (annotate' c1), (annotate' c2) with
      | Some c1, Some c2 => Some (@CstAnn.app LF_Sig c1 c2)
      | _, _ => None
  end
  (* Variables *)
  | Cst.var x => Some (@CstAnn.var LF_Sig x)
  (* Natural numbers *)
  | Cst.nat => Some (@CstAnn.nat LF_Sig)
  | Cst.zero => Some (@CstAnn.zero LF_Sig)
  | Cst.succ c =>
      match annotate' c with
      | Some c => Some (@CstAnn.succ LF_Sig c)
      | None => None
      end
  | Cst.natrec n mx m z sx sr s =>
      match (annotate' n), (annotate' m), (annotate'  z), (annotate' s) with
      | Some n, Some m, Some z, Some s => Some (@CstAnn.natrec LF_Sig n mx m z sx sr s)
      | _, _, _, _ => None
      end
  end.

Definition elaborate' (cst : Cst.obj) (ctx : list string) : option (exp LF_Sig) :=
  match annotate' cst with
  | Some cst => elaborate cst ctx
  | _ => None
  end.
