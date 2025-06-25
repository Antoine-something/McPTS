From McPTS.Core Require Import Base.
From McPTS.Core.PTSSignature Require Import Signature.

Module SyntaxFunctor (P : PtsSig).
  Import P.

  (* Expressions M,N,A,B *)
  Inductive Exp : Type :=
  | a_st : St -> Exp                                             (* s *)
  | a_var : nat -> Exp                                            (* x_i *)
  | a_pi : forall (s1 s2 s3 : St), Ru s1 s2 s3 -> Exp -> Exp -> Exp   (* Π_r A.B *)
  | a_lam : Exp -> Exp                                           (* λM *)
  | a_app : Exp -> Exp -> Exp                                    (* M N *)
  | a_clo : Sub -> Exp -> Exp                                    (* [σ]M *)

  (* Substitutions σ,τ*)
  with Sub : Type :=
  | a_id : Sub                                                   (* id *)
  | a_wk : Sub                                                   (* wk *)
  | a_empty : Sub                                                (* .. *)
  | a_ext : Sub -> Exp -> Sub                                     (* σ, M *)
  | a_comp : Sub -> Sub -> Sub.                                   (* σ ∘ τ *) 

  (* Typ is syntactic sugar to help differentiate terms and types *)
  Notation Typ := Exp.

  (* Contexts Γ,Δ *)
  (*
   *  I originally want to define Ctx as (list (Typ * St)).
   *  For some reason, whenever I use this Ctx, Coq complains that ""Typ" has type "Type" while it is expected to have type "nat""
   *  Defining it directly as an inductive type fixes the issue, but will it cause problems later on?
   *)
  Inductive Ctx : Type :=
  | a_nil : Ctx
  | a_cons : Ctx -> Exp -> St -> Ctx.

  Fixpoint length (Γ : Ctx) : nat :=
    match Γ with
    | a_nil => 0
    | a_cons Γ _ _ => S (length Γ)
    end.

  (* Notation Ctx := (list (Typ * St)). *)
  

  (* Neutral forms E *)
  Inductive Ne : Type :=
  | ne_var : nat -> Ne                                             (* x_i *)
  | ne_app : Ne -> Nf -> Ne                                       (* E V *)
                         
  (* Normal forms V *)
  with Nf : Type :=
  | nf_ne : Ne -> Nf                                              (* E *)
  | nf_st : St -> Nf                                              (* s *)
  | nf_pi : forall (s1 s2 s3 : St), Ru s1 s2 s3 -> Nf -> Nf -> Nf       (* Π_r V1.V2 *)
  | nf_lam : Nf -> Nf.                                            (* λV *)


  (* Coercion of neutral and normal forms into expressions.  Basically identity functions *)
  Fixpoint Ne_to_Exp (E : Ne) : Exp :=
    match E with
    | ne_var i => a_var i
    | ne_app E' V => a_app (Ne_to_Exp E') (Nf_to_Exp V)
    end
  with Nf_to_Exp (V : Nf) : Exp :=
    match V with
    | nf_ne E => Ne_to_Exp E
    | nf_st s => a_st s
    | nf_pi s1 s2 s3 r V1 V2 => a_pi s1 s2 s3 r (Nf_to_Exp V1) (Nf_to_Exp V2)
    | nf_lam V => a_lam (Nf_to_Exp V)
    end.

  Coercion Nf_to_Exp : Nf >-> Exp.
  Coercion Ne_to_Exp : Ne >-> Exp.

  (* Convenient notation for writing expressions *)
  (* #[global] Declare Custom Entry Exp. *)
  (* #[global] Declare Custom Entry Nf. *)

  #[global] Bind Scope mctt_scope with Exp.
  #[global] Bind Scope mctt_scope with Sub.
  #[global] Bind Scope mctt_scope with Nf.
  #[global] Bind Scope mctt_scope with Ne.
  Open Scope mctt_scope.

  (* We need to define substitution notation first to assert [left associativity] of level 0. *)
  Notation "[ σ ] e" := (a_clo σ e) (in custom Exp at level 0, e custom Exp, σ custom Exp at level 60, left associativity, format "[ σ ] e") : mctt_scope.
  Notation "{{{ x }}}" := x (at level 0, x custom Exp at level 99, format "'{{{'  x  '}}}'") : mctt_scope.
  Notation "( x )" := x (in custom Exp at level 0, x custom Exp at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom Exp at level 0, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom Exp at level 0, x ident) : mctt_scope.

  Notation "'Sort' @ s" := (a_st s) (in custom Exp at level 0, s constr at level 0, format "'Sort' @ s") : mctt_scope.
  Notation "'#' i" := (a_var i) (in custom Exp at level 0, i constr at level 0, format "'#' i") : mctt_scope.  
  Notation "'Π' r A B" := (a_pi _ _ _ r A B) (in custom Exp at level 1, r constr at level 0, A custom Exp at level 0, B custom Exp at level 60) : mctt_scope.
  Notation "'λ' M" := (a_lam M) (in custom Exp at level 1, M custom Exp at level 60) : mctt_scope.
  Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom Exp at level 40, f custom Exp, x custom Exp at next level, y custom Exp at next level) : mctt_scope.

  (* Notation for substitutions *)
  Notation "'Id'" := a_id (in custom Exp at level 0) : mctt_scope.
  Notation "'Wk'" := a_wk (in custom Exp at level 0) : mctt_scope.
  Notation "'..'" := a_empty (in custom Exp at level 0) : mctt_scope.
  Notation "σ ∘ τ" := (a_comp σ τ) (in custom Exp at level 40, right associativity, format "σ ∘ τ") : mctt_scope.
  Notation "σ ,, e" := (a_ext σ e) (in custom Exp at level 50, left associativity, format "σ ,, e") : mctt_scope.

  (* Notation for contexts *)
  Notation "⋅" := (a_nil) (in custom Exp at level 0) : mctt_scope.
  Notation "Γ , A : s" := (a_cons Γ A s) (in custom Exp at level 50, left associativity, format "Γ ,  A : s") : mctt_scope.


  (* Notation for normal and neutral forms *)
  Notation "n{{{ x }}}" := x (at level 0, x custom Nf at level 99, format "'n{{{'  x  '}}}'") : mctt_scope.
  Notation "( x )" := x (in custom Nf at level 0, x custom Nf at level 60) : mctt_scope.
  Notation "'^' x" := x (in custom Nf at level 0, x constr at level 0) : mctt_scope.
  Notation "x" := x (in custom Nf at level 0, x ident) : mctt_scope.

  Notation "'Sort' @ s" := (nf_st s) (in custom Nf at level 0, s constr at level 0, format "'Sort' @ s") : mctt_scope.
  Notation "'Π' r V1 V2" := (nf_pi _ _ _ r V1 V2) (in custom Nf at level 2, V1 custom Nf at level 1, V2 custom Nf at level 60) : mctt_scope.
  Notation "'λ' V" := (nf_lam V) (in custom Nf at level 2, V custom Nf at level 60) : mctt_scope.
  Notation "f x .. y" := (ne_app .. (ne_app f x) .. y) (in custom Nf at level 40, f custom Nf, x custom Nf at next level, y custom Nf at next level) : mctt_scope.
  Notation "'#' i" := (ne_var i) (in custom Nf at level 0, i constr at level 0, format "'#' i") : mctt_scope.
  Notation "'⇑' E" := (nf_ne E) (in custom Nf at level 0, E custom Nf at level 99, format "'⇑'  E") : mctt_scope.
End SyntaxFunctor.
