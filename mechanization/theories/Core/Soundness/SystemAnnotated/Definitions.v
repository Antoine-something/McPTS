From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax System Corollaries.
Import Syntax_Notations.


Reserved Notation "⊫ Γ > sts " (in custom judg at level 80, Γ custom exp, sts constr).
Reserved Notation "Γ : sts ⊫ M : A > s" (in custom judg at level 80, Γ custom exp, sts constr, M custom exp, A custom exp, s constr).
Reserved Notation "Γ : sts ⊫ A > s" (in custom judg at level 80, Γ custom exp, sts constr, A custom exp, s constr).
Reserved Notation "Γ : stsΓ ⊫s σ : Δ > stsΔ" (in custom judg at level 80, Γ custom exp, stsΓ constr, σ custom exp, Δ custom exp, stsΔ constr).
(* Reserved Notation "'#' x : A > s ∈ Γ : sts" (in custom judg at level 80, x constr at level 0, A custom exp, s constr, Γ custom exp at level 50, sts constr). *)

Generalizable All Variables.

(* Inductive ctx_lookup_ann {P} : nat -> typ P -> P -> ctx P -> list P -> Prop :=  *)
(* | here_a : `({{ #0 : A > s ∈ Γ, A : s :: sts }} ) *)
(* | there_a : `({{ #n : A > s ∈ Γ : sts }} -> {{ #(S n) : A[Wk] > s ∈ Γ, B : (sb :: sts) }}) *)
(* where "'#' x : A > s ∈ Γ : sts" := (ctx_lookup_ann x A s Γ sts) (in custom judg) : type_scope. *)



Inductive wf_ctx_ann {P} : ctx P -> list P -> Prop :=
| wfa_ctx_empty : {{ ⊫ ⋅ > nil }}
| wfa_ctx_extend :
  `( {{ ⊫ Γ > sts }} ->
     {{ Γ : sts ⊫ A : Sort@s > s' }} ->
     {{ ⊫ Γ, A > (s :: sts) }} )
where "⊫ Γ > sts" := (wf_ctx_ann Γ sts) (in custom judg) : type_scope

with wf_exp_ann {P} : ctx P -> list P -> exp P -> P -> exp P -> Prop :=
| wfa_st :
  `( Ax P s1 s2 -> Ax P s2 s3 ->
     {{ ⊫ Γ > sts }} ->
     {{ Γ : sts ⊫ Sort@s1 : Sort@s2 > s3 }} )
(** Functions *)
| wfa_pi :
  `( forall (r : Ru P s1 s2 s3),
        Ax P s3 s3' ->
        {{ Γ : sts ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ : sts ⊫ Π A B : Sort@s3 > s3' }} )
| wfa_fn :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ : sts ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ M : B > s2 }} ->
        {{ Γ : sts ⊫ λ A M : Π A B > s3 }} )
| wfa_app :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ : sts ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ : sts ⊫ M : Π A B > s3 }} ->
        {{ Γ : sts ⊫ N : A > s1 }} ->
        {{ Γ : sts ⊫ M N : B[Id,,N] > s2 }} )
   
| wfa_vlookup :
  `( {{ ⊫ Γ > sts }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ : sts ⊫ A : Sort@s > s' }} ->
     {{ Γ : sts ⊫ #x : A > s }} )
   
(** Naturals *)
(* | wfa_nat : *)
(*   `( forall (r : Ru_nat P sn), *)
(*         Ax P sn sn' -> *)
(*         {{ ⊫ Γ > sts }} -> *)
(*         {{ Γ : sts ⊫ ℕ : Sort@sn > sn' }} ) *)
(* | wfa_zero : *)
(*   `( forall (r : Ru_nat P sn), *)
(*         {{ ⊫ Γ > sts }} -> *)
(*         {{ Γ : sts ⊫ zero : ℕ > sn }} ) *)
(* | wfa_succ : *)
(*   `( forall (r : Ru_nat P sn), *)
(*         {{ Γ : sts ⊫ M : ℕ > sn' }} -> *)
(*         {{ Γ : sts ⊫ succ M : ℕ > sn }} ) *)
(* | wfa_rec : *)
(*   `( forall (r : Ru_nat P sn), *)
(*         {{ Γ, ℕ : (sn :: sts) ⊫ A : Sort@sa > sa' }} -> *)
(*         {{ Γ : sts ⊫ MZ : A[Id,,zero] > sa }} -> *)
(*         {{ Γ, ℕ, A : (sa :: (sn :: sts)) ⊫ MS : A[Wk∘Wk,,succ #1] > sa }} -> *)
(*         {{ Γ : sts ⊫ M : ℕ > sn }} -> *)
(*         {{ Γ : sts ⊫ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] > sa }} ) *)

| wfa_exp_sub :
  `( {{ Γ : sts ⊫s σ : Δ > sts' }} ->
     {{ Δ : sts' ⊫ M : A > s }} ->
     {{ Γ : sts ⊫ M[σ] : A[σ] > s }} )

| wfa_exp_conv :
  `( {{ Γ : sts ⊫ M : A > s }} ->
     {{ Γ ⊢ A ≈ A' }} ->
     {{ Γ : sts ⊫ M : A' > s }} )
| wfa_exp_conv_st :
  `( {{ Γ : sts ⊫ M : A > s }} ->
     {{ Γ : sts ⊫ A > s' }} ->
     {{ Γ : sts ⊫ M : A > s' }} )
where "Γ : sts ⊫ M : A > s" := (wf_exp_ann Γ sts A s M) (in custom judg) : type_scope

with wf_typ_ann {P} : ctx P -> list P -> typ P -> P -> Prop :=
| wfa_typ_st :
  `( Ax P s s' ->
     {{ ⊫ Γ > sts }} ->
     {{ Γ : sts ⊫ Sort@s > s' }} )
| wfa_typ_exp :
  `( {{ Γ : sts ⊫ A : Sort@s > s' }} ->
     {{ Γ : sts ⊫ A > s }} )
| wfa_typ_clo :
  `( {{ Γ : sts ⊫s σ : Δ > sts' }} ->
     {{ Δ : sts' ⊫ A > s }} ->
     {{ Γ : sts ⊫ A[σ] > s }} )
where "Γ : sts ⊫ A > s" := (wf_typ_ann Γ sts A s) (in custom judg) : type_scope
                                                                             
with wf_sub_ann {P} : ctx P -> list P -> ctx P -> list P -> sub P -> Prop :=
| wfa_sub_id :
  `( {{ ⊫ Γ > sts }} ->
     {{ Γ : sts ⊫s Id : Γ > sts }} )
| wfa_sub_weaken :
  `( {{ ⊫ Γ, A > s :: sts }} ->
     {{ Γ, A : s :: sts ⊫s Wk : Γ > sts }} )
| wfa_sub_compose :
  `( {{ Γ1 : sts1 ⊫s σ2 : Γ2 > sts2 }} ->
     {{ Γ2 : sts2 ⊫s σ1 : Γ3 > sts3 }} ->
     {{ Γ1 : sts1 ⊫s σ1∘σ2 : Γ3 > sts3 }} )
| wfa_sub_extend :
  `( {{ Γ : stsΓ ⊫s σ : Δ > stsΔ }} ->
     {{ Δ : stsΔ ⊫ A : Sort@s > s' }} ->
     {{ Γ : stsΓ ⊫ M : A[σ] > s }} ->
     {{ Γ : stsΓ ⊫s σ,,M : Δ, A > s :: stsΔ }} )
| wfa_sub_conv :
  `( {{ Γ : stsΓ ⊫s σ : Δ > stsΔ }} ->
     {{ ⊫ Δ' > stsΔ' }} ->
     {{ ⊢ Δ ≈ Δ' }} ->
     {{ Γ : stsΓ ⊫s σ : Δ' > stsΔ' }} )
| wfa_sub_conv_sts :
  `( {{ Γ : stsΓ ⊫s σ : Δ > stsΔ }} ->
     {{ ⊫ Δ > stsΔ' }} ->
     {{ Γ : stsΓ ⊫s σ : Δ > stsΔ' }} )
where "Γ : stsΓ ⊫s σ : Δ > stsΔ" := (wf_sub_ann Γ stsΓ Δ stsΔ σ) (in custom judg) : type_scope.

#[export]
Hint Constructors wf_ctx_ann wf_exp_ann wf_typ_ann wf_sub_ann : mcpts.

Scheme wf_ctx_ann_mut_ind := Induction for wf_ctx_ann Sort Prop
with wf_exp_ann_mut_ind := Induction for wf_exp_ann Sort Prop
with wf_sub_ann_mut_ind := Induction for wf_sub_ann Sort Prop.                                          
Combined Scheme syntactic_wf_ann_mut_ind from
  wf_ctx_ann_mut_ind,
  wf_exp_ann_mut_ind,
  wf_sub_ann_mut_ind.
