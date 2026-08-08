From Coq Require Import String.
From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax System.
Import Syntax_Notations.

(** * Notation for annotated judgments *)

(** ** Context lookups *)
Reserved Notation "'`#' x : A @ so ∈ Δ @ annsΔ" (in custom judg at level 80, x constr at level 0, A custom exp, so constr, Δ custom exp, annsΔ custom exp).
Reserved Notation "'#' x : A '@' so ∈ Γ @ annsΓ" (in custom judg at level 80, x constr at level 0, A custom exp, so constr, Γ custom exp, annsΓ custom exp).
(** ** Well-formed contexts *)
Reserved Notation "⊫ Δ @ annsΔ" (in custom judg at level 80, Δ custom exp, annsΔ custom exp).
Reserved Notation "Δ @ annsΔ ⊫ Γ @ annsΓ" (in custom judg at level 80, Δ custom exp, annsΔ custom exp, Γ custom exp, annsΓ custom exp).
(** ** Well-formed expressions *)
Reserved Notation "Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so" (in custom judg at level 80, Δ custom exp, annsΔ custom exp, Γ custom exp, annsΓ custom exp, M custom exp, A custom exp, so custom exp).
(** ** Well-formed types *)
Reserved Notation "Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so" (in custom judg at level 80, Δ custom exp, annsΔ custom exp, Γ custom exp, annsΓ custom exp, A custom exp, so custom exp).
(** ** Well-formed substitutions *)
Reserved Notation "Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ'" (in custom judg at level 80, Δ custom exp, annsΔ custom exp, Γ custom exp, annsΓ custom exp, σ custom exp, Γ' custom exp, annsΓ' custom exp).

(** ** Shorthands for annotations *)
Notation gctx_anns := (fun (P : PtsSig) => list (SortOption P)%type).
Notation ctx_anns := (fun (P : PtsSig) => list (SortOption P)%type).
Notation typ_ann := (fun (P : PtsSig) => SortOption P).
  
Generalizable All Variables.

(** * Definitions of annotated judgments *)
(** Lookup in global contexts *)
Inductive gctx_lookup_ann {P : PtsSig} : string -> typ P -> typ_ann P -> gctx P -> gctx_anns P -> Prop :=
| ghere_ann : `( {{ `#x : A @ so ∈ Δ, x:A @ annsΔ, so }} )
| gthere_ann : `( {{ `#x : A @ so ∈ Δ @ annsΔ }} ->
                  x <> y ->
                  {{ `#x : A @so ∈ Δ, y:B @ annsΔ, so' }} )
where "'`#' x : A @ so ∈ Δ @ annsΔ" := (gctx_lookup_ann x A so Δ annsΔ) (in custom judg).

#[export]
Hint Constructors gctx_lookup_ann : mcpts.
 
(** Lokup in local contexts *)
Inductive ctx_lookup_ann {P : PtsSig} : nat -> typ P -> typ_ann P -> ctx P -> ctx_anns P -> Prop :=
| here_ann : `( {{ #0 : A[Wk] @ so ∈ Γ,A @ annsΓ, so }})
| there_ann : `( {{ #n : A @ so ∈ Γ @ annsΓ }} -> {{ #(S n) : A[Wk] @ so ∈ Γ, B @ annsΓ, so' }} )
where "'#' x : A '@' so ∈ Γ @ annsΓ" := (ctx_lookup_ann x A so Γ annsΓ) (in custom judg).

#[export]
Hint Constructors ctx_lookup_ann : mcpts.

Inductive wf_gctx_ann {P : PtsSig} : gctx P -> gctx_anns P -> Prop :=
| wf_gctx_empty_ann : {{ ⊫ ⋅ @ ⋅ }}
| wf_gctx_extend_ann :
  `( {{ ⊫ Δ @ annsΔ }} ->
     {{ Δ @ annsΔ ; ⋅ @ ⋅ ⊫ A @ so }} ->
     {{ `#x ∉ Δ }} ->
     {{ ⊫ Δ, x:A @ annsΔ , so }} )
where "⊫ Δ @ annsΔ" := (wf_gctx_ann Δ annsΔ) (in custom judg)

with wf_ctx_ann {P : PtsSig} : gctx P -> gctx_anns P -> ctx P -> ctx_anns P -> Prop :=
| wfa_ctx_empty :
  `( {{ ⊫ Δ @ annsΔ }} ->
     {{ Δ @ annsΔ ⊫ ⋅ @ ⋅ }} )
| wfa_ctx_enxtend :
  `( {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }} ->
     {{ Δ @ annsΔ ⊫ Γ, A @ annsΓ, so }} )
where "Δ @ annsΔ ⊫ Γ @ annsΓ" := (wf_ctx_ann Δ annsΔ Γ annsΓ) (in custom judg) : type_scope

with wf_exp_ann {P : PtsSig} : gctx P -> gctx_anns P -> ctx P -> ctx_anns P -> typ P -> typ_ann P -> exp P -> Prop :=
(** Sorts *)
| wf_exp_st_ann :
  `( Ax_typ P s1 s2 ->
     {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ Sort@s1 : Sort@s2 @ ^so_None }} )

(** Functions *)
| wf_exp_pi_ann :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A : Sort@s1 @ so1 }} ->
        {{ Δ @ annsΔ ; Γ, A @ annsΓ, ^(so_Some s1) ⊫ B : Sort@s2 @ so2 }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ Π r A B : Sort@s3 @ ^so_None }} )
| wf_exp_fn_ann :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A : Sort@s1 @ so1 }} ->
        {{ Δ @ annsΔ ; Γ, A @ annsΓ, ^(so_Some s1) ⊫ B : Sort@s2 @ so2 }} ->
        {{ Δ @ annsΔ ; Γ, A @ annsΓ, ^(so_Some s1) ⊫ M : B @ ^(so_Some s2) }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ λ r A B M : Π r A B @ ^(so_Some s3) }} )
| wf_exp_app_ann :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A : Sort@s1 @ so1 }} ->
        {{ Δ @ annsΔ ; Γ, A @ annsΓ, ^(so_Some s1) ⊫ B : Sort@s2 @ so2 }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : Π r A B @ ^(so_Some s3) }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ N : A @ ^(so_Some s1) }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M N : B[Id,,N] @ ^(so_Some s2) }} )

(** Variables *)
| wf_exp_vlookup_ann :
  `( {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} ->
     {{ #x : A@so ∈ Γ @ annsΓ }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ #x : A @ so }} )
| wf_exp_gvlookup_ann :
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : ⋅ @ ⋅ }} ->
     {{ `#x : A @ so ∈ Δ @ annsΔ }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ `#x : A[σ] @ so }} )
   
(** Naturals *)
| wf_exp_nat_ann :
  `( forall (r : Ru_nat P sn),
        {{ Δ @ annsΔ ⊫ Γ @ annsΓ}} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ ℕ : Sort@sn @ ^so_None }} )
| wf_exp_zero_ann :
  `( forall (r : Ru_nat P sn),
        {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ zero : ℕ @ ^(so_Some sn) }} )
| wf_exp_succ_ann :
  `( forall (r : Ru_nat P sn),
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : ℕ @ ^(so_Some sn) }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ succ M : ℕ @ ^(so_Some sn) }} )
| wf_exp_rec_ann :
  `( forall (r : Ru_nat P sn),
        {{ Δ @ annsΔ ; Γ, ℕ @ annsΓ, ^(so_Some sn) ⊫ A @ so }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ MZ : A[Id,,zero] @ so' }} ->
        {{ Δ @ annsΔ ; Γ, ℕ, A @ annsΓ, ^(so_Some sn), so ⊫ MS : A[Wk∘Wk,,succ #1] @ so''  }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : ℕ @ ^(so_Some sn) }} ->
        {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] @ so }} )

(** explicit substitutions *)
| wf_exp_sub_ann:
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} ->
     {{ Δ @ annsΔ ; Γ' @ annsΓ' ⊫ M : A @ so }} ->
     {{ Δ @ annsΔ ; Γ' @ annsΓ' ⊫ A @ so }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M[σ] : A[σ] @ so }} )

(** Conversions *)
| wf_exp_conv_ann :
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A' @ so' }} ->
     {{ Δ ; Γ ⊢ A ⊆ A' }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A' @ so' }} )
| wfa_exp_conv_annotation :
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so' }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so' }} )
where "Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so" := (wf_exp_ann Δ annsΔ Γ annsΓ A so M) (in custom judg)

with wf_typ_ann {P : PtsSig} : gctx P -> gctx_anns P -> ctx P -> ctx_anns P -> typ P -> typ_ann P -> Prop :=
| wf_typ_st_ann :
  `( {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ Sort@s @ ^so_None }} )
| wf_typ_exp_ann :
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A : Sort@s @ so }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ ^(so_Some s) }} )
| wf_typ_sub_ann :
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} ->
     {{ Δ @ annsΔ ; Γ' @ annsΓ' ⊫ A @ so}} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A[σ] @ so }} )
where "Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so" := (wf_typ_ann Δ annsΔ Γ annsΓ A so) (in custom judg)

with wf_sub_ann {P : PtsSig} : gctx P -> gctx_anns P -> ctx P -> ctx_anns P -> ctx P -> ctx_anns P -> sub P -> Prop :=
| wf_sub_id_ann :
  `( {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s Id : Γ @ annsΓ }} )
| wfa_sub_weaken :
  `( {{ Δ @ annsΔ ⊫ Γ, A @ annsΓ, so }} ->
     {{ Δ @ annsΔ ; Γ, A @ annsΓ, so ⊫s Wk : Γ @ annsΓ }} )
| wfa_sub_compose :
  `( {{ Δ @ annsΔ ; Γ1 @ annsΓ1 ⊫s σ2 : Γ2 @ annsΓ2 }} ->
     {{ Δ @ annsΔ ; Γ2 @ annsΓ2 ⊫s σ1 : Γ3 @ annsΓ3 }} ->
     {{ Δ @ annsΔ ; Γ1 @ annsΓ1 ⊫s σ1∘σ2 : Γ3 @ annsΓ3 }} )
| wfa_sub_extend :
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} ->
     {{ Δ @ annsΔ ; Γ' @ annsΓ' ⊫ A @ so }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A[σ] @ so }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ,,M : Γ', A @ annsΓ', so  }} )
| wfa_sub_conv :
  `( {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} ->
     {{ Δ @ annsΔ ⊫ Γ'' @ annsΓ'' }} ->
     {{ Δ ⊢ Γ' ⊆ Γ'' }} ->
     {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ'' @ annsΓ'' }} )
where "Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ'" := (wf_sub_ann Δ annsΔ Γ annsΓ Γ' annsΓ' σ) (in custom judg).

#[export]
Hint Constructors wf_gctx_ann wf_ctx_ann wf_exp_ann wf_typ_ann wf_sub_ann : mcpts.


Scheme wf_gctx_ann_mut_ind := Induction for wf_gctx_ann Sort Prop
with wf_ctx_ann_mut_ind := Induction for wf_ctx_ann Sort Prop
with wf_exp_ann_mut_ind := Induction for wf_exp_ann Sort Prop
with wf_typ_ann_mut_ind := Induction for wf_typ_ann Sort Prop
with wf_sub_ann_mut_ind := Induction for wf_sub_ann Sort Prop.
Combined Scheme syntactic_wf_ann_mut_ind from
  wf_gctx_ann_mut_ind,
  wf_ctx_ann_mut_ind,
  wf_exp_ann_mut_ind,
  wf_typ_ann_mut_ind,
  wf_sub_ann_mut_ind.
