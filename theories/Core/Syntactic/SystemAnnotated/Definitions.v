From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax System.
Import Syntax_Notations.

Reserved Notation "⊫ Γ 'with' anns" (in custom judg at level 80, Γ custom exp, anns constr).
Reserved Notation "Γ 'with' anns ⊫ M : A @ s" (in custom judg at level 80, Γ custom exp, anns constr, M custom exp, A custom exp, s custom exp).
Reserved Notation "Γ 'with' anns ⊫ A @ s" (in custom judg at level 80, Γ custom exp, anns constr, A custom exp, s custom exp).
Reserved Notation "Γ 'with' anns ⊫s σ : Δ 'with' anns'" (in custom judg at level 80, Γ custom exp, anns constr, σ custom exp, Δ custom exp, anns' constr).
Reserved Notation "'#' x : A '@' so ∈ Γ 'with' anns" (in custom judg at level 80, x constr at level 0, so constr, anns constr, A custom exp, Γ custom exp at level 50).
Notation ctx_anns := (fun (P : PtsSig) => list (SortOption P)%type).

Generalizable All Variables.

Inductive anns_lookup {P : PtsSig} : nat -> typ P -> SortOption P -> ctx_anns P -> ctx P -> Prop :=
| here : `( {{ #0 : A[Wk] @ so ∈ Γ,A with (so::anns) }})
| there : `( {{ #n : A @ so ∈ Γ with anns }} -> {{ #(S n) : A[Wk] @ so ∈ Γ, B with (so'::anns) }} )
where "'#' x : A '@' so ∈ Γ 'with' anns" := (anns_lookup x A so anns Γ) (in custom judg).

#[export]
Hint Constructors anns_lookup : mcpts.

Inductive wf_ctx_ann {P} : ctx_anns P -> ctx P -> Prop :=
| wfa_ctx_empty : {{ ⊫ ⋅ with nil}}
| wfa_ctx_enxtend :
  `( {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫ A @ so }} ->
     {{ ⊫ Γ, A with so::anns }} )
where "⊫ Γ 'with' anns" := (wf_ctx_ann anns Γ) (in custom judg) : type_scope
with wf_exp_ann {P} : ctx_anns P -> ctx P -> typ P -> SortOption P -> exp P -> Prop :=
(** Sorts *)
| wfa_st :
  `( Ax_typ P s1 s2 ->
     {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫ Sort@s1 : Sort@s2 @ ^so_None }} )

(** Functions *)
| wfa_pi :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ Π r A B : Sort@s3 @ ^so_None }} )
| wfa_fn :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ M : B @ ^(so_Some s2) }} ->
        {{ Γ with anns ⊫ λ r A B M : Π r A B @ ^(so_Some s3) }} )
| wfa_app :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ M : Π r A B @ ^(so_Some s3) }} ->
        {{ Γ with anns ⊫ N : A @ ^(so_Some s1) }} ->
        {{ Γ with anns ⊫ M N : B[Id,,N] @ ^(so_Some s2) }} )

(** Sigmas *)
| wfa_sigma :
  `( forall (r : Ru_sigma P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ Σ r A B : Sort@s3 @ ^so_None }} )
| wfa_pair :
  `( forall (r : Ru_sigma P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ M : A @ ^(so_Some s1) }} ->
        {{ Γ with anns ⊫ N : B[Id,,M] @ ^(so_Some s2) }} ->
        {{ Γ with anns ⊫ ⟨r; M : A; N : B⟩ : Σ r A B @ ^(so_Some s3) }} )
| wfa_fst :
  `( forall (r : Ru_sigma P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ M : Σ r A B @ ^(so_Some s3) }} ->
        {{ Γ with anns ⊫ fst M : A @ ^(so_Some s1) }} )
| wfa_snd :
  `( forall (r : Ru_sigma P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (so_Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ M : Σ r A B @ ^(so_Some s3) }} ->
        {{ Γ with anns ⊫ snd M : B[Id,,fst M] @ ^(so_Some s2) }} )
(** Variables *)
| wfa_vlookup :
  `( {{ ⊫ Γ with anns }} ->
     {{ #x : A@so ∈ Γ with anns }} ->
     {{ Γ with anns ⊫ #x : A @ so }} )

(** Naturals *)
| wfa_nat :
  `( forall (r : Ru_nat P sn),
        {{ ⊫ Γ with anns}} ->
        {{ Γ with anns ⊫ ℕ : Sort@sn @ ^so_None }} )
| wfa_zero :
  `( forall (r : Ru_nat P sn),
        {{ ⊫ Γ with anns }} ->
        {{ Γ with anns ⊫ zero : ℕ @ ^(so_Some sn) }} )
| wfa_succ :
  `( forall (r : Ru_nat P sn),
        {{ Γ with anns ⊫ M : ℕ @ ^(so_Some sn) }} ->
        {{ Γ with anns ⊫ succ M : ℕ @ ^(so_Some sn) }} )
| wfa_rec :
  `( forall (r : Ru_nat P sn),
        {{ Γ, ℕ with (so_Some sn)::anns ⊫ A @ so }} ->
        {{ Γ with anns ⊫ MZ : A[Id,,zero] @ so }} ->
        {{ Γ, ℕ, A with so ::(so_Some sn)::anns ⊫ MS : A[Wk∘Wk,,succ #1] @ so  }} ->
        {{ Γ with anns ⊫ M : ℕ @ ^(so_Some sn) }} ->
        {{ Γ with anns ⊫ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] @ so }} )

(** explicit substitutions *)
| wfa_exp_sub:
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ Δ with anns' ⊫ M : A @ so }} ->
     {{ Δ with anns' ⊫ A @ so }} ->
     {{ Γ with anns ⊫ M[σ] : A[σ] @ so }} )

(** Conversions *)
| wfa_exp_conv :
  `( {{ Γ with anns ⊫ M : A @ so }} ->
     {{ Γ with anns ⊫ A' @ so' }} ->
     {{ Γ ⊢ A ⊆ A' }} ->
     {{ Γ with anns ⊫ M : A' @ so' }} )
| wfa_exp_conv_ann :
  `( {{ Γ with anns ⊫ M : A @ so }} ->
     {{ Γ with anns ⊫ A @ so' }} ->
     {{ Γ with anns ⊫ M : A @ so' }} )
where "Γ 'with' anns ⊫ M : A @ so" := (wf_exp_ann anns Γ A so M) (in custom judg) : type_scope

with wf_typ_ann {P} : ctx_anns P -> ctx P -> typ P -> SortOption P -> Prop :=
| wfa_typ_st :
  `( {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫ Sort@s @ ^so_None }} )
| wfa_typ_exp :
  `( {{ Γ with anns ⊫ A : Sort@s @ so }} ->
     {{ Γ with anns ⊫ A @ ^(so_Some s) }} )
| wfa_typ_sub :
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ Δ with anns' ⊫ A @ so}} ->
     {{ Γ with anns ⊫ A[σ] @ so }} )
where "Γ 'with' anns ⊫ A @ so" := (wf_typ_ann anns Γ A so) (in custom judg) : type_scope
with wf_sub_ann {P} : ctx_anns P -> ctx_anns P -> ctx P -> ctx P -> sub P -> Prop :=
| wfa_sub_id :
  `( {{ ⊫ Γ with anns }} ->
     {{ Γ with anns ⊫s Id : Γ with anns }} )
| wfa_sub_weaken :
  `( {{ ⊫ Γ, A with so::anns }} ->
     {{ Γ, A with so::anns ⊫s Wk : Γ with anns}} )
| wfa_sub_compose :
  `( {{ Γ1 with anns1 ⊫s σ2 : Γ2 with anns2 }} ->
     {{ Γ2 with anns2 ⊫s σ1 : Γ3 with anns3 }} ->
     {{ Γ1 with anns1 ⊫s σ1∘σ2 : Γ3 with anns3 }} )
| wfa_sub_extend :
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ Δ with anns' ⊫ A @ so }} ->
     {{ Γ with anns ⊫ M : A[σ] @ so }} ->
     {{ Γ with anns ⊫s σ,,M : Δ, A with so::anns'  }} )
| wfa_sub_conv :
  `( {{ Γ with anns ⊫s σ : Δ with anns' }} ->
     {{ ⊫ Δ' with anns'' }} ->
     {{ ⊢ Δ ⊆ Δ' }} ->
     {{ Γ with anns ⊫s σ : Δ' with anns'' }} )
where "Γ 'with' anns ⊫s σ : Δ 'with' anns'" := (wf_sub_ann anns anns' Γ Δ σ) (in custom judg) : type_scope.


#[export]
Hint Constructors wf_ctx_ann wf_exp_ann wf_typ_ann wf_sub_ann : mcpts.


Scheme wf_ctx_ann_mut_ind := Induction for wf_ctx_ann Sort Prop
with  wf_exp_ann_mut_ind := Induction for wf_exp_ann Sort Prop
with wf_typ_ann_mut_ind := Induction for wf_typ_ann Sort Prop
with wf_sub_ann_mut_ind := Induction for wf_sub_ann Sort Prop.
Combined Scheme syntactic_wf_ann_mut_ind from
  wf_ctx_ann_mut_ind,
  wf_exp_ann_mut_ind,
  wf_typ_ann_mut_ind,
  wf_sub_ann_mut_ind.
