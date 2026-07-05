From Coq Require Import List Classes.RelationClasses Setoid Morphisms.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export Syntax System Corollaries.
From McPTS.Core.Soundness Require Import LogicalRelation.
Import Syntax_Notations.


Reserved Notation "⊫ Γ 'with' anns" (in custom judg at level 80, Γ custom exp, anns constr).
Reserved Notation "Γ 'with' anns ⊫ M : A @ s" (in custom judg at level 80, Γ custom exp, anns constr, M custom exp, A custom exp, s custom exp).
Reserved Notation "Γ 'with' anns ⊫ A @ s" (in custom judg at level 80, Γ custom exp, anns constr, A custom exp, s custom exp).
Reserved Notation "Γ 'with' anns ⊫s σ : Δ 'with' anns'" (in custom judg at level 80, Γ custom exp, anns constr, σ custom exp, Δ custom exp, anns' constr).

Generalizable All Variables.

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
     {{ Γ with anns ⊫ Sort@s1 : Sort@s2 @ ^None }} )

(** Functions *)
| wfa_pi :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ Π r A B : Sort@s3 @ ^None }} )
| wfa_fn :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ M : B @ ^(Some s2) }} ->
        {{ Γ with anns ⊫ λ r A B M : Π r A B @ ^(Some s3) }} )
| wfa_app :
  `( forall (r : Ru_pi P s1 s2 s3),
        {{ Γ with anns ⊫ A : Sort@s1 @ so1 }} ->
        {{ Γ, A with (Some s1)::anns ⊫ B : Sort@s2 @ so2 }} ->
        {{ Γ with anns ⊫ M : Π r A B @ ^(Some s3) }} ->
        {{ Γ with anns ⊫ N : A @ ^(Some s1) }} ->
        {{ Γ with anns ⊫ M N : B[Id,,N] @ ^(Some s2) }} )

(** Variables *)
| wfa_vlookup :
  `( {{ ⊫ Γ with anns }} ->
     {{ #x : A@so ∈ Γ with anns }} ->
     {{ Γ with anns ⊫ #x : A @ so }} )

(** Naturals *)
| wfa_nat :
  `( forall (r : Ru_nat P sn),
        {{ ⊫ Γ with anns}} ->
        {{ Γ with anns ⊫ ℕ : Sort@sn @ ^None }} )
| wfa_zero :
  `( forall (r : Ru_nat P sn),
        {{ ⊫ Γ with anns }} ->
        {{ Γ with anns ⊫ zero : ℕ @ ^(Some sn) }} )
| wfa_succ :
  `( forall (r : Ru_nat P sn),
        {{ Γ with anns ⊫ M : ℕ @ ^(Some sn) }} ->
        {{ Γ with anns ⊫ succ M : ℕ @ ^(Some sn) }} )
| wfa_rec :
  `( forall (r : Ru_nat P sn),
        {{ Γ, ℕ with (Some sn)::anns ⊫ A @ so }} ->
        {{ Γ with anns ⊫ MZ : A[Id,,zero] @ so }} ->
        {{ Γ, ℕ, A with so ::(Some sn)::anns ⊫ MS : A[Wk∘Wk,,succ #1] @ so  }} ->
        {{ Γ with anns ⊫ M : ℕ @ ^(Some sn) }} ->
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
     {{ Γ with anns ⊫ Sort@s @ ^None }} )
| wfa_typ_exp :
  `( {{ Γ with anns ⊫ A : Sort@s @ so }} ->
     {{ Γ with anns ⊫ A @ ^(Some s) }} )
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

#[local]
Ltac apply_fullness_once P full_P H :=
  match type of H with
  | Ax_typ P ?s1 ?s2 =>
      let s2' := fresh "s2'" in
      assert (exists s2', Ax_typ P s2 s2') as [s2'] by (eapply full_P)
  | Ru_pi P ?s1 ?s2 ?s3 =>
      let s3' := fresh "s3'" in
      assert (exists s3', Ax_typ P s3 s3') as [s3'] by (eapply full_P)
  | _ => idtac
  end.

#[local]
Ltac apply_fullness_all P full_P :=
  on_all_hyp: (fun H => apply_fullness_once P full_P H).


#[local]
Ltac gen_annotated_judg_IH P ann_ctx ann_exp ann_typ ann_sub :=
  match goal with 
  | H1 : {{ ⊢ ^?Γ }} |- _ => 
      let HΓ := fresh "HΓ" in
      pose proof ann_ctx P Γ H1 as HΓ;
      destruct HΓ as [anns]
  | H1 : {{ ^?Γ ⊢ ^?M : ^?A }},
      H2 : {{ ⊫ ^?Γ' with ?anns }} |- _ => 
        constr_eq Γ Γ';
        let HM := fresh "HM" in
        pose proof ann_exp P anns Γ M A H2 H1 as HM
  | H1: {{ ^?Γ ⊢ ^?A }},
      H2 : {{ ⊫ ^?Γ' with ?anns }} |- _ =>
      constr_eq Γ Γ';
      let HA := fresh "HA" in
      pose proof ann_typ P anns Γ A H2 H1 as HA
  | H1: {{ ^?Γ ⊢s ^?σ : ^?Δ }},
      H2 : {{ ⊫ ^?Γ' with ?anns }} |- _ => 
      constr_eq Γ Γ';
      let Hσ := fresh "Hσ" in
      pose proof ann_sub P anns Γ σ Δ H2 H1 as Hσ
  end.


Ltac gen_ext_wf_ctx P :=
match goal with
    | H1 : {{ ^?Γ with ?anns ⊫ ^?A : Sort@?s @ ^?so }},
        H2 : {{ ⊫ ^?Γ with ?anns }} |- _ =>
        assert {{ ⊫ Γ, A with (Some s)::anns }} by mauto
    end.
                

#[local]
Ltac gen_sort_none P :=
  repeat
    match goal with
    | s : P |- _ =>
        let Hs := fresh "Hs" in
        eassert {{ ^?Γ with ?anns ⊫ Sort@s @ ^None }} by mauto 3;
        mark s
    end;
  unmark_all.

Lemma ctx_ann_decomp {P : PtsSig} : forall {Γ : ctx P} {A anns so}, {{ ⊫ Γ, A with so::anns }} -> {{ ⊫ Γ with anns }} /\ {{ Γ with anns ⊫ A @ so }}.
Proof with now eauto.
  inversion 1...
Qed.

#[local]
Hint Resolve ctx_ann_decomp : mcpts.

Corollary ctx_ann_decomp_left {P : PtsSig} : forall {Γ : ctx P} {A anns so}, {{ ⊫ Γ, A with so::anns }} -> {{ ⊫ Γ with anns }}.
Proof with easy.
  intros * ?%ctx_ann_decomp...
Qed.

Corollary ctx_ann_decomp_right {P : PtsSig} : forall {Γ : ctx P} {A anns so}, {{ ⊫ Γ, A with so::anns }} -> {{ Γ with anns ⊫ A @ so }}.
Proof with easy.
  intros * ?%ctx_ann_decomp...
Qed.

#[local]
Hint Resolve ctx_ann_decomp_left ctx_ann_decomp_right : mcpts.

Lemma presup_sub_ann_ctx_ann {P} : forall {Γ : ctx P} {anns anns' σ Δ},
    {{ Γ with anns ⊫s σ : Δ with anns' }} -> {{ ⊫ Γ with anns }} /\ {{ ⊫ Δ with anns' }}.
Proof.
  induction 1; destruct_conjs; split; mauto 3.
Qed.

#[local]
Hint Resolve presup_sub_ann_ctx_ann : mcpts.

Lemma presup_sub_ann_ctx_ann_left {P} : forall {Γ : ctx P} {anns anns' σ Δ},
    {{ Γ with anns ⊫s σ : Δ with anns' }} -> {{ ⊫ Γ with anns }}.
Proof with easy.
  intros * ?%presup_sub_ann_ctx_ann...
Qed.

Lemma presup_sub_ann_ctx_ann_right {P} : forall {Γ : ctx P} {anns anns' σ Δ},
    {{ Γ with anns ⊫s σ : Δ with anns' }} -> {{ ⊫ Δ with anns' }}.
Proof with easy.
  intros * ?%presup_sub_ann_ctx_ann...
Qed.

#[local]
Hint Resolve presup_sub_ann_ctx_ann_left presup_sub_ann_ctx_ann_right : mcpts.

Lemma presup_exp_ann_ctx_ann {P} : forall {Γ : ctx P} {M A anns so},
    {{ Γ with anns ⊫ M : A @ so }} -> {{ ⊫ Γ with anns }}.
Proof.
  induction 1; mauto 3.
Qed.

#[local]
  Hint Resolve presup_exp_ann_ctx_ann : mcpts.

Lemma presup_typ_ann_ctx_ann {P} : forall {Γ : ctx P} {A anns so},
    {{ Γ with anns ⊫ A @ so }} -> {{ ⊫ Γ with anns }}.
Proof.
  induction 1; mauto 3.
Qed.

#[local]
  Hint Resolve presup_typ_ann_ctx_ann : mcpts.

Lemma ann_lookup_implies_lookup {P} : forall {anns : ctx_anns P} {so Γ x A},
    {{ #x : A @ so ∈ Γ with anns }} ->
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.  

#[export]
  Hint Resolve ann_lookup_implies_lookup : mcpts.

Lemma lookup_implies_ann_lookup {P} : forall {anns : ctx_anns P} {Γ x A},
    {{ #x : A ∈ Γ }} ->
    {{ ⊫ Γ with anns }} ->
    exists so, {{ #x : A @ so ∈ Γ with anns }}.
Proof with mautosolve.
  intros.
  gen anns.
  induction H.
  - intros.
    inversion H0; subst.
    eexists.
    mauto 2.
  - intros.
    inversion H0; subst.
    assert (exists so : SortOption P, {{ # n : A @ so ∈ Γ with anns0 }}) as [] by mauto 2.
    eexists; econstructor; mauto.
Qed.

#[export]
  Hint Resolve lookup_implies_ann_lookup : mcpts.


Lemma wf_ctx_implies_wf_ctx_ann {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} -> exists anns, {{ ⊫ Γ with anns }}
with wf_exp_implies_wf_exp_ann {P} : forall {anns : ctx_anns P} {Γ M A},
     {{ ⊫ Γ with anns }} -> {{ Γ ⊢ M : A }} -> exists so, {{ Γ with anns ⊫ M : A @ so }}
with wf_typ_implies_wf_typ_ann {P} : forall {anns : ctx_anns P} {Γ A},
     {{ ⊫ Γ with anns }} -> {{ Γ ⊢ A }} -> exists so, {{ Γ with anns ⊫ A @ so }}
with wf_sub_implies_wf_sub_ann {P} : forall {anns : ctx_anns P} {Γ σ Δ},
    {{ ⊫ Γ with anns }} -> {{ Γ ⊢s σ : Δ }} -> exists anns', {{ Γ with anns ⊫s σ : Δ with anns' }}.
Proof.
  2,3,4: intros * Hanns H; gen anns; inversion_clear H; intros;
    try (gen_annotated_judg_IH P wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann);
    try (gen_annotated_judg_IH P wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann);
  destruct_conjs;
  try (gen_ext_wf_ctx P);
  destruct_conjs;
    try (gen_annotated_judg_IH P wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann);
    destruct_conjs;
    try solve[
        clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann;
        mauto 4].
  intros.
  inversion_clear H.
  - eexists.
    econstructor.
  - epose proof (wf_ctx_implies_wf_ctx_ann _ _ H0) as [anns].
    epose proof (wf_typ_implies_wf_typ_ann _ _ _ _ H H1) as [so].
    eexists; econstructor; eassumption.
    

    
  
  - eexists.
    epose proof wf_exp_implies_wf_exp_ann P ((Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H4 H1.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    destruct_conjs.
    econstructor; mauto.
    

  - clear HM0 HM1 H H5.
    epose proof wf_exp_implies_wf_exp_ann P anns Γ A0 {{{ Sort@s1 }}} Hanns H0 as [so].
    assert {{ ⊫ Γ, A0 with {{{ anns, ^ (Some s1) }}} }} by mauto 3.
    epose proof wf_exp_implies_wf_exp_ann P ((Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H5 H1 as [so'].
    epose proof wf_exp_implies_wf_exp_ann P anns Γ _ _ Hanns H2 as [soΠ].
    eexists.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    destruct_conjs.
    econstructor; mauto.

  - assert {{ ⊢ Γ, A }} by mauto 2.
    assert (exists so : SortOption P, {{ # x : A @ so ∈ Γ with anns }}) as [so'] by mauto 2.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    eexists; mauto.
  - clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    eexists; mauto.
  - clear HM0 HM1 H H5.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    assert {{ ⊫ Γ, ℕ with (Some s)::anns }} by mauto 4.
    assert (exists so : SortOption P, {{ Γ, ℕ with {{{ anns, ^ (Some s) }}} ⊫ A0 @ so }}) as [so] by mauto 2.
    assert {{ ⊢ Γ, ℕ, A0 }} by mauto 2.
    assert {{ ⊫ Γ, ℕ, A0 with so::(Some s)::anns }} by mauto 3.
    assert (exists so, {{ Γ with anns ⊫ MZ : A0[Id,,zero] @ so }}) as [so'] by mauto 2.
    assert (exists so', {{ Γ, ℕ, A0 with so::(Some s)::anns ⊫ MS : A0[Wk∘Wk,,succ #1] @ so' }}) as [so''] by mauto 2.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    assert  {{ Γ with anns ⊫ zero : ℕ @ ^ (Some s) }} by mauto 2.
    assert {{ Γ with anns ⊫ ℕ[Id] @ ^(Some s) }} by mauto 4.
    assert {{ Γ with anns ⊫ ℕ @ ^(Some s) }} by mauto 4.
    assert {{ Γ with anns ⊫ zero : ℕ[Id] @ ^ (Some s) }} by (econstructor; mauto).
    assert {{ Γ with anns ⊫s Id,,zero : Γ, ℕ with {{{ anns, ^ (Some s) }}} }} by mauto 4.
    assert {{ Γ ⊢ A0[Id,,zero] ⊆ A0[Id,,zero] }} by (gen_presup H1; mauto 3).
    assert {{ Γ with anns ⊫ MZ : A0[Id,,zero] @ so }} by mauto 3.
    assert {{ Γ, ℕ, A0 ⊢ A0[Wk∘Wk,,succ #1] ⊆ A0[Wk∘Wk,,succ #1] }} by (gen_presup H2; mauto 3).
    assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@s }} by mauto 4.
    assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk][Wk] ⊆ ℕ }} by mauto 3.
    assert {{ Γ, ℕ, A0 ⊢ ℕ ⊆ ℕ[Wk][Wk] }} by mauto 4.
    assert {{ Γ, ℕ, A0 ⊢s Wk∘Wk : Γ }} by mauto 4.
    assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk∘Wk] : Sort@s }} by mauto 3.
    assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk][Wk] ≈ ℕ[Wk∘Wk] : Sort@s }} by (econstructor; mauto 3).
    assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk][Wk] ⊆ ℕ[Wk∘Wk] }} by mauto 3.
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (Some s), so }}} ⊫ ℕ[Wk][Wk] @ ^ (Some s) }} by (do 2 (econstructor; mauto 3)).
    assert {{ # 1 : ℕ[Wk][Wk] @ Some s ∈ Γ, ℕ, A0 with {{{ anns, ^ (Some s), so }}} }} by mauto 3.
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (Some s), so }}} ⊫ #1 : ℕ[Wk][Wk] @ ^ (Some s) }} by mauto 2.
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (Some s), so }}} ⊫ #1 : ℕ @ ^ (Some s) }} by mauto 4.
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (Some s), so }}} ⊫ succ #1 : ℕ[Wk][Wk] @ ^ (Some s) }} by mauto .
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (Some s), so }}} ⊫ ℕ[Wk∘Wk] @ ^ (Some s) }} by (econstructor; mauto 4).
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (Some s), so }}} ⊫s Wk∘Wk,,succ #1 : Γ, ℕ with (Some s)::anns }} by (econstructor; mauto 4).

    eexists; mauto.
  - clear Hσ0 Hσ1 H H4.
    assert {{ ⊫ Δ with Hσ }} by mauto 2.
    assert (exists so, {{ Δ with Hσ ⊫ M0 : A0 @ so }}) as [so] by mauto 2.
    assert (exists so, {{ Δ with Hσ ⊫ A0 @ so }}) as [so'] by mauto 2.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    mauto.
  - clear HM0 HM1 H H5.
    assert (exists so, {{ Γ with anns ⊫ A @ so }}) as [so] by mauto 2.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    eexists; mauto 2.
  - clear Hσ0 Hσ1 H H3.
    assert (exists anns' : list (SortOption P), {{ Γ with anns ⊫s σ : Δ with anns' }}) as [anns'] by mauto 2.
    assert {{ ⊫ Δ with anns' }} by mauto 2.
    assert (exists so : SortOption P, {{ Δ with anns' ⊫ A0 @ so }}) as [so] by mauto 2.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    eexists; mauto.
  - inversion Hanns; subst.
    eexists.
    econstructor; eassumption.
  - clear Hσ0 Hσ1 H H3.
    assert (exists anns', {{ Γ with anns ⊫s σ2 : Γ2 with anns' }}) as [anns'] by mauto 2.
    assert {{ ⊫ Γ2 with anns' }} by mauto 2.
    assert (exists anns'', {{ Γ2 with anns' ⊫s σ1 : Δ with anns'' }}) as [anns''] by mauto 2.
    assert {{ ⊫ Δ with anns'' }} by mauto 2.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    eexists; mauto.
  - clear HM0 HM1 H H4.
    assert (exists anns', {{ Γ with anns ⊫s σ0 : Δ0 with anns' }}) as [anns'] by mauto 2.
    assert (exists so, {{ Δ0 with anns' ⊫ A @ so }}) as [so] by mauto 3.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    eexists; mauto.
  - assert {{ ⊫ Δ0 with Hσ }} by mauto 2.
    assert (exists anns', {{ ⊫ Δ with anns' }}) as [anns'] by mauto 2.
    eexists.
    econstructor; mauto 2.
Qed.    

#[export]
  Hint Resolve wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann : mcpts.


Lemma wf_judg_ann_implies_wf_judg {P} :
  (forall (anns : ctx_anns P) (Γ : ctx P), {{ ⊫ Γ with anns }} -> {{ ⊢ Γ }}) /\
    (forall (anns : ctx_anns P) (Γ : ctx P) A so M, {{ Γ with anns ⊫ M : A @ so }} -> {{ Γ ⊢ M : A }}) /\
    (forall (anns : ctx_anns P) (Γ : ctx P) A so, {{ Γ with anns ⊫ A @ so }} -> {{ Γ ⊢ A }}) /\
    (forall (anns : ctx_anns P) (anns' : ctx_anns P) (Γ : ctx P) Δ σ, {{ Γ with anns ⊫s σ : Δ with anns' }} -> {{ Γ ⊢s σ : Δ }}).
Proof.
  eapply syntactic_wf_ann_mut_ind; mauto 3.
Qed.

Corollary wf_ctx_ann_implies_wf_ctx {P} : forall {anns : ctx_anns P } {Γ},
    {{ ⊫ Γ with anns }} -> {{ ⊢ Γ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_exp_ann_implies_wf_exp {P} : forall {anns : ctx_anns P } {Γ A s M},
    {{ Γ with anns ⊫ M : A @ s }} -> {{ Γ ⊢ M : A }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_typ_ann_implies_wf_typ {P} : forall {anns : ctx_anns P } {Γ A s},
    {{ Γ with anns ⊫ A @ s }} -> {{ Γ ⊢ A }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_sub_ann_implies_wf_sub {P} : forall {anns : ctx_anns P } {anns' Γ Δ σ},
    {{ Γ with anns ⊫s σ : Δ with anns' }} -> {{ Γ ⊢s σ : Δ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.
