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
        {{ Γ : sts ⊫ Π r A B : Sort@s3 > s3' }} )
| wfa_fn :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ : sts ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ M : B > s2 }} ->
        {{ Γ : sts ⊫ λ r A M : Π r A B > s3 }} )
| wfa_app :
  `( forall (r : Ru P s1 s2 s3),
        {{ Γ : sts ⊫ A : Sort@s1 > s1' }} ->
        {{ Γ, A : (s1 :: sts) ⊫ B : Sort@s2 > s2' }} ->
        {{ Γ : sts ⊫ M : Π r A B > s3 }} ->
        {{ Γ : sts ⊫ N : A > s1 }} ->
        {{ Γ : sts ⊫ M N : B[Id,,N] > s2 }} )
   
| wfa_vlookup :
  `( {{ ⊫ Γ > sts }} ->
     {{ #x : A ∈ Γ }} ->
     {{ Γ : sts ⊫ A > s }} ->
     {{ Γ : sts ⊫ #x : A > s }} )
   
(** Naturals *)
| wfa_nat :
  `( forall (r : Ru_nat P sn),
        Ax P sn sn' ->
        {{ ⊫ Γ > sts }} ->
        {{ Γ : sts ⊫ ℕ : Sort@sn > sn' }} )
| wfa_zero :
  `( forall (r : Ru_nat P sn),
        {{ ⊫ Γ > sts }} ->
        {{ Γ : sts ⊫ zero : ℕ > sn }} )
| wfa_succ :
  `( forall (r : Ru_nat P sn),
        {{ Γ : sts ⊫ M : ℕ > sn' }} ->
        {{ Γ : sts ⊫ succ M : ℕ > sn }} )
| wfa_rec :
  `( forall (r : Ru_nat P sn),
        {{ Γ, ℕ : (sn :: sts) ⊫ A : Sort@sa > sa' }} ->
        {{ Γ : sts ⊫ MZ : A[Id,,zero] > sa }} ->
        {{ Γ, ℕ, A : (sa :: (sn :: sts)) ⊫ MS : A[Wk∘Wk,,succ #1] > sa }} ->
        {{ Γ : sts ⊫ M : ℕ > sn }} ->
        {{ Γ : sts ⊫ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] > sa }} )

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


#[local]
Ltac gen_irrel_IH P full_P exp_irrel typ_irrel sub_irrel H :=
  match type of H with
  | {{ ^?Γ : ?sts ⊫ ^?M : ^?A > ?s }} =>
      let IH := fresh "IHwf_exp_ann" in
      pose proof exp_irrel P full_P Γ sts M A s H as IH
  | {{ ^?Γ : ?sts ⊫ ^?A > ?s }} =>
      let IH := fresh "IHwf_typ_ann" in
      pose proof typ_irrel P full_P Γ sts A s H as IH 
  | {{ ^?Γ : ?stsΓ ⊫s ^?σ : ^?Δ > ?stsΔ }} =>
      let Hσ := fresh "IHwf_sub_ann" in
      pose proof sub_irrel P full_P Γ stsΓ σ Δ stsΔ H as Hσ
  end.

#[local]
Ltac specialize_IHs :=
  match goal with
  | IH : forall sts', {{ ⊫ ^?Γ > sts' }} -> {{ ^?Γ : sts' ⊫ ^?M : ^?A > ?s }},
    HΓ : {{ ⊫ ^?Γ > ?sts' }} |- _ => specialize (IH _ HΓ)
  | IH : forall sts', {{ ⊫ ^?Γ > sts' }} -> {{ ^?Γ : sts' ⊫ ^?A > ?s }},
    HΓ : {{ ⊫ ^?Γ > ?sts' }} |- _ => specialize (IH _ HΓ)
  | IH : forall sts', {{ ⊫ ^?Γ > sts' }} -> {{ ^?Γ : sts' ⊫s ^?σ : ^?Δ > ?stsΔ }},
    HΓ : {{ ⊫ ^?Γ > ?sts' }} |- _ => specialize (IH _ HΓ)
end.

  
Lemma wf_exp_sts_irrel {P} (full_P : FullSig P) : forall {Γ : ctx P} {sts} {M A s},
    {{ Γ : sts ⊫ M : A > s }} ->
    forall sts', {{ ⊫ Γ > sts' }} ->
            {{ Γ : sts' ⊫ M : A > s }}

with wf_typ_sts_irrel {P} (full_P : FullSig P) : forall {Γ : ctx P} {sts} {A s},
    {{ Γ : sts ⊫ A > s }} ->
    forall sts', {{ ⊫ Γ > sts' }} ->
            {{ Γ : sts' ⊫ A > s }}
              
with wf_sub_sts_irrel {P} (full_P : FullSig P) : forall {Γ : ctx P} {stsΓ σ Δ stsΔ},
    {{ Γ : stsΓ ⊫s σ : Δ > stsΔ }} ->
    forall stsΓ', {{ ⊫ Γ > stsΓ' }} ->
             {{ Γ : stsΓ' ⊫s σ : Δ > stsΔ }}.
Proof.
  all: (inversion_clear 1;
        (on_all_hyp: gen_irrel_IH P full_P wf_exp_sts_irrel wf_typ_sts_irrel wf_sub_sts_irrel);
        clear wf_exp_sts_irrel wf_typ_sts_irrel wf_sub_sts_irrel;
        intros stsΓ' HΓ);
    try specialize_IHs;
    only 2-4: (assert {{ ⊫ Γ,A0 > s1 :: stsΓ' }} as HΓA by mauto 2);
    only 9: (assert (exists sn', Ax P sn sn') as [sn'] by (eapply full_P);
             assert {{ Γ : stsΓ' ⊫ ℕ : Sort@sn > sn' }} by mauto 2;
             assert {{ ⊫ Γ, ℕ > sn :: stsΓ' }} by mauto 2;
             try specialize_IHs;
             assert {{ ⊫ Γ, ℕ, A0 > s :: sn :: stsΓ' }} by mauto 2
            );
    only 12: (specialize_IHs);
    only 17: (inversion_clear HΓ);
    try solve [econstructor; mauto 2].

  inversion_clear H0.
  assert {{ Δ, A : s0 :: sts ⊫s Wk : Δ > sts }} by mauto 3.
  eapply wfa_sub_conv_sts; mauto 2.
Qed.

  
#[local]
Ltac gen_ann_presup_IH P exp_presup typ_presup sub_presup H :=
  match type of H with
  | {{ ^?Γ : ?sts ⊫ ^?M : ^?A > ?s }} =>
      let HM := fresh "HM" in
      pose proof exp_presup _ _ _ _ _ _ H as HM
  | {{ ^?Γ : ?sts ⊫ ^?A > ?s }} =>
      let HA := fresh "HA" in
      pose proof typ_presup _ _ _ _ _ H as HM
  | {{ ^?Γ : ?sts ⊫s ^?σ : ^?Δ > ?sts' }} =>
      let Hσ := fresh "Hσ" in
      pose proof sub_presup _ _ _ _ _ _ H as Hσ
  end.
  
Lemma wf_exp_ann_ctx_presup {P} : forall {Γ : ctx P} {sts M A s},
    {{ Γ : sts ⊫ M : A > s }} ->
    {{ ⊫ Γ > sts }}

with wf_typ_ann_ctx_presup {P} : forall {Γ : ctx P} {sts A s},
    {{ Γ : sts ⊫ A > s }} ->
    {{ ⊫ Γ > sts }}
      
with wf_sub_ann_ctx_presup {P} : forall {Γ : ctx P} {sts σ Δ sts'},
    {{ Γ : sts ⊫s σ : Δ > sts' }} ->
    {{ ⊫ Γ > sts }}.
Proof.
  all: inversion_clear 1;
    (on_all_hyp: gen_ann_presup_IH P wf_exp_ann_ctx_presup wf_typ_ann_ctx_presup wf_sub_ann_ctx_presup);
    clear wf_exp_ann_ctx_presup wf_typ_ann_ctx_presup wf_sub_ann_ctx_presup;
    mauto 2.
Qed.


Lemma wf_sub_ann_domain_presup {P} : forall {Γ : ctx P} {sts σ Δ sts'},
    {{ Γ : sts ⊫s σ : Δ > sts' }} ->
    {{ ⊫ Δ > sts' }}.
Proof.
  induction 1; mauto 2.
  inversion_clear H; eassumption.
Qed.  

#[local]
Ltac gen_annotated_judg_IH P full_P ann_ctx ann_exp ann_typ ann_sub H :=
  match type of H with
  | {{ ⊢ ^?Γ }} =>
      let HΓ := fresh "HΓ" in
      pose proof ann_ctx P full_P Γ H as HΓ
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      let HM := fresh "HM" in
      pose proof ann_exp P full_P Γ M A H as HM
  | {{ ^?Γ ⊢ ^?A }} =>
      let HA := fresh "HA" in
      pose proof ann_typ P full_P Γ A H as HA
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      let Hσ := fresh "Hσ" in
      pose proof ann_sub P full_P Γ σ Δ H as Hσ
  end.

Lemma wf_ctx_implies_wf_ctx_ann {P} (full_P : FullSig P) : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    exists sts, {{ ⊫ Γ > sts }}

with wf_exp_implies_wf_exp_ann {P} (full_P : FullSig P) : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    exists sts s, {{ Γ : sts ⊫ M : A > s }}

with wf_typ_implies_wf_typ_ann {P} (full_P : FullSig P) : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    exists sts s, {{ Γ : sts ⊫ A > s }}
               
with wf_sub_implies_wf_sub_ann {P} (full_P : FullSig P) : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    exists sts sts', {{ Γ : sts ⊫s σ : Δ > sts' }}.
Proof.
  all: inversion_clear 1;
    (on_all_hyp: gen_annotated_judg_IH P full_P wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann);
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann;
    mauto 3.
  
  - destruct HM as [sts [s' HA]].
    destruct HΓ as [sts' HΓ].
    assert {{ Γ0 : sts' ⊫ A : Sort@s > s' }} by (eapply wf_exp_sts_irrel; mauto 2).
    eexists; mauto 2.
  - destruct HΓ as [sts HΓ].
    assert (exists s3, Ax P s2 s3) as [s3] by (eapply full_P).
    do 2 eexists; mauto 2.
  - destruct HM0 as [sts [s1' HA]].
    destruct HM as [sts' [s2' HB]].
    assert {{ ⊫ Γ > sts }} by (eapply wf_exp_ann_ctx_presup; mauto 2).
    assert {{ ⊫ Γ, A0 > s1 :: sts }} by mauto 2.
    assert {{ Γ, A0 : (s1 :: sts) ⊫ B : Sort@s2 > s2' }} by (eapply wf_exp_sts_irrel; mauto 2).
    assert (exists s3', Ax P s3 s3') as [s3'] by (eapply full_P).
    do 2 eexists; mauto 2.
  - destruct HM1 as [stsΓ [s1' HA0]].
    destruct HM0 as [stsΓA0 [s2' HB]].
    destruct HM as [stsΓA0' [sb HM0]].
    assert {{ ⊫ Γ > stsΓ }} by (eapply wf_exp_ann_ctx_presup; mauto 2).
    assert {{ ⊫ Γ, A0 > s1 :: stsΓ }} by mauto 2.
    assert {{ Γ, A0 : s1 :: stsΓ ⊫ B : Sort@s2 > s2' }} by (eapply wf_exp_sts_irrel; mauto 2).
    assert {{ Γ, A0 : s1 :: stsΓ ⊫ B > s2 }} by mauto 2.
    assert {{ Γ, A0 : s1 :: stsΓ ⊫ M0 : B > sb }} by (eapply wf_exp_sts_irrel; mauto 2).
    assert {{ Γ, A0 : s1 :: stsΓ ⊫ M0 : B > s2 }} by (eapply wfa_exp_conv_st; mauto 2).
    do 2 eexists; mauto 2.
  - destruct HM as [sts [sa0 HN]].
    assert {{ ⊫ Γ > sts }} as HΓ by (eapply wf_exp_ann_ctx_presup; mauto 2).

    destruct HM2 as [sts'' [s1' HA0]].
    assert {{ Γ : sts ⊫ A0 : Sort@s1 > s1' }} by (eapply wf_exp_sts_irrel; mauto 2).
    clear HA0; rename H into HA0.

    assert {{ Γ : sts ⊫ A0 > s1 }} as HA0s1 by mauto 2.
    assert {{ Γ : sts ⊫ N : A0 > s1 }} by mauto 2.
    clear HN; rename H into HN.
    
    destruct HM1 as [stsΓA0 [s2' HB]].
    assert {{ ⊫ Γ, A0 > s1 :: sts }} as HΓA by mauto 2.
    assert {{ Γ, A0 : s1 :: sts ⊫ B : Sort@s2 > s2' }} by (eapply wf_exp_sts_irrel; mauto 2).
    clear HB; rename H into HB.
    
    destruct HM0 as [sts' [sΠ HM0]].
    assert {{ Γ : sts ⊫ M0 : Π r A0 B > sΠ }} by (eapply wf_exp_sts_irrel; mauto 2).
    clear HM0; rename H into HM0.
    assert {{ Γ : sts ⊫ Π r A0 B > s3 }} as HΠ.
    {
      assert (exists s3', Ax P s3 s3') as [s3'] by (eapply full_P).
      mauto 3.
    }
    assert {{ Γ : sts ⊫ M0 : Π r A0 B > s3 }} by mauto 3.
    clear HM0; rename H into HM0.
    
    do 2 eexists; mauto 2.
    
  - destruct HΓ as [sts HΓ].
    assert (exists s, {{ Γ ⊢ A : Sort@s }}) as [s] by mauto 2.
    do 2 eexists; mauto 2.
    
  - destruct HΓ as [sts HΓ].
    assert (exists s', Ax P s s') as [s'] by (eapply full_P).
    do 2 eexists; mauto 2.
  - destruct HΓ as [sts HΓ].
    do 2 eexists; mauto 2.
  - destruct HM as [sts [s' HM0]].
    do 2 eexists; mauto 2.
  - rename s into sn.
    rename s' into s.
    assert (exists sn', Ax P sn sn') as [sn'] by (eapply full_P).
    destruct HM1 as [stsΓ [sa HMZ]].
    assert {{ ⊫ Γ > stsΓ }} by (eapply wf_exp_ann_ctx_presup; mauto 2).
    assert {{ Γ : stsΓ ⊫ ℕ : Sort@sn > sn' }} by mauto 2.
    assert {{ ⊫ Γ, ℕ > sn :: stsΓ }} by mauto 2.
    
    destruct HM2 as [stsΓℕ [s' HA0]].
    assert {{ Γ, ℕ : sn :: stsΓ ⊫ A0 : Sort@s > s' }} by (eapply wf_exp_sts_irrel; mauto 2).
    clear HA0; rename H7 into HA0.

    assert {{ Γ, ℕ : sn :: stsΓ ⊫ A0 > s }} by mauto 2.
    assert {{ ⊫ Γ, ℕ, A0 > s :: sn :: stsΓ }} by mauto 2.
    assert {{ Γ : stsΓ ⊫ MZ : A0[Id,,zero] > s }}.
    {
      enough {{ Γ : stsΓ ⊫ A0[Id,,zero] > s }} by mauto 3.
      eapply wfa_typ_clo; mauto 2.
      econstructor; mauto 2.
      econstructor; mauto 2.
      econstructor; mauto 2.
      symmetry.
      econstructor; mauto 3.
    }
    clear HMZ; rename H0 into HMZ.
    clear sa.
    
    destruct HM0 as [stsΓℕA0 [sa HMS]].
    assert {{ Γ, ℕ, A0 : s :: sn :: stsΓ ⊫ MS : A0[Wk∘Wk,,succ #1] > s }}.
    {
      assert {{ Γ, ℕ, A0 : s :: sn :: stsΓ ⊫ MS : A0[Wk∘Wk,,succ #1] > sa }} by (eapply wf_exp_sts_irrel; mauto 2).
      enough {{ Γ, ℕ, A0 : s :: sn :: stsΓ ⊫ A0[Wk∘Wk,,succ #1] > s }} by mauto 3.
      eapply wfa_typ_clo; mauto 2.
      econstructor; mauto 4.
      gen_presup H2.
      assert {{ Γ, ℕ, A0 ⊢s Wk∘Wk : Γ }} by (econstructor; mauto 3).
      assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk∘Wk] ≈ ℕ : Sort@sn }} by (econstructor; mauto 2).
      assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk∘Wk] ≈ ℕ[Wk][Wk] : Sort@sn }}.
      {
        eapply wf_exp_eq_conv' with (A := {{{ Sort@sn[Wk∘Wk] }}}); mauto 3.
        eapply wf_exp_eq_sub_compose; econstructor; mauto 2.
      }
      assert {{ Γ, ℕ, A0 ⊢ ℕ[Wk][Wk] ≈ ℕ : Sort@sn }} by (etransitivity; mauto 2).
      eapply wfa_exp_conv with (A := {{{ ℕ }}}); mauto 2.
      - eapply wfa_succ; [eapply r|].
        eapply wfa_exp_conv with (A := {{{ ℕ[Wk][Wk] }}}); mauto 2.
        econstructor; mauto 3.
        eapply wf_conv with (A := {{{ Sort@sn[Wk][Wk] }}}); mauto 2.
        + econstructor; mauto 2.
          econstructor; econstructor; mauto 2.
        + transitivity {{{ Sort@sn[Wk∘Wk] }}}; [symmetry|]; econstructor; mauto 2.
          eapply wf_exp_eq_conv' with (A := {{{ Sort@sn'[Wk∘Wk] }}}); mauto 3.
          eapply wf_exp_eq_sub_compose; econstructor; mauto 2.
      - symmetry; mauto 3.
    }
    clear HMS; rename H0 into HMS.

    destruct HM as [stsΓ' [sn'' HM0]].
    assert {{ Γ : stsΓ ⊫ M0 : ℕ > sn }}.
    {
      assert {{ Γ : stsΓ ⊫ M0 : ℕ > sn'' }} by (eapply wf_exp_sts_irrel; mauto 2).
      assert {{ Γ : stsΓ ⊫ ℕ > sn }} by mauto 2.
      mauto 2.
    }
    clear HM0; rename H0 into HM0.

    do 2 eexists; mauto 2.
    
  - destruct HM as [sts [s HA0]].
    destruct Hσ as [stsΓ [stsΔ Hσ]].
    assert {{ ⊫ Δ > stsΔ }} by (eapply wf_sub_ann_domain_presup; mauto 2).
    assert {{ Δ : stsΔ ⊫ M0 : A0 > s }} by (eapply wf_exp_sts_irrel; mauto 2).
    do 2 eexists; mauto 2.    
  - destruct HM as [sts [s HM]].
    do 2 eexists; mauto 2.
  - destruct HΓ as [sts HΓ].
    assert (exists s', Ax P s s') as [s'] by (eapply full_P).
    do 2 eexists; mauto 2.
  - destruct HM as [sts [s' HA]].
    do 2 eexists; mauto 2.
  - destruct HA as [stsΔ [s HA0]].
    destruct Hσ as [stsΓ [stsΔ' Hσ]].
    assert {{ ⊫ Δ > stsΔ' }} by (eapply wf_sub_ann_domain_presup; mauto 2).
    assert {{ Δ : stsΔ' ⊫ A0 > s }} by (eapply wf_typ_sts_irrel; mauto 2).
    do 2 eexists; mauto 2.
  - destruct HΓ as [sts HΔ].
    do 2 eexists; mauto 2.
  - destruct HΓ as [sts HΔA].
    inversion_clear HΔA.
    assert {{ ⊫ Δ, A > s :: sts0 }} by mauto 2.
    do 2 eexists; mauto 2.
  - destruct Hσ as [stsΓ2 [stsΔ Hσ1]].
    destruct Hσ0 as [stsΓ [stsΓ2' Hσ2]].
    assert {{ ⊫ Γ2 > stsΓ2' }} by (eapply wf_sub_ann_domain_presup; mauto 2).
    assert {{ Γ2 : stsΓ2' ⊫s σ1 : Δ > stsΔ }} by (eapply wf_sub_sts_irrel; mauto 2).
    do 2 eexists; mauto 2.
  - destruct HM as [stsΓ [sa HM]].
    destruct HM0 as [stsΔ0 [s' HA]].
    destruct Hσ as [stsΓ' [stsΔ0' Hσ0]].
    assert {{ ⊫ Δ0 > stsΔ0' }} by (eapply wf_sub_ann_domain_presup; mauto 2).
    assert {{ Δ0 : stsΔ0' ⊫ A : Sort@s > s' }} by (eapply wf_exp_sts_irrel; mauto 2).
    assert {{ ⊫ Γ > stsΓ' }} by (eapply wf_exp_ann_ctx_presup; mauto 2).
    assert {{ Γ : stsΓ' ⊫ M : A[σ0] > sa }} by (eapply wf_exp_sts_irrel; mauto 2).
    assert {{ Δ0 : stsΔ0' ⊫ A > s }} by mauto 2.
    assert {{ Γ : stsΓ' ⊫ M : A[σ0] > s }} by mauto 3.    
    do 2 eexists; mauto 2.
    
  - destruct HΓ as [sts HΔ].
    destruct Hσ as [stsΓ [stsΔ0 Hσ]].
    do 2 eexists; mauto 2.
Qed.

Lemma wf_judg_ann_implies_wf_judg {P} :
  (forall (Γ : ctx P) sts, {{ ⊫ Γ > sts }} -> {{ ⊢ Γ }}) /\
    (forall (Γ : ctx P) sts A s M, {{ Γ : sts ⊫ M : A > s }} -> {{ Γ ⊢ M : A }}) /\
    (forall (Γ : ctx P) sts Δ sts' σ, {{ Γ : sts ⊫s σ : Δ > sts' }} -> {{ Γ ⊢s σ : Δ }}).
Proof.
  eapply syntactic_wf_ann_mut_ind; mauto 2.
Qed.

Corollary wf_ctx_ann_implies_wf_ctx {P} : forall {Γ : ctx P} {sts},
    {{ ⊫ Γ > sts }} -> {{ ⊢ Γ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_exp_ann_implies_wf_exp {P} : forall {Γ : ctx P} {sts A s M},
    {{ Γ : sts ⊫ M : A > s }} -> {{ Γ ⊢ M : A }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.

Corollary wf_sub_ann_implies_wf_sub {P} : forall {Γ : ctx P} {sts Δ sts' σ},
    {{ Γ : sts ⊫s σ : Δ > sts' }} -> {{ Γ ⊢s σ : Δ }}.
Proof. intros; eapply wf_judg_ann_implies_wf_judg; mauto 2. Qed.
