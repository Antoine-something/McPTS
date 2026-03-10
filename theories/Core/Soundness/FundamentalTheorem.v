From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Soundness Require Import
  ContextCases
  FunctionCases
  SubstitutionCases
  TermStructureCases
  SortCases.
From McPTS.Core.Soundness Require Export LogicalRelation.
From McPTS.Core.Soundness.Extension Require Import SystemAnnotated.
Import Domain_Notations.

Section soundness_fundamental.
  Theorem soundness_fundamental {P} (pred_P : PredicativeSig P) :
    (forall Γ, {{ ⊫ Γ }} -> {{ ⟪ pred_P ⟫ ⊩ Γ }}) /\
      (forall Γ A s M, {{ Γ ⊫ M : A @ s }} -> {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ s }}) /\
      (forall Γ A s, {{ Γ ⊫ A @ s }} -> {{ ⟪ pred_P ⟫ Γ ⊩u A @ s }}) /\
      (forall Γ Δ σ, {{ Γ ⊫s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }}).
  Proof.
    eapply syntactic_wf_ann_mut_ind; mauto 3; intros.
  Qed.

  #[local]
  Ltac solve_it pred_P := pose proof soundness_fundamental pred_P; firstorder.
  
  Corollary soundness_fundamental_ctx_ann {P} (pred_P : PredicativeSig P) :
    forall Γ, {{ ⊫ Γ }} -> {{ ⟪ pred_P ⟫ ⊩ Γ }}.
  Proof. solve_it pred_P. Qed.
  
  Corollary soundness_fundamental_exp_ann {P} (pred_P : PredicativeSig P) :
    forall Γ A so M, {{ Γ ⊫ M : A @ so }} -> {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ so }}.
  Proof. solve_it pred_P. Qed.
  
  Corollary soundness_fundamental_typ_ann {P} (pred_P : PredicativeSig P) :
    forall Γ A so, {{ Γ ⊫ A @ so }} -> {{ ⟪ pred_P ⟫ Γ ⊩u A @ so }}.
  Proof. solve_it pred_P. Qed.
  
  Corollary soundness_fundamental_sub_ann {P} (pred_P : PredicativeSig P) :
    forall Γ Δ σ, {{ Γ ⊫s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }}.
  Proof. solve_it pred_P. Qed.  

  
  Theorem soundness_fundamental_ctx {P} (pred_P : PredicativeSig P) :
    forall Γ, {{ ⊢ Γ }} -> {{ ⟪ pred_P ⟫ ⊩ Γ }}.
  Proof.
    intros.
    assert {{ ⊫ Γ }} by mauto 2. 
    eapply soundness_fundamental_ctx_ann; mauto 2.
  Qed.

  Theorem soundness_fundamental_exp {P} (pred_P : PredicativeSig P) :
    forall Γ M A, {{ Γ ⊢ M : A }} -> exists so, {{ ⟪ pred_P ⟫ Γ ⊩u M : A @ so }}.
  Proof.
    intros.
    assert (exists so, {{ Γ ⊫ M : A @ so }}) as [so] by mauto 2.
    eexists.
    eapply soundness_fundamental_exp_ann; mauto 2.
  Qed.

  Theorem soundness_fundamental_typ {P} (pred_P : PredicativeSig P) :
    forall Γ A, {{ Γ ⊢ A }} -> exists so, {{ ⟪ pred_P ⟫ Γ ⊩u A @ so }}.
  Proof.
    intros.
    assert (exists so, {{ Γ ⊫ A @ so }}) as [so] by mauto 2.
    eexists.
    eapply soundness_fundamental_typ_ann; mauto 2.
  Qed.
  
  Theorem soundness_fundamental_sub {P} (pred_P : PredicativeSig P) (full_P : FullSig P) :
    forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }}.
  Proof.
    intros.
    assert {{ Γ ⊫s σ : Δ }} by mauto 2.
    eapply soundness_fundamental_sub_ann; mauto 2.
  Qed.  
End soundness_fundamental.




(* Section soundness_fundamental. *)
(*   Theorem soundness_fundamental {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     (forall Γ, {{ ⊫ Γ }} -> {{ ⟪ pred_P ⟫ ⊩ Γ }}) /\ *)
(*       (forall Γ A s M, {{ Γ ⊫ M : A @ s }} -> {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }}) /\ *)
(*       (forall Γ A s, {{ Γ ⊫ A @ s }} -> {{ ⟪ pred_P ⟫ Γ ⊩ A @ s }}) /\ *)
(*       (forall Γ Δ σ, {{ Γ ⊫s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }}). *)
(*   Proof. *)
(*     eapply syntactic_wf_ann_mut_ind; mauto 3; intros. *)
(*   Qed. *)

(*   #[local] *)
(*   Ltac solve_it pred_P full_P := pose proof soundness_fundamental pred_P full_P; firstorder. *)
  
(*   Corollary soundness_fundamental_ctx_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ, {{ ⊫ Γ }} -> {{ ⟪ pred_P ⟫ ⊩ Γ }}. *)
(*   Proof. solve_it pred_P full_P. Qed. *)
  
(*   Corollary soundness_fundamental_exp_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ A s M, {{ Γ ⊫ M : A @ s }} -> {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }}. *)
(*   Proof. solve_it pred_P full_P. Qed. *)
  
(*   Corollary soundness_fundamental_typ_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ A s, {{ Γ ⊫ A @ s }} -> {{ ⟪ pred_P ⟫ Γ ⊩ A @ s }}. *)
(*   Proof. solve_it pred_P full_P. Qed. *)
  
(*   Corollary soundness_fundamental_sub_ann {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ Δ σ, {{ Γ ⊫s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }}. *)
(*   Proof. solve_it pred_P full_P. Qed.   *)


  
(*   Theorem soundness_fundamental_ctx {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ, {{ ⊢ Γ }} -> {{ ⟪ pred_P ⟫ ⊩ Γ }}. *)
(*   Proof. *)
(*     intros. *)
(*     assert {{ ⊫ Γ }} by (eapply wf_ctx_implies_wf_ctx_ann; mauto 2). *)
(*     eapply soundness_fundamental_ctx_ann; mauto 2. *)
(*   Qed. *)

(*   Theorem soundness_fundamental_exp {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ M A, {{ Γ ⊢ M : A }} -> exists s, {{ ⟪ pred_P ⟫ Γ ⊩ M : A @ s }}. *)
(*   Proof. *)
(*     intros. *)
(*     assert (exists s, {{ Γ ⊫ M : A @ s }}) as [s] by (eapply wf_exp_implies_wf_exp_ann; mauto 2). *)
(*     eexists. *)
(*     eapply soundness_fundamental_exp_ann; mauto 2. *)
(*   Qed. *)

(*   Theorem soundness_fundamental_typ {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ A, {{ Γ ⊢ A }} -> exists s, {{ ⟪ pred_P ⟫ Γ ⊩ A @ s }}. *)
(*   Proof. *)
(*     intros. *)
(*     assert (exists s, {{ Γ ⊫ A @ s }}) as [s] by (eapply wf_typ_implies_wf_typ_ann; mauto 2). *)
(*     eexists. *)
(*     eapply soundness_fundamental_typ_ann; mauto 2. *)
(*   Qed. *)
  
(*   Theorem soundness_fundamental_sub {P} (pred_P : PredicativeSig P) (full_P : FullSig P) : *)
(*     forall Γ σ Δ, {{ Γ ⊢s σ : Δ }} -> {{ ⟪ pred_P ⟫ Γ ⊩s σ : Δ }}. *)
(*   Proof. *)
(*     intros. *)
(*     assert {{ Γ ⊫s σ : Δ }} by (eapply wf_sub_implies_wf_sub_ann; mauto 2). *)
(*     eapply soundness_fundamental_sub_ann; mauto 2. *)
(*   Qed.   *)
(* End soundness_fundamental. *)
