From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Import Syntax System Corollaries.
From McPTS.Core.Syntactic.SystemAnnotated Require Import Definitions.
Import Syntax_Notations.

(** * Basic properties of annotated judgments *)
(** ** Inversion for local contexts *)
Lemma wf_ctx_ann_decomp {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so},
    {{ ⊫ Γ, A @ annsΓ, so }} -> {{ ⊫ Γ @ annsΓ }} /\ {{ Γ @ annsΓ ⊫ A @ so }}.
Proof with now eauto.
  inversion 1...
Qed.

Lemma wf_ctx_ann_decomp_left {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so},
    {{ ⊫ Γ, A @ annsΓ, so }} -> {{ ⊫ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%wf_ctx_ann_decomp...
Qed.

Lemma wf_ctx_ann_decomp_right {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so},
    {{ ⊫ Γ, A @ annsΓ, so }} -> {{ Γ @ annsΓ ⊫ A @ so }}.
Proof with easy.
  intros * ?%wf_ctx_ann_decomp...
Qed.

#[local]
Hint Resolve wf_ctx_ann_decomp wf_ctx_ann_decomp_left wf_ctx_ann_decomp_right : mcpts.

(** ** Basic context presupposition *)
(** For well-formed substitutions *)
Lemma presup_wf_sub_ann {P : PtsSig} : forall {Γ : ctx P} {annsΓ Γ' annsΓ' σ},
    {{ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ ⊫ Γ @ annsΓ }} /\ {{ ⊫ Γ' @ annsΓ' }}.
Proof.
  induction 1; destruct_pairs; repeat split; mauto 2.
Qed.

Lemma presup_wf_sub_ann_codom {P : PtsSig} : forall {Γ : ctx P} {annsΓ Γ' annsΓ' σ},
    {{ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ ⊫ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

Lemma presup_wf_sub_ann_dom {P : PtsSig} : forall {Γ : ctx P} {annsΓ Γ' annsΓ' σ},
    {{ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ ⊫ Γ' @ annsΓ' }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

#[local]
Hint Resolve presup_wf_sub_ann presup_wf_sub_ann_codom presup_wf_sub_ann_dom : mcpts.

(** For well-formed expressions *)
Lemma presup_wf_exp_ann_ctx {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so M},
    {{ Γ @ annsΓ ⊫ M : A @ so }} -> {{ ⊫ Γ @ annsΓ }}.
Proof.
  induction 1; destruct_pairs; mauto 2.
Qed.  

#[local]
Hint Resolve presup_wf_exp_ann_ctx : mcpts.

(** For well-formed types *)
Lemma presup_wf_typ_ann {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so},
    {{ Γ @ annsΓ ⊫ A @ so }} -> {{ ⊫ Γ @ annsΓ }}.
Proof.
  induction 1; destruct_pairs; mauto 2.
Qed.  

#[local]
Hint Resolve presup_wf_typ_ann : mcpts.

(** ** Useful tactics related to presupposition *)
#[local]
Ltac invert_wf_ctx_ann1 H :=
  match type of H with
  | {{ ⊫ ^?Γ, ^?A @ ^?annsΓ, ^?so }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      pose proof wf_ctx_ann_decomp H as [HΓ HA]
      (* ; *)
      (* match goal with *)
      (* | _: {{ Δ ▶ Γ ⊢ A }} |- _ => clear HA *)
      (* | _: __mark__ _ {{ Δ ▶ Γ ⊢ A }} |- _ => clear HA *)
      (* end *)
  end.

Ltac invert_wf_ctx_ann :=
  (on_all_hyp: fun H => invert_wf_ctx_ann1 H);
  clear_dups.

#[local]
Ltac gen_presup_ann H :=
  match type of H with
  | {{ ^?Γ @ ^?annsΓ ⊫ ^?M : ^?A @ ^?so }} =>
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_exp_ann_ctx H as HΓ
  | {{ ^?Γ @ ^?annsΓ ⊫ ^?A @ ^?so }} =>
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_typ_ann H as HΓ
  | {{ ^?Γ @ ^?annsΓ ⊫s ^?σ : ^?Γ' @ ^?annsΓ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      pose proof presup_wf_sub_ann H as [HΓ HΓ']
  end.

#[local]
Ltac gen_presup_anns :=
  (on_all_hyp: fun H => gen_presup_ann H); invert_wf_ctx_ann; clear_dups.


(** * Soundness of annotated judgments *)
Lemma soundness_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so x},
    {{ #x : A @ so ∈ Γ @ annsΓ }} ->
    {{ #x : A ∈ Γ }}.
Proof.
  induction 1; mauto 2.
Qed.

#[local]
Hint Resolve soundness_ctx_lookup : mcpts.

Lemma soundness_ann_judg {P : PtsSig} :
  (forall (Γ : ctx P) annsΓ, {{ ⊫ Γ @ annsΓ }} -> {{ ⊢ Γ }}) /\
    (forall (Γ : ctx P) annsΓ A so M, {{ Γ @ annsΓ ⊫ M : A @ so }} -> {{ Γ ⊢ M : A }}) /\
    (forall (Γ : ctx P) annsΓ A so, {{ Γ @ annsΓ ⊫ A @ so }} -> {{ Γ ⊢ A }}) /\
    (forall (Γ : ctx P) annsΓ Γ' annsΓ' σ, {{ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ Γ ⊢s σ : Γ' }}).
Proof.
  apply syntactic_wf_ann_mut_ind;
    intros; mauto 2.
  all: mauto 3.
Qed.    

#[local]
Ltac solve_soundness_ann P :=
  intros; pose proof @soundness_ann_judg P; destruct_conjs; eauto.

Corollary soundness_wf_ctx {P : PtsSig} : forall {Γ : ctx P} {annsΓ},
    {{ ⊫ Γ @ annsΓ}} ->
    {{ ⊢ Γ }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_exp {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so M},
    {{ Γ @ annsΓ ⊫ M : A @ so}} ->
    {{ Γ ⊢ M : A }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_typ {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so},
    {{ Γ @ annsΓ ⊫ A @ so}} ->
    {{ Γ ⊢ A }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_sub {P : PtsSig} : forall {Γ : ctx P} {annsΓ Γ' annsΓ' σ},
    {{ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ'}} ->
    {{ Γ ⊢s σ : Γ' }}.
Proof. solve_soundness_ann P. Qed.

#[export]
Hint Resolve soundness_wf_ctx soundness_wf_exp soundness_wf_typ soundness_wf_sub : mcpts.
 

(** * Completeness of annotated judgments *)
Lemma complete_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {annsΓ A x},
    {{ #x : A ∈ Γ }} ->
    {{ ⊫ Γ @ annsΓ }} ->
    exists so, {{ #x : A @ so ∈ Γ @ annsΓ }}.
Proof.
  intros * H.
  gen annsΓ.
  induction H; intros * HΓ;
    dependent destruction HΓ; mauto 2.
  specialize (IHctx_lookup annsΓ0 ltac:(eassumption)) as [so'].
  mauto 3.
Qed.

#[local]
Hint Resolve complete_ctx_lookup : mcpts.

Ltac completeness_ann_specialize_IH :=
  match goal with
  | [H : exists annsΓ, {{ ⊫ ^?Γ @ annsΓ }} |- _] =>
      let annsΓ := fresh "annsΓ" in
      destruct H as [annsΓ]; gen_presup_anns;
      mark_with H 100
  | [ H : forall annsΓ, {{ ⊫ ^?Γ @ annsΓ }} -> exists so, {{ ^?Γ @ annsΓ ⊫ ^?A @ so }} |- _] =>
      let so := fresh "so" in
      specialize (H _ ltac:(try eassumption; mauto 3)) as [so]; gen_presup_anns;
      mark_with H 100
  | [ H : forall annsΓ, {{ ⊫ ^?Γ @ annsΓ }} -> exists so, {{ ^?Γ @ annsΓ ⊫ ^?M : ^?A @ so }} |- _] =>
      let so := fresh "so" in
      specialize (H _ ltac:(try eassumption; mauto 3)) as [so]; gen_presup_anns;
      mark_with H 100
  | [ H : forall annsΓ, {{ ⊫ ^?Γ @ annsΓ }} -> exists annsΓ', {{ ^?Γ @ annsΓ ⊫s ^?σ : ^?Γ' @ annsΓ' }} |- _] =>
      let annsΓ' := fresh "annsΓ'" in
      specialize (H _ ltac:(try eassumption; mauto 3)) as [annsΓ']; gen_presup_anns;
      mark_with H 100
  end.

Ltac completeness_ann_specialize_IHs := repeat completeness_ann_specialize_IH; unmark_all_with 100.

Lemma completeness_ann_judg {P : PtsSig} :
  (forall (Γ : ctx P), {{ ⊢ Γ }} -> exists annsΓ, {{ ⊫ Γ @ annsΓ }}) /\
    (forall (Γ : ctx P) A M, {{ Γ ⊢ M : A }} -> forall annsΓ, {{ ⊫ Γ @ annsΓ }} -> exists so, {{ Γ @ annsΓ ⊫ M : A @ so }}) /\
    (forall (Γ : ctx P) A, {{ Γ ⊢ A }} -> forall annsΓ, {{ ⊫ Γ @ annsΓ }} -> exists so, {{ Γ @ annsΓ ⊫ A @ so }}) /\
    (forall (Γ : ctx P) Γ' σ, {{ Γ ⊢s σ : Γ' }} -> forall annsΓ, {{ ⊫ Γ @ annsΓ }} -> exists annsΓ', {{ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }}).
Proof.
  apply syntactic_wf_mut_ind';
    intros; deex; destruct_conjs; mauto 3;
    completeness_ann_specialize_IHs; mauto 3.

  (** ** [wf_exp_ann] cases *)
  (** Function cases *)
  - assert {{ Γ, A @ annsΓ, ^ (so_Some s1) ⊫ M : B @ ^(so_Some s2) }} by mauto 3.
    mauto 3.
  - assert {{ Γ @ annsΓ ⊫ N : A @ ^(so_Some s1) }} by mauto 3.
    assert {{ Γ @ annsΓ ⊫ Π r A B : Sort@s3 @ ^so_None }} by mauto 2.
    assert {{ Γ @ annsΓ ⊫ M : Π r A B @ ^(so_Some s3) }} by mauto 3.
    mauto 3.
    
  (** Variables cases *)
  - pose proof complete_ctx_lookup ltac:(eassumption) H0 as [so].    
    mauto 3.

  (** Nat cases *)
  - assert {{ Γ @ annsΓ ⊫ ℕ : Sort@s @ ^so_None }} by mauto 2.
    assert {{ Γ @ annsΓ ⊫ M : ℕ @ ^(so_Some s) }} by mauto 3.
    mauto 3.
  - assert {{ Γ @ annsΓ ⊫ ℕ : Sort@s @ ^so_None }} by mauto 2. 
    assert {{ ⊫ Γ, ℕ @ annsΓ, ^(so_Some s) }} by mauto 3.
    specialize (H _ ltac:(mauto 3)) as [so2].
    specialize (H1 _ ltac:(mauto 3)) as [so3].
    assert {{ Γ @ annsΓ ⊫ M : ℕ @ ^(so_Some s) }} by mauto 3.
    mauto 3.

  (** Closure case *)
  - assert {{ Γ' @ annsΓ'0 ⊫ M : A @ so0 }} by mauto 2.
    mauto 3.

  (** ** Cases for [wf_sub_ann] *)
  - inversion H0; subst.
    mauto 3.
  - assert {{ Γ @ annsΓ ⊫ M : A[σ] @ so1 }} by mauto 3.
    mauto 3.
Qed.
    
Corollary completeness_wf_ctx_ann {P : PtsSig} : forall {Γ : ctx P},
    {{ ⊢ Γ }} -> exists annsΓ, {{ ⊫ Γ @ annsΓ }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs; mauto 3.
Qed.

Corollary completeness_wf_exp_ann {P : PtsSig} : forall {Γ : ctx P} {A M},
    {{ Γ ⊢ M : A }} -> exists annsΓ so, {{ Γ @ annsΓ ⊫ M : A @ so }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  intros * HM.
  gen_presups.
  specialize (H _ HΓ) as [annsΓ HΓann].
  mauto 3.
Qed.

Corollary completeness_wf_typ_ann {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} -> exists annsΓ so, {{ Γ @ annsΓ ⊫ A @ so }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  intros * HA.
  gen_presups.
  specialize (H _ HΓ) as [annsΓ HΓann].
  mauto 3.
Qed.

Corollary completeness_wf_sub_ann {P : PtsSig} : forall {Γ : ctx P} {Γ' σ},
    {{ Γ ⊢s σ : Γ' }} -> exists annsΓ annsΓ', {{ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  intros * Hσ.
  gen_presups.
  specialize (H _ HΓ) as [annsΓ HΓann].
  mauto 3.
Qed.

#[export]
Hint Resolve completeness_wf_ctx_ann completeness_wf_exp_ann completeness_wf_typ_ann completeness_wf_sub_ann : mcpts.

