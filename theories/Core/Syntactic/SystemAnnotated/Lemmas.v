From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax System Corollaries.
From McPTS.Core.Syntactic.SystemAnnotated Require Import Definitions.
Import Syntax_Notations.

(** * Basic properties of annotated judgments *)

(** ** Inversion for global contexts *)
Lemma wf_gctx_ann_decomp {P : PtsSig} : forall {Δ : gctx P} {annsΔ A so x},
    {{ ▶ Δ, x:A @ annsΔ, so }} -> {{ ▶ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ▶ ⋅ @ ⋅ ⊫ A @ so }}.
Proof with now eauto.
  inversion 1...
Qed.

Lemma wf_gctx_ann_decomp_left {P : PtsSig} : forall {Δ : gctx P} {annsΔ A so x},
    {{ ▶ Δ, x:A @ annsΔ, so }} -> {{ ▶ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%wf_gctx_ann_decomp...
Qed.

Lemma wf_gctx_ann_decomp_right {P : PtsSig} : forall {Δ : gctx P} {annsΔ A so x},
    {{ ▶ Δ, x:A @ annsΔ, so }} -> {{ Δ @ annsΔ ▶ ⋅ @ ⋅ ⊫ A @ so }}.
Proof with easy.
  intros * ?%wf_gctx_ann_decomp...
Qed.

#[local]
Hint Resolve wf_gctx_ann_decomp wf_gctx_ann_decomp_left wf_gctx_ann_decomp_right : mcpts.

(** ** Inversion for local contexts *)
Lemma wf_ctx_ann_decomp {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ▶ Γ, A @ annsΓ, so }} -> {{ Δ @ annsΔ ▶ Γ @ annsΓ }} /\ {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }}.
Proof with now eauto.
  inversion 1...
Qed.

Lemma wf_ctx_ann_decomp_left {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ▶ Γ, A @ annsΓ, so }} -> {{ Δ @ annsΔ ▶ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%wf_ctx_ann_decomp...
Qed.

Lemma wf_ctx_ann_decomp_right {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ▶ Γ, A @ annsΓ, so }} -> {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }}.
Proof with easy.
  intros * ?%wf_ctx_ann_decomp...
Qed.

#[local]
Hint Resolve wf_ctx_ann_decomp wf_ctx_ann_decomp_left wf_ctx_ann_decomp_right : mcpts.

(** ** Basic context presupposition *)
(** For local contexts *)
Lemma presup_wf_ctx_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ }} -> {{ ▶ Δ @ annsΔ }}.
Proof.
  induction 1; mauto 2.
Qed.

#[local]
Hint Resolve presup_wf_ctx_ann : mcpts.

(** For well-formed substitutions *)
Lemma presup_wf_sub_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ ▶ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ▶ Γ @ annsΓ }} /\ {{ Δ @ annsΔ ▶ Γ' @ annsΓ' }}.
Proof.
  induction 1; destruct_pairs; repeat split; mauto 2.
Qed.

Lemma presup_wf_sub_ann_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ ▶ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

Lemma presup_wf_sub_ann_left {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ Δ @ annsΔ ▶ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

Lemma presup_wf_sub_ann_right {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ Δ @ annsΔ ▶ Γ' @ annsΓ' }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

#[local]
Hint Resolve presup_wf_sub_ann presup_wf_sub_ann_gctx presup_wf_sub_ann_left presup_wf_sub_ann_right : mcpts.

(** For well-formed expressions *)
Lemma presup_wf_exp_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ M : A @ so }} -> {{ ▶ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ▶ Γ @ annsΓ }}.
Proof.
  induction 1; destruct_pairs; split; mauto 2.
Qed.  

Lemma presup_wf_exp_ann_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ M : A @ so }} -> {{ ▶ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%presup_wf_exp_ann...
Qed.

Lemma presup_wf_exp_ann_ctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ M : A @ so }} -> {{ Δ @ annsΔ ▶ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%presup_wf_exp_ann...
Qed.

#[local]
Hint Resolve presup_wf_exp_ann presup_wf_exp_ann_gctx presup_wf_exp_ann_ctx : mcpts.

(** For well-formed types *)
Lemma presup_wf_typ_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }} -> {{ ▶ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ▶ Γ @ annsΓ }}.
Proof.
  induction 1; destruct_pairs; split; mauto 2.
Qed.  

Lemma presup_wf_typ_ann_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }} -> {{ ▶ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%presup_wf_typ_ann...
Qed.

Lemma presup_wf_typ_ann_ctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so },
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }} -> {{ Δ @ annsΔ ▶ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%presup_wf_typ_ann...
Qed.

#[local]
Hint Resolve presup_wf_typ_ann presup_wf_typ_ann_gctx presup_wf_typ_ann_ctx : mcpts.

(** ** Useful tactics related to presupposition *)
#[local]
Ltac invert_wf_gctx_ann1 H :=
  match type of H with
  | {{ ▶ ^?Δ, ^?x : ^?A @ ^?annsΔ, ^?so }} =>
      let HΔ := fresh "HΔ" in
      let HA := fresh "HA" in
      let Hx := fresh "Hx" in
      pose proof wf_gctx_ann_decomp H as [HΔ [HA Hx]];
      match goal with
      | _: {{ Δ @ annsΔ ▶ ⋅ @ ⋅ ⊫ A @ so }} |- _ => clear HA
      | _: __mark__ _ {{ Δ @ annsΔ ▶ ⋅ @ ⋅ ⊫ A @ so }} |- _ => clear HA
      end
  end.

#[local]
Ltac invert_wf_gctx_ann :=
  (on_all_hyp: fun H => invert_wf_gctx_ann1 H);
  clear_dups.

#[local]
Ltac invert_wf_ctx_ann1 H :=
  match type of H with
  | {{ ^?Δ @ ^?annsΔ ▶ ^?Γ, ^?A @ ^?annsΓ, ^?so }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      pose proof wf_ctx_ann_decomp H as [HΓ HA];
      match goal with
      | _: {{ Δ ▶ Γ ⊢ A }} |- _ => clear HA
      | _: __mark__ _ {{ Δ ▶ Γ ⊢ A }} |- _ => clear HA
      end
  end.

Ltac invert_wf_ctx_ann :=
  (on_all_hyp: fun H => invert_wf_ctx_ann1 H);
  clear_dups.

#[local]
Ltac gen_presup_ann H :=
  match type of H with
  | {{ ^?Δ @ ^?annsΔ ▶ ^?Γ @ ^?annsΓ }} =>
      let HΔ := fresh "HΔ" in
      pose proof presup_wf_ctx_ann H as HΔ
  | {{ ^?Δ @ ^?annsΔ ▶ ^?Γ @ ^?annsΓ ⊫ ^?M : ^?A @ ^?so }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_exp_ann H as [HΔ HΓ]
  | {{ ^?Δ @ ^?annsΔ ▶ ^?Γ @ ^?annsΓ ⊫ ^?A @ ^?so }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_typ_ann H as [HΔ HΓ]
  | {{ ^?Δ @ ^?annsΔ ▶ ^?Γ @ ^?annsΓ ⊫s ^?σ : ^?Γ' @ ^?annsΓ' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      pose proof presup_wf_sub_ann H as [HΔ [HΓ HΓ']]
  end.

#[local]
Ltac gen_presup_anns :=
  (on_all_hyp: fun H => gen_presup_ann H); invert_wf_gctx_ann; invert_wf_ctx_ann; clear_dups.


(** * Soundness of annotated judgments *)
Lemma soundness_gctx_lookup {P : PtsSig} : forall {Δ : gctx P} {annsΔ A so x},
    {{ `#x : A @ so ∈ Δ @ annsΔ }} ->
    {{ `#x : A ∈ Δ }}.
Proof.
  induction 1; mauto 2.
Qed.

#[local]
Hint Resolve soundness_gctx_lookup : mcpts.

Lemma soundness_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {annsΓ A so x},
    {{ #x : A @ so ∈ Γ @ annsΓ }} ->
    {{ #x : A ∈ Γ }}.
Proof.
  induction 1; mauto 2.
Qed.

#[local]
Hint Resolve soundness_ctx_lookup : mcpts.

Lemma soundness_ann_judg {P : PtsSig} :
  (forall (Δ : gctx P) annsΔ, {{ ▶ Δ @ annsΔ }} -> {{ ▶ Δ }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ, {{ Δ @ annsΔ ▶ Γ @ annsΓ }} -> {{ Δ ▶ Γ }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ A so M, {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ M : A @ so }} -> {{ Δ ▶ Γ ⊢ M : A }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ A so, {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }} -> {{ Δ ▶ Γ ⊢ A }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ Γ' annsΓ' σ, {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ Δ ▶ Γ ⊢s σ : Γ' }}).
Proof.
  apply syntactic_wf_ann_mut_ind;
    intros; mauto 2.
  all: mauto 3.
Qed.    

#[local]
Ltac solve_soundness_ann P :=
  intros; pose proof @soundness_ann_judg P; destruct_conjs; eauto.

Corollary soundness_wf_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ},
    {{ ▶ Δ @ annsΔ }} ->
    {{ ▶ Δ }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_ctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ}} ->
    {{ Δ ▶ Γ }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_exp {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ M : A @ so}} ->
    {{ Δ ▶ Γ ⊢ M : A }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_typ {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so}} ->
    {{ Δ ▶ Γ ⊢ A }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_sub {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ'}} ->
    {{ Δ ▶ Γ ⊢s σ : Γ' }}.
Proof. solve_soundness_ann P. Qed.

#[export]
Hint Resolve soundness_wf_gctx soundness_wf_ctx soundness_wf_exp soundness_wf_typ soundness_wf_sub : mcpts.
 

(** * Completeness of annotated judgments *)
Lemma complete_gctx_lookup {P : PtsSig} : forall {Δ : gctx P} {annsΔ A x},
    {{ `#x : A ∈ Δ }} ->
    {{ ▶ Δ @ annsΔ }} ->
    exists so, {{ `#x : A @ so ∈ Δ @ annsΔ }}.
Proof.
  intros * H.
  gen annsΔ.
  induction H; intros * HΔ;
    dependent destruction HΔ; mauto 2.
  specialize (IHgctx_lookup annsΔ0 ltac:(eassumption)) as [so'].
  mauto 3.
Qed.

#[local]
Hint Resolve complete_gctx_lookup : mcpts.

Lemma complete_ctx_lookup {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A x},
    {{ #x : A ∈ Γ }} ->
    {{ Δ @ annsΔ ▶ Γ @ annsΓ }} ->
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
  | [H : forall annsΔ, {{ ▶ ^?Δ @ annsΔ }} -> exists annsΓ, {{ ^?Δ @ annsΔ ▶ ^?Γ @ annsΓ }} |- _] =>
      let annsΓ := fresh "annsΓ" in
      specialize (H _ ltac:(try eassumption; mauto 3)) as [annsΓ]; gen_presup_anns;
      mark_with H 100
  | [ H : forall annsΔ annsΓ, {{ ^?Δ @ annsΔ ▶ ^?Γ @ annsΓ }} -> exists so, {{ ^?Δ @ annsΔ ▶ ^?Γ @ annsΓ ⊫ ^?A @ so }} |- _] =>
      let so := fresh "so" in
      specialize (H _ _ ltac:(try eassumption; mauto 3)) as [so]; gen_presup_anns;
      mark_with H 100
  | [ H : forall annsΔ annsΓ, {{ ^?Δ @ annsΔ ▶ ^?Γ @ annsΓ }} -> exists so, {{ ^?Δ @ annsΔ ▶ ^?Γ @ annsΓ ⊫ ^?M : ^?A @ so }} |- _] =>
      let so := fresh "so" in
      specialize (H _ _ ltac:(try eassumption; mauto 3)) as [so]; gen_presup_anns;
      mark_with H 100
  | [ H : forall annsΔ annsΓ, {{ ^?Δ @ annsΔ ▶ ^?Γ @ annsΓ }} -> exists annsΓ', {{ ^?Δ @ annsΔ ▶ ^?Γ @ annsΓ ⊫s ^?σ : ^?Γ' @ annsΓ' }} |- _] =>
      let annsΓ' := fresh "annsΓ'" in
      specialize (H _ _ ltac:(try eassumption; mauto 3)) as [annsΓ']; gen_presup_anns;
      mark_with H 100
  end.

Ltac completeness_ann_specialize_IHs := repeat completeness_ann_specialize_IH; unmark_all_with 100.

Lemma completeness_ann_judg {P : PtsSig} :
  (forall (Δ : gctx P), {{ ▶ Δ }} -> exists annsΔ, {{ ▶ Δ @ annsΔ }}) /\
    (forall (Δ : gctx P) Γ, {{ Δ ▶ Γ }} -> forall annsΔ, {{ ▶ Δ @ annsΔ }} -> exists annsΓ, {{ Δ @ annsΔ ▶ Γ @ annsΓ }}) /\
    (forall (Δ : gctx P) Γ A M, {{ Δ ▶ Γ ⊢ M : A }} -> forall annsΔ annsΓ, {{ Δ @ annsΔ ▶ Γ @ annsΓ }} -> exists so, {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ M : A @ so }}) /\
    (forall (Δ : gctx P) Γ A, {{ Δ ▶ Γ ⊢ A }} -> forall annsΔ annsΓ, {{ Δ @ annsΔ ▶ Γ @ annsΓ }} -> exists so, {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }}) /\
    (forall (Δ : gctx P) Γ Γ' σ, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> forall annsΔ annsΓ, {{ Δ @ annsΔ ▶ Γ @ annsΓ }} -> exists annsΓ', {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }}).
Proof.
  apply syntactic_wf_mut_ind';
    intros; deex; destruct_conjs; mauto 3;
    completeness_ann_specialize_IHs; mauto 3.

  (** ** [wf_exp_ann] cases *)
  (** Function cases *)
  - assert {{ Δ @ annsΔ▶ Γ, A @ annsΓ, ^ (so_Some s1) ⊫ M : B @ ^(so_Some s2) }} by mauto 3.
    mauto 3.
  - assert {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ N : A @ ^(so_Some s1) }} by mauto 3.
    assert {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ Π r A B : Sort@s3 @ ^so_None }} by mauto 2.
    assert {{ Δ @ annsΔ▶ Γ @ annsΓ ⊫ M : Π r A B @ ^(so_Some s3) }} by mauto 3.
    mauto 3.
    
  (** Variables cases *)
  - pose proof complete_ctx_lookup ltac:(eassumption) H0 as [so].    
    mauto 3.
  - inversion HΓ'; subst.
    pose proof complete_gctx_lookup ltac:(eassumption) ltac:(eassumption) as [so].
    mauto 3.

  (** Nat cases *)
  - assert {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ ℕ : Sort@s @ ^so_None }} by mauto 2.
    assert {{ Δ @ annsΔ▶ Γ @ annsΓ ⊫ M : ℕ @ ^(so_Some s) }} by mauto 3.
    mauto 3.
  - assert {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ ℕ : Sort@s @ ^so_None }} by mauto 2. 
    assert {{ Δ @ annsΔ ▶ Γ, ℕ @ annsΓ, ^(so_Some s) }} by mauto 3.
    specialize (H _ _ ltac:(mauto 3)) as [so2].
    specialize (H1 _ _ ltac:(mauto 3)) as [so3].
    assert {{ Δ @ annsΔ▶ Γ @ annsΓ ⊫ M : ℕ @ ^(so_Some s) }} by mauto 3.
    mauto 3.

  (** Closure case *)
  - assert {{ Δ @ annsΔ▶ Γ' @ annsΓ'0 ⊫ M : A @ so0 }} by mauto 2.
    mauto 3.

  (** ** Cases for [wf_sub_ann] *)
  - inversion H0; subst.
    mauto 3.
  - assert {{ Δ @ annsΔ▶ Γ @ annsΓ ⊫ M : A[σ] @ so1 }} by mauto 3.
    mauto 3.
Qed.
    
Corollary completeness_wf_gctx_ann {P : PtsSig} : forall {Δ : gctx P},
    {{ ▶ Δ }} -> exists annsΔ, {{ ▶ Δ @ annsΔ }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  mauto 2.
Qed.

Corollary completeness_wf_ctx_ann {P : PtsSig} : forall {Δ : gctx P} {Γ},
    {{ Δ ▶ Γ }} -> exists annsΔ annsΓ, {{ Δ @ annsΔ ▶ Γ @ annsΓ }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  intros * HΓ.
  gen_presups.
  specialize (H _ HΔ) as [annsΔ HΔann].
  specialize (H0 _ _ HΓ _ HΔann) as [annsΓ HΓann].
  mauto 3.
Qed.

Corollary completeness_wf_exp_ann {P : PtsSig} : forall {Δ : gctx P} {Γ A M},
    {{ Δ ▶ Γ ⊢ M : A }} -> exists annsΔ annsΓ so, {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ M : A @ so }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  intros * HM.
  gen_presups.
  specialize (H _ HΔ) as [annsΔ HΔann].
  specialize (H0 _ _ HΓ _ HΔann) as [annsΓ HΓann].
  specialize (H1 _ _ _ _ HM _ _ HΓann) as [so HMann].
  repeat eexists; mauto 2.
Qed.

Corollary completeness_wf_typ_ann {P : PtsSig} : forall {Δ : gctx P} {Γ A},
    {{ Δ ▶ Γ ⊢ A }} -> exists annsΔ annsΓ so, {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫ A @ so }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  intros * HA.
  gen_presups.
  specialize (H _ HΔ) as [annsΔ HΔann].
  specialize (H0 _ _ HΓ _ HΔann) as [annsΓ HΓann].
  specialize (H2 _ _ _ HA _ _ HΓann) as [so HAann].
  repeat eexists; mauto 2.
Qed.

Corollary completeness_wf_sub_ann {P : PtsSig} : forall {Δ : gctx P} {Γ Γ' σ},
    {{ Δ ▶ Γ ⊢s σ : Γ' }} -> exists annsΔ annsΓ annsΓ', {{ Δ @ annsΔ ▶ Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }}.
Proof.
  pose proof @completeness_ann_judg P; destruct_conjs.
  intros * Hσ.
  gen_presups.
  specialize (H _ HΔ) as [annsΔ HΔann].
  specialize (H0 _ _ HΓ _ HΔann) as [annsΓ HΓann].
  specialize (H3 _ _ _ _ Hσ _ _ HΓann) as [annsΓ' Hσann].
  repeat eexists; mauto 2.
Qed.

#[export]
Hint Resolve completeness_wf_gctx_ann completeness_wf_ctx_ann completeness_wf_exp_ann completeness_wf_typ_ann completeness_wf_sub_ann : mcpts.

