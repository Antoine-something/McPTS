From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax System Corollaries.
From McPTS.Core.Syntactic.SystemAnnotated Require Import Definitions.
Import Syntax_Notations.

(** * Basic properties of annotated judgments *)

(** ** Inversion for global contexts *)
Lemma wf_gctx_ann_decomp {P : PtsSig} : forall {Δ : gctx P} {annsΔ A so x},
    {{ ⊫ Δ, x:A @ annsΔ, so }} -> {{ ⊫ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ; ⋅ @ ⋅ ⊫ A @ so }}.
Proof with now eauto.
  inversion 1...
Qed.

Lemma wf_gctx_ann_decomp_left {P : PtsSig} : forall {Δ : gctx P} {annsΔ A so x},
    {{ ⊫ Δ, x:A @ annsΔ, so }} -> {{ ⊫ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%wf_gctx_ann_decomp...
Qed.

Lemma wf_gctx_ann_decomp_right {P : PtsSig} : forall {Δ : gctx P} {annsΔ A so x},
    {{ ⊫ Δ, x:A @ annsΔ, so }} -> {{ Δ @ annsΔ ; ⋅ @ ⋅ ⊫ A @ so }}.
Proof with easy.
  intros * ?%wf_gctx_ann_decomp...
Qed.

#[local]
Hint Resolve wf_gctx_ann_decomp wf_gctx_ann_decomp_left wf_gctx_ann_decomp_right : mcpts.

(** ** Inversion for local contexts *)
Lemma wf_ctx_ann_decomp {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ⊫ Γ, A @ annsΓ, so }} -> {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} /\ {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }}.
Proof with now eauto.
  inversion 1...
Qed.

Lemma wf_ctx_ann_decomp_left {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ⊫ Γ, A @ annsΓ, so }} -> {{ Δ @ annsΔ ⊫ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%wf_ctx_ann_decomp...
Qed.

Lemma wf_ctx_ann_decomp_right {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ⊫ Γ, A @ annsΓ, so }} -> {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }}.
Proof with easy.
  intros * ?%wf_ctx_ann_decomp...
Qed.

#[local]
Hint Resolve wf_ctx_ann_decomp wf_ctx_ann_decomp_left wf_ctx_ann_decomp_right : mcpts.

(** ** Basic context presupposition *)
(** For local contexts *)
Lemma presup_wf_ctx_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ},
    {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} -> {{ ⊫ Δ @ annsΔ }}.
Proof.
  induction 1; mauto 2.
Qed.

#[local]
Hint Resolve presup_wf_ctx_ann : mcpts.

(** For well-formed substitutions *)
Lemma presup_wf_sub_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ ⊫ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} /\ {{ Δ @ annsΔ ⊫ Γ' @ annsΓ' }}.
Proof.
  induction 1; destruct_pairs; repeat split; mauto 2.
Qed.

Lemma presup_wf_sub_ann_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ ⊫ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

Lemma presup_wf_sub_ann_left {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ Δ @ annsΔ ⊫ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

Lemma presup_wf_sub_ann_right {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ Δ @ annsΔ ⊫ Γ' @ annsΓ' }}.
Proof with easy.
  intros * ?%presup_wf_sub_ann...
Qed.

#[local]
Hint Resolve presup_wf_sub_ann presup_wf_sub_ann_gctx presup_wf_sub_ann_left presup_wf_sub_ann_right : mcpts.

(** For well-formed expressions *)
Lemma presup_wf_exp_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so }} -> {{ ⊫ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ⊫ Γ @ annsΓ }}.
Proof.
  induction 1; destruct_pairs; split; mauto 2.
Qed.  

Lemma presup_wf_exp_ann_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so }} -> {{ ⊫ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%presup_wf_exp_ann...
Qed.

Lemma presup_wf_exp_ann_ctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so }} -> {{ Δ @ annsΔ ⊫ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%presup_wf_exp_ann...
Qed.

#[local]
Hint Resolve presup_wf_exp_ann presup_wf_exp_ann_gctx presup_wf_exp_ann_ctx : mcpts.

(** For well-formed types *)
Lemma presup_wf_typ_ann {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }} -> {{ ⊫ Δ @ annsΔ }} /\ {{ Δ @ annsΔ ⊫ Γ @ annsΓ }}.
Proof.
  induction 1; destruct_pairs; split; mauto 2.
Qed.  

Lemma presup_wf_typ_ann_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }} -> {{ ⊫ Δ @ annsΔ }}.
Proof with easy.
  intros * ?%presup_wf_typ_ann...
Qed.

Lemma presup_wf_typ_ann_ctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so },
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }} -> {{ Δ @ annsΔ ⊫ Γ @ annsΓ }}.
Proof with easy.
  intros * ?%presup_wf_typ_ann...
Qed.

#[local]
Hint Resolve presup_wf_typ_ann presup_wf_typ_ann_gctx presup_wf_typ_ann_ctx : mcpts.

(** ** Useful tactics related to presupposition *)
#[local]
Ltac invert_wf_gctx_ann1 H :=
  match type of H with
  | {{ ⊫ ^?Δ, ^?x : ^?A @ ^?annsΔ, ^?so }} =>
      let HΔ := fresh "HΔ" in
      let HA := fresh "HA" in
      let Hx := fresh "Hx" in
      pose proof wf_gctx_ann_decomp H as [HΔ [HA Hx]];
      match goal with
      | _: {{ Δ @ annsΔ ; ⋅ @ ⋅ ⊫ A @ so }} |- _ => clear HA
      | _: __mark__ _ {{ Δ @ annsΔ ; ⋅ @ ⋅ ⊫ A @ so }} |- _ => clear HA
      end
  end.

#[local]
Ltac invert_wf_gctx_ann :=
  (on_all_hyp: fun H => invert_wf_gctx_ann1 H);
  clear_dups.

#[local]
Ltac invert_wf_ctx_ann1 H :=
  match type of H with
  | {{ ^?Δ @ ^?annsΔ ⊫ ^?Γ, ^?A @ ^?annsΓ, ^?so }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HA" in
      pose proof wf_ctx_ann_decomp H as [HΓ HA];
      match goal with
      | _: {{ Δ ; Γ ⊢ A }} |- _ => clear HA
      | _: __mark__ _ {{ Δ ; Γ ⊢ A }} |- _ => clear HA
      end
  end.

Ltac invert_wf_ctx_ann :=
  (on_all_hyp: fun H => invert_wf_ctx_ann1 H);
  clear_dups.

#[local]
Ltac gen_presup_ann H :=
  match type of H with
  | {{ ^?Δ @ ^?annsΔ ⊫ ^?Γ @ ^?annsΓ }} =>
      let HΔ := fresh "HΔ" in
      pose proof presup_wf_ctx_ann H as HΔ
  | {{ ^?Δ @ ^?annsΔ ; ^?Γ @ ^?annsΓ ⊫ ^?M : ^?A @ ^?so }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_exp_ann H as [HΔ HΓ]
  | {{ ^?Δ @ ^?annsΔ ; ^?Γ @ ^?annsΓ ⊫ ^?A @ ^?so }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_typ_ann H as [HΔ HΓ]
  | {{ ^?Δ @ ^?annsΔ ; ^?Γ @ ^?annsΓ ⊫s ^?σ : ^?Γ' @ ^?annsΓ' }} =>
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
  (forall (Δ : gctx P) annsΔ, {{ ⊫ Δ @ annsΔ }} -> {{ ⊢ Δ }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ, {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} -> {{ Δ ⊢ Γ }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ A so M, {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so }} -> {{ Δ ; Γ ⊢ M : A }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ A so, {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }} -> {{ Δ ; Γ ⊢ A }}) /\
    (forall (Δ : gctx P) annsΔ Γ annsΓ Γ' annsΓ' σ, {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }} -> {{ Δ ; Γ ⊢s σ : Γ' }}).
Proof.
  apply syntactic_wf_ann_mut_ind;
    intros; mauto 2.
  all: mauto 3.
Qed.    

#[local]
Ltac solve_soundness_ann P :=
  intros; pose proof @soundness_ann_judg P; destruct_conjs; eauto.

Corollary soundness_wf_gctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ},
    {{ ⊫ Δ @ annsΔ }} ->
    {{ ⊢ Δ }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_ctx {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ},
    {{ Δ @ annsΔ ⊫ Γ @ annsΓ}} ->
    {{ Δ ⊢ Γ }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_exp {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so M},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so}} ->
    {{ Δ ; Γ ⊢ M : A }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_typ {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ A so},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so}} ->
    {{ Δ ; Γ ⊢ A }}.
Proof. solve_soundness_ann P. Qed.

Corollary soundness_wf_sub {P : PtsSig} : forall {Δ : gctx P} {annsΔ Γ annsΓ Γ' annsΓ' σ},
    {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ'}} ->
    {{ Δ ; Γ ⊢s σ : Γ' }}.
Proof. solve_soundness_ann P. Qed.

#[export]
Hint Resolve soundness_wf_gctx soundness_wf_ctx soundness_wf_exp soundness_wf_typ soundness_wf_sub : mcpts.
 

(** * Completeness of annotated judgments *)
Lemma complete_gctx_lookup {P : PtsSig} : forall {Δ : gctx P} {annsΔ A x},
    {{ `#x : A ∈ Δ }} ->
    {{ ⊫ Δ @ annsΔ }} ->
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
    {{ Δ @ annsΔ ⊫ Γ @ annsΓ }} ->
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

Lemma completeness_ann_judg {P : PtsSig} :
  (forall (Δ : gctx P), {{ ⊢ Δ }} -> exists annsΔ, {{ ⊫ Δ @ annsΔ }}) /\
    (forall (Δ : gctx P) Γ, {{ Δ ⊢ Γ }} -> exists annsΔ annsΓ, {{ Δ @ annsΔ ⊫ Γ @ annsΓ }}) /\
    (forall (Δ : gctx P) Γ A M, {{ Δ ; Γ ⊢ M : A }} -> exists annsΔ annsΓ so, {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ M : A @ so }}) /\
    (forall (Δ : gctx P) Γ A, {{ Δ ; Γ ⊢ A }} -> exists annsΔ annsΓ so, {{ Δ @ annsΔ ; Γ @ annsΓ ⊫ A @ so }}) /\
    (forall (Δ : gctx P) Γ Γ' σ, {{ Δ ; Γ ⊢s σ : Γ' }} -> exists annsΔ annsΓ annsΓ', {{ Δ @ annsΔ ; Γ @ annsΓ ⊫s σ : Γ' @ annsΓ' }}).
Proof.
  apply syntactic_wf_mut_ind';
    intros; destruct_conjs; mauto 3;
    gen_presup_anns;
    try solve [repeat eexists; mauto 2].

  - inversion HΓ; subst.
    eexists; econstructor; mauto 3.

  - 
    
#[local]
Ltac gen_annotated_judg_IH P ann_gctx ann_ctx ann_exp ann_typ ann_sub :=
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
        assert {{ ⊫ Γ, A with (so_Some s)::anns }} by mauto
    end.
                

#[local]
Ltac gen_sort_none P :=
  repeat
    match goal with
    | s : P |- _ =>
        let Hs := fresh "Hs" in
        eassert {{ ^?Γ with ?anns ⊫ Sort@s @ ^so_None }} by mauto 3;
        mark s
    end;
  unmark_all.





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
    epose proof wf_exp_implies_wf_exp_ann P ((so_Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H4 H1.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    destruct_conjs.
    econstructor; mauto.
    

  - clear HM0 HM1 H H5.
    epose proof wf_exp_implies_wf_exp_ann P anns Γ A0 {{{ Sort@s1 }}} Hanns H0 as [so].
    assert {{ ⊫ Γ, A0 with {{{ anns, ^ (so_Some s1) }}} }} by mauto 3.
    epose proof wf_exp_implies_wf_exp_ann P ((so_Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H5 H1 as [so'].
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
    assert {{ ⊫ Γ, ℕ with (so_Some s)::anns }} by mauto 4.
    assert (exists so : SortOption P, {{ Γ, ℕ with {{{ anns, ^ (so_Some s) }}} ⊫ A0 @ so }}) as [so] by mauto 2.
    assert {{ ⊢ Γ, ℕ, A0 }} by mauto 2.
    assert {{ ⊫ Γ, ℕ, A0 with so::(so_Some s)::anns }} by mauto 3.
    assert (exists so, {{ Γ with anns ⊫ MZ : A0[Id,,zero] @ so }}) as [so'] by mauto 2.
    assert (exists so', {{ Γ, ℕ, A0 with so::(so_Some s)::anns ⊫ MS : A0[Wk∘Wk,,succ #1] @ so' }}) as [so''] by mauto 2.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    assert  {{ Γ with anns ⊫ zero : ℕ @ ^ (so_Some s) }} by mauto 2.
    assert {{ Γ with anns ⊫ ℕ[Id] @ ^(so_Some s) }} by mauto 4.
    assert {{ Γ with anns ⊫ ℕ @ ^(so_Some s) }} by mauto 4.
    assert {{ Γ with anns ⊫ zero : ℕ[Id] @ ^ (so_Some s) }} by (econstructor; mauto).
    assert {{ Γ with anns ⊫s Id,,zero : Γ, ℕ with {{{ anns, ^ (so_Some s) }}} }} by mauto 4.
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
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (so_Some s), so }}} ⊫ ℕ[Wk][Wk] @ ^ (so_Some s) }} by (do 2 (econstructor; mauto 3)).
    assert {{ # 1 : ℕ[Wk][Wk] @ so_Some s ∈ Γ, ℕ, A0 with {{{ anns, ^ (so_Some s), so }}} }} by mauto 3.
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (so_Some s), so }}} ⊫ #1 : ℕ[Wk][Wk] @ ^ (so_Some s) }} by mauto 2.
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (so_Some s), so }}} ⊫ #1 : ℕ @ ^ (so_Some s) }} by mauto 4.
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (so_Some s), so }}} ⊫ succ #1 : ℕ[Wk][Wk] @ ^ (so_Some s) }} by mauto .
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (so_Some s), so }}} ⊫ ℕ[Wk∘Wk] @ ^ (so_Some s) }} by (econstructor; mauto 4).
    assert {{ Γ, ℕ, A0 with {{{ anns, ^ (so_Some s), so }}} ⊫s Wk∘Wk,,succ #1 : Γ, ℕ with (so_Some s)::anns }} by (econstructor; mauto 4).

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
