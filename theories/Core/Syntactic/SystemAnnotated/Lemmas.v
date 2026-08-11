From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Import Syntax System Corollaries.
From McPTS.Core.Syntactic.SystemAnnotated Require Import Definitions.
Import Syntax_Notations.


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

Lemma t1 {P} : forall {Γ : ctx P} {anns M0 A},
  exists so : SortOption P, {{ Γ with anns ⊫ fst M0 : A @ so }}.
Admitted.
Lemma t2 {P} : forall {Γ : ctx P} {anns M0 B},
  exists so : SortOption P, {{ Γ with anns ⊫ snd M0 : B[Id,,fst M0] @ so }}.
Admitted.
Lemma t3 {P} : forall {Γ : ctx P} {anns M0 A0 N B s1 s2 s3} {r : Ru_sigma P s1 s2 s3},
  exists so : SortOption P, {{ Γ with anns ⊫ ⟨ r; M0 : A0; N : B ⟩ : Σ r A0 B @ so }}.
Admitted.

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
  - destruct (wf_ctx_implies_wf_ctx_ann _ _ H0) as [anns].
    destruct (wf_typ_implies_wf_typ_ann _ _ _ _ H H1) as [so].
    eexists; econstructor; eassumption.
  - eexists.
    destruct (wf_exp_implies_wf_exp_ann P ((so_Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H4 H1).
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    econstructor; mauto.
  - clear HM0 HM1 H H5.
    destruct (wf_exp_implies_wf_exp_ann P anns Γ A0 {{{ Sort@s1 }}} Hanns H0) as [so].
    assert {{ ⊫ Γ, A0 with {{{ anns, ^ (so_Some s1) }}} }} by mauto 3.
    destruct (wf_exp_implies_wf_exp_ann P ((so_Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H5 H1) as [so'].
    destruct (wf_exp_implies_wf_exp_ann P anns Γ _ _ Hanns H2) as [soΠ].
    eexists.
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    econstructor; mauto 4.
  - clear HM0 HM1 H H5.
    destruct (wf_exp_implies_wf_exp_ann P anns Γ A0 {{{ Sort@s1 }}} Hanns H0) as [so].
    assert {{ ⊫ Γ, A0 with (so_Some s1)::anns }} by mauto 3.
    destruct (wf_exp_implies_wf_exp_ann P ((so_Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H5 H1) as [so'].
    destruct (wf_exp_implies_wf_exp_ann P anns Γ M0 A0 Hanns H2) as [soM].
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    assert {{ Γ ⊢ A0 ≈ A0[Id] : Sort@s1 }} by mauto 3.
    assert {{ Γ ⊢ A0 ⊆ A0[Id] }} by mauto 3.
    assert {{ Γ with anns ⊫ M0 : A0[Id] @ ^ (so_Some s1) }} by (econstructor; mauto 4).
    assert {{ Γ with anns ⊫s Id,,M0 : Γ, A0 with (so_Some s1)::anns }} by mauto 4.
    eexists.
    econstructor; mauto 4.
  - destruct (wf_exp_implies_wf_exp_ann P anns Γ A {{{ Sort@s1 }}} Hanns H0) as [so].
    assert {{ ⊫ Γ, A with {{{ anns, ^ (so_Some s1) }}} }} by mauto 3.
    destruct (wf_exp_implies_wf_exp_ann P ((so_Some s1)::anns) {{{ Γ, A }}} B {{{ Sort@s2 }}} H6 H1) as [so'].
    destruct (wf_exp_implies_wf_exp_ann P anns Γ M0 {{{ Σ r A B }}} Hanns H2) as [soM].
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    assert {{ Γ with anns ⊫ Σ r A B : Sort@s3 @ ^(so_None) }} by mauto 3.
    assert {{ Γ with anns ⊫ Σ r A B @ ^(so_Some s3) }} by mauto 2.
    assert {{ Γ with anns ⊫ M0 : Σ r A B @ ^(so_Some s3) }} by mauto 2.
    econstructor; mauto 3.
  - destruct (wf_exp_implies_wf_exp_ann P anns Γ A0 {{{ Sort@s1 }}} Hanns H0) as [so].
    assert {{ ⊫ Γ, A0 with {{{ anns, ^ (so_Some s1) }}} }} by mauto 3.
    destruct (wf_exp_implies_wf_exp_ann P ((so_Some s1)::anns) {{{ Γ, A0 }}} B {{{ Sort@s2 }}} H6 H1) as [so'].
    destruct (wf_exp_implies_wf_exp_ann P anns Γ M0 {{{ Σ r A0 B }}} Hanns H2) as [soM].
    clear wf_ctx_implies_wf_ctx_ann wf_exp_implies_wf_exp_ann wf_typ_implies_wf_typ_ann wf_sub_implies_wf_sub_ann.
    assert {{ Γ with anns ⊫ Σ r A0 B : Sort@s3 @ ^(so_None) }} by mauto 3.
    assert {{ Γ with anns ⊫ Σ r A0 B @ ^(so_Some s3) }} by mauto 2.
    assert {{ Γ with anns ⊫ M0 : Σ r A0 B @ ^(so_Some s3) }} by mauto 2.
    econstructor; mauto 3.
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
