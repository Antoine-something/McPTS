From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic.System Require Import Definitions Lemmas.Instances.
Import Syntax_Notations.

(** * Basic properties of context judgments *)
(** ** Properties of context lookups *)
(** Can only lookup variables in the contexts *)
Lemma ctx_lookup_lt {P : PtsSig} : forall {Γ : ctx P} {A x},
    {{ #x : A ∈ Γ }} ->
    x < length Γ.
Proof.
  induction 1; simpl; lia.
Qed.
#[export]
Hint Resolve ctx_lookup_lt : mcpts.

(** Context lookup is unique *)
Lemma functional_ctx_lookup {P : PtsSig} : forall {Γ : ctx P} {A A' x},
    {{ #x : A ∈ Γ }} ->
    {{ #x : A' ∈ Γ }} ->
    A = A'.
Proof with mautosolve.
  intros * Hx Hx'; gen A'.
  dependent induction Hx; intros; inversion_clear Hx'; 
    f_equal;
    intuition.
Qed.

#[export]
Hint Resolve functional_ctx_lookup : mcpts. 

(** ** Basic inversion principle for contexts *)
Lemma ctx_decomp {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A }}.
Proof with now eauto.
  inversion 1; split; mauto 2.
Qed.

#[export]
Hint Resolve ctx_decomp : mcpts.

Corollary ctx_decomp_left {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

Corollary ctx_decomp_right {P : PtsSig} : forall {Γ : ctx P} {A}, {{ ⊢ Γ, A }} -> {{ Γ ⊢ A }}.
Proof with easy.
  intros * ?%ctx_decomp...
Qed.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mcpts.

(** Tactic to apply the inversion principle *)
#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | {{ ⊢ ^?Γ, ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HAs" in
      pose proof ctx_decomp H as [HΓ HA];
      match goal with
      | _: {{ Γ ⊢ A }} |- _ => clear HA
      | _: __mark__ _ {{ Γ ⊢ A }} |- _ => clear HA
      end
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.


(** * Basic presupposition results *)
(** ** For contexts equality *)
Lemma presup_wf_ctx_eq {P : PtsSig} : forall {Γ Γ' : ctx P}, {{ ⊢ Γ ≈ Γ' }} -> {{ ⊢ Γ }} /\ {{ ⊢ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_ctx_eq_left {P : PtsSig} : forall {Γ Γ' : ctx P}, {{ ⊢ Γ ≈ Γ' }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_eq...
Qed.

Corollary presup_wf_ctx_eq_right {P : PtsSig} : forall {Γ Γ' : ctx P}, {{ ⊢ Γ ≈ Γ' }} -> {{ ⊢ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_ctx_eq...
Qed.

#[export]
Hint Resolve presup_wf_ctx_eq presup_wf_ctx_eq_left presup_wf_ctx_eq_right : mcpts.

(** ** For context subtyping *)
Lemma presup_wf_ctx_subtyp {P} : forall {Γ Γ' : ctx P}, {{ ⊢ Γ ⊆ Γ' }} -> {{ ⊢ Γ }} /\ {{ ⊢ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.

Corollary presup_wf_ctx_subtyp_left {P} : forall {Γ Γ' : ctx P}, {{ ⊢ Γ ⊆ Γ' }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_wf_ctx_subtyp...
Qed.

Corollary presup_wf_ctx_subtyp_right {P} : forall {Γ Γ' : ctx P}, {{ ⊢ Γ ⊆ Γ' }} -> {{ ⊢ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_ctx_subtyp...
Qed.

#[export]
Hint Resolve presup_wf_ctx_subtyp presup_wf_ctx_subtyp_left presup_wf_ctx_subtyp_right : mcpts.

(** ** For substitution well-formedness *)
Lemma presup_wf_sub {P : PtsSig} : forall {Γ : ctx P} {Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> {{ ⊢ Γ }} /\ {{ ⊢ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs...
Qed.
  
Corollary presup_wf_sub_codom {P : PtsSig} : forall {Γ : ctx P} {Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_wf_sub...
Qed.

Corollary presup_wf_sub_dom {P : PtsSig} : forall {Γ : ctx P} {Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> {{ ⊢ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_sub...
Qed.

#[export]
Hint Resolve presup_wf_sub presup_wf_sub_dom presup_wf_sub_codom : mcpts.


(** * Context presupposition *)
(** ** For expression well-formedness *)
Corollary presup_wf_exp_ctx {P : PtsSig} : forall {Γ : ctx P} {M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_wf_exp_ctx : mcpts.

(** ** For type well-formedness *)
Lemma presup_wf_typ {P} : forall {Γ : ctx P} {A}, {{ Γ ⊢ A }} -> {{ ⊢ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve presup_wf_typ : mcpts.

(** ** For substitution equality *)
Lemma presup_wf_sub_eq_ctx {P : PtsSig} : forall {Γ : ctx P} {Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ⊢ Γ }} /\ {{ ⊢ Γ' }}.
Proof with mautosolve.
  induction 1; destruct_pairs; split; mauto 3.
Qed.

Corollary presup_wf_sub_eq_ctx_codom {P : PtsSig} : forall {Γ : ctx P} {Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_wf_sub_eq_ctx...
Qed.

Corollary presup_wf_sub_eq_ctx_dom {P : PtsSig} : forall {Γ : ctx P} {Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> {{ ⊢ Γ' }}.
Proof with easy.
  intros * ?%presup_wf_sub_eq_ctx...
Qed.

#[export]
Hint Resolve presup_wf_sub_eq_ctx presup_wf_sub_eq_ctx_codom presup_wf_sub_eq_ctx_dom : mcpts.

(** ** For expression equality *)
Lemma presup_wf_exp_eq_ctx {P : PtsSig} : forall {Γ : ctx P} {M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1; destruct_pairs...
Qed.

#[export]
Hint Resolve presup_wf_exp_eq_ctx : mcpts.

(** ** For type equality *)
Lemma presup_wf_typ_eq_ctx {P : PtsSig} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ≈ A' }} -> {{ ⊢ Γ }}.
Proof with mautosolve 2.
  induction 1; destruct_pairs...
Qed.

#[export]
Hint Resolve presup_wf_typ_eq_ctx : mcpts.

(** ** For subtyping *)
Lemma presup_wf_typ_subtyp_core {P} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ⊆ A' }} -> {{ ⊢ Γ }} /\ {{ Γ ⊢ A' }}.
Proof with mautosolve 2.
  induction 1; destruct_conjs; split; mauto 3.
Qed.

Corollary presup_wf_typ_subtyp_ctx {P} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ⊆ A' }} -> {{ ⊢ Γ }}.
Proof with easy.
  intros * ?%presup_wf_typ_subtyp_core...
Qed.

Corollary presup_wf_typ_subtyp_right {P} : forall {Γ : ctx P} {A B}, {{ Γ ⊢ A ⊆ B }} -> {{ Γ ⊢ B }}.
Proof with easy.
  intros * ?%presup_wf_typ_subtyp_core...
Qed.

#[export]
Hint Resolve presup_wf_typ_subtyp_core presup_wf_typ_subtyp_ctx presup_wf_typ_subtyp_right : mcpts.

(** ** Presupposition for context lookups *)    
Lemma presup_ctx_lookup_typ {P : PtsSig} : forall {Γ : ctx P} {A x},
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    {{ Γ ⊢ A }}.
Proof with mautosolve 4.
  intros * HΓ.
  induction 1; inversion_clear HΓ.
  - assert {{ Γ, A ⊢s Wk : Γ }} by mauto 3.
    eapply wf_typ_sub; mauto 2.
  - assert {{ Γ, B ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ ⊢ A }} by mauto 2.
    eapply wf_typ_sub; mauto 2.
Qed.

#[export]
Hint Resolve presup_ctx_lookup_typ : mcpts.


(** * Immediate consequences of context presupposition *)
(** Context subtyping is reflexive with respect to context equality *)
Corollary wf_ctx_sub_refl {P} : forall {Γ : ctx P} {Γ'},
    {{ ⊢ Γ ≈ Γ' }} ->
    {{ ⊢ Γ ⊆ Γ' }}.
Proof. induction 1; mauto. Qed.

#[export]
Hint Resolve wf_ctx_sub_refl : mcpts.

(** Propagation of identity substitutions is admissible *)
Corollary wf_typ_eq_sub_id {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ A[Id] ≈ A }}.
Proof.
  induction 1; mauto 3.
  transitivity {{{ A[σ∘Id] }}}; mauto 4.
  symmetry.
  mauto 4.
Qed.

#[export]
Hint Resolve wf_typ_eq_sub_id : mcpts.


(** ** Equality-based conversions *)
(** For expression well-formedness *)
Corollary wf_exp_conv_exp_eq {P} : forall {Γ : ctx P} {M A s A'},
    {{ Γ ⊢ M : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A : Sort@s }} -> 
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
  intros.
  assert {{ Γ ⊢ A }} by mauto 2.
  assert {{ Γ ⊢ A' }} by mauto 2.
  mauto.
Qed.

#[export]
Hint Resolve wf_exp_conv_exp_eq : mcpts.
  
Corollary wf_exp_conv_typ_eq {P} : forall {Γ : ctx P} {M A A'},
    {{ Γ ⊢ M : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ A' }} ->
    {{ Γ ⊢ A ≈ A'  }} ->
    {{ Γ ⊢ M : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_conv_typ_eq : mcpts.

(** For substitution well-formedness *)
Corollary wf_sub_conv_eq {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' σ},
  {{ Γ ⊢s σ : Γ' }} ->
  {{ ⊢ Γ' ≈ Γ'' }} ->
  {{ Γ ⊢s σ : Γ'' }}.
Proof.
  intros.
  assert {{ ⊢ Γ'' }} by mauto 2.
  mauto.
Qed.

#[export]
Hint Resolve wf_sub_conv_eq : mcpts.

(* Substitution can already get its rewrite rule, but for expressions we wait until the optimized version *)
Add Parametric Morphism {P : PtsSig} (Γ : ctx P) : (wf_sub Γ)
    with signature wf_ctx_eq ==> eq ==> iff as wf_sub_morphism_iff1.
Proof.
  intros Γ' Γ'' H **; split; [| symmetry in H]; mauto.
Qed.

(** For expression equality *)
Corollary wf_exp_eq_conv_exp_eq {P} : forall {Γ : ctx P} {M M' A A' s},
    {{ Γ ⊢ M ≈ M' : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A : Sort@s }} -> 
    {{ Γ ⊢ A' : Sort@s }} ->
    {{ Γ ⊢ A ≈ A' : Sort@s }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed. 

#[export]
Hint Resolve wf_exp_eq_conv_exp_eq : mcpts.

Corollary wf_exp_eq_conv_typ_eq {P} : forall {Γ : ctx P} {M M' A A'},
    {{ Γ ⊢ M ≈ M' : A }} ->
    (** The next two arguments will be removed in SystemOpt *)
    {{ Γ ⊢ A }} -> 
    {{ Γ ⊢ A' }} ->
    {{ Γ ⊢ A ≈ A' }} ->
    {{ Γ ⊢ M ≈ M' : A' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_conv_typ_eq : mcpts.

(** For equality of substitutions *)
Corollary wf_sub_eq_conv_eq {P : PtsSig} : forall {Γ : ctx P} {Γ' Γ'' σ σ'},
    {{ Γ ⊢s σ ≈ σ' : Γ' }} ->
    {{ ⊢ Γ' ≈ Γ'' }} ->
    {{ Γ ⊢s σ ≈ σ' : Γ'' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_eq_conv_eq : mcpts.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) : (wf_sub_eq Γ)
    with signature wf_ctx_eq ==> eq ==> eq ==> iff as wf_sub_eq_morphism_iff3.
Proof.
  intros Γ' Γ'' H **; split; [| symmetry in H]; mauto.
Qed.

(** ** Main presupposition result for expression well-formedness *)
Lemma presup_wf_exp_typ {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ A }}.
Proof with mautosolve 3.
  induction 1; assert {{ ⊢ Γ }} by mauto 2; destruct_conjs; mauto 3.
  - enough {{ Γ ⊢s Id,,N : Γ, A }}; mauto 3.
    econstructor; mauto 2.
    enough {{ Γ ⊢ A[Id] ≈ A }}; mauto 3.
    symmetry in H4.
    mauto 4.
  - enough {{ Γ ⊢s Id,,M : Γ, ℕ }}; mauto 3.
    econstructor; mauto 3.
    enough {{ Γ ⊢ ℕ[Id] ≈ ℕ }}; mauto 3.
    symmetry in H4.
    mauto 4.
Qed.

Lemma presup_wf_exp {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ {{ Γ ⊢ A }}.
Proof.
  intros; split; mauto 2 using presup_wf_exp_typ.
Qed.

#[export]
Hint Resolve presup_wf_exp : mcpts.

(** * Tactics to apply core presupposition results *)
Ltac gen_core_presup H :=
  match type of H with
  (** For context judgments *)
  | {{ ⊢ ^?Γ ≈ ^?Γ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ'' := fresh "HΓ'" in
      pose proof presup_wf_ctx_eq H as [HΓ HΓ']
  | {{ ⊢ ^?Γ ⊆ ^?Γ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      pose proof presup_wf_ctx_subtyp H as [HΓ HΓ']
  (** For expression judgments *)
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HAwf := fresh "HAwf" in
      pose proof presup_wf_exp H as [HΓ HAwf]
  | {{ ^?Γ ⊢ ^?M ≈ ^?M' : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HAwf := fresh "HAwf" in
      pose proof presup_wf_exp_eq_ctx H as [HΓ HAwf]
  (** For type judgments *)
  | {{ ^?Γ ⊢ ^?A }} =>
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_typ H as HΓ
  | {{ ^?Γ ⊢ ^?A ≈ ^?A' }} =>
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_typ_eq_ctx H as HΓ
  | {{ ^?Γ ⊢ ^?A ⊆ ^?A' }} =>
      let HΓ := fresh "HΓ" in
      let HA' := fresh "HA'wf" in
      pose proof presup_wf_typ_subtyp_core H as [HΓ HA']
  (** For substitution judgments *)
  | {{ ^?Γ ⊢s ^?σ : ^?Γ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in      
      pose proof presup_wf_sub H as [HΓ HΓ']
  | {{ ^?Γ ⊢s ^?σ ≈ ^?σ' : ^?Γ' }} =>
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in      
      pose proof presup_wf_sub_eq_ctx H as [HΓ HΓ']
  end.

Ltac gen_lookup_presup H :=
  match type of H with
  | {{ #?x : ^?A ∈ ^?Γ }} =>
      match goal with
      | _: {{ Γ ⊢ A }} |- _ => fail
      | _ =>
          let HA := fresh "HAwf" in
          pose proof presup_ctx_lookup_typ ltac:(eassumption) H as HA
      end
  end.

Ltac gen_core_presups := (on_all_hyp: fun H => gen_core_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.

