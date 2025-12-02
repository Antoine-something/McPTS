From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

Generalizable All Variables.


Section Translation.
  Context (P : PtsSig) (pred_P : PredicativeSig P).

  Definition eSig : PtsSig := eP P.
  Definition ePred : PredicativeSig eSig := epred_P P pred_P.
  
  Fixpoint translate_exp (M : exp P) : exp eSig :=
    match M with
    | a_st s => @a_st eSig (st_P s)
    | a_pi r A B => @a_pi eSig _ _ _ (ru_P r) (translate_exp A) (translate_exp B)
    | a_fn r A M => @a_fn eSig _ _ _ (ru_P r) (translate_exp A) (translate_exp M)
    | a_app M N => a_app (translate_exp M) (translate_exp N)
    | a_var n => a_var n
    | a_sub M σ => a_sub (translate_exp M) (translate_sub σ)
    end
      
  with translate_sub (σ : sub P) : sub eSig :=
    match σ with
    | a_id => a_id
    | a_weaken => a_weaken
    | a_compose σ τ => a_compose (translate_sub σ) (translate_sub τ)
    | a_extend σ M => a_extend (translate_sub σ) (translate_exp M)
    end.

  Definition translate_ctx (Γ : ctx P) : ctx eSig := List.map (translate_exp) Γ.
End Translation.

Arguments translate_exp {P}.
Arguments translate_sub {P}.
Arguments translate_ctx {P}.

Lemma translate_wf_ctx_lookup {P} : forall {A : typ P} {n Γ},
    {{ #n : A ∈ Γ }} ->
    {{ #n : ^(translate_exp A) ∈ ^(translate_ctx Γ) }}.
Proof.
  intros * H.
  induction H; simpl; mauto.
Qed.

#[export]
Hint Resolve translate_wf_ctx_lookup : mcpts.
 
#[local]
Ltac gen_translate_IH translate_wf_ctx translate_wf_exp translate_wf_typ translate_wf_sub translate_wf_ctx_eq translate_wf_exp_eq translate_wf_typ_eq translate_wf_sub_eq H :=
  match type of H with
  | {{ ⊢ ^?Γ }} =>
      pose proof translate_wf_ctx _ _ H
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      pose proof translate_wf_exp _ _ _ _ H
  | {{ ^?Γ ⊢ ^?A }} =>
      pose proof translate_wf_typ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      pose proof translate_wf_sub _ _ _ _ H
  | {{ ⊢ ^?Γ ≈ ^?Δ }} =>
      pose proof translate_wf_ctx_eq _ _ _ H
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} =>
      pose proof translate_wf_exp_eq _ _ _ _ _ H
  | {{ ^?Γ ⊢ ^?A ≈ ^?B }} =>
      pose proof translate_wf_typ_eq _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} =>
      pose proof translate_wf_sub_eq _ _ _ _ _ H
  end.

Lemma translate_wf_ctx {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ ^(translate_ctx Γ) }}
with translate_wf_exp {P} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp M) : ^(translate_exp A) }}
with translate_wf_typ {P} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp A) }}
with translate_wf_sub {P} : forall {Γ : ctx P} {σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ ^(translate_ctx Γ) ⊢s ^(translate_sub σ) : ^(translate_ctx Δ) }}
with translate_wf_ctx_eq {P} : forall {Γ : ctx P} {Δ},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ ⊢ ^(translate_ctx Γ) ≈ ^(translate_ctx Δ) }}
with translate_wf_exp_eq {P} : forall {Γ : ctx P} {M M' A},
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp M) ≈ ^(translate_exp M') : ^(translate_exp A) }}
with translate_wf_typ_eq {P} : forall {Γ : ctx P} {A A'},
    {{ Γ ⊢ A ≈ A' }} ->
    {{ ^(translate_ctx Γ) ⊢ ^(translate_exp A) ≈ ^(translate_exp A') }}      
with translate_wf_sub_eq {P} : forall {Γ : ctx P} {σ σ' Δ},
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ^(translate_ctx Γ) ⊢s ^(translate_sub σ) ≈ ^(translate_sub σ') : ^(translate_ctx Δ) }}.
Proof.
  all: inversion_clear 1;
    (on_all_hyp: gen_translate_IH translate_wf_ctx translate_wf_exp translate_wf_typ translate_wf_sub translate_wf_ctx_eq translate_wf_exp_eq translate_wf_typ_eq translate_wf_sub_eq);
    clear translate_wf_ctx translate_wf_exp translate_wf_typ translate_wf_sub translate_wf_ctx_eq translate_wf_exp_eq translate_wf_typ_eq translate_wf_sub_eq;
    try mautosolve 3.

  all: try (econstructor; mautosolve 4).
  all: econstructor; [econstructor|]; eauto.
Qed.

