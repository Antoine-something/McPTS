From McPTS Require Import PtsSignature LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic Require Export System.
Import Syntax_Notations.

(** ** Stability under global context subtyping *)

Lemma wf_gctx_sub_refl {P} : forall {Δ : gctx P},
    {{ ▶ Δ }} ->
    {{ ▶ Δ ⊆ Δ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve wf_gctx_sub_refl : mcpts.
 
Module gctxsub_judg.
  Lemma gctxsub_main {P : PtsSig} :
    (forall (Δ : gctx P) Γ, {{ Δ ▶ Γ }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ }}) /\
      (forall (Δ : gctx P) Γ Γ', {{ Δ ▶ Γ ⊆ Γ' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊆ Γ' }}) /\
      (forall (Δ : gctx P) Γ A M, {{ Δ ▶ Γ ⊢ M : A }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ M : A }}) /\
      (forall (Δ : gctx P) Γ A M M', {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ M ≈ M' : A }}) /\
      (forall (Δ : gctx P) Γ A, {{ Δ ▶ Γ ⊢ A }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ A }}) /\
      (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ≈ A' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ A ≈ A' }}) /\
      (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ A ⊆ A' }}) /\
      (forall (Δ : gctx P) Γ Γ' σ, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢s σ : Γ' }}) /\
      (forall (Δ : gctx P) Γ Γ' σ σ', {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢s σ ≈ σ' : Γ' }}).
  Proof.
    apply syntactic_wf_local_mut_ind;
      intros;
      (on_all_hyp: ltac:(fun H =>
                           match type of H with
                           | {{ ▶ ^?Δ' ⊆ ^?Δ }} => rename H into HΔΔ'          
                           | _ => idtac
                           end)
      );
      destruct (presup_wf_gctx_subtyp HΔΔ');
      mauto 4;
      try (solve [econstructor; mauto 2]).
    
    - pose proof (wf_gctx_subtyp_gctx_lookup HΔΔ' ltac:(eassumption)) as [A' []].
      assert {{ Δ' ▶ Γ ⊢ A'[σ] ⊆ A[σ] }} by mauto 3.
      eapply wf_exp_conv; mauto 3.
      enough {{ Δ' ▶ ⋅ ⊢ A' }}; mauto 3.
    - assert {{ Δ'▶ Γ ⊢ Sort@s1 : Sort@s2 }} by mauto 2.
      assert {{ Δ'▶ Γ' ⊢ Sort@s1 : Sort@s2 }} by mauto 2.
      assert {{ Δ'▶ Γ ⊢s σ : Γ' }} by mauto 2.
      mauto 3.
    - pose proof (wf_gctx_subtyp_gctx_lookup HΔΔ' ltac:(eassumption)) as [A' []].
      assert {{ Δ' ▶ Γ ⊢ A'[σ] ⊆ A[σ] }} by mauto 3.
      eapply wf_exp_eq_conv; mauto 3.    
  Qed.

  #[local]
  Ltac solve_gctxsub P :=
    pose proof (@gctxsub_main P); destruct_conjs; eauto.

  Corollary gctxsub_wf_ctx {P} : forall {Δ : gctx P} {Γ}, {{ Δ ▶ Γ }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ }}.
  Proof. solve_gctxsub P. Qed.

  Corollary gctxsub_wf_ctx_subtyp {P} : forall {Δ : gctx P} {Γ Γ'}, {{ Δ ▶ Γ ⊆ Γ' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊆ Γ' }}.
  Proof. solve_gctxsub P. Qed.

  Corollary gctxsub_wf_exp {P} : forall {Δ : gctx P} {Γ A M}, {{ Δ ▶ Γ ⊢ M : A }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ M : A }}.
  Proof. solve_gctxsub P. Qed.

  Corollary gctxsub_wf_exp_eq {P} : forall {Δ : gctx P} {Γ A M M'}, {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ M ≈ M' : A }}.
  Proof. solve_gctxsub P. Qed.

  Corollary gctxsub_wf_typ {P} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ ⊢ A }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ A }}.
  Proof. solve_gctxsub P. Qed.

  Corollary gctxsub_wf_typ_eq {P} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ≈ A' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ A ≈ A' }}.
  Proof. solve_gctxsub P. Qed.

  Corollary gctxsub_wf_typ_subtyp {P} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢ A ⊆ A' }}.
  Proof. solve_gctxsub P. Qed.

  Corollary gctxsub_wf_sub {P} : forall {Δ : gctx P} {Γ Γ' σ}, {{ Δ ▶ Γ ⊢s σ : Γ' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢s σ : Γ' }}.
  Proof. solve_gctxsub P. Qed.  

  Corollary gctxsub_wf_sub_eq {P} : forall {Δ : gctx P} {Γ Γ' σ σ'}, {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ⊢s σ ≈ σ' : Γ' }}.
  Proof. solve_gctxsub P. Qed.

  #[export]
  Hint Resolve gctxsub_wf_ctx gctxsub_wf_ctx_subtyp gctxsub_wf_exp gctxsub_wf_exp_eq gctxsub_wf_typ gctxsub_wf_typ_eq gctxsub_wf_typ_subtyp gctxsub_wf_sub gctxsub_wf_sub_eq : mcpts.

  Corollary gctxsub_wf_ctx_eq {P} : forall {Δ : gctx P} {Γ Γ'}, {{ Δ ▶ Γ ≈ Γ' }} -> forall {Δ'}, {{ ▶ Δ' ⊆ Δ }} -> {{ Δ' ▶ Γ ≈ Γ' }}.
  Proof.
    induction 1; mauto 3.
    intros; econstructor; mauto 3.
  Qed.

  #[export]
  Hint Resolve gctxsub_wf_ctx_eq : mcpts.
End gctxsub_judg.

Export gctxsub_judg.

Lemma wf_gctx_subtyp_trans {P} : forall (Δ0 Δ1 : gctx P),
    {{ ▶ Δ0 ⊆ Δ1 }} ->
    forall Δ2,
      {{ ▶ Δ1 ⊆ Δ2 }} ->
      {{ ▶ Δ0 ⊆ Δ2 }}.
Proof.
  induction 1; intros; progressive_inversion; [constructor |].
  eapply wf_gctx_subtyp_extend; mauto 3.
Qed.

#[export]
Hint Resolve wf_gctx_subtyp_trans : mcpts.

#[export]
Instance wf_gctx_subtyp_trans_ins {P} : Transitive (@wf_gctx_subtyp P).
Proof. eauto using wf_gctx_subtyp_trans. Qed.

(** Rewrite rules based on global context subtyping *)
Add Parametric Morphism {P} : (@wf_ctx P)
  with signature wf_gctx_subtyp --> eq ==> Basics.impl as gctxsub_ctx_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_ctx_eq P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> Basics.impl as gctxsub_ctx_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_ctx_subtyp P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> Basics.impl as gctxsub_ctx_subtyp_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_exp P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> eq ==> Basics.impl as gctxsub_exp_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_exp_eq P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> eq ==> eq ==> Basics.impl as gctxsub_exp_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_typ P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> Basics.impl as gctxsub_typ_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_typ_eq P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> eq ==> Basics.impl as gctxsub_typ_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_typ_subtyp P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> eq ==> Basics.impl as gctxsub_typ_subtyp_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_sub P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> eq ==> Basics.impl as gctxsub_sub_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_sub_eq P)
  with signature wf_gctx_subtyp --> eq ==> eq ==> eq ==> eq ==> Basics.impl as gctxsub_sub_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.


(** ** Stability under local context subtyping *)
Lemma wf_ctx_sub_refl {P} : forall {Δ : gctx P} {Γ},
    {{ Δ ▶ Γ }} ->
    {{ Δ ▶ Γ ⊆ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve wf_ctx_sub_refl : mcpts.

Module ctxsub_judg.
  Lemma ctxsub_main {P : PtsSig} :
    (forall (Δ : gctx P) Γ A M, {{ Δ ▶ Γ ⊢ M : A }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ M : A }}) /\
      (forall (Δ : gctx P) Γ A M M', {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ M ≈ M' : A }}) /\
      (forall (Δ : gctx P) Γ A, {{ Δ ▶ Γ ⊢ A }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ A }}) /\
      (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ≈ A' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ A ≈ A' }}) /\
      (forall (Δ : gctx P) Γ A A', {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ A ⊆ A' }}) /\
      (forall (Δ : gctx P) Γ Γ'' σ, {{ Δ ▶ Γ ⊢s σ : Γ'' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢s σ : Γ'' }}) /\
      (forall (Δ : gctx P) Γ Γ'' σ σ', {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ'' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢s σ ≈ σ' : Γ'' }}).
  Proof.
    apply syntactic_wf_no_ctx_mut_ind;
    intros;
      (on_all_hyp: ltac:(fun H =>
                           match type of H with
                           | {{ ^?Δ ▶ ^?Γ' ⊆ ^?Γ }} => rename H into HΓΓ'
                           | _ => idtac
                           end)
      );
      destruct (presup_wf_ctx_subtyp HΓΓ') as [HΔ [HΓ HΓ']];
      mauto 4.

    (** Function cases *)
    1-3,7-11: (assert {{ Δ ▶ Γ' ⊢ A : Sort@s1 }} by eauto;
               assert {{ Δ ▶ Γ', A ⊆ Γ, A }} by (econstructor; mauto 2);
               econstructor; mauto 2).

    (** Recursion cases *)
    2,4-6:(assert {{ Δ ▶ Γ' ⊢ ℕ }} by mauto 3;
           assert {{ Δ ▶ Γ ⊢ ℕ }} by mauto 3;
           assert {{ Δ ▶ Γ', ℕ ⊆ Γ, ℕ }} by mauto 4;
           assert {{ Δ ▶ Γ', ℕ, A ⊆ Γ, ℕ, A }} by (econstructor; mauto);
           econstructor; mauto 2).

    (** Local variable cases *)
    1,3: (assert (exists A', {{ #x : A' ∈ Γ' }} /\ {{ Δ ▶ Γ' ⊢ A' ⊆ A }}) as [A' []] by mauto 2;
          assert {{ Δ ▶ Γ' ⊢ #x : A' }} by mauto 3;
          solve [econstructor; mauto 3]).

    (** Conversion cases *)
    1,3: econstructor; mauto 2.

    (** Weakening cases *)
    3,4: (inversion_clear HΓΓ';
          assert {{ Δ ▶ Γ0, A0 }} by mauto 3;
          solve [econstructor; mauto 2]).
    
    (* wf_exp_eq, variable shift case *)
    - inversion_clear HΓΓ'.
      assert (exists A1, {{ #x : A1 ∈ Γ0 }} /\ {{ Δ ▶ Γ0 ⊢ A1 ⊆ A }}) as [A1 []] by mauto 2.
      assert {{ Δ ▶ Γ0, A0 }} by mauto 3.
      eapply wf_exp_eq_conv; mauto 3.
      enough {{ Δ ▶ Γ0 ⊢ A }}; mauto 3.

    (* wf_typ_subtyp, pi case *)
    - assert {{ Δ ▶ Γ' ⊢ A' }} by mauto 3.
      assert {{ Δ ▶ Γ', A' ⊆ Γ, A' }} by mauto 5.
      assert {{ Δ ▶ Γ' ⊢ A }} by mauto 3.
      assert {{ Δ ▶ Γ', A ⊆ Γ, A }} by mauto 5.
      assert {{ Δ ▶ Γ', A' ⊢ B ⊆ B' }} by mauto 2.
      assert {{ Δ ▶ Γ', A' ⊢ B' }} by mauto 2.
      assert {{ Δ ▶ Γ', A ⊢ B }} by mauto 3.
      assert {{ Δ ▶ Γ' ⊢ A ≈ A' }} by mauto 3.
      solve [econstructor; mauto 3].
  Qed.

  #[local]
  Ltac solve_ctxsub P :=
    pose proof (@ctxsub_main P); destruct_conjs; eauto.
  
  Corollary ctxsub_wf_exp {P : PtsSig} : forall {Δ : gctx P} {Γ A M}, {{ Δ ▶ Γ ⊢ M : A }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ M : A }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_exp_eq {P : PtsSig} : forall {Δ : gctx P} {Γ A M M'}, {{ Δ ▶ Γ ⊢ M ≈ M' : A }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ M ≈ M' : A }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_typ {P : PtsSig} : forall {Δ : gctx P} {Γ A}, {{ Δ ▶ Γ ⊢ A }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ A }}.
  Proof. solve_ctxsub P. Qed.
    
  Corollary ctxsub_wf_typ_eq {P : PtsSig} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ≈ A' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ A ≈ A' }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_typ_subtyp {P : PtsSig} : forall {Δ : gctx P} {Γ A A'}, {{ Δ ▶ Γ ⊢ A ⊆ A' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢ A ⊆ A' }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_sub {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'' σ}, {{ Δ ▶ Γ ⊢s σ : Γ'' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢s σ : Γ'' }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_sub_eq {P : PtsSig} : forall {Δ : gctx P} {Γ Γ'' σ σ'}, {{ Δ ▶ Γ ⊢s σ ≈ σ' : Γ'' }} -> forall {Γ'}, {{ Δ ▶ Γ' ⊆ Γ }} -> {{ Δ ▶ Γ' ⊢s σ ≈ σ' : Γ'' }}.
  Proof. solve_ctxsub P. Qed.

  #[export]
  Hint Resolve ctxsub_wf_exp ctxsub_wf_exp_eq ctxsub_wf_typ ctxsub_wf_typ_eq ctxsub_wf_typ_subtyp ctxsub_wf_sub ctxsub_wf_sub_eq : mcpts.
End ctxsub_judg.
   
Export ctxsub_judg.

Lemma wf_ctx_subtyp_trans {P} : forall (Δ : gctx P) Γ0 Γ1,
    {{ Δ ▶ Γ0 ⊆ Γ1 }} ->
    forall  Γ2,
    {{ Δ ▶ Γ1 ⊆ Γ2 }} ->
    {{ Δ ▶ Γ0 ⊆ Γ2 }}.
Proof.
  induction 1; intros; progressive_inversion; [constructor; mauto 2 |].
  eapply wf_ctx_subtyp_extend; mauto 3.
Qed.

#[export]
Hint Resolve wf_ctx_subtyp_trans : mcpts.

#[export]
Instance wf_ctx_sub_trans_ins {P} {Δ : gctx P} : Transitive (wf_ctx_subtyp Δ).
Proof. eauto using wf_ctx_subtyp_trans. Qed.

(** Rewrite rules based on local context subtyping *)
Add Parametric Morphism {P} {Δ : gctx P} : (wf_exp Δ)
  with signature wf_ctx_subtyp Δ --> eq ==> eq ==> Basics.impl as ctxsub_exp_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} {Δ : gctx P} : (wf_exp_eq Δ)
  with signature wf_ctx_subtyp Δ --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_exp_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} {Δ : gctx P} : (wf_typ Δ)
  with signature wf_ctx_subtyp Δ --> eq ==> Basics.impl as ctxsub_typ_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} {Δ : gctx P} : (wf_typ_eq Δ)
  with signature wf_ctx_subtyp Δ --> eq ==> eq ==> Basics.impl as ctxsub_typ_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} {Δ : gctx P} : (wf_typ_subtyp Δ)
  with signature wf_ctx_subtyp Δ --> eq ==> eq ==> Basics.impl as ctxsub_typ_subtyp_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} {Δ : gctx P} : (wf_sub Δ)
  with signature wf_ctx_subtyp Δ --> eq ==> eq ==> Basics.impl as ctxsub_sub_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} {Δ : gctx P} : (wf_sub_eq Δ)
  with signature wf_ctx_subtyp Δ --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_sub_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.
