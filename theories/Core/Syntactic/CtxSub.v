From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export System.
Import Syntax_Notations.

(** * Stability under local context subtyping *)
Module ctxsub_judg.
  Lemma ctxsub_main {P : PtsSig} :
    (forall (Γ : ctx P) A M, {{ Γ ⊢ M : A }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ M : A }}) /\
      (forall (Γ : ctx P) A M M', {{ Γ ⊢ M ≈ M' : A }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ M ≈ M' : A }}) /\
      (forall (Γ : ctx P) A, {{ Γ ⊢ A }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ A }}) /\
      (forall (Γ : ctx P) A A', {{ Γ ⊢ A ≈ A' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ A ≈ A' }}) /\
      (forall (Γ : ctx P) A A', {{ Γ ⊢ A ⊆ A' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ A ⊆ A' }}) /\
      (forall (Γ : ctx P) Γ'' σ, {{ Γ ⊢s σ : Γ'' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢s σ : Γ'' }}) /\
      (forall (Γ : ctx P) Γ'' σ σ', {{ Γ ⊢s σ ≈ σ' : Γ'' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢s σ ≈ σ' : Γ'' }}).
  Proof.
    apply syntactic_wf_no_ctx_mut_ind;
    intros;
      (on_all_hyp: ltac:(fun H =>
                           match type of H with
                           | {{ ⊢ ^?Γ' ⊆ ^?Γ }} => rename H into HΓΓ'
                           | _ => idtac
                           end)
      );
      destruct (presup_wf_ctx_subtyp HΓΓ') as [HΓ HΓ'];
      mauto 4.

    (** Function cases *)
    1-3,7-11: (assert {{ Γ' ⊢ A : Sort@s1 }} by eauto;
               assert {{ ⊢ Γ', A ⊆ Γ, A }} by (econstructor; mauto 2);
               econstructor; mauto 2).

    (** Recursion cases *)
    2,4-6:(assert {{ Γ' ⊢ ℕ }} by mauto 3;
           assert {{ Γ ⊢ ℕ }} by mauto 3;
           assert {{ ⊢ Γ', ℕ ⊆ Γ, ℕ }} by mauto 4;
           assert {{ ⊢ Γ', ℕ, A ⊆ Γ, ℕ, A }} by (econstructor; mauto);
           econstructor; mauto 2).

    (** Local variable cases *)
    1,3: (assert (exists A', {{ #x : A' ∈ Γ' }} /\ {{ Γ' ⊢ A' ⊆ A }}) as [A' []] by mauto 2;
          assert {{ Γ' ⊢ #x : A' }} by mauto 3;
          solve [econstructor; mauto 3]).

    (** Conversion cases *)
    1,3: econstructor; mauto 2.

    (** Weakening cases *)
    3,4: (inversion_clear HΓΓ';
          assert {{ ⊢ Γ0, A0 }} by mauto 3;
          solve [econstructor; mauto 2]).
    
    (* wf_exp_eq, variable shift case *)
    - inversion_clear HΓΓ'.
      assert (exists A1, {{ #x : A1 ∈ Γ0 }} /\ {{ Γ0 ⊢ A1 ⊆ A }}) as [A1 []] by mauto 2.
      assert {{ ⊢ Γ0, A0 }} by mauto 3.
      eapply wf_exp_eq_conv; mauto 3.
      enough {{ Γ0 ⊢ A }}; mauto 3.

    (* wf_typ_subtyp, pi case *)
    - assert {{ Γ' ⊢ A' }} by mauto 3.
      assert {{ ⊢ Γ', A' ⊆ Γ, A' }} by mauto 5.
      assert {{ Γ' ⊢ A }} by mauto 3.
      assert {{ ⊢ Γ', A ⊆ Γ, A }} by mauto 5.
      assert {{ Γ', A' ⊢ B ⊆ B' }} by mauto 2.
      assert {{ Γ', A' ⊢ B' }} by mauto 2.
      assert {{ Γ', A ⊢ B }} by mauto 3.
      assert {{ Γ' ⊢ A ≈ A' }} by mauto 3.
      solve [econstructor; mauto 3].
  Qed.

  #[local]
  Ltac solve_ctxsub P :=
    pose proof (@ctxsub_main P); destruct_conjs; eauto.
  
  Corollary ctxsub_wf_exp {P : PtsSig} : forall {Γ : ctx P} {A M}, {{ Γ ⊢ M : A }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ M : A }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_exp_eq {P : PtsSig} : forall {Γ : ctx P} {A M M'}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ M ≈ M' : A }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_typ {P : PtsSig} : forall {Γ : ctx P} {A}, {{ Γ ⊢ A }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ A }}.
  Proof. solve_ctxsub P. Qed.
    
  Corollary ctxsub_wf_typ_eq {P : PtsSig} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ≈ A' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ A ≈ A' }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_typ_subtyp {P : PtsSig} : forall {Γ : ctx P} {A A'}, {{ Γ ⊢ A ⊆ A' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢ A ⊆ A' }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_sub {P : PtsSig} : forall {Γ : ctx P} {Γ'' σ}, {{ Γ ⊢s σ : Γ'' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢s σ : Γ'' }}.
  Proof. solve_ctxsub P. Qed.

  Corollary ctxsub_wf_sub_eq {P : PtsSig} : forall {Γ : ctx P} {Γ'' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ'' }} -> forall {Γ'}, {{ ⊢ Γ' ⊆ Γ }} -> {{ Γ' ⊢s σ ≈ σ' : Γ'' }}.
  Proof. solve_ctxsub P. Qed.

  #[export]
  Hint Resolve ctxsub_wf_exp ctxsub_wf_exp_eq ctxsub_wf_typ ctxsub_wf_typ_eq ctxsub_wf_typ_subtyp ctxsub_wf_sub ctxsub_wf_sub_eq : mcpts.
End ctxsub_judg.
   
Export ctxsub_judg.

(** We can finally prove transitivity of subtyping *)
Lemma wf_ctx_subtyp_trans {P} : forall {Γ0 : ctx P} {Γ1},
    {{ ⊢ Γ0 ⊆ Γ1 }} ->
    forall  Γ2,
      {{ ⊢ Γ1 ⊆ Γ2 }} ->
      {{ ⊢ Γ0 ⊆ Γ2 }}.
Proof.
  induction 1; intros; progressive_inversion; [constructor; mauto 2 |].
  eapply wf_ctx_subtyp_extend; mauto 3.
Qed.

#[export]
Hint Resolve wf_ctx_subtyp_trans : mcpts.

#[export]
Instance wf_ctx_sub_trans_ins {P} : Transitive (@wf_ctx_subtyp P).
Proof. eauto using wf_ctx_subtyp_trans. Qed.


(** Rewrite rules based on local context subtyping *)
Add Parametric Morphism {P} : (@wf_exp P)
  with signature wf_ctx_subtyp --> eq ==> eq ==> Basics.impl as ctxsub_exp_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_exp_eq P)
  with signature wf_ctx_subtyp --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_exp_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_typ P)
  with signature wf_ctx_subtyp --> eq ==> Basics.impl as ctxsub_typ_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_typ_eq P)
  with signature wf_ctx_subtyp --> eq ==> eq ==> Basics.impl as ctxsub_typ_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_typ_subtyp P)
  with signature wf_ctx_subtyp --> eq ==> eq ==> Basics.impl as ctxsub_typ_subtyp_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_sub P)
  with signature wf_ctx_subtyp --> eq ==> eq ==> Basics.impl as ctxsub_sub_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.

Add Parametric Morphism {P} : (@wf_sub_eq P)
  with signature wf_ctx_subtyp --> eq ==> eq ==> eq ==> Basics.impl as ctxsub_sub_eq_morphism.
Proof.
  cbv; intros; mauto 3.
Qed.
