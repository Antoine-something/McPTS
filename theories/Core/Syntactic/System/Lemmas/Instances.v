From Coq Require Import List Classes.RelationClasses Setoid Morphisms String.

From McPTS Require Import PtsSignature LibTactics Base.
From McPTS.Core.Syntactic Require Export Syntax System.Definitions.
Import Syntax_Notations.


(** * Equality judgments are equivalences *)
(** ** For wf_exp_eq *)
(** wf_exp_eq is reflexive with respect to wf_exp *)
Lemma wf_exp_eq_refl {P : PtsSig} : forall {Γ : ctx P} {M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M ≈ M : A }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_exp_eq_refl : mcpts.

(** wf_exp_eq is symmetric and transitive *)
#[export]
Instance wf_exp_eq_PER {P : PtsSig} (Γ : ctx P) (A : typ P) : PER (wf_exp_eq Γ A).
Proof.
  split.
  - eauto using wf_exp_eq_sym.
  - eauto using wf_exp_eq_trans.
Qed.

#[export]
Instance wf_exp_eq_per_elem {P : PtsSig} (Γ : ctx P) (A : typ P) : PERElem _ (wf_exp Γ A) (wf_exp_eq Γ A).
Proof.
  intros a Ha. mauto.
Qed.

(** ** For wf_sub_eq *)
(** wf_sub_eq is reflexive with respect to wf_sub *)
Lemma wf_sub_eq_refl {P : PtsSig} : forall {Γ Γ' : ctx P} {σ},
    {{ Γ ⊢s σ : Γ' }} ->
    {{ Γ ⊢s σ ≈ σ : Γ' }}.
Proof. mauto. Qed.

#[export]
Hint Resolve wf_sub_eq_refl : mcpts.

(** wf_sub_eq is symmetric and transitive *)
#[export]
Instance wf_sub_eq_PER {P : PtsSig} (Γ Γ' : ctx P) : PER (wf_sub_eq Γ Γ').
Proof.
  split.
  - eauto using wf_sub_eq_sym.
  - eauto using wf_sub_eq_trans.
Qed.

#[export]
Instance wf_sub_eq_per_elem {P : PtsSig} (Γ Γ' : ctx P) : PERElem _ (wf_sub Γ Γ') (wf_sub_eq Γ Γ').
Proof.
  intros a Ha. mauto.
Qed.

(** ** For wf_typ_eq *)
(* For wf_typ_eq, reflexivity follows from symmetry and transitivity *)
(** wf_typ_eq is symmetric and transitive *)
#[export]
Instance wf_typ_eq_PER {P : PtsSig} (Γ : ctx P) : PER (wf_typ_eq Γ).
Proof.
  split.
  - eauto using wf_typ_eq_sym.
  - eauto using wf_typ_eq_trans.
Qed.

(** wf_typ_eq is reflexive with respect to wf_typ *)
Lemma wf_typ_eq_refl {P : PtsSig} : forall {Γ : ctx P} {A},
    {{ Γ ⊢ A }} ->
    {{ Γ ⊢ A ≈ A }}.
Proof.
  induction 1.
  - transitivity {{{ Sort@s[Id] }}}; mauto.
  - enough {{ Γ ⊢ A ≈ A : Sort@s }}; mauto.
  - enough {{ Γ ⊢s σ ≈ σ : Γ' }}; mauto.
Qed.

#[export]
Hint Resolve wf_typ_eq_refl : mcpts.

#[export]
Instance wf_typ_eq_per_elem {P : PtsSig} (Γ : ctx P) : PERElem _ (wf_typ Γ) (wf_typ_eq Γ).
Proof.
  intros A HA%wf_typ_eq_refl; eassumption.
Qed.


(** ** For contexts *)
(** wf_ctx_eq is reflexive with respect to wf_ctx *)
Lemma wf_ctx_eq_refl {P : PtsSig} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ≈ Γ }}.
Proof.
  induction 1; mauto 4.
Qed.

#[export]
Hint Resolve wf_ctx_eq_refl : mcpts.

#[export]
Instance wf_ctx_eq_Symmetric {P : PtsSig} : Symmetric (@wf_ctx_eq P).
Proof.
  induction 1; mauto.
Qed.

#[export]
Instance wf_ctx_eq_per_elem {P : PtsSig} : PERElem _ (@wf_ctx P) (@wf_ctx_eq P).
Proof.
  induction 1; mauto.
Qed.


(** * Subtyping relations are orders *)
(* NOTE:
 * Ultimately, we would like to know that the subtyping judgments are partial orders, but it does not seem that antisymmetry can be established through stricly syntactic methods
 * Instead, we settle for pre-orders
 *)
(** For types *)
#[export]
Instance wf_typ_subtyp_per_elem {P : PtsSig} (Γ : ctx P) : PERElem _ (wf_typ Γ) (wf_typ_subtyp Γ).
Proof.
  intros A HA.
  enough {{ Γ ⊢ A ≈ A }} by mauto.
  apply wf_typ_eq_per_elem; mauto.
Qed.

#[export]
Instance wf_typ_subtyp_Transitive {P : PtsSig} (Γ : ctx P) : Transitive (wf_typ_subtyp Γ).
Proof.
  hnf; mauto.
Qed.  

(** For local contexts *)
(* NOTE:
 * For contexts, we cannot establish transitivity at this point, for similar reason as in the equality case
 *)
Lemma wf_ctx_sub_refl {P} : forall {Γ : ctx P},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ⊆ Γ }}.
Proof.
  induction 1; mauto;
    econstructor; mauto;
    apply wf_typ_subtyp_per_elem; mauto.
Qed.

#[export]
Hint Resolve wf_ctx_sub_refl : mcpts.

#[export]
Instance wf_ctx_subtyp_per_elem {P : PtsSig} : PERElem _ (@wf_ctx P) (@wf_ctx_subtyp P).
Proof. intros ? ?; mauto. Qed.


(** * Immediately admissible rules *)
(** Sort subtyping respects st_subtyp *)
Lemma wf_typ_subtyp_sort_st_subtyp {P : PtsSig} : forall {Γ : ctx P} {s1 s2},
    {{ ⊢ Γ }} ->
    st_subtyp s1 s2 ->
    {{ Γ ⊢ Sort@s1 ⊆ Sort@s2 }}.
Proof.
  intros.
  induction H0.
  - enough {{ Γ ⊢ Sort@s ≈ Sort@s }} by mauto 3.
    enough {{ Γ ⊢ Sort@s }}; mauto 2.
  - transitivity {{{ Sort@s2 }}}; mauto 2.
Qed.

#[export]
Hint Resolve wf_typ_subtyp_sort_st_subtyp : mcpts.

(** Lift equivalence of well-sorted types to subtyping *)
Lemma wf_exp_eq_sort_subtyp {P : PtsSig} : forall {Γ : ctx P} {A B s},
    {{ Γ ⊢ A ≈ B : Sort@s }} ->
    {{ Γ ⊢ B }} ->
    {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros.
  assert {{ Γ ⊢ A ≈ B }} by mauto 2.
  mauto 2.
Qed.

#[export]
Hint Resolve wf_exp_eq_sort_subtyp : mcpts.


(** * Basic rewriting rules *)
(** ** For wf_exp_eq *)
Add Parametric Morphism {P : PtsSig} (Γ : ctx P) (A : typ P) : (wf_exp_eq Γ A)
    with signature wf_exp_eq Γ A ==> eq ==> iff as wf_exp_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) (A : typ P) : (wf_exp_eq Γ A)
    with signature eq ==> wf_exp_eq Γ A ==> iff as wf_exp_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

(** ** For wf_typ_eq *)
Add Parametric Morphism {P : PtsSig} (Γ : ctx P) : (wf_typ_eq Γ)
    with signature wf_typ_eq Γ ==> eq ==> iff as wf_typ_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ : ctx P) : (wf_typ_eq Γ)
    with signature eq ==> wf_typ_eq Γ ==> iff as wf_typ_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) (s : P) : (wf_typ_eq Γ)
  with signature eq ==> wf_exp_eq Γ {{{ Sort@s }}} ==> iff as wf_typ_eq_morphism_iff3.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P} (Γ : ctx P) (s : P) : (wf_typ_eq Γ)
  with signature wf_exp_eq Γ {{{ Sort@s }}} ==> eq ==> iff as wf_typ_eq_morphism_iff4.
Proof.
  split; mauto.
Qed.

(** ** For wf_sub_eq *)
Add Parametric Morphism {P : PtsSig} (Γ Γ' : ctx P) : (wf_sub_eq Γ Γ')
    with signature wf_sub_eq Γ Γ' ==> eq ==> iff as wf_sub_eq_morphism_iff1.
Proof.
  split; mauto.
Qed.

Add Parametric Morphism {P : PtsSig} (Γ Γ' : ctx P) : (wf_sub_eq Γ Γ')
    with signature eq ==> wf_sub_eq Γ Γ' ==> iff as wf_sub_eq_morphism_iff2.
Proof.
  split; mauto.
Qed.

(** ** Rewrite using specific constructors of equality judgments *)
#[export]
Hint Rewrite -> @wf_exp_eq_typ_sub using mauto 3 : mcpts.

#[export]
Hint Rewrite -> @wf_exp_eq_sub_id
                 @wf_exp_eq_pi_sub using mauto 4 : mcpts.

#[export]
Hint Rewrite -> @wf_exp_eq_typ_sub using mauto 3 : mcpts.

#[export]
Hint Rewrite -> @wf_sub_eq_id_compose_right
                 @wf_sub_eq_id_compose_left
                 @wf_sub_eq_compose_assoc (* prefer right association *)
                 @wf_sub_eq_p_extend using mauto 4 : mcpts.
