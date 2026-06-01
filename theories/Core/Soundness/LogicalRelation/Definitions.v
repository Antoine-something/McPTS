From Coq Require Import Relation_Definitions RelationClasses.
From Equations Require Import Equations.

From McPTS Require Import LibTactics PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export PER.
From McPTS.Core.Soundness.Weakening Require Export Definitions.

Import Domain_Notations.
Global Open Scope predicate_scope.

Generalizable All Variables.

Notation "'glu_typ_pred_args' P" := (Tcons (ctx P) (Tcons (typ P) Tnil)) (at level 80, P constr at level 0).
Notation "'glu_typ_pred' P" := (predicate (glu_typ_pred_args P)) (at level 80, P constr at level 0).
Notation "'glu_typ_pred_equivalence' P" := (@predicate_equivalence (glu_typ_pred_args P)) (at level 80, P constr at level 0, only parsing).
(** This type annotation is to distinguish this notation from others *)
Notation "Γ ⊢ A ® R" := ((R Γ A : (Prop : Type)) : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, A custom exp, R constr).

Notation "'glu_exp_pred_args' P" := (Tcons (ctx P) (Tcons (typ P) (Tcons (exp P) (Tcons (domain P) Tnil)))) (at level 80, P constr at level 0).
Notation "'glu_exp_pred' P" := (predicate (glu_exp_pred_args P)) (at level 80, P constr at level 0).
Notation "'glu_exp_pred_equivalence' P" := (@predicate_equivalence (glu_exp_pred_args P)) (at level 80, P constr at level 0, only parsing).
Notation "Γ ⊢ M : A ® m ∈ R" := (R Γ A M m : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp, m custom domain, R constr).

Notation "'glu_sub_pred_args' P" := (Tcons (ctx P) (Tcons (sub P) (Tcons (env P) Tnil))) (at level 80, P constr at level 0).
Notation "'glu_sub_pred' P" := (predicate (glu_sub_pred_args P)) (at level 80, P constr at level 0).
Notation "'glu_sub_pred_equivalence' P" := (@predicate_equivalence (glu_sub_pred_args P)) (at level 80, P constr at level 0, only parsing).
Notation "Γ ⊢s σ ® ρ ∈ R" := ((R Γ σ ρ : Prop) : (Prop : (Type : Type))) (in custom judg at level 80, Γ custom exp, σ custom exp, ρ custom domain, R constr).

Notation "'DG' a ∈ R ↘ P ↘ El" := (R P El a : ((Prop : Type) : (Type : Type))) (in custom judg at level 90, a custom domain, R constr, P constr, El constr).
Notation "'EG' A ∈ R ↘ Sb " := (R Sb A : ((Prop : (Type : Type)) : (Type : Type))) (in custom judg at level 90, A custom exp, R constr, Sb constr).



Definition neut_glu_typ_pred {P : PtsSig} s a : glu_typ_pred P :=
  fun Γ A => {{ Γ ⊢ A : Sort@s }} /\
            (forall Δ σ A', {{ Δ ⊢w σ : Γ }} -> {{ Rne a in length Δ ↘ A' }} -> {{ Δ ⊢ A[σ] ≈ A' : Sort@s }}).
Arguments neut_glu_typ_pred {P} s a Γ A/.

Variant neut_glu_exp_pred {P : PtsSig} s a : glu_exp_pred P :=
| mk_neut_glu_exp_pred :
  `{ {{ Γ ⊢ A ® neut_glu_typ_pred s a }} ->
     {{ Γ ⊢ M : A }} ->
     {{ Dom m ≈ m ∈ per_bot }} ->
     (forall Δ σ M', {{ Δ ⊢w σ : Γ }} ->
                   {{ Rne m in length Δ ↘ M' }} ->
                   {{ Δ ⊢ M[σ] ≈ M' : A[σ] }}) ->
     {{ Γ ⊢ M : A ® ⇑ b m ∈ neut_glu_exp_pred s a }} }.


Variant pi_glu_typ_pred {P : PtsSig} {s1 s2 s3 s} (r : Ru_pi P s1 s2 s3) (sub_s3_s : st_subtyp s3 s)
  (IR : relation (domain P))
  (IP : glu_typ_pred P)
  (IEl : glu_exp_pred P)
  (OP : forall c (equiv_c : {{ Dom c ≈ c ∈ IR }}), glu_typ_pred P) : glu_typ_pred P :=
| mk_pi_glu_typ_pred :
  `{ {{ Γ ⊢ A ≈ Π r IT OT : Sort@s }} ->
     {{ Γ ⊢ IT : Sort@s1 }} ->
     {{ Γ , IT@s1 ⊢ OT : Sort@s2 }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Δ ⊢ IT[σ] ® IP }}) ->
     (forall Δ σ M m,
         {{ Δ ⊢w σ : Γ }} ->
         {{ Δ ⊢ M : IT[σ] ® m ∈ IEl }} ->
         forall (equiv_m : {{ Dom m ≈ m ∈ IR }}),
           {{ Δ ⊢ OT[σ,,M] ® OP _ equiv_m }}) ->
     {{ Γ ⊢ A ® pi_glu_typ_pred r sub_s3_s IR IP IEl OP }} }.

Variant pi_glu_exp_pred {P : PtsSig} {s1 s2 s3 s} (r : Ru_pi P s1 s2 s3) (sub_s3_s : st_subtyp s3 s)
  (IR : relation (domain P))
  (IP : glu_typ_pred P)
  (IEl : glu_exp_pred P)
  (elem_rel : relation (domain P))
  (OEl : forall c (equiv_c : {{ Dom c ≈ c ∈ IR }}), glu_exp_pred P): glu_exp_pred P :=
| mk_pi_glu_exp_pred :
  `{ {{ Γ ⊢ M : A }} ->
     {{ Dom m ≈ m ∈ elem_rel }} ->
     {{ Γ ⊢ A ≈ Π r IT OT : Sort@s }} ->
     {{ Γ ⊢ IT : Sort@s1 }} ->
     {{ Γ , IT@s1 ⊢ OT : Sort@s2 }} ->
     (forall Δ σ, {{ Δ ⊢w σ : Γ }} -> {{ Δ ⊢ IT[σ] ® IP }}) ->
     (forall Δ σ N n,
         {{ Δ ⊢w σ : Γ }} ->
         {{ Δ ⊢ N : IT[σ] ® n ∈ IEl }} ->
         forall (equiv_n : {{ Dom n ≈ n ∈ IR }}),
         exists mn, {{ $| m & n |↘ mn }} /\ {{ Δ ⊢ M[σ] N : OT[σ,,N] ® mn ∈ OEl _ equiv_n }}) ->
     {{ Γ ⊢ M : A ® m ∈ pi_glu_exp_pred r sub_s3_s IR IP IEl elem_rel OEl }} }.

#[export]
Hint Constructors neut_glu_exp_pred pi_glu_typ_pred pi_glu_exp_pred : mcpts.

Definition sort_glu_typ_pred {P : PtsSig} (pred_P : PredicativeSig P) (s1 s2 : P) : glu_typ_pred P :=
  fun Γ A => {{ Γ ⊢ A ≈ Sort@s1 : Sort@s2 }}.
Arguments sort_glu_typ_pred {P} pred_P s1 s2 Γ A/.
Transparent sort_glu_typ_pred.

Inductive glu_nat {P} {s} (r : Ru_nat P s) : ctx P -> exp P -> domain P -> Prop :=
| glu_nat_zero :
  `{ {{ Γ ⊢ M ≈ zero : ℕ }} ->
     glu_nat r Γ M d{{{ zero }}} }
| glu_nat_succ :
  `{ {{ Γ ⊢ M ≈ succ M' : ℕ }} ->
     glu_nat r Γ M' m' ->
     glu_nat r Γ M d{{{ succ m' }}} }
| glu_nat_neut :
  `{ per_bot m m ->
     (forall {Δ σ M'}, {{ Δ ⊢w σ : Γ }} -> {{ Rne m in length Δ ↘ M' }} -> {{ Δ ⊢ M[σ] ≈ M' : ℕ }}) ->
     glu_nat r Γ M d{{{ ⇑ a m }}} }.

#[export]
Hint Constructors glu_nat : mcpts.

Definition nat_glu_typ_pred {P : PtsSig} {s' s} (r : Ru_nat P s') (sub_s'_s : st_subtyp s' s) : glu_typ_pred P := fun Γ A => {{ Γ ⊢ A ≈ ℕ : Sort@s }}.
Arguments nat_glu_typ_pred {P} {s' s} r sub_s'_s Γ A/.

Definition nat_glu_exp_pred {P : PtsSig} {s' s} (r : Ru_nat P s') (sub_s'_s : st_subtyp s' s) : glu_exp_pred P := fun Γ A M m => {{ Γ ⊢ A ® nat_glu_typ_pred r sub_s'_s }} /\ glu_nat r Γ M m.
Arguments nat_glu_exp_pred {P} {s' s} r sub_s'_s Γ A M m/.

Section Gluing.
  Context
    `(pred_P : PredicativeSig P)
      (s : P)
      (* Intuitively, glu_sort_typ_elem_rec s' lt_s'_s = glu_sort_elem_core s' *)
      (glu_sort_typ_elem_rec : forall s', pred_rel pred_P s' s -> glu_typ_pred P -> glu_exp_pred P -> domain P -> Prop).
  Arguments glu_sort_typ_elem_rec {_}.

  (* Intuitively, glu_sort_typ_rec s' lt_s'_s a is gluing types with a *)
  Definition glu_sort_typ_rec {s'} (lt_s'_s : pred_rel pred_P s' s) (a : domain P) : glu_typ_pred P :=
    fun Γ A => exists typ_rel exp_rel, glu_sort_typ_elem_rec lt_s'_s typ_rel exp_rel a /\ {{ Γ ⊢ A ® typ_rel }}.

  Definition sort_glu_exp_pred' {s'} (lt_s'_s : pred_rel pred_P s' s) : glu_exp_pred P :=
    fun Γ A M m =>
      {{ Γ ⊢ M : A }} /\
        {{ Γ ⊢ A ≈ Sort@s' : Sort@s }} /\
        {{ Γ ⊢ M ® glu_sort_typ_rec lt_s'_s m }}.

  #[global]
  Arguments sort_glu_exp_pred' {s'} lt_s'_s Γ A M m/.
  
  Inductive glu_sort_elem_core : glu_typ_pred P -> glu_exp_pred P -> domain P -> Prop :=
  | glu_sort_elem_core_sort :
    `{ forall typ_rel
         exp_rel
         (ax_s''_s' : Ax_typ P s'' s')
         (sub_s'_s : st_subtyp s' s),
          typ_rel <∙> sort_glu_typ_pred pred_P s'' s ->
          exp_rel <∙> sort_glu_exp_pred' (ord_ax_typ_sub pred_P ax_s''_s' sub_s'_s) ->
          {{ DG Sort@s'' ∈ glu_sort_elem_core ↘ typ_rel ↘ exp_rel }} }

  | glu_sort_elem_core_pi :
    `{ forall (r : Ru_pi P s1 s2 s3)
         (sub_s3_s : st_subtyp s3 s)
         (in_rel : relation (domain P))
         (IP : glu_typ_pred P)
         (IEL : glu_exp_pred P)
         (OP : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred P)
         (OEL : forall c (equiv_c_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred P)
         typ_rel el_rel
         (elem_rel : relation (domain P))
         (glu_a : (s1 = s -> {{ DG a ∈ glu_sort_elem_core ↘ IP ↘ IEL }}) /\ (forall (lt_s1_s : pred_rel pred_P s1 s), {{ DG a ∈ glu_sort_typ_elem_rec lt_s1_s ↘ IP ↘ IEL }})),
          {{ DF a ≈ a ∈ per_sort_elem pred_P s1 ↘ in_rel }} ->
          (forall {c} (equiv_c : {{ Dom c ≈ c ∈ in_rel}}) b,
              {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
              (s2 = s -> {{ DG b ∈ glu_sort_elem_core ↘ OP _ equiv_c ↘ OEL _ equiv_c }}) /\ (forall (lt_s2_s : pred_rel pred_P s2 s), {{ DG b ∈ glu_sort_typ_elem_rec lt_s2_s ↘ OP _ equiv_c ↘ OEL _ equiv_c }})) ->
          {{ DF Π r a ρ B ≈ Π r a ρ B ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
          typ_rel <∙> pi_glu_typ_pred r sub_s3_s in_rel IP IEL OP ->
          el_rel <∙> pi_glu_exp_pred r sub_s3_s in_rel IP IEL elem_rel OEL ->
          {{ DG Π r a ρ B ∈ glu_sort_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_sort_elem_core_nat :
    `{ forall (r : Ru_nat P s')
         (sub_s'_s : st_subtyp s' s)
         typ_rel el_rel,
          typ_rel <∙> nat_glu_typ_pred r sub_s'_s ->
          el_rel <∙> nat_glu_exp_pred r sub_s'_s ->
          {{ DG ℕ ∈ glu_sort_elem_core ↘ typ_rel ↘ el_rel }} }

  | glu_sort_elem_core_neut :
    `{ forall typ_rel el_rel,
          {{ Dom b ≈ b ∈ per_bot }} ->
          typ_rel <∙> neut_glu_typ_pred s b ->
          el_rel <∙> neut_glu_exp_pred s b ->
          {{ DG ⇑ a b ∈ glu_sort_elem_core ↘ typ_rel ↘ el_rel }} }
  .


  Hypothesis
    (motive : glu_typ_pred P -> glu_exp_pred P -> domain P -> Prop)

      (case_sort :
        forall {s'' s'} typ_rel exp_rel
          (ax_s''_s' : Ax_typ P s'' s')
          (sub_s'_s : st_subtyp s' s),
          typ_rel <∙> sort_glu_typ_pred pred_P s'' s ->
          exp_rel <∙> sort_glu_exp_pred' (ord_ax_typ_sub pred_P ax_s''_s' sub_s'_s) ->
          motive typ_rel exp_rel d{{{ Sort@s'' }}})

      (case_pi :
        forall {s1 s2 s3 a ρ B}
          (r : Ru_pi P s1 s2 s3)
          (sub_s3_s : st_subtyp s3 s)
          (in_rel : relation (domain P))
          (IP : glu_typ_pred P)
          (IEL : glu_exp_pred P)
          (OP : forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}), glu_typ_pred P)
          (OEL : forall c (equiv_c : {{ Dom c ≈ c ∈ in_rel }}), glu_exp_pred P)
          typ_rel el_rel
          (elem_rel : relation (domain P)),
          ((s1 = s -> {{ DG a ∈ glu_sort_elem_core ↘ IP ↘ IEL }} /\ motive IP IEL a) /\ (forall (lt_s1_s : pred_rel pred_P s1 s), {{ DG a ∈ glu_sort_typ_elem_rec lt_s1_s ↘ IP ↘ IEL }})) ->
          {{ DF a ≈ a ∈ per_sort_elem pred_P s1 ↘ in_rel }} ->
          (forall {c} (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) b,
              {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
              (s2 = s -> {{ DG b ∈ glu_sort_elem_core ↘ OP c equiv_c ↘ OEL c equiv_c }} /\ motive (OP c equiv_c) (OEL c equiv_c) b) /\ (forall (lt_s2_s : pred_rel pred_P s2 s), {{ DG b ∈ glu_sort_typ_elem_rec lt_s2_s ↘ OP c equiv_c ↘ OEL c equiv_c }})) ->
          {{ DF Π r a ρ B ≈ Π r a ρ B ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
          typ_rel <∙> pi_glu_typ_pred r sub_s3_s in_rel IP IEL OP ->
          el_rel <∙> pi_glu_exp_pred r sub_s3_s in_rel IP IEL elem_rel OEL ->
          motive typ_rel el_rel d{{{ Π r a ρ B }}} )

      (case_nat :
        forall {s'} (r : Ru_nat P s')
          (sub_s'_s : st_subtyp s' s)
          typ_rel el_rel,
          typ_rel <∙> nat_glu_typ_pred r sub_s'_s ->
          el_rel <∙> nat_glu_exp_pred r sub_s'_s ->
          motive typ_rel el_rel d{{{ ℕ }}})

      (case_neut :
        forall {a b}
          typ_rel el_rel,
          {{ Dom b ≈ b ∈ per_bot }} ->
          typ_rel <∙> neut_glu_typ_pred s b ->
          el_rel <∙> neut_glu_exp_pred s b ->
          motive typ_rel el_rel d{{{ ⇑ a b }}} )
  .


  #[derive(equations=no, eliminator=no)]
  Equations glu_sort_elem_core_strong_ind typ_rel exp_rel a (H : glu_sort_elem_core typ_rel exp_rel a) : motive typ_rel exp_rel a :=
  | typ_rel, exp_rel, a, (glu_sort_elem_core_sort typ_rel exp_rel ax_s''_s' sub_s'_s HT HE) => (case_sort typ_rel exp_rel ax_s''_s' sub_s'_s HT HE)
  | typ_rel, exp_rel, a, (glu_sort_elem_core_pi r sub_s3_s in_rel IP IEL OP OEL typ_rel exp_rel elem_rel glu_a Ha glu_B HPi Htyp Hexp) =>
      (case_pi r sub_s3_s
         in_rel
         IP
         IEL
         OP
         OEL
         typ_rel
         exp_rel
         elem_rel
         (let 'conj HA _ := glu_a in
           conj (fun eq => conj _ (glu_sort_elem_core_strong_ind _ _ _ (HA eq))) _)
         Ha
         (fun c equiv_c b HB =>
            let 'conj HB' _ := glu_B c equiv_c b HB in
            conj (fun eq => conj _ (glu_sort_elem_core_strong_ind _ _ _ (HB' eq))) _)
         HPi
         Htyp
         Hexp)
  | typ_rel, exp_rel, a, (glu_sort_elem_core_nat r sub_s'_s typ_rel exp_rel Htyp Hexp) => (case_nat r sub_s'_s typ_rel exp_rel Htyp Hexp)
  | typ_rel, exp_rel, a, (glu_sort_elem_core_neut typ_rel exp_rel Hb Htyp Hexp) => (case_neut typ_rel exp_rel Hb Htyp Hexp)
  .
End Gluing.

#[export]
Hint Constructors glu_sort_elem_core : mcpts.

Section Glu_sort_elem_def.
  Context `(pred_P : PredicativeSig P).

  Instance Glu_sort_elem_def_wf : WellFounded (pred_rel pred_P) := (wf_rel pred_P).

  Equations glu_sort_elem (s : P) : glu_typ_pred P -> glu_exp_pred P -> domain P -> Prop by wf s :=
  | s => glu_sort_elem_core pred_P s (fun s' lt_s'_s typ_rel exp_rel a => {{ DG a ∈ glu_sort_elem s' ↘ typ_rel ↘ exp_rel }}).
End Glu_sort_elem_def.


Definition glu_sort_typ {P} (pred_P : PredicativeSig P) (s : P) (a : domain P) : glu_typ_pred P :=
  fun Γ A => exists typ_rel exp_rel, {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} /\ {{ Γ ⊢ A ® typ_rel }}.
Arguments glu_sort_typ {P} pred_P s a Γ A/.

Definition sort_glu_exp_pred {P} (pred_P : PredicativeSig P) s' s : glu_exp_pred P :=
    fun Γ A M m =>
      {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ A ≈ Sort@s' : Sort@s }} /\
        {{ Γ ⊢ M ® glu_sort_typ pred_P s' m }}.
Arguments sort_glu_exp_pred {P} pred_P s' s Γ A M m/.


Section GluingInduction.
  Context
    (P : PtsSig)
      (pred_P : PredicativeSig P).

  Let dom := domain P.

  Hypothesis
    (motive : P -> glu_typ_pred P -> glu_exp_pred P -> dom -> Prop)

      (case_sort :
        forall s'' s' s
          (typ_rel : glu_typ_pred P) (exp_rel : glu_exp_pred P)
          (ax_s''_s' : Ax_typ P s'' s')
          (sub_s'_s : st_subtyp s' s),
          (forall typ_rel' exp_rel' a, {{ DG a ∈ glu_sort_elem pred_P s'' ↘ typ_rel' ↘ exp_rel' }} -> motive s'' typ_rel' exp_rel' a) ->
          typ_rel <∙> sort_glu_typ_pred pred_P s'' s ->
          exp_rel <∙> sort_glu_exp_pred pred_P s'' s ->
          motive s typ_rel exp_rel d{{{ Sort@s'' }}})

      (case_pi :
        forall s1 s2 s3 s (r : Ru_pi P s1 s2 s3)
          (sub_s3_s : st_subtyp s3 s)
          a B (ρ : env P)
          (in_rel : relation dom) (IP : glu_typ_pred P) (IEL : glu_exp_pred P)
          (OP : forall (c : dom), {{ Dom c ≈ c ∈ in_rel }} -> glu_typ_pred P)
          (OEL : forall (c : dom), {{ Dom c ≈ c ∈ in_rel }} -> glu_exp_pred P)
          (typ_rel : glu_typ_pred P) (exp_rel : glu_exp_pred P) (elem_rel : relation dom),
          {{ DG a ∈ glu_sort_elem pred_P s1 ↘ IP ↘ IEL }} ->
          motive s1 IP IEL a ->
          {{ DF a ≈ a ∈ per_sort_elem pred_P s1 ↘ in_rel }} ->
          (forall (c : dom) (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) (b : dom),
              {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
              {{ DG b ∈ glu_sort_elem pred_P s2 ↘ OP c equiv_c ↘ OEL c equiv_c }}) ->
          (forall (c : dom) (equiv_c : {{ Dom c ≈ c ∈ in_rel }}) (b : dom),
              {{ ⟦ B ⟧ ρ ↦ c ↘ b }} ->
              motive s2 (OP c equiv_c) (OEL c equiv_c) b) ->
          {{ DF Π r a ρ B ≈ Π r a ρ B ∈ per_sort_elem pred_P s ↘ elem_rel }} ->
          typ_rel <∙> pi_glu_typ_pred r sub_s3_s in_rel IP IEL OP ->
          exp_rel <∙> pi_glu_exp_pred r sub_s3_s in_rel IP IEL elem_rel OEL ->
          motive s typ_rel exp_rel d{{{ Π r a ρ B }}} )

      (case_nat :
        forall s' s (r : Ru_nat P s') (sub_s'_s : st_subtyp s' s)
          (typ_rel : glu_typ_pred P) (exp_rel : glu_exp_pred P),
          typ_rel <∙> nat_glu_typ_pred r sub_s'_s ->
          exp_rel <∙> nat_glu_exp_pred r sub_s'_s ->
          motive s typ_rel exp_rel d{{{ ℕ }}})

      (case_neut :
        forall s a b
          (typ_rel : glu_typ_pred P)
          (exp_rel : glu_exp_pred P),
          {{ Dom b ≈ b ∈ per_bot }} ->
          typ_rel <∙> neut_glu_typ_pred s b ->
          exp_rel <∙> neut_glu_exp_pred s b ->
          motive s typ_rel exp_rel d{{{ ⇑ a b }}})
  .

  #[local]
  Ltac def_simp := simp glu_sort_elem in *; mauto 3.

  Instance Glu_sort_elem_ind_wf : WellFounded (pred_rel pred_P) := (wf_rel pred_P).

  #[derive(equations=no, eliminator=no), tactic="def_simp"]
  Equations glu_sort_elem_ind s typ_rel exp_rel a
    (H : glu_sort_elem pred_P s typ_rel exp_rel a) : motive s typ_rel exp_rel a by wf s :=
  | s, typ_rel, exp_rel, a, H =>
      glu_sort_elem_core_strong_ind pred_P
        s
        (fun s' ax_s'_s typ_rel exp_rel a => glu_sort_elem pred_P s' typ_rel exp_rel a)
        (motive s)
        (fun s'' s' typ_rel' exp_rel' ax_s''_s' sub_s'_s HP' HEl' =>
           case_sort s'' s' s typ_rel' exp_rel' ax_s''_s' sub_s'_s
             (fun typ_rel'' exp_rel'' A H => glu_sort_elem_ind s'' typ_rel'' exp_rel'' A H)
             HP'
             HEl')
        _ (* case_pi s *)
        (fun s' r sub_s'_s => case_nat _ s r sub_s'_s)
        (* (case_nat _ s) *)
        (case_neut s)
        typ_rel exp_rel a _.
  Next Obligation.
    eapply ord_ax_typ_sub; eassumption.
  Qed.
  Next Obligation.
    assert ((pred_rel pred_P s1 s \/ s1 = s) /\ (pred_rel pred_P s2 s \/ s2 = s)) by (eapply ord_ru_pi_sub; mauto).
    destruct_conjs.
    eapply (case_pi s1 s2 s3 s r sub_s3_s); def_simp; eauto.
    - destruct H7.
      + eapply H6; mauto.
      + subst; eapply H0; mauto.
    - destruct H7.
      + eapply glu_sort_elem_ind.
        def_simp; eauto.
        eassumption.
      + subst. eapply H0.
        reflexivity.

    - destruct H8; intros.
      + eapply H2; mauto.
      + assert (s2 = s ->
                glu_sort_elem_core pred_P s
                  (fun (s' : P) (_ : pred_rel pred_P s' s) (typ_rel : ctx P -> exp P -> Prop)
                       (exp_rel : ctx P -> exp P -> exp P -> domain P -> Prop)
                     (a : domain P) => glu_sort_elem pred_P s' typ_rel exp_rel a) (OP c equiv_c)
                  (OEL c equiv_c) b /\ motive s (OP c equiv_c) (OEL c equiv_c) b) by (eapply H2; mauto).
        subst.
        eapply H10; mauto.
    - intros.
      destruct H8.
      + eapply glu_sort_elem_ind; mauto.
        def_simp; eauto.
        eapply H2; mauto.
      + assert (s2 = s ->
     glu_sort_elem_core pred_P s
       (fun (s' : P) (_ : pred_rel pred_P s' s) (typ_rel : ctx P -> exp P -> Prop)
          (exp_rel : ctx P -> exp P -> exp P -> domain P -> Prop)
          (a : domain P) => glu_sort_elem pred_P s' typ_rel exp_rel a) (OP c equiv_c)
       (OEL c equiv_c) b /\ motive s (OP c equiv_c) (OEL c equiv_c) b) by (eapply H2; mauto).
        subst.
        eapply H10; mauto.
  Qed.
End GluingInduction.


(** Gluing relation that includes top sorts *)
Definition top_sort_glu_typ_pred {P : PtsSig} (pred_P : PredicativeSig P) (s : P) : glu_typ_pred P :=
  fun Γ A => (A = {{{ Sort@s }}}).
Arguments top_sort_glu_typ_pred {P} pred_P s Γ A/.
Transparent top_sort_glu_typ_pred.

Definition top_sort_glu_exp_pred {P} (pred_P : PredicativeSig P) (s : P) : glu_exp_pred P :=
  fun Γ A M m => (A = {{{ Sort@s }}}) /\
                (exists typ_rel exp_rel, {{ DG m ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} /\
                                      {{ Γ ⊢ M ® typ_rel }}).
Arguments top_sort_glu_exp_pred {P} pred_P s Γ A M m/.
Transparent top_sort_glu_exp_pred.

(**
    We still need annotations for the soundness proof, but top sorts cannot be annotated.
    The simple solution is to use a sort option for the annotation.
    The built-in option type in Rocq can only be used in Type, but our sorts are defined in Set.
    So, we define our own option for sorts
 *)

Inductive SortOption (P : PtsSig) : Type :=
| None : SortOption P
| Some : P -> SortOption P
.

Arguments None {P}.
Arguments Some {P} s.

Inductive glu_typ_elem {P} (pred_P : PredicativeSig P) : SortOption P -> glu_typ_pred P -> glu_exp_pred P -> domain P -> Prop :=
| glu_typ_elem_top_sort :
  `{ (* (forall s', Ax_typ P s s' -> False) -> *)
     typ_rel <∙> top_sort_glu_typ_pred pred_P s ->
     exp_rel <∙> top_sort_glu_exp_pred pred_P s ->
     {{ DG Sort@s ∈ glu_typ_elem pred_P None ↘ typ_rel ↘ exp_rel }} }
| glu_typ_elem_sort :
  `{ {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
     {{ DG a ∈ glu_typ_elem pred_P (Some s) ↘ typ_rel ↘ exp_rel }} }
.




(** Top and bottom relations *)
Variant glu_elem_bot {P} (pred_P : PredicativeSig P) s a Γ A M m : Prop :=
  | glu_elem_bot_make : forall typ_rel exp_rel,
      {{ Γ ⊢ M : A }} ->
      {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
      {{ Γ ⊢ A ® typ_rel }} ->
      {{ Dom m ≈ m ∈ per_bot }} ->
      (forall Δ σ M', {{ Δ ⊢w σ : Γ }} -> {{ Rne m in length Δ ↘ M' }} -> {{ Δ ⊢ M[σ] ≈ M' : A[σ] }}) ->
      {{ Γ ⊢ M : A ® m ∈ glu_elem_bot pred_P s a }}.

#[export]
Hint Constructors glu_elem_bot : mcpts.


Variant glu_elem_top {P} (pred_P : PredicativeSig P) s a Γ A M m : Prop :=
| glu_elem_top_make : forall typ_rel exp_rel,
    {{ Γ ⊢ M : A }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Dom ⇓ a m ≈ ⇓ a m ∈ per_top }} ->
    (forall Δ σ W, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ a m in length Δ ↘ W }} -> {{ Δ ⊢ M[σ] ≈ W : A[σ] }}) ->
    {{ Γ ⊢ M : A ® m ∈ glu_elem_top pred_P s a }}.
#[export]
Hint Constructors glu_elem_top : mcpts.

Variant glu_typ_top {P} (pred_P : PredicativeSig P) (s : P) a Γ A : Prop :=
| glu_typ_top_make :
    {{ Γ ⊢ A  : Sort@s }} ->
    {{ Dom a ≈ a ∈ per_top_typ }} ->
    (forall Δ σ A', {{ Δ ⊢w σ : Γ }} -> {{ Rtyp a in length Δ ↘ A' }} -> {{ Δ ⊢ A[σ] ≈ A' : Sort@s }}) ->
    {{ Γ ⊢ A ® glu_typ_top pred_P s a }}.
#[export]
Hint Constructors glu_typ_top : mcpts.


Inductive glu_elem_bot_unsorted {P} (pred_P : PredicativeSig P) : SortOption P -> domain P -> ctx P -> typ P -> exp P -> domain_ne P -> Prop :=
| glu_elem_bot_unsorted_top_sort : forall a Γ A M m typ_rel exp_rel,
    (* (forall s', Ax_typ P s s' -> False) -> *)
    {{ Γ ⊢ M : A }} ->
    {{ DG a ∈ glu_typ_elem pred_P None ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Δ σ M', {{ Δ ⊢w σ : Γ }} -> {{ Rne m in length Δ ↘ M' }} -> {{ Δ ⊢ M[σ] ≈ M' : A }}) ->
    {{ Γ ⊢ M : A ® m ∈ glu_elem_bot_unsorted pred_P None a }}
| glu_elem_bot_unsorted_sorted : forall s a Γ A M m typ_rel exp_rel,
    {{ Γ ⊢ M : A }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Dom m ≈ m ∈ per_bot }} ->
    (forall Δ σ M', {{ Δ ⊢w σ : Γ }} -> {{ Rne m in length Δ ↘ M' }} -> {{ Δ ⊢ M[σ] ≈ M' : A[σ] }}) ->
    {{ Γ ⊢ M : A ® m ∈ glu_elem_bot_unsorted pred_P (Some s) a }}.
#[export]
Hint Constructors glu_elem_bot_unsorted : mcpts.

Inductive glu_elem_top_unsorted {P} (pred_P : PredicativeSig P) : SortOption P -> domain P -> ctx P -> typ P -> exp P -> domain P -> Prop :=
| glu_elem_top_unsorted_top_sort : forall a Γ A M m typ_rel exp_rel,
    (* (forall s', Ax_typ P s s' -> False) -> *)
    {{ Γ ⊢ M : A }} ->
    {{ DG a ∈ glu_typ_elem pred_P None ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Dom ⇓ a m ≈ ⇓ a m ∈ per_top }} ->
    (forall Δ σ W, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ a m in length Δ ↘ W }} -> {{ Δ ⊢ M[σ] ≈ W : A }}) ->
    {{ Γ ⊢ M : A ® m ∈ glu_elem_top_unsorted pred_P None a }}
| glu_elem_top_unsorted_sorted : forall s a Γ A M m typ_rel exp_rel,
    {{ Γ ⊢ M : A }} ->
    {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
    {{ Γ ⊢ A ® typ_rel }} ->
    {{ Dom ⇓ a m ≈ ⇓ a m ∈ per_top }} ->
    (forall Δ σ W, {{ Δ ⊢w σ : Γ }} -> {{ Rnf ⇓ a m in length Δ ↘ W }} -> {{ Δ ⊢ M[σ] ≈ W : A[σ] }}) ->
    {{ Γ ⊢ M : A ® m ∈ glu_elem_top_unsorted pred_P (Some s) a }}.
#[export]
Hint Constructors glu_elem_top_unsorted : mcpts.

Inductive glu_typ_top_unsorted {P} (pred_P : PredicativeSig P) : SortOption P -> domain P -> ctx P -> exp P -> Prop :=
| glu_typ_top_unsorted_top_sort :
  forall s a Γ A,
    (* (forall s', Ax_typ P s s' -> False) -> *)
    (A = {{{ Sort@s }}}) ->
    (a = d{{{ Sort@s }}}) ->
    {{ Γ ⊢ A ® glu_typ_top_unsorted pred_P None a }}
| glu_typ_top_unsorted_sorted :
  forall s a Γ A,
    {{ Γ ⊢ A  : Sort@s }} ->
    {{ Dom a ≈ a ∈ per_top_typ }} ->
    (forall Δ σ A', {{ Δ ⊢w σ : Γ }} -> {{ Rtyp a in length Δ ↘ A' }} -> {{ Δ ⊢ A[σ] ≈ A' : Sort@s }}) ->
    {{ Γ ⊢ A ® glu_typ_top_unsorted pred_P (Some s) a }}.
#[export]
Hint Constructors glu_typ_top_unsorted : mcpts.



(** Gluing model for contexts and substitutions *)
Definition nil_glu_sub_pred {P} : glu_sub_pred P :=
  fun Δ σ ρ => {{ Δ ⊢s σ : ⋅ }}.
Arguments nil_glu_sub_pred {P} Δ σ ρ/.


(** The parameters are ordered differently from the Agda version
    so that we can return [glu_sub_pred]. *)
Variant cons_glu_sub_pred {P} (pred_P : PredicativeSig P) (s : P) Γ A (TSb : glu_sub_pred P) : glu_sub_pred P :=
| mk_cons_glu_sub_pred :
  `{ forall typ_rel exp_rel,
        {{ Δ ⊢s σ : Γ, A@s }} ->
        {{ ⟦ A ⟧ ρ ↯ ↘ a }} ->
        {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
        {{ #| ρ[0] |↘ m }} ->
        (** Here we use [{{{ A[Wk][σ] }}}] instead of [{{{ A[Wk∘σ] }}}]
            as syntactic judgement derived from that is
            a more direct consequence of [{{ Γ, A ⊢ #0 : A[Wk] }}] *)
        {{ Δ ⊢ #0[σ] : A[Wk][σ] ® m ∈ exp_rel }} ->
        {{ Δ ⊢s Wk ∘ σ ® ρ ↯ ∈ TSb }} ->
        {{ Δ ⊢s σ ® ρ ∈ cons_glu_sub_pred pred_P s Γ A TSb }} }.

Variant glu_rel_typ_with_sub {P} (pred_P : PredicativeSig P) s Δ A σ ρ : Prop :=
| mk_glu_rel_typ_with_sub :
  `{ forall typ_rel exp_rel,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
        {{ Δ ⊢ A[σ] ® typ_rel }} ->
        glu_rel_typ_with_sub pred_P s Δ A σ ρ }.


Inductive glu_ctx_env {P} (pred_P : PredicativeSig P) : glu_sub_pred P -> ctx P -> Prop :=
| glu_ctx_env_nil :
  `{ forall Sb,
        Sb <∙> nil_glu_sub_pred ->
        {{ EG ⋅ ∈ glu_ctx_env pred_P ↘ Sb }} }
| glu_ctx_env_cons :
  `{ forall TSb Sb,
        {{ EG Γ ∈ glu_ctx_env pred_P ↘ TSb }} ->
        {{ Γ ⊢ A : Sort@s }} ->
        (forall Δ σ ρ,
            {{ Δ ⊢s σ ® ρ ∈ TSb }} ->
            glu_rel_typ_with_sub pred_P s Δ A σ ρ) ->
        Sb <∙> cons_glu_sub_pred pred_P s Γ A TSb ->
        {{ EG Γ, A@s ∈ glu_ctx_env pred_P ↘ Sb }} }.

(** Logical relation for contexts *)
Definition glu_rel_ctx {P} (pred_P : PredicativeSig P) Γ : Prop := exists Sb, {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }}.
Arguments glu_rel_ctx {P} pred_P Γ/.


(** Logical relations for substitutions *)
Variant glu_rel_sub_with_sub {P} (pred_P : PredicativeSig P) Δ τ (Sb : glu_sub_pred P) σ ρ : Prop :=
| mk_glu_rel_sub_with_sub :
  `{ {{ ⟦ τ ⟧s ρ ↘ ρ' }} ->
     {{ Δ ⊢s τ ∘ σ ® ρ' ∈ Sb }} ->
     glu_rel_sub_with_sub pred_P Δ τ Sb σ ρ}.

Definition glu_rel_sub_resp_sub_env {P} (pred_P : PredicativeSig P) Sb Sb' τ :=
  forall Δ σ ρ,
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ.
Arguments glu_rel_sub_resp_sub_env {P} pred_P Sb Sb' τ/.

Definition glu_rel_sub {P} (pred_P : PredicativeSig P) Γ τ Γ' : Prop :=
  exists Sb Sb',
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} /\
    {{ EG Γ' ∈ glu_ctx_env pred_P ↘ Sb' }} /\
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_sub_with_sub pred_P Δ τ Sb' σ ρ.
Arguments glu_rel_sub {P} pred_P Γ τ Γ'/.


(** Logical relations for expressions *)
Variant glu_rel_exp_with_sub {P} (pred_P : PredicativeSig P) s Δ M A σ ρ : Prop :=
| mk_glu_rel_exp_with_sub :
  `{ forall typ_rel exp_rel,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ ⟦ M ⟧ ρ ↘ m }} ->
        {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
        {{ Δ ⊢ M[σ] : A[σ] ® m ∈ exp_rel }} ->
        glu_rel_exp_with_sub pred_P s Δ M A σ ρ }.

Definition glu_rel_exp_resp_sub_env {P} (pred_P : PredicativeSig P) s Sb M A :=
  forall Δ σ ρ,
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    glu_rel_exp_with_sub pred_P s Δ M A σ ρ.
Arguments glu_rel_exp_resp_sub_env {P} pred_P s Sb M A/.

Definition glu_rel_exp {P} (pred_P : PredicativeSig P) s Γ M A : Prop :=
  exists Sb,
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} /\
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_exp_with_sub pred_P s Δ M A σ ρ.
Arguments glu_rel_exp {P} pred_P s Γ M A/.


Inductive glu_rel_exp_with_sub_unsorted {P} (pred_P : PredicativeSig P) : SortOption P -> ctx P -> exp P -> typ P -> sub P -> env P -> Prop :=
| glu_rel_exp_with_sub_unsorted_top_sort :
  `{ forall typ_rel exp_rel,
        (* (forall s', Ax_typ P s s' -> False) -> *)
        (A = {{{ Sort@s }}}) ->
        (a = d{{{ Sort@s }}}) ->
        {{ ⟦ M ⟧ ρ ↘ m }} ->
        {{ DG a ∈ glu_typ_elem pred_P None ↘ typ_rel ↘ exp_rel }} ->
        {{ Δ ⊢ M[σ] : Sort@s ® m ∈ exp_rel }} ->
        glu_rel_exp_with_sub_unsorted pred_P None Δ M A σ ρ }
| glu_rel_exp_with_sub_unsorted_sorted :
  `{ forall typ_rel exp_rel,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ ⟦ M ⟧ ρ ↘ m }} ->
        {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
        {{ Δ ⊢ M[σ] : A[σ] ® m ∈ exp_rel }} ->
        glu_rel_exp_with_sub_unsorted pred_P (Some s) Δ M A σ ρ }.


Definition glu_rel_exp_resp_sub_env_unsorted {P} (pred_P : PredicativeSig P) so Sb M A :=
  forall Δ σ ρ,
    {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
    glu_rel_exp_with_sub_unsorted pred_P so Δ M A σ ρ.
Arguments glu_rel_exp_resp_sub_env_unsorted {P} pred_P so Sb M A/.

Definition glu_rel_exp_unsorted {P} (pred_P : PredicativeSig P) so Γ M A : Prop :=
  exists Sb,
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} /\
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_exp_with_sub_unsorted pred_P so Δ M A σ ρ.
Arguments glu_rel_exp_unsorted {P} pred_P so Γ M A/.


(** Logical relation for types *)
Definition glu_rel_typ {P} (pred_P : PredicativeSig P) s Γ A : Prop :=
  exists Sb,
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} /\
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_typ_with_sub pred_P s Δ A σ ρ.


Inductive glu_rel_typ_with_sub_unsorted {P} (pred_P : PredicativeSig P) : SortOption P -> ctx P -> typ P -> sub P -> env P -> Prop :=
| glu_rel_typ_with_sub_unsorted_top_sort :
  `{ forall typ_rel exp_rel,
        (A = {{{ Sort@s }}}) ->
        (a = d{{{ Sort@s }}}) ->
        {{ DG a ∈ glu_typ_elem pred_P None ↘ typ_rel ↘ exp_rel }} ->
        glu_rel_typ_with_sub_unsorted pred_P None Δ A σ ρ }
| glu_rel_typ_with_sub_unsorted_sorted :
  `{ forall typ_rel exp_rel,
        {{ ⟦ A ⟧ ρ ↘ a }} ->
        {{ DG a ∈ glu_sort_elem pred_P s ↘ typ_rel ↘ exp_rel }} ->
        {{ Δ ⊢ A[σ] ® typ_rel }} ->
        glu_rel_typ_with_sub_unsorted pred_P (Some s) Δ A σ ρ }.


Definition glu_rel_typ_unsorted {P} (pred_P : PredicativeSig P) so Γ A : Prop :=
  exists Sb,
    {{ EG Γ ∈ glu_ctx_env pred_P ↘ Sb }} /\
      forall Δ σ ρ,
        {{ Δ ⊢s σ ® ρ ∈ Sb }} ->
        glu_rel_typ_with_sub_unsorted pred_P so Δ A σ ρ.



Notation "⟪ pred_P ⟫ ⊩ Γ" := (glu_rel_ctx pred_P Γ) (in custom judg at level 80, pred_P constr, Γ custom exp).
Notation "⟪ pred_P ⟫ Γ ⊩s τ : Γ'" := (glu_rel_sub pred_P Γ τ Γ') (in custom judg at level 80, pred_P constr, Γ custom exp, τ custom exp, Γ' custom exp).
Notation "⟪ pred_P ⟫ Γ ⊩ M : A '@' s" := (glu_rel_exp pred_P s Γ M A) (in custom judg at level 80, pred_P constr, Γ custom exp, M custom exp, A custom exp, s custom exp).
Notation "⟪ pred_P ⟫ Γ ⊩u M : A '@' so" := (glu_rel_exp_unsorted pred_P so Γ M A) (in custom judg at level 80, pred_P constr, Γ custom exp, M custom exp, A custom exp, so custom exp).
Notation "⟪ pred_P ⟫ Γ ⊩ A '@' s" := (glu_rel_typ pred_P s Γ A) (in custom judg at level 80, pred_P constr, Γ custom exp, A custom exp, s custom exp).
Notation "⟪ pred_P ⟫ Γ ⊩u A '@' so" := (glu_rel_typ_unsorted pred_P so Γ A) (in custom judg at level 80, pred_P constr, Γ custom exp, A custom exp, so custom exp).
