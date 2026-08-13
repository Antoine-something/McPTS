From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Evaluation.
From McPTS.Core.Semantic Require Export Domain.
Import Domain_Notations.

Reserved Notation "Δ ▶ 'Rnf' m 'in' i ↘ M" (in custom judg at level 80, Δ custom exp, m custom domain, i constr, M custom nf).
Reserved Notation "Δ ▶ 'Rne' m 'in' i ↘ M" (in custom judg at level 80, Δ custom exp, m custom domain, i constr, M custom nf).
Reserved Notation "Δ ▶ 'Rtyp' a 'in' i ↘ A" (in custom judg at level 80, Δ custom exp, a custom domain, i constr, A custom nf).

Generalizable All Variables.

Inductive read_nf {P : PtsSig} : gctx P -> nat -> domain_nf P -> nf P -> Prop :=
| read_nf_type :
  `( {{ Δ ▶ Rtyp a in i ↘ A }} ->
     {{ Δ ▶ Rnf ⇓ Sort@s a in i ↘ A }} )
| read_nf_fn :
  `( forall r : Ru_pi P s1 s2 s3,
        (** Normal form of arg type *)
        {{ Δ ▶ Rtyp a in i ↘ A }} ->
        (** Normal form of eta-expanded body *)
        {{ Δ ▶ $| m & ⇑! a i |↘ m' }} ->
        {{ Δ ▶ ⟦ B ⟧ ρ ↦ ⇑! a i ↘ b }} ->
        {{ Δ ▶ Rtyp b in S i ↘ B' }} ->
        {{ Δ ▶ Rnf ⇓ b m' in S i ↘ M }} ->
        (** Normal form of the whole function *)
        {{ Δ ▶ Rnf ⇓ (Π r a ρ B) m in i ↘ λ r A B' M }} )
| read_nf_zero :
  `( {{ Δ ▶ Rnf ⇓ ℕ zero in i ↘ zero }} )
| read_nf_succ :
  `( {{ Δ ▶ Rnf ⇓ ℕ m in i ↘ M }} ->
     {{ Δ ▶ Rnf ⇓ ℕ (succ m) in i ↘ succ M }} )
| read_nf_nat_neut :
  `( {{ Δ ▶ Rne m in i ↘ M }} ->
     {{ Δ ▶ Rnf ⇓ ℕ (⇑ a m) in i ↘ ⇑ M }} )
| read_nf_neut :
  `( {{ Δ ▶ Rne m in i ↘ M }} ->
     {{ Δ ▶ Rnf ⇓ (⇑ a b) (⇑ c m) in i ↘ ⇑ M }} )
where "Δ ▶ 'Rnf' m 'in' i ↘ M" := (read_nf Δ i m M) (in custom judg) : type_scope
with read_ne {P : PtsSig} : gctx P -> nat -> domain_ne P -> ne P -> Prop :=
| read_ne_var :
  `( {{ Δ ▶ Rne !x in i ↘ #(i - x - 1) }} )
| read_ne_gvar :
  `( {{ Δ ▶ Rne `!x in i ↘ `#x }} )
| read_ne_app :
  `( {{ Δ ▶ Rne m in i ↘ M }} ->
     {{ Δ ▶ Rnf n in i ↘ N }} ->
     {{ Δ ▶ Rne m n in i ↘ M N }} )
| read_ne_natrec :
  `( (** Normal form of motive *)
     {{ Δ ▶ ⟦ B ⟧ ρ ↦ ⇑! ℕ i ↘ b }} ->
     {{ Δ ▶ Rtyp b in S i ↘ B' }} ->
     (** Normal form of mz *)
     {{ Δ ▶ ⟦ B ⟧ ρ ↦ zero ↘ bz }} ->
     {{ Δ ▶ Rnf ⇓ bz mz in i ↘ MZ }} ->
     (** Normal form of MS *)
     {{ Δ ▶ ⟦ B ⟧ ρ ↦ succ (⇑! ℕ i) ↘ bs }} ->
     {{ Δ ▶ ⟦ MS ⟧ (ρ ↦ ⇑! ℕ i) ↦ ⇑! b (S i) ↘ ms }} ->
     {{ Δ ▶ Rnf ⇓ bs ms in S (S i) ↘ MS' }} ->
     (** Neutral form of m *)
     {{ Δ ▶ Rne m in i ↘ M }} ->
     {{ Δ ▶ Rne rec m under ρ return B | zero -> mz | succ -> MS end in i ↘ rec M return B' | zero -> MZ | succ -> MS' end }} )
where "Δ ▶ 'Rne' m 'in' i ↘ M" := (read_ne Δ i m M) (in custom judg) : type_scope
with read_typ {P : PtsSig} : gctx P -> nat -> domain P -> nf P -> Prop :=
| read_typ_univ :
  `( {{ Δ ▶ Rtyp Sort@s in i ↘ Sort@s }} )
| read_typ_pi :
  `( forall r : Ru_pi P s1 s2 s3,
        (** Normal form of arg type *)
        {{ Δ ▶ Rtyp a in i ↘ A }} ->
        (** Normal form of ret type *)
        {{ Δ ▶ ⟦ B ⟧ ρ ↦ ⇑! a i ↘ b }} ->
        {{ Δ ▶ Rtyp b in S i ↘ B' }} ->
        (** Normal form of the whole function space *)
        {{ Δ ▶ Rtyp Π r a ρ B in i ↘ Π r A B' }})
| read_typ_nat :
  `( {{ Δ ▶ Rtyp ℕ in i ↘ ℕ }} )
| read_typ_neut :
  `( {{ Δ ▶ Rne b in i ↘ B }} ->
     {{ Δ ▶ Rtyp ⇑ a b in i ↘ ⇑ B }})
where "Δ ▶ 'Rtyp' m 'in' i ↘ M" := (read_typ Δ i m M) (in custom judg) : type_scope
.

Scheme read_nf_mut_ind := Induction for read_nf Sort Prop
with read_ne_mut_ind := Induction for read_ne Sort Prop
with read_typ_mut_ind := Induction for read_typ Sort Prop.
Combined Scheme read_mut_ind from
  read_nf_mut_ind,
  read_ne_mut_ind,
  read_typ_mut_ind.

#[export]
Hint Constructors read_nf read_ne read_typ : mcpts.
