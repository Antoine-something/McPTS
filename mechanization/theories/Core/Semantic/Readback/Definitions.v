From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Evaluation.
From McPTS.Core.Semantic Require Export Domain.
Import Domain_Notations.

Reserved Notation "'Rnf' m 'in' s ↘ M" (in custom judg at level 80, m custom domain, s constr, M custom nf).
Reserved Notation "'Rne' m 'in' s ↘ M" (in custom judg at level 80, m custom domain, s constr, M custom nf).
Reserved Notation "'Rtyp' a 'in' s ↘ A" (in custom judg at level 80, a custom domain, s constr, A custom nf).

Generalizable All Variables.

Inductive read_nf {P : PtsSig} : nat -> domain_nf P -> nf P -> Prop :=
| read_nf_type :
  `( {{ Rtyp a in i ↘ A }} ->
     {{ Rnf ⇓ Sort@s a in i ↘ A }} )
| read_nf_fn :
  `( forall r : Ru P s1 s2 s3,
        (** Normal form of arg type *)
        {{ Rtyp a in i ↘ A }} ->
        (** Normal form of eta-expanded body *)
        {{ $| m & ⇑! a i |↘ m' }} ->
        {{ ⟦ B ⟧ ρ ↦ ⇑! a i ↘ b }} ->
        {{ Rnf ⇓ b m' in S i ↘ M }} ->
        (** Normal form of the whole function *)
        {{ Rnf ⇓ (Π r a ρ B) m in i ↘ λ r A M }} )
| read_nf_zero :
  `( {{ Rnf ⇓ ℕ zero in i ↘ zero }} )
| read_nf_succ :
  `( {{ Rnf ⇓ ℕ m in i ↘ M }} ->
     {{ Rnf ⇓ ℕ (succ m) in i ↘ succ M }} )
| read_nf_nat_neut :
  `( {{ Rne m in i ↘ M }} ->
     {{ Rnf ⇓ ℕ (⇑ a m) in i ↘ ⇑ M }} )
| read_nf_neut :
  `( {{ Rne m in i ↘ M }} ->
     {{ Rnf ⇓ (⇑ a b) (⇑ c m) in i ↘ ⇑ M }} )
where "'Rnf' m 'in' i ↘ M" := (read_nf i m M) (in custom judg) : type_scope
with read_ne {P : PtsSig} : nat -> domain_ne P -> ne P -> Prop :=
| read_ne_var :
  `( {{ Rne !x in i ↘ #(i - x - 1) }} )
| read_ne_app :
  `( {{ Rne m in i ↘ M }} ->
     {{ Rnf n in i ↘ N }} ->
     {{ Rne m n in i ↘ M N }} )
| read_ne_natrec :
  `( (** Normal form of motive *)
     {{ ⟦ B ⟧ ρ ↦ ⇑! ℕ i ↘ b }} ->
     {{ Rtyp b in S i ↘ B' }} ->
     (** Normal form of mz *)
     {{ ⟦ B ⟧ ρ ↦ zero ↘ bz }} ->
     {{ Rnf ⇓ bz mz in i ↘ MZ }} ->
     (** Normal form of MS *)
     {{ ⟦ B ⟧ ρ ↦ succ (⇑! ℕ i) ↘ bs }} ->
     {{ ⟦ MS ⟧ (ρ ↦ ⇑! ℕ i) ↦ ⇑! b (S i) ↘ ms }} ->
     {{ Rnf ⇓ bs ms in S (S i) ↘ MS' }} ->
     (** Neutral form of m *)
     {{ Rne m in i ↘ M }} ->
     {{ Rne rec m under ρ return B | zero -> mz | succ -> MS end in i ↘ rec M return B' | zero -> MZ | succ -> MS' end }} )
where "'Rne' m 'in' i ↘ M" := (read_ne i m M) (in custom judg) : type_scope
with read_typ {P : PtsSig} : nat -> domain P -> nf P -> Prop :=
| read_typ_univ :
  `( {{ Rtyp Sort@s in i ↘ Sort@s }} )
| read_typ_pi :
  `( forall r : Ru P s1 s2 s3,
        (** Normal form of arg type *)
        {{ Rtyp a in i ↘ A }} ->
        
        (** Normal form of ret type *)
        {{ ⟦ B ⟧ ρ ↦ ⇑! a i ↘ b }} ->
        {{ Rtyp b in S i ↘ B' }} ->
        
        (** Normal form of the whole function space *)
        {{ Rtyp Π r a ρ B in i ↘ Π r A B' }})
| read_typ_nat :
  `( {{ Rtyp ℕ in i ↘ ℕ }} )
| read_typ_neut :
  `( {{ Rne b in i ↘ B }} ->
     {{ Rtyp ⇑ a b in i ↘ ⇑ B }})
where "'Rtyp' m 'in' i ↘ M" := (read_typ i m M) (in custom judg) : type_scope
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
