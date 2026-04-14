From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Export NbE.
From McPTS.Core.Syntactic Require Export SystemOpt.
Import Syntax_Notations.

(* Reserved Notation "Γ '⊢am' M : A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp). *)
Reserved Notation "Γ '⊢a' M ⟹ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).
Reserved Notation "Γ '⊢a' M ⟸ A" (in custom judg at level 80, Γ custom exp, M custom exp, A custom exp).

Generalizable All Variables.


Inductive alg_type_check {P} : ctx P -> typ P -> exp P -> Prop :=
(** Sorts *)
| atc_sort : `( Ax P s1 s2 ->
                {{ Γ ⊢a Sort@s1 ⟸ Sort@s2 }} )
             
(** Naturals *)
| atc_nat : `( Ru_nat P s ->
               {{ Γ ⊢a ℕ ⟸ Sort@s }} )
             
(** Conversion *)
| atc_conv : `( {{ Γ ⊢a M ⟹ A }} ->
                nbe_ty Γ A W ->
                nbe_ty Γ B W ->
                {{ Γ ⊢a M ⟸ B }} )
              
where "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) (in custom judg) : type_scope

with alg_type_infer {P} : ctx P -> typ P -> exp P -> Prop :=
(** Variables *)
| ati_var : `( {{ #x : A @ s ∈ Γ }} ->
               {{ Γ ⊢a #x ⟹ A }} )
             
(** Functions *)
| atc_pi : `( forall {r : Ru P s1 s2 s3},
                 {{ Γ ⊢a A ⟸ Sort@s1 }} ->
                 {{ Γ, A@s1 ⊢a B ⟹ Sort@s2 }} ->
                 {{ Γ ⊢a Π r A B ⟹ Sort@s3 }} )

| ati_lam : `( forall {r : Ru P s1 s2 s3},
                  {{ Γ ⊢a A ⟸ Sort@s1 }} ->
                  {{ Γ, A@s1 ⊢a M ⟹ B }} ->
                  {{ Γ ⊢a λ r A M ⟹ Π r A B }} )
             
| ati_app : `( forall {r : Ru P s1 s2 s3},
                  {{ Γ ⊢a M ⟹ Π r A B }} ->
                  {{ Γ ⊢a N ⟸ A }} ->
                  {{ Γ ⊢a M N ⟹ B[Id,,N] }} )
                  
(** Naturals *)
| ati_zero : `( Ru_nat P s ->
                {{ Γ ⊢a zero ⟹ ℕ }} )
| ati_succ : `( Ru_nat P s ->
                {{ Γ ⊢a M ⟹ ℕ }} ->
                {{ Γ ⊢a succ M ⟹ ℕ }} )
| ati_rec : `( Ru_nat P s ->
               {{ Γ, ℕ@s ⊢a A ⟸ Sort@s' }} ->
               {{ Γ ⊢a MZ ⟸ A[Id,,zero] }} ->
               {{ Γ, ℕ@s, A@s' ⊢a MS ⟸ A[Wk∘Wk,,succ #1] }} ->
               {{ Γ ⊢a N ⟹ ℕ }} ->
               {{ Γ ⊢a rec N return A | zero -> MZ | succ -> MS end ⟹ A[Id,,N] }} )
where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) (in custom judg) : type_scope.



(* Inductive alg_type_main {P : PtsSig} : ctx P -> typ P -> exp P -> Prop := *)
(* | atm : `( nbe_ty Γ A WA -> *)
(*            nbe Γ M A WM -> *)
(*            {{ Γ ⊢a WM ⟸ WA }} -> *)
(*            {{ Γ ⊢am M : A }} ) *)
(* where "Γ '⊢am' M : A" := (alg_type_main Γ A M) (in custom judg) : type_scope *)
                                                                   
(* with alg_type_check {P : PtsSig} : ctx P -> nf P -> nf P -> Prop := *)
(* (** Sorts *) *)
(* | atc_sort : `( Ax P s1 s2 -> *)
(*                 {{ Γ ⊢a Sort@s1 ⟸ Sort@s2 }} ) *)

(* (** Functions *) *)
(* | atc_pi : `( forall (r : Ru P s1 s2 s3), *)
(*                  {{ Γ ⊢a A ⟸ Sort@s1 }} -> *)
(*                  {{ Γ, ^(nf_to_exp A)@s1 ⊢a B ⟸ Sort@s2 }} -> *)
(*                  {{ Γ ⊢a Π r A B ⟸ Sort@s3 }} ) *)
(* | atc_lam : `( forall (r : Ru P s1 s2 s3), *)
(*                   {{ Γ ⊢a A ⟸ Sort@s1 }} -> *)
(*                   {{ Γ, ^(nf_to_exp A)@s1 ⊢a M ⟸ B }} -> *)
(*                   {{ Γ ⊢a λ r A M ⟸ Π r A B }} ) *)

(* (** Naturals *) *)
(* | atc_nat : `( Ru_nat P s -> *)
(*                {{ Γ ⊢a ℕ ⟸ Sort@s }} ) *)
(* | atc_zero : `( Ru_nat P s -> *)
(*                 {{ Γ ⊢a zero ⟸ ℕ }} ) *)
(* | atc_succ : `( Ru_nat P s -> *)
(*                 {{ Γ ⊢a M ⟸ ℕ }} -> *)
(*                 {{ Γ ⊢a succ M ⟸ ℕ }} ) *)

(* (** Neutrals *) *)
(* | atc_conv : `( {{ Γ ⊢a M ⟹ A }} -> *)
(*                 nbe_ty Γ A W -> *)
(*                 {{ Γ ⊢a ^(nf_neut M) ⟸ W }} ) *)
                
(* where "Γ '⊢a' M ⟸ A" := (alg_type_check Γ A M) (in custom judg) : type_scope *)

(* with alg_type_infer {P : PtsSig} : ctx P -> nf P -> ne P -> Prop := *)
(* (** Variables *) *)
(* | ati_var : `( {{ #x : A @ s ∈ Γ }} -> *)
(*                (* {{ Γ ⊢a #x ⟹ A }} )  *) *)
(*                nbe_ty Γ A W -> *)
(*                {{ Γ ⊢a #x ⟹ W }} ) *)
  
(* (** Function application *) *)
(* | ati_app : `( forall (r : Ru P s1 s2 s3), *)
(*                   {{ Γ ⊢a M ⟹ Π r A B }} -> *)
(*                   (* nbe_ty Γ A W -> *) *)
(*                   {{ Γ ⊢a N ⟸ A }} -> *)
(*                   (* {{ Γ ⊢a M N ⟹ B[Id,,N] }} ) *) *)
(*                   nbe_ty Γ {{{ B[Id,, N] }}} W -> *)
(*                   {{ Γ ⊢a M N ⟹ W }} ) *)

(* (** Recursor *) *)
(* | ati_natrec : `( Ru_nat P s -> *)
(*                   {{ Γ, ℕ@s ⊢a A ⟸ Sort@s' }} -> *)
(*                   nbe_ty Γ {{{ A[Id,,zero] }}} WZ -> *)
(*                   {{ Γ ⊢a MZ ⟸ WZ }} -> *)
(*                   nbe_ty {{{ Γ, ℕ@s, ^(nf_to_exp A)@s' }}} {{{ A[Wk∘Wk,,succ #1] }}} WS -> *)
(*                   {{ Γ, ℕ@s, ^(nf_to_exp A)@s' ⊢a MS ⟸ WS }} -> *)
(*                   {{ Γ ⊢a M ⟹ ℕ }} -> *)
(*                   nbe_ty Γ {{{ A[Id,,M] }}} WM -> *)
(*                   {{ Γ ⊢a rec M return A | zero -> MZ | succ -> MS end ⟹ WM }} ) *)
(* where "Γ '⊢a' M ⟹ A" := (alg_type_infer Γ A M) (in custom judg) : type_scope. *)


#[export]
Hint Constructors (* alg_type_main *) alg_type_check alg_type_infer : mcpts.

Scheme (* alg_type_main_mut_ind := Induction for alg_type_main Sort Prop *)
    (* with *)
    alg_type_check_mut_ind := Induction for alg_type_check Sort Prop
with alg_type_infer_mut_ind := Induction for alg_type_infer Sort Prop.
Combined Scheme alg_type_mut_ind from
  (* alg_type_main_mut_ind, *)
  alg_type_check_mut_ind,
  alg_type_infer_mut_ind.
