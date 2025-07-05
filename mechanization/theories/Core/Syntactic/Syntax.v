From Coq Require Import List.

From McPTS Require Import PtsSignature.
From McPTS.Core Require Import Base.


(* Expressions M,N,A,B *)
Inductive Exp (P : PtsSig) : Type :=
| a_st : St P -> Exp P                                                  (* s *)
| a_var : nat -> Exp P                                                   (* x_i *)
| a_pi : forall (s1 s2 s3 : St P), Ru P s1 s2 s3 -> Exp P -> Exp P -> Exp P   (* Π_r A.B *)
| a_lam : forall (s1 s2 s3 : St P), Ru P s1 s2 s3 -> Exp P ->Exp P -> Exp P   (* λ_r A M *)
| a_app : Exp P -> Exp P -> Exp P                                       (* M N *)
| a_clo : Sub P -> Exp P -> Exp P                                       (* [σ]M *)

(* Substitutions σ,τ*)
with Sub (P : PtsSig) : Type :=
| a_id : Sub P                                                        (* id *)
| a_wk : Sub P                                                        (* wk *)
| a_empty : Sub P                                                     (* .. *)
| a_ext : Sub P -> Exp P -> Sub P                                     (* σ, M *)
| a_comp : Sub P -> Sub P -> Sub P                                    (* σ ∘ τ *) 
.

(* The signature needs to be passed as an extra argument to each constructor, but is inferrable *)
Arguments a_st {_}.
Arguments a_var {_}.
Arguments a_pi {_}.
Arguments a_lam {_}.
Arguments a_app {_}.
Arguments a_clo {_}.

Arguments a_id {_}.
Arguments a_wk {_}.
Arguments a_empty {_}.
Arguments a_ext {_}.
Arguments a_comp {_}.


Definition Typ (P : PtsSig) := Exp P.
Definition Knd (P : PtsSig) := Exp P.
Definition Ctx (P : PtsSig) := list (Typ P * Knd P)%type.


(* Neutral forms E *)
Inductive Ne (P : PtsSig) : Type :=
| ne_var : nat -> Ne P                                                      (* x_i *) 
| ne_app : Ne P -> Nf P -> Ne P                                            (* E V *)
                       
(* Normal forms V *)
with Nf (P : PtsSig) : Type :=
| nf_ne : Ne P -> Nf P                                                     (* E *)
| nf_st : St P -> Nf P                                                     (* s *)
| nf_pi : forall (s1 s2 s3 : St P), Ru P s1 s2 s3 -> Nf P -> Nf P -> Nf P       (* Π_r V1.V2 *)
| nf_lam : forall (s1 s2 s3 : St P), Ru P s1 s2 s3 -> Nf P -> Nf P -> Nf P      (* λ_r V_A V_M *)
.

Arguments ne_var {_}.
Arguments ne_app {_}.

Arguments nf_ne {_}.
Arguments nf_st {_}.
Arguments nf_pi {_}.
Arguments nf_lam {_}.


(* Coercion of neutral and normal forms into expressions.  Basically identity functions *)
Fixpoint Ne_to_Exp (P : PtsSig) (E : Ne P) : Exp P :=
  match E with
  | ne_var i => a_var i
  | ne_app E' V => a_app (Ne_to_Exp P E') (Nf_to_Exp P V)
  end
with Nf_to_Exp (P : PtsSig) (V : Nf P) : Exp P :=
       match V with
       | nf_ne E => Ne_to_Exp P E
       | nf_st s => a_st s
       | nf_pi s1 s2 s3 r V1 V2 => a_pi s1 s2 s3 r (Nf_to_Exp P V1) (Nf_to_Exp P V2)
       | nf_lam s1 s2 s3 r VA VM => a_lam s1 s2 s3 r (Nf_to_Exp P VA) (Nf_to_Exp P VM)
       end.

Coercion Nf_to_Exp : Nf >-> Exp.
Coercion Ne_to_Exp : Ne >-> Exp.


(* Convenient notation for writing expressions *)
#[global] Declare Custom Entry Exp.
#[global] Declare Custom Entry Nf.

#[global] Bind Scope mcpts_scope with Exp.
#[global] Bind Scope mcpts_scope with Sub.
#[global] Bind Scope mcpts_scope with Nf.
#[global] Bind Scope mcpts_scope with Ne.
Open Scope mcpts_scope.

(* We need to define substitution notation first to assert [left associativity] of level 0. *)
Notation "[ σ ] e" := (a_clo σ e) (in custom Exp at level 0, e custom Exp, σ custom Exp at level 60, left associativity, format "[ σ ] e") : mcpts_scope.
Notation "{{{ x }}}" := x (at level 0, x custom Exp at level 99, format "'{{{'  x  '}}}'") : mcpts_scope.
Notation "( x )" := x (in custom Exp at level 0, x custom Exp at level 60) : mcpts_scope.
Notation "'^' x" := x (in custom Exp at level 0, x constr at level 0) : mcpts_scope.
Notation "x" := x (in custom Exp at level 0, x ident) : mcpts_scope.

Notation "'Sort' @ s" := (a_st s) (in custom Exp at level 0, s constr at level 0, format "'Sort' @ s") : mcpts_scope.
Notation "'#' i" := (a_var i) (in custom Exp at level 0, i constr at level 0, format "'#' i") : mcpts_scope.  
Notation "'Π' r A B" := (a_pi _ _ _ r A B) (in custom Exp at level 1, r constr at level 0, A custom Exp at level 0, B custom Exp at level 60) : mcpts_scope.
Notation "'λ' r A M" := (a_lam _ _ _ r A M) (in custom Exp at level 1, r constr at level 0, A custom Exp at level 1, M custom Exp at level 60) : mcpts_scope.
Notation "f x .. y" := (a_app .. (a_app f x) .. y) (in custom Exp at level 40, f custom Exp, x custom Exp at next level, y custom Exp at next level) : mcpts_scope.

(* Notation for substitutions *)
Notation "'Id'" := a_id (in custom Exp at level 0) : mcpts_scope.
Notation "'Wk'" := a_wk (in custom Exp at level 0) : mcpts_scope.
Notation "'..'" := a_empty (in custom Exp at level 0) : mcpts_scope.
Notation "σ ∘ τ" := (a_comp σ τ) (in custom Exp at level 40, right associativity, format "σ ∘ τ") : mcpts_scope.
Notation "σ ,, e" := (a_ext σ e) (in custom Exp at level 50, left associativity, format "σ ,, e") : mcpts_scope.

(* Notation for contexts *)
Notation "⋅" := (nil) (in custom Exp at level 0) : mcpts_scope.
Notation "Γ , A :: K" := (cons (A, K) Γ) (in custom Exp at level 50, left associativity, format "Γ ,  A :: K") : mcpts_scope.


(* Notation for normal and neutral forms *)
Notation "n{{{ x }}}" := x (at level 0, x custom Nf at level 99, format "'n{{{'  x  '}}}'") : mcpts_scope.
Notation "( x )" := x (in custom Nf at level 0, x custom Nf at level 60) : mcpts_scope.
Notation "'^' x" := x (in custom Nf at level 0, x constr at level 0) : mcpts_scope.
Notation "x" := x (in custom Nf at level 0, x ident) : mcpts_scope.

Notation "'Sort' @ s" := (nf_st s) (in custom Nf at level 0, s constr at level 0, format "'Sort' @ s") : mcpts_scope.
Notation "'Π' r V1 V2" := (nf_pi _ _ _ r V1 V2) (in custom Nf at level 2, r constr at level 0, V1 custom Nf at level 1, V2 custom Nf at level 60) : mcpts_scope.
Notation "'λ' r VA VM" := (nf_lam _ _ _ r VA VM) (in custom Nf at level 2, r constr at level 0, VA custom Nf at level 1, VM custom Exp at level 60) : mcpts_scope.
Notation "f x .. y" := (ne_app .. (ne_app f x) .. y) (in custom Nf at level 40, f custom Nf, x custom Nf at next level, y custom Nf at next level) : mcpts_scope.
Notation "'#' i" := (ne_var i) (in custom Nf at level 0, i constr at level 0, format "'#' i") : mcpts_scope.
Notation "'⇑' E" := (nf_ne E) (in custom Nf at level 0, E custom Nf at level 99, format "'⇑'  E") : mcpts_scope.
