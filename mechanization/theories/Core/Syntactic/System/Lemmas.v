From McPTS.Core Require Import Base.
From McPTS.Core.PTSSignature Require Import Signature.
From McPTS.Core.Syntactic Require Export Syntax.
From McPTS.Core.Syntactic.System Require Import Definitions.

Module SystemLemmaFunctor (P : PtsSig).
  Module Syn := SyntaxFunctor P.  
  Module Sys := SystemFunctor P.
  
  Import P Syn Sys.
  
  (* Basic context properties *)
  Lemma ctx_lookup_lt : forall {Γ x A s},
      {{ #x : A : s ∈ Γ }} ->
      x < length Γ.
  Proof.
    induction 1; simpl; lia.
  Qed.
  #[export]
    Hint Resolve ctx_lookup_lt : mctt.

  Lemma functional_ctx_lookup : forall {Γ A A' x},
      {{ #x : A ∈ Γ }} ->
      {{ #x : A' ∈ Γ }} ->
      A = A'.
  Proof with mautosolve.
    intros * Hx Hx'; gen A'.
    induction Hx as [|* ? IHHx]; intros; inversion_clear Hx';
      f_equal;
      intuition.
  Qed.

  Lemma ctx_decomp : forall {Γ A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
  Proof with now eauto.
    inversion 1...
  Qed.

End SystemLemma.
