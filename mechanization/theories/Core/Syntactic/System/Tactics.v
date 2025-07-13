From McPTS Require Import LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Import Definitions Lemmas.

(* #[export] *)
(* Hint Rewrite -> wf_exp_eq_pi_sub using pi_univ_level_tac : mctt. *)

#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | {{ ⊢ ^?Γ, ^?A :: ^?K }} =>
      let HΓ := fresh "HΓ" in
      let HAs := fresh "HAs" in
      pose proof ctx_decomp H as [HΓ HAs];
      match goal with
      | _: {{ Γ ⊢ A }} |- _ => clear HAs
      | _: __mark__ _ {{ Γ ⊢ A }} |- _ => clear HAs
      | _: {{ Γ ⊢ A : Sort@_ }} |- _ => clear HAs
      | _: __mark__ _ {{ Γ ⊢ A : Sort@_ }} |- _ => clear HAs
      | _ =>
          let s := fresh "s" in
          let HA := fresh "HA" in
          destruct HAs as [s HA]
      end
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.

Ltac gen_core_presup H :=
  match type of H with
  | {{ ⊢ ^?Γ ≈ ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_ctx_eq H as [HΓ HΔ]
  | {{ ^?Γ ⊢ ^?M : ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HAwf := fresh "HAwf" in
      pose proof presup_exp H as [HΓ HAwf];
      match goal with
      | _: {{ Γ ⊢ A }} |- _ => idtac
      (* | _: __mark__ _ {{ Γ ⊢ A }} |- _ => clear HAwf *)
      | _: {{ Γ ⊢ A : Sort@_ }} |- _ => idtac
      (* | _: __mark__ _ {{ Γ ⊢ A : Sort@_ }} |- _ => clear HAwf *)
      | _ =>
          let HA := fresh "HA" in
          destruct HAwf as [s HA]
      end
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} =>
      let HΓ := fresh "HΓ" in
      let HΔ := fresh "HΔ" in
      pose proof presup_sub H as [HΓ HΔ]
  end.

Ltac gen_lookup_presup H :=
  match type of H with
  | {{ #?x : ^?A :: ^?K ∈ ^?Γ }} =>
      match goal with
      | _: {{ Γ ⊢ A }} |- _ => fail
      (* | _: __mark__ _ {{ Γ ⊢ A }} |- _ => fail *)
      | _: {{ Γ ⊢ A : Sort@_ }} |- _ => fail
      (* | _: __mark__ _ {{ Γ ⊢ A : Sort@_ }} |- _ => fail *)
      | _ =>
          let s := fresh "s" in
          let HA := fresh "HA" in
          pose proof presup_ctx_lookup_typ ltac:(eassumption) H as [s HA]
      end
  end.

Ltac gen_core_presups := (on_all_hyp: fun H => gen_core_presup H); invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
