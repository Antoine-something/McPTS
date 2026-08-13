From McPTS Require Import LibTactics.
From McPTS.Core Require Import Base.
From McPTS.Core.Syntactic.System Require Export Definitions Lemmas.
Import Syntax_Notations.

#[local]
Ltac invert_wf_gctx1 H :=
  match type of H with
  | {{ ▶ ^?Δ, ^?x : ^?A }} =>
      let HΔ := fresh "HΔ" in
      let HA := fresh "HA" in
      let Hx := fresh "Hx" in
      pose proof gctx_decomp H as [HΔ [HA Hx]];
      match goal with
      | _: {{ Δ ▶ ⋅ ⊢ A }} |- _ => clear HA
      | _: __mark__ _ {{ Δ ▶ ⋅ ⊢ A }} |- _ => clear HA
      end
  end.

Ltac invert_wf_gctx :=
  (on_all_hyp: fun H => invert_wf_gctx1 H);
  clear_dups.
  
#[local]
Ltac invert_wf_ctx1 H :=
  match type of H with
  | {{ ^?Δ ▶ ^?Γ, ^?A }} =>
      let HΓ := fresh "HΓ" in
      let HA := fresh "HAs" in
      pose proof ctx_decomp H as [HΓ HA];
      match goal with
      | _: {{ Δ ▶ Γ ⊢ A }} |- _ => clear HA
      | _: __mark__ _ {{ Δ ▶ Γ ⊢ A }} |- _ => clear HA
      (* | _: {{ Γ ⊢ A : Sort@_ }} |- _ => clear HAs *)
      (* | _: __mark__ _ {{ Γ ⊢ A : Sort@_ }} |- _ => clear HAs *)
      (* | _ => *)
      (*     let s := fresh "s" in *)
      (*     let HA := fresh "HA" in *)
      (*     destruct HAs as [s HA] *)
      end
  end.

Ltac invert_wf_ctx :=
  (on_all_hyp: fun H => invert_wf_ctx1 H);
  clear_dups.

Ltac gen_core_presup H :=
  match type of H with
  | {{ ▶ ^?Δ ≈ ^?Δ' }} =>
      let HΔ := fresh "HΔ" in
      let HΔ' := fresh "HΔ'" in
      pose proof presup_wf_gctx_eq H as [HΔ HΔ']
  | {{ ▶ ^?Δ ⊆ ^?Δ' }} =>
      let HΔ := fresh "HΔ" in
      let HΔ' := fresh "HΔ'" in
      pose proof presup_wf_gctx_subtyp H as [HΔ HΔ']
  | {{ ^?Δ ▶ ^?Γ }} =>
      let HΔ := fresh "HΔ" in
      pose proof presup_wf_ctx H as HΔ
  | {{ ^?Δ ▶ ^?Γ ≈ ^?Γ' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HΓ'' := fresh "HΓ'" in
      pose proof presup_wf_ctx_eq H as [HΔ [HΓ HΓ']]
  | {{ ^?Δ ▶ ^?Γ ⊆ ^?Γ' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in
      pose proof presup_wf_ctx_subtyp H as [HΔ [HΓ HΓ']]
  | {{ ^?Δ ▶ ^?Γ ⊢s ^?σ : ^?Γ' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in      
      pose proof presup_wf_sub H as [HΔ [HΓ HΓ']]
  | {{ ^?Δ ▶ ^?Γ ⊢ ^?M : ^?A }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HAwf := fresh "HAwf" in
      pose proof presup_wf_exp H as [HΔ [HΓ HAwf]]
      (* match goal with *)
      (* | _: {{ Δ ; Γ ⊢ A }} |- _ => idtac *)
      (* | _: {{ Δ ; Γ ⊢ A : Sort@_ }} |- _ => idtac *)
      (* | _ => *)
      (*     let HA := fresh "HA" in *)
      (*     destruct HAwf as [s HA] *)
      (* end *)
  | {{ ^?Δ ▶ ^?Γ ⊢ ^?A }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_typ H as [HΔ HΓ]
  | {{ ^?Δ ▶ ^?Γ ⊢s ^?σ ≈ ^?σ' : ^?Γ' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HΓ' := fresh "HΓ'" in      
      pose proof presup_wf_sub_eq_gctx_ctx H as [HΔ [HΓ HΓ']]
  | {{ ^?Δ ▶ ^?Γ ⊢ ^?M ≈ ^?M' : ^?A }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HAwf := fresh "HAwf" in
      pose proof presup_wf_exp_eq_gctx_ctx H as [HΔ [HΓ HAwf]]
  | {{ ^?Δ ▶ ^?Γ ⊢ ^?A ≈ ^?A' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      pose proof presup_wf_typ_eq_gctx_ctx H as [HΔ HΓ]
  | {{ ^?Δ ▶ ^?Γ ⊢ ^?A ⊆ ^?A' }} =>
      let HΔ := fresh "HΔ" in
      let HΓ := fresh "HΓ" in
      let HA' := fresh "HA'" in
      pose proof presup_wf_typ_subtyp_core H as [HΔ [HΓ HA']]
  end.

Ltac gen_lookup_presup H :=
  match type of H with
  | {{ `#?x : ^?A ∈ ^?Δ }} =>
      match goal with
      | _: {{ Δ ▶ ⋅ ⊢ A }} |- _ => fail
      | _ =>
          let HA := fresh "HA" in
          pose proof presup_gctx_lookup_typ ltac:(eassumption) H as HA
      end
  | {{ #?x : ^?A ∈ ^?Γ }} =>
      match goal with
      | _: {{ ^?Δ ▶ Γ ⊢ A }} |- _ => fail
      (* | _: {{ ^?Δ ; Γ ⊢ A : Sort@_ }} |- _ => fail *)
      | _ =>
          (* let s := fresh "s" in *)
          let HA := fresh "HA" in
          pose proof presup_ctx_lookup_typ ltac:(eassumption) H as HA
      end
  end.

Ltac gen_core_presups := (on_all_hyp: fun H => gen_core_presup H); invert_wf_gctx; invert_wf_ctx; (on_all_hyp: fun H => gen_lookup_presup H); clear_dups.
