From Coq Require Import Morphisms_Relations.
From Equations Require Import Equations.

From McPTS Require Import PtsSignature LibTactics.
From McPTS.Algorithmic Require Import Typing.
From McPTS.Core Require Import Base.
From McPTS.Core.Semantic Require Import Consequences Realizability.
From McPTS.Extraction Require Import NbE PseudoMonadic Subtyping.
From McPTS.Frontend Require Import Elaborator.
Import Domain_Notations.

Section lookup.
  #[local]
  Ltac impl_obl_tac1 :=
    match goal with
    | |- ~ _ => intro
    | H: {{ ⊢ ^_, ^_ @ ^_ }} |- _ => inversion_clear H
    | H: {{ # _ : ^_ @ ^_ ∈ ⋅ }} |- _ => inversion_clear H
    | H: {{ # (S _) : ^_ @ ^_ ∈ ^_, ^_ @ ^_ }} |- _ => inversion_clear H
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros;
    repeat impl_obl_tac1;
    intuition (mauto 4).

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations lookup {P} (dec_P : DecidableSig P) (Γ : ctx P) (HΓ : {{ ⊢ Γ }}) x : { A & {s | {{ #x : A @ s ∈ Γ }} } } + { forall A s, ~ {{ #x : A @ s ∈ Γ }} } :=
  | dec_P, {{{ Γ, A@s }}}, HΓ, x with x => {
    | 0 => pureo (existT _ {{{ A[Wk] }}} (exist _ s _))
    | S x' => 
        let*o (existT _ B (exist _ s' _)) := lookup dec_P Γ _ x' while _ in
        pureo (existT _ {{{ B[Wk] }}} (exist _ s' _))
    }
  | dec_P, {{{ ⋅ }}}, HΓ, x => inright _.
End lookup.

Section type_check.
  #[derive(equations=no,eliminator=no)]
  Equations get_level_of_sort_nf {P} (dec_P : DecidableSig P) (A : nf P) : { s | A = n{{{ Sort@s }}} } + { forall s, A <> n{{{ Sort@s }}} } :=
  | dec_P, n{{{ Sort@s }}} => pureo (exist _ s _)
  | _, _                   => inright _
  .
  
  (** Don't forget to use 9th bit of [Extraction Flag] (for example, [Set Extraction Flag 1007.]).
      Otherwise, this function would introduce redundant pair construction/pattern matching. *)
  #[derive(equations=no,eliminator=no)]
  Equations get_subterms_of_pi_nf {P} (dec_P : DecidableSig P) (A : nf P) : { s1 & { s2 & { s3 & { r & { B & { C | A = @nf_pi P s1 s2 s3 r B C } } } } } } + { forall s1 s2 s3 r B C, A <> @nf_pi P s1 s2 s3 r B C } :=
  | dec_P, n{{{ Π r B C }}} => pureo (existT _ s1 (existT _ s2 (existT _ s3 (existT _ r (existT _ B (exist _ C _))))))
  | _, _                    => inright _
  .

  Extraction Inline get_level_of_sort_nf get_subterms_of_pi_nf.

  Inductive type_check_order {P} : exp P -> Prop :=
  | tc_ti : forall {A}, type_infer_order A -> type_check_order A
  with type_infer_order {P} : exp P -> Prop :=
  | ti_typ : forall {s}, type_infer_order {{{ Sort@s }}}
  | ti_nat : type_infer_order {{{ ℕ }}}
  | ti_zero : type_infer_order {{{ zero }}}
  | ti_succ : forall {M}, type_check_order M -> type_infer_order {{{ succ M }}}
  | ti_natrec : forall {A MZ MS M}, type_check_order M -> type_infer_order A -> type_check_order MZ -> type_check_order MS -> type_infer_order {{{ rec M return A | zero -> MZ | succ -> MS end }}}
  | ti_pi : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {A B}, type_check_order A -> type_check_order B -> type_infer_order {{{ Π r A B }}}
  | ti_fn : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {A B M}, type_check_order A -> type_check_order B -> type_check_order M -> type_infer_order {{{ λ r A B M }}}
  | ti_app : forall {M N}, type_infer_order M -> type_check_order N -> type_infer_order {{{ M N }}}
  | ti_vlookup : forall {x}, type_infer_order {{{ #x }}}
  .

  #[local]
  Hint Constructors type_check_order type_infer_order : mcpts.

  Lemma user_exp_to_type_infer_order {P} : forall M,
      user_exp P M ->
      type_infer_order M.
  Proof.
    intros M HM.
    enough (type_check_order M) as [] by eassumption.
    induction HM; progressive_inversion; do 2 constructor; trivial with mcpts.
  Qed.

  #[local]
  Ltac clear_defs :=
    do 2 lazymatch goal with
      | H: (forall (Γ : ?ctx) (A : ?expA),
               {{ Γ ⊢ A }} ->
               forall M : ?expM,
                 type_check_order M ->
                 ({ {{ Γ ⊢a M ⟸ A }} } + { ~ {{ Γ ⊢a M ⟸ A }} }))
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall (P : PtsSig), (?dec_P : DecidableSig P) -> PredicativeSig P -> FunctionalSig P ->
            forall (Γ : ?ctx) (A : ?expA),
              {{ Γ ⊢ A }} -> forall M : ?expM, type_check_order M -> { {{ Γ ⊢a M ⟸ A }} } + { ~ {{ Γ ⊢a M ⟸ A }} })
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall (P : PtsSig), DecidableSig P -> PredicativeSig P -> FunctionalSig P -> 
            forall Γ : ?ctx,
              {{ ⊢ Γ }} ->
              forall M : ?expM,
                type_infer_order M ->
                ({ B : nf P | {{ Γ ⊢a M ⟹ B }} /\ {{ Γ ⊢aty ^(nf_to_exp B) }} } + { forall C : nf P, ~ {{ Γ ⊢a M ⟹ C }} }))
        |- _ =>
          clear H
      | H: (forall Γ : ?ctx,
               {{ ⊢ Γ }} ->
               forall M : ?expM,
                 type_infer_order M ->
                 ({ B : nf ?P | {{ Γ ⊢a M ⟹ B }} /\{{ Γ ⊢aty ^(nf_to_exp B) }} } + { forall C : nf ?P, ~ {{ Γ ⊢a M ⟹ C }} }))
        |- _ =>
          clear H
    end.

  #[local]
  Ltac clear_redundant_pat :=
    repeat match goal with
      | H: { A | {{ ^?Γ ⊢a ^?M ⟹ A }} /\ {{ ^?Γ ⊢aty ^_ }} }
          , H1: {{ ^?Γ ⊢a ^?M ⟹ ^?B }} /\ {{ ^?Γ ⊢aty ^_ }} |- _ => clear H
      | H: { s | ?A = n{{{ Sort@s }}} }
          , H1: ?A = n{{{ Sort@?s }}} |- _ => clear H
      | H: { B & { C | ?A = n{{{ Π ?r B C }}} } }
          , H1: ?A = n{{{ Π ?r ^?B ^?C }}} |- _ => clear H
      end.

  #[local]
  Ltac clean_obl := intros; clear_defs; clear_redundant_pat; destruct_conjs; subst; simpl in *.

  #[local]
  Obligation Tactic := clean_obl.

  #[local]
  Ltac impl_obl_tac := clean_obl; eauto 3.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_check {P : PtsSig} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) (Γ : ctx P) A (HA : {{ Γ ⊢ A }}) M (H : type_check_order M) : { {{ Γ ⊢a M ⟸ A }} } + { ~ {{ Γ ⊢a M ⟸ A }} } by struct H :=
  | dec_P, pred_P, func_P, Γ, A, HA, M, H =>
      let*o->b (exist _ B _) := type_infer dec_P pred_P func_P Γ _ M _ while _ in
      let*b _ := subtyping_impl dec_P Γ (B : nf P) A _ while _ in
      pureb _
  with type_infer {P : PtsSig} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) (Γ : ctx P) (HΓ : {{ ⊢ Γ }}) M (H : type_infer_order M) : { A : nf P | {{ Γ ⊢a M ⟹ A }} /\ {{ Γ ⊢aty A }} } + { forall A, ~ {{ Γ ⊢a M ⟹ A }} } by struct H :=
  | dec_P, pred_P, func_P, Γ, HΓ, M, H with M => {
    | {{{ Sort@s }}} =>
        let*o (existT _ s' _) := dec_ax_typ dec_P s while _ in
        pureo (exist _ n{{{ Sort@s' }}} _)
    | {{{ ℕ }}} =>
        let*o (existT _ s _) := dec_ru_nat dec_P while _ in
        pureo (exist _ n{{{ Sort@s }}} _)
    | {{{ zero }}} =>
        let*o (existT _ s _) := dec_ru_nat dec_P while _ in
        pureo (exist _ n{{{ ℕ }}} _)
    | {{{ succ M' }}} =>
        let*o (existT _ s _) := dec_ru_nat dec_P while _ in
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ ℕ }}} _ M' _ while _ in
        pureo (exist _ n{{{ ℕ }}} _)
    | {{{ rec M' return A' | zero -> MZ | succ -> MS end }}} =>
        let*o (existT _ s _) := dec_ru_nat dec_P while _ in
        let*o (exist _ UA' _) := type_infer dec_P pred_P func_P {{{ Γ, ℕ@s }}} _ A' _ while _ in
        let*o (exist _ s' _) :=  get_level_of_sort_nf dec_P UA' while _ in
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ A'[Id,,zero] }}} _ MZ _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, ℕ@s, A'@s' }}} {{{ A'[Wk∘Wk,,succ #1] }}} _ MS _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ ℕ }}} _ M' _ while _ in
        let (A'', _) := nbe_ty_impl Γ {{{ A'[Id,,M'] }}} _ in
        pureo (exist _ A'' _)
    | {{{ Π r B C }}} =>
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ Sort@s1 }}} _ B _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, B@s1 }}} {{{ Sort@s2 }}} _ C _ while _ in
        pureo (exist _ n{{{ Sort@s3 }}} _)
    | {{{ λ r A' B' M' }}} =>
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ Sort@s4 }}} _ A' _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, A'@s4 }}} {{{ Sort@s5 }}} _ B' _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, A'@s4 }}} B' _ M' _ while _ in
        let (A'', _) := nbe_impl Γ A' {{{ Sort@s4 }}} _ in
        let (B'', _) := nbe_impl {{{ Γ, A'@s4 }}} B' {{{ Sort@s5 }}} _ in
        pureo (exist _ n{{{ Π r A'' B'' }}} _)
    | {{{ M' N' }}} =>
        let*o (exist _ C _) := type_infer dec_P pred_P func_P Γ _ M' _ while _ in
        let*o (existT _ s1 (existT _ s2 (existT _ s3 (existT _ r (existT _ A (exist _ B _)))))) :=
          get_subterms_of_pi_nf dec_P C while _ in
        let*b->o _ := type_check dec_P pred_P func_P Γ (A : nf P) _ N' _ while _ in
        let (B', _) := nbe_ty_impl Γ {{{ ^(B : nf P)[Id,,N'] }}} _ in
        pureo (exist _ B' _)
    | {{{ #x }}} =>
        let*o (existT _ A (exist _ s' _)) := lookup dec_P Γ _ x while _ in
        let (A', _) := nbe_ty_impl Γ A _ in
        pureo (exist _ A' _)
    | _ => inright _
    }
  .  

  #[local]
  Ltac invert_type_check_infer_order :=
    repeat match goal with
      | H: type_infer_order _ |- _ => progressive_invert H
      end.

  #[local]
  Ltac impl_type_check_infer_obl_tac :=
    lazymatch goal with
      | H: type_check_order ?A |- type_infer_order ?A =>
          inversion_clear H; eassumption
      | |- type_infer_order _ => invert_type_check_infer_order; eassumption
      | |- type_check_order _ => invert_type_check_infer_order; eassumption
      end.

  #[local]
  Ltac impl_wf_context_obl_tac :=
    lazymatch goal with
      | |- {{ ⊢ ^?Γ, ^?A@^?s }} =>
          gen_presups;
          assert {{ ⊢ Γ }} by mauto 2;
          unshelve (eassert {{ Γ ⊢ A : ^n{{{ Sort@_ }}} }}; solve [mauto 2 using alg_type_infer_sound]); solve [constructor]
      | |- {{ ⊢ ^?Γ }} => gen_presups; mauto 2
      end.

  #[local]
  Ltac impl_ill_typed_obl_tac :=
    match goal with
      | |- ~ _ =>
          let H := fresh "H" in
          intros H; inversion_clear H;
          functional_alg_type_infer_rewrite_clear;
          solve [firstorder | congruence]
      end.

  #[local]
  Ltac resolve_alg_sound :=
    repeat match goal with
      | H: {{ ^?Γ ⊢a ^?M ⟹ ^?A }} |- _ => assert {{ Γ ⊢ M : A }} by eauto 2 using alg_type_infer_sound; fail_if_dup
      | H: {{ ^?Γ ⊢a ^?M ⟸ ^?A }} |- _ => assert {{ Γ ⊢ M : A }} by eauto 2 using alg_type_check_sound; fail_if_dup
      | H: {{ ^?Γ ⊢aty ^?A }} |- _ => assert {{ Γ ⊢ A }} by eauto 2 using alg_aty_sound; fail_if_dup
      end.

  #[local]
  Ltac simplify_nbe_order :=
    lazymatch goal with
    | |- nbe_ty_order ?Γ ?A => enough ({{ Γ ⊢ A }}) as [? []]%soundness_ty by eauto 3 using nbe_ty_order_sound
    | |- nbe_order ?Γ ?M ?A => enough ({{ Γ ⊢ M : A }}) as [? []]%soundness by eauto 3 using nbe_order_sound
    end.

  #[local]
  Ltac impl_nbe_order_obl_tac :=
    lazymatch goal with
    | |- nbe_ty_order ?Γ ?A =>
        gen_presups;
        resolve_alg_sound;
        simplify_nbe_order;
        unshelve (eexists; solve [eauto 2]);
        solve [constructor]
    | |- nbe_order ?Γ ?M ?A =>
        gen_presups;
        resolve_alg_sound;
        simplify_nbe_order;
        solve [eauto 2]
    end.

  #[local]
  Ltac impl_subtyping_order_obl_tac :=
    match goal with
    | |- subtyping_order ?Γ ?B ?A =>
        gen_presups;
        resolve_alg_sound;
        econstructor;
        lazymatch goal with
        | |- nbe_ty_order ?Γ ?A =>
            simplify_nbe_order;
            solve [eassumption]
        | |- nbe_order ?Γ ?M ?A =>
            simplify_nbe_order;
            solve [eassumption]
        end
    end.

  #[local]
  Ltac impl_exist_lvl_wf_exp_obl_tac :=
    match goal with
    | |- exists s, {{ ^?Γ ⊢ ^?A : Sort@s }} => enough (exists s, {{ Γ ⊢ A : ^(nf_to_exp (nf_st s)) }}) by eauto 2
    | |- exists s, {{ ^?Γ ⊢ ^?A : ^(nf_to_exp (nf_st s)) }} => idtac
    end;
    autoinjections;
    progressive_inversion;
    resolve_alg_sound;
    mautosolve 3.

  #[local]
  Ltac impl_infer_spec_obl_tac :=
    match goal with
    | |- (_ /\ _) => split; mautosolve 3
    end.

  Solve Obligations with
    (clean_obl;
     first
       [ impl_type_check_infer_obl_tac
       | impl_wf_context_obl_tac
       | impl_ill_typed_obl_tac
       | impl_nbe_order_obl_tac
       | impl_subtyping_order_obl_tac
       | impl_exist_lvl_wf_exp_obl_tac
       | impl_infer_spec_obl_tac
       | idtac
       ]
    ).

  Next Obligation.
    mautosolve 3.
  Qed.
  
  Next Obligation.
    mautosolve 3.
  Qed.

  Next Obligation.
    dependent destruction H.
    assert {{ Γ ⊢ B : Sort@s1 }} by mauto 3 using alg_type_check_sound.
    mauto 3.
  Qed.

  Next Obligation.
    intros Hf.
    inversion Hf; subst.
    intuition.
  Qed.

  Next Obligation.
    inversion H; mauto 2.
  Qed.
  
  Next Obligation.
    dependent destruction H.
    assert {{ Γ ⊢ A' : Sort@s4 }} by mauto 3 using alg_type_check_sound.
    mauto 3.
  Qed.

  Next Obligation.
    intros Hf.
    inversion Hf; subst.
    intuition.
  Qed.

  Next Obligation.
    assert {{ Γ ⊢ A' : Sort@s4 }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, A'@s4 }} by mauto 2.
    assert {{ Γ, A'@s4 ⊢ B' : Sort@s5 }} by mauto 3 using alg_type_check_sound.
    mauto 2.
  Qed.

  Next Obligation.
    simplify_nbe_order.
    mauto 3 using alg_type_check_sound.
  Qed.

  Next Obligation.
    simplify_nbe_order.
    assert {{ Γ ⊢ A' : Sort@s4 }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, A'@s4 }} by mauto 2.
    mauto 3 using alg_type_check_sound.
  Qed.

  Next Obligation.
    split; [mautosolve 3|].
    assert (user_exp P A'') by trivial using user_exp_nf.
    assert (user_exp P B'') by trivial using user_exp_nf.    
    enough {{ Γ ⊢ Π r A'' B'' : Sort@s6 }}; [eapply alg_aty_complete; mauto 2|].
    assert {{ Γ ⊢ A' : Sort@s4 }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ, A'@s4 ⊢ B' : Sort@s5 }} by (eapply alg_type_check_sound; mauto 3).

    assert {{ Γ ⊢ A' ≈ A'' : Sort@s4 }} by mauto 2 using soundness'.
    assert {{ Γ, A'@s4 ⊢ B' ≈ B'' : Sort@s5 }} by mauto 2 using soundness'.
    gen_presups.
    assert {{ ⊢ Γ, A'@s4 ≈ Γ, ^(nf_to_exp A'')@s4 }} by mauto 3.
    econstructor; mauto 2.
  Qed.

  Next Obligation.
    dependent destruction H5.
    dependent destruction H4.
    dependent destruction H3.
    dependent destruction H2.
    dependent destruction H1.
    dependent destruction e.
    resolve_alg_sound.
    simpl in H3.
    gen_presups.
    simpl in HAwf0.
    eapply wf_typ_pi_inversion in HAwf0.
    destruct_conjs.
    mauto 2.
  Qed.

  Next Obligation.
    dependent destruction H5.
    dependent destruction H4.
    dependent destruction H3.
    dependent destruction H2.
    dependent destruction e.
    inversion a0; subst.
    simplify_nbe_order.
    resolve_alg_sound.
    eapply wf_typ_pi_inversion in H6.
    destruct_conjs.
    gen_presup H4.
    assert {{ Γ ⊢ A0 ⊆ A }} by mauto 3 using alg_subtyping_sound.
    assert {{ Γ ⊢ N' : A }} by mauto 2.
    mauto 4.
  Qed.

  Next Obligation.
    dependent destruction H5.
    dependent destruction H4.
    dependent destruction H3.
    dependent destruction H2.
    dependent destruction e.
    split; [mautosolve 3|].
    assert {{ Γ ⊢ Π r A B }} by (mauto 2 using alg_aty_sound).
    eapply wf_typ_pi_inversion in H2 as [].
    assert {{ Γ, ^(nf_to_exp A)@s1 ⊢ B }} by (gen_presups; mauto 2).
    assert {{ Γ ⊢ N' : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢s Id,,N' : Γ, ^(nf_to_exp A)@s1 }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,N'] }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,N'] ≈ B' }} by mauto 2 using soundness_ty'.
    assert (user_exp P B') by trivial using user_exp_nf.    
    eapply alg_aty_complete; mauto 3.
  Qed.  

  Next Obligation.
    simplify_nbe_order.
    mauto 3.
  Qed.

  Next Obligation.
    split; [mautosolve 3|].
    assert {{ Γ ⊢ A }} by mauto 3.
    assert {{ Γ ⊢ A ≈ A' }} by mauto 2 using soundness_ty'.
    assert (user_exp P A') by trivial using user_exp_nf.    
    eapply alg_aty_complete; mauto 3.
  Qed.

  
  Next Obligation.    
    split; mautosolve 4.
  Qed.

  Next Obligation.
    mautosolve 3.
  Qed.

  Next Obligation.
    split; mautosolve 4.
  Qed.

  Next Obligation.
    intros Hf.
    inversion Hf; subst.
    functional_alg_type_infer_rewrite_clear.
    assert (s = s0) by (eapply Func_ru_nat; eassumption); subst.
    intuition.
  Qed.

  Next Obligation.
    intros Hf.
    inversion Hf; subst.
    assert (s = s0) by (eapply Func_ru_nat; eassumption); subst.
    functional_alg_type_infer_rewrite_clear.
    intuition.
  Qed.
  
  Next Obligation.
    assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
    assert {{ ⊢ Γ, ℕ@s }} by mauto 2.
    resolve_alg_sound.
    simpl in *.
    assert {{ Γ, ℕ@s ⊢ A' }} by mauto 2.
    assert {{ Γ ⊢ zero : ℕ }} by mauto 2.
    assert {{ Γ ⊢s Id,,zero : Γ, ℕ@s }} by mauto 2.
    mauto 2.
  Qed.

  Next Obligation.
    assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
    assert {{ ⊢ Γ, ℕ@s }} by mauto 2.
    resolve_alg_sound.
    simpl in *.
    assert {{ ⊢ Γ, ℕ@s, A'@s' }} by mauto 2.
    assert {{ Γ ⊢s Id,,zero : Γ, ℕ@s }} by mauto 3.
    assert {{ Γ ⊢ A'[Id,,zero] : Sort@s' }} by mauto 3.
    assert {{ Γ, ℕ@s, A'@s' ⊢s Wk∘Wk : Γ }} by (econstructor; mauto 3).
    assert {{ Γ, ℕ@s, A'@s' ⊢s Wk∘Wk,,succ #1 : Γ, ℕ@s }} by mauto 4.
    assert {{ Γ, ℕ@s, A'@s' ⊢ A'[Wk∘Wk,,succ #1] : Sort@s' }} by mauto 4.
    mauto 2.
  Qed.

  Next Obligation.
    
    inversion 1.
    assert (pat0 = s) by (eapply Func_ru_nat; mauto 2).
    assert (s0 = s) by (eapply Func_ru_nat; mauto 2).
    subst.
    
  Admitted.

  Inductive ctx_st_subtyp {P} : ctx P -> ctx P -> Prop :=
  | css_nil : ctx_st_subtyp {{{ ⋅ }}} {{{ ⋅ }}}
  | css_cons : forall Γ Γ' s s' A,
      ctx_st_subtyp Γ Γ' ->
      st_subtyp s s' ->
      {{ Γ ⊢ A : Sort@s }} ->
      {{ Γ' ⊢ A : Sort@s }} ->
      ctx_st_subtyp {{{ Γ, A@s }}} {{{ Γ', A@s' }}}
  .

  #[local]
   Hint Constructors ctx_st_subtyp : mcpts.
  
  Lemma ctx_st_subtyp_implies_wf_ctx {P} : forall {Γ Γ' : ctx P},
      ctx_st_subtyp Γ Γ' ->
      {{ ⊢ Γ }} /\ {{ ⊢ Γ' }}.
  Proof.
    induction 1; split; destruct_conjs; mauto 2.
    assert {{ Γ' ⊢ Sort@s ⊆ Sort@s' }} by mauto 2.
    mauto 3.
  Qed.


  #[local]
    Ltac gen_ctx_st_subtyp_presup H :=
    match type of H with
    | ctx_st_subtyp ?Γ ?Γ' =>
        let HΓ := fresh "HΓ" in
        let HΓ' := fresh "HΓ'" in
        pose proof ctx_st_subtyp_implies_wf_ctx H as [HΓ HΓ']
    | _ => idtac
    end.

  Ltac gen_ctx_st_subtyp_presups := match_by_head ctx_st_subtyp ltac:(fun H => gen_ctx_st_subtyp_presup H).    
  
  Lemma ctx_st_subtyp_exp {P} : forall {Γ : ctx P} {M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, ctx_st_subtyp Δ Γ -> {{ Δ ⊢ M : A }}.
  Proof.
    induction 1; intros;
      gen_ctx_st_subtyp_presups;
      mauto 3.
    - assert {{ Δ ⊢ A : Sort@s1 }} by mauto 2.
      assert (ctx_st_subtyp {{{ Δ, A@s1 }}} {{{ Γ, A@s1 }}}) by mauto 2.
      assert {{ Δ, A@s1 ⊢ B : Sort@s2 }} by mauto 2.
      mauto 2.

    - assert {{ Δ ⊢ A : Sort@s1 }} by mauto 2.
      assert (ctx_st_subtyp {{{ Δ, A@s1 }}} {{{ Γ, A@s1 }}}) by mauto 2.
      assert {{ Δ, A@s1 ⊢ B : Sort@s2 }} by mauto 2.
      assert {{ Δ, A@s1 ⊢ M : B }} by mauto 2.
      mauto 2.
      
    - admit.
    - admit.

    - 
      assert {{ Δ ⊢ ℕ : Sort@s }} by mauto 2.
      assert (ctx_st_subtyp {{{ Δ, ℕ@s }}} {{{ Γ, ℕ@s }}}) by mauto 3.
      assert {{ Δ, ℕ@s ⊢ A : Sort@s' }} by mauto 2.
      assert (ctx_st_subtyp {{{ Δ, ℕ@s, A@s' }}} {{{ Γ, ℕ@s, A@s' }}}) by mauto 3.

      assert {{ Δ ⊢ MZ : A[Id,,zero] }} by mauto 2.
      assert {{ Δ ⊢ M : ℕ }} by mauto 2.
      assert {{ Δ, ℕ@s, A@s' ⊢ MS : A[Wk∘Wk,,succ #1] }} by mauto 2.
      mauto 2.

    - admit. (* need another lemma for well-formed substitution *)
      
    - admit. (* need another lemma for subtyping *)
  Admitted.
  
  Lemma ctx_st_subtyp_irrelevance {P} : forall {Γ Γ' : ctx P},
      ctx_st_subtyp Γ Γ' ->
      forall M A, {{ Γ' ⊢ M : A }} -> {{ Γ ⊢ M : A }}.
  Proof.
    induction 1; intros; mauto 2.
    
  
  Next Obligation.
    mautosolve 3.
  Qed.
  
  Next Obligation.
    simplify_nbe_order.
    assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
    assert {{ ⊢ Γ, ℕ@s }} by mauto 2.
    resolve_alg_sound.
    simpl in H4.
    assert {{ Γ, ℕ@s ⊢ A' }} by mauto 2.
    assert {{ Γ ⊢ M' : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢s Id,,M' : Γ, ℕ@s }} by mauto 2.
    mauto 3.
  Qed.
                
  Final Obligation.
    split; [mautosolve 3|].
    assert {{ Γ ⊢ ℕ : Sort@s }} by mauto 2.
    assert {{ ⊢ Γ, ℕ@s }} by mauto 2.
    resolve_alg_sound.
    simpl in H4.
    assert {{ Γ ⊢ M' : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢s Id,,M' : Γ, ℕ@s }} by mauto 2.
    assert {{ Γ ⊢ A'[Id,,M'] }} by mauto 3.
    assert {{ Γ ⊢ A'[Id,,M'] ≈ A'' }} by mauto 2 using soundness_ty'.
    assert (user_exp P A'') by trivial using user_exp_nf.  
    eapply alg_aty_complete; mauto 3.
  Qed.

  Extraction Inline type_check_functional type_infer_functional.

  Lemma type_infer_order_soundness : forall Γ M A,
      {{ Γ ⊢a M ⟹ A }} ->
      type_infer_order M
  with type_check_order_soundness : forall Γ M A,
      {{ Γ ⊢a M ⟸ A }} ->
      type_check_order M.
  Proof.
    - clear type_infer_order_soundness.
      induction 1; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
    - clear type_check_order_soundness.
      induction 1; mauto 3.
  Qed.
End type_check.

#[local]
Hint Resolve type_check_order_soundness type_infer_order_soundness : mcpts.

Lemma type_check_complete' : forall Γ M A (HA : exists i, {{ Γ ⊢ A : Sort@i }}),
    {{ Γ ⊢a M ⟸ A }} ->
    exists H H', type_check Γ A HA M H = left H'.
Proof.
  intros ? ? ? [] ?.
  assert (Horder : type_check_order M) by mauto.
  exists Horder.
  dec_complete.
Qed.

Lemma type_infer_complete : forall Γ M A (HΓ : {{ ⊢ Γ }}),
    {{ Γ ⊢a M ⟹ A }} ->
    exists H H', type_infer Γ HΓ M H = inleft (exist _ A H').
Proof.
  intros.
  assert (Horder : type_infer_order M) by mauto.
  exists Horder.
  destruct (type_infer Γ HΓ M Horder) as [[? []] |].
  - functional_alg_type_infer_rewrite_clear.
    eexists; reflexivity.
  - contradict H; intuition.
Qed.

Section type_check_closed.
  #[local]
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    mauto 3 using user_exp_to_type_infer_order, type_check_order, type_infer_order.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_check_closed A (HA : user_exp A) M (HM : user_exp M) : { {{ ⋅ ⊢ M : A }} } + { ~ {{ ⋅ ⊢ M : A }} } :=
  | A, HA, M, HM =>
      let*o->b (exist _ UA _) := type_infer {{{ ⋅ }}} _ A _ while _ in
      let*o->b (exist _ i _) :=  get_level_of_type_nf UA while _ in
      let*b _ := type_check {{{ ⋅ }}} A _ M _ while _ in
      pureb _
  .
  Next Obligation. (* False *)
    assert {{ ⊢ ⋅ }} by mauto 2.
    assert (exists i, {{ ⋅ ⊢ A : Sort@i }}) as [i] by (gen_presups; eauto 2).
    assert (exists j, {{ ⋅ ⊢a A ⟹ Sort@j }} /\ j <= i) as [j []] by mauto 3.
    firstorder.
  Qed.
  Next Obligation. (* False *)
    assert (exists i, {{ ⋅ ⊢ A : Sort@i }}) as [i] by (gen_presups; eauto 2).
    assert (exists j, {{ ⋅ ⊢a A ⟹ Sort@j }} /\ j <= i) as [j []] by mauto 3.
    functional_alg_type_infer_rewrite_clear.
    intuition.
  Qed.
  Next Obligation. (* exists i, {{ ⋅ ⊢ A : Sort@i }} *)
    assert {{ ⊢ ⋅ }} by mauto 2.
    assert {{ ⋅ ⊢ A : ^n{{{ Sort@i }}} }} by mauto 2 using alg_type_infer_sound.
    simpl in *.
    firstorder.
  Qed.
  Next Obligation. (* {{ ⋅ ⊢ M : A }} *)
    assert {{ ⊢ ⋅ }} by mauto 2.
    assert {{ ⋅ ⊢ A : ^n{{{ Sort@i }}} }} by mauto 3 using alg_type_infer_sound.
    simpl in *.
    mauto 3 using alg_type_check_sound.
  Qed.
End type_check_closed.

Lemma type_check_closed_complete : forall A (HA : user_exp A) M (HM : user_exp M),
    {{ ⋅ ⊢ M : A }} ->
    exists H', type_check_closed A HA M HM = left H'.
Proof. intros; dec_complete. Qed.
