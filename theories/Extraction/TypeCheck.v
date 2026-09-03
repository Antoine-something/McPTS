From Stdlib Require Import Morphisms_Relations.
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
    | H: {{ ⊢ ^_, ^_ }} |- _ => inversion_clear H
    | H: {{ # _ : ^_ ∈ ⋅ }} |- _ => inversion_clear H
    | H: {{ # (S _) : ^_ ∈ ^_, ^_ }} |- _ => inversion_clear H
    end.

  #[local]
  Ltac impl_obl_tac :=
    intros;
    repeat impl_obl_tac1;
    intuition (mauto 4).

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations lookup {P} (dec_P : DecidableSig P) (Γ : ctx P) (HΓ : {{ ⊢ Γ }}) x : { A | {{ #x : A ∈ Γ }} } + { forall A, ~ {{ #x : A ∈ Γ }} } :=
  | dec_P, {{{ Γ, A }}}, HΓ, x with x => {
    | 0 => pureo (exist _ {{{ A[Wk] }}} _)
    | S x' => 
        let*o (exist _ B _) := lookup dec_P Γ _ x' while _ in
        pureo (exist _ {{{ B[Wk] }}} _)
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
  | ti_natrec : forall {A MZ MS M}, type_check_order M -> type_aty_order A -> type_check_order MZ -> type_check_order MS -> type_infer_order {{{ rec M return A | zero -> MZ | succ -> MS end }}}
  | ti_pi : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {A B}, type_check_order A -> type_check_order B -> type_infer_order {{{ Π r A B }}}
  | ti_fn : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {A B M}, type_check_order A -> type_check_order B -> type_check_order M -> type_infer_order {{{ λ r A B M }}}
  | ti_app : forall {M N}, type_infer_order M -> type_check_order N -> type_infer_order {{{ M N }}}
  | ti_vlookup : forall {x}, type_infer_order {{{ #x }}}
  with type_aty_order {P} : typ P -> Prop :=
  | aty_st : forall {s}, type_aty_order {{{ Sort@s }}}
  | aty_sted : forall {A}, type_infer_order A -> type_aty_order A
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
    econstructor; eassumption.
  Qed.

  #[local]
  Ltac clear_defs :=
    do 3 lazymatch goal with
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
      | H: (let H := fixproto in
            forall (P : PtsSig), DecidableSig P -> PredicativeSig P -> FunctionalSig P -> 
            forall Γ : ?ctx,
              {{ ⊢ Γ }} ->
              forall A : ?expA,
                type_aty_order A ->
                { {{ Γ ⊢aty A }} } + { ~ {{ Γ ⊢aty A }} })
        |- _ =>
          clear H
      | H: (forall (Γ : ?ctx),
               {{ ⊢ Γ }} ->
               forall A : ?expA,
                 type_aty_order A ->
                 ({ {{ Γ ⊢aty A }} } + { ~ {{ Γ ⊢aty A }} }))
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
  with type_aty {P : PtsSig} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) (Γ : ctx P) (HΓ : {{ ⊢ Γ }}) A (H : type_aty_order A) : { {{ Γ ⊢aty A }} } + { ~ {{ Γ ⊢aty A }} } by struct H :=
  | dec_P, pred_P, func_P, Γ, HΓ, A, H with A => {
    | {{{ Sort@s }}} => pureb _
    | A' =>
        let*o->b (exist _ UA _) := type_infer dec_P pred_P func_P Γ _ A' _ while _ in
        let*o->b (exist _ s _) :=  get_level_of_sort_nf dec_P UA while _ in
        pureb _
    }
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
        let*b->o _ := type_aty dec_P pred_P func_P {{{ Γ, ℕ }}} _ A' _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ A'[Id,,zero] }}} _ MZ _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, ℕ, A' }}} {{{ A'[Wk∘Wk,,succ #1] }}} _ MS _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ ℕ }}} _ M' _ while _ in
        let (A'', _) := nbe_ty_impl Γ {{{ A'[Id,,M'] }}} _ in
        pureo (exist _ A'' _)
    | {{{ Π r B C }}} =>
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ Sort@s1 }}} _ B _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, B }}} {{{ Sort@s2 }}} _ C _ while _ in
        pureo (exist _ n{{{ Sort@s3 }}} _)
    | {{{ λ r A' B' M' }}} =>
        let*b->o _ := type_check dec_P pred_P func_P Γ {{{ Sort@s4 }}} _ A' _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, A' }}} {{{ Sort@s5 }}} _ B' _ while _ in
        let*b->o _ := type_check dec_P pred_P func_P {{{ Γ, A' }}} B' _ M' _ while _ in
        let (A'', _) := nbe_impl Γ A' {{{ Sort@s4 }}} _ in
        let (B'', _) := nbe_impl {{{ Γ, A' }}} B' {{{ Sort@s5 }}} _ in
        pureo (exist _ n{{{ Π r A'' B'' }}} _)
    | {{{ M' N' }}} =>
        let*o (exist _ C _) := type_infer dec_P pred_P func_P Γ _ M' _ while _ in
        let*o (existT _ s1 (existT _ s2 (existT _ s3 (existT _ r (existT _ A (exist _ B _)))))) :=
          get_subterms_of_pi_nf dec_P C while _ in
        let*b->o _ := type_check dec_P pred_P func_P Γ (A : nf P) _ N' _ while _ in
        let (B', _) := nbe_ty_impl Γ {{{ ^(B : nf P)[Id,,N'] }}} _ in
        pureo (exist _ B' _)
    | {{{ #x }}} =>
        let*o (exist _ A _) := lookup dec_P Γ _ x while _ in
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
    | H: type_aty_order ?A |- type_infer_order ?A =>
        inversion_clear H; eassumption
    | |- type_infer_order _ => invert_type_check_infer_order; eassumption
    | |- type_check_order _ => invert_type_check_infer_order; eassumption
    | |- type_aty_order _ => invert_type_check_infer_order; eassumption
      end.

  #[local]
  Ltac impl_wf_context_obl_tac :=
    lazymatch goal with
      | |- {{ ⊢ ^?Γ, ^?A }} =>
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
          solve [intuition]
    end.

  #[local]
  Ltac impl_ill_typed_obl_tac' :=
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

  Ltac impl_aty_type_check :=
      match goal with
      | H1 : {{ ^?Γ ⊢a ^?M ⟹ ^?B }},
          H2 : {{ ^?Γ ⊢a ^(nf_to_exp ?B) ⊆ ^?A }} |- {{ Γ ⊢a M ⟸ A }} =>
          eapply atc_conv; eauto
      end.

   Ltac impl_aty_constructor :=
      match goal with
      | _ : _ |- {{ ^?Γ ⊢aty ^?A }} => solve [econstructor; eauto]
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
       | impl_aty_constructor
       | impl_aty_type_check
       | idtac
       ]
    ).

  Next Obligation.
    mautosolve 3.
  Qed.
  Next Obligation.
    assert {{ Γ ⊢ Sort@s1 }} by mauto 2.
    resolve_alg_sound.
    assert {{ ⊢ Γ, B }} by mauto 3.
    mautosolve 2.
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
    mauto 4.
  Qed.

  Next Obligation.
    intros Hf.
    inversion Hf; subst.
    intuition.
  Qed.

  Next Obligation.
    assert {{ Γ ⊢ A' : Sort@s4 }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, A' }} by mauto 3.
    assert {{ Γ, A' ⊢ B' : Sort@s5 }} by mauto 3 using alg_type_check_sound.
    mauto 2.
  Qed.

  Next Obligation.
    simplify_nbe_order.
    mauto 3 using alg_type_check_sound.
  Qed.

  Next Obligation.
    simplify_nbe_order.
    assert {{ Γ ⊢ A' : Sort@s4 }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, A' }} by mauto 3.
    mauto 3 using alg_type_check_sound.
  Qed.

  Next Obligation.
    split; [mautosolve 3|].
    assert (user_exp P A'') by trivial using user_exp_nf.
    assert (user_exp P B'') by trivial using user_exp_nf.    
    enough {{ Γ ⊢ Π r A'' B'' : Sort@s6 }}; [eapply alg_aty_complete; mauto 2|].
    assert {{ Γ ⊢ A' : Sort@s4 }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ, A' ⊢ B' : Sort@s5 }} by (eapply alg_type_check_sound; mauto 4).

    assert {{ Γ ⊢ A' ≈ A'' : Sort@s4 }} by mauto 2 using soundness'.
    assert {{ Γ, A' ⊢ B' ≈ B'' : Sort@s5 }} by mauto 2 using soundness'.
    gen_presups.
    assert {{ ⊢ Γ, A' ≈ Γ, ^(nf_to_exp A'') }} by mauto 4.
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
    intros Hf.
    inversion Hf; subst.
    functional_alg_type_infer_rewrite_clear.
    inversion H3; subst.
    intuition.
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
    assert {{ Γ ⊢s Id,,N' : Γ, ^(nf_to_exp A) }} by mauto 4.
    mauto 3.
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
    assert {{ Γ, ^(nf_to_exp A) ⊢ B }} by (gen_presups; mauto 2).
    assert {{ Γ ⊢ N' : A }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢s Id,,N' : Γ, ^(nf_to_exp A) }} by mauto .
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
    mautosolve 3.
  Qed.

  Next Obligation.
    assert {{ Γ ⊢ ℕ }} by mauto 3.
    mauto 3.
  Qed.

  Next Obligation.
    assert {{ Γ ⊢ ℕ }} by mauto 3.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    resolve_alg_sound.
    assert {{ Γ ⊢s Id,,zero : Γ, ℕ }} by mauto 3.
    mauto 2.
  Qed.

  Next Obligation.
    assert {{ Γ ⊢ ℕ }} by mauto 3.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    resolve_alg_sound.
    assert {{ ⊢ Γ, ℕ, A' }} by mauto 2.
    assert {{ Γ, ℕ ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ, A' ⊢s Wk : Γ, ℕ }} by mauto 4.
    assert {{ Γ, ℕ, A' ⊢s Wk∘Wk : Γ }} by mauto 3.
    assert {{ Γ, ℕ, A' ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }} by mauto 4.
    mauto 2.
  Qed.

  Next Obligation.
    mautosolve 3.
  Qed.


  Next Obligation.
    simplify_nbe_order.
    assert {{ Γ ⊢ ℕ }} by mauto 3.
    assert {{ Γ ⊢ M' : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ ⊢ Γ, ℕ }} by mauto 3.
    resolve_alg_sound.
    assert {{ Γ ⊢s Id,,M' : Γ, ℕ }} by mauto 3.
    mauto 2.
  Qed.
    
  Final Obligation.
    split; [mautosolve 3|].
    assert {{ Γ ⊢ ℕ }} by mauto 3.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    resolve_alg_sound.
    assert {{ Γ ⊢ M' : ℕ }} by mauto 3 using alg_type_check_sound.
    assert {{ Γ ⊢s Id,,M' : Γ, ℕ }} by mauto 2.
    assert {{ Γ ⊢ A'[Id,,M'] }} by mauto 3.
    assert {{ Γ ⊢ A'[Id,,M'] ≈ A'' }} by mauto 2 using soundness_ty'.
    assert (user_exp P A'') by trivial using user_exp_nf.  
    eapply alg_aty_complete; mauto 3.
  Qed.

  Extraction Inline type_check_functional type_infer_functional.

  Lemma type_infer_order_soundness {P} : forall {Γ : ctx P} M A,
      {{ Γ ⊢a M ⟹ A }} ->
      type_infer_order M
  with type_check_order_soundness {P} : forall {Γ : ctx P} M A,
      {{ Γ ⊢a M ⟸ A }} ->
      type_check_order M
  with type_aty_order_soundness {P} : forall {Γ : ctx P} A,
      {{ Γ ⊢aty A }} ->
      type_aty_order A.
  Proof.
    - clear type_infer_order_soundness.
      induction 1; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
    - clear type_check_order_soundness.
      induction 1; mauto 3.
    - clear type_aty_order_soundness.
      induction 1; mauto 3.
      + econstructor; mauto 3.
      + econstructor; mauto 3.
  Qed.
End type_check.

#[local]
Hint Resolve type_check_order_soundness type_infer_order_soundness type_aty_order_soundness : mcpts.

Lemma type_check_complete' {P} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) : forall {Γ : ctx P} M A (HA : {{ Γ ⊢ A }}),
    {{ Γ ⊢a M ⟸ A }} ->
    exists H H', type_check dec_P pred_P func_P Γ A HA M H = left H'.
Proof.
  intros.
  assert (Horder : type_check_order M) by mauto.
  exists Horder.
  dec_complete.
Qed.

Lemma type_infer_complete {P} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) : forall Γ M A (HΓ : {{ ⊢ Γ }}),
    {{ Γ ⊢a M ⟹ A }} ->
    exists H H', type_infer dec_P pred_P func_P Γ HΓ M H = inleft (exist _ A H').
Proof.
  intros.
  assert (Horder : type_infer_order M) by mauto.
  exists Horder.
  destruct (type_infer dec_P pred_P func_P Γ HΓ M Horder) as [[? []] |].
  - functional_alg_type_infer_rewrite_clear.
    eexists; reflexivity.
  - contradict H; intuition.
Qed.

Lemma type_aty_complete {P} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) : forall {Γ : ctx P} A (HΓ : {{ ⊢ Γ }}),
    {{ Γ ⊢aty A }} ->
    exists H H', type_aty dec_P pred_P func_P Γ HΓ A H = left H'.
Proof.
  intros.
  assert (Horder : type_aty_order A) by mauto.
  exists Horder.
  dec_complete.
Qed.

Section type_check_closed.
  #[local]
  Ltac impl_obl_tac :=
    unfold not in *;
    intros;
    mauto 3 using user_exp_to_type_infer_order, type_check_order, type_infer_order, type_aty_order.

  #[tactic="impl_obl_tac",derive(equations=no,eliminator=no)]
  Equations type_check_closed {P : PtsSig} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) A (HA : user_exp P A) M (HM : user_exp P M) : { {{ ⋅ ⊢ M : A }} } + { ~ {{ ⋅ ⊢ M : A }} } :=
  | dec_P, pred_P, func_P, A, HA, M, HM =>
      let*b _ := type_aty dec_P pred_P func_P {{{ ⋅ }}} _ A _ while _ in
      let*b _ := type_check dec_P pred_P func_P {{{ ⋅ }}} A _ M _ while _ in
      pureb _
  .
  Next Obligation.
    pose proof (@wf_ctx_empty P).
    assert {{ ⋅ ⊢ A }} by (gen_presups; eauto 2).
    assert {{ ⋅ ⊢aty A }} by mauto 2 using alg_aty_sound.
    firstorder.
  Qed.
  Next Obligation.
    pose proof (@wf_ctx_empty P).
    eapply alg_aty_sound; mauto 2.
  Qed.
  Next Obligation.
    pose proof (@wf_ctx_empty P).
    eapply alg_type_check_sound; mauto 2.
    eapply alg_aty_sound; mauto 2.
  Qed.
End type_check_closed.

Lemma type_check_closed_complete {P : PtsSig} (dec_P : DecidableSig P) (pred_P : PredicativeSig P) (func_P : FunctionalSig P) : forall A (HA : user_exp P A) M (HM : user_exp P M),
    {{ ⋅ ⊢ M : A }} ->
    exists H', type_check_closed dec_P pred_P func_P A HA M HM = left H'.
Proof. intros; dec_complete. Qed.
