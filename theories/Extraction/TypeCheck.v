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
  | ti_pi : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {A B}, type_infer_order A -> type_infer_order B -> type_infer_order {{{ Π r A B }}}
  | ti_fn : forall {s1 s2 s3} {r : Ru_pi P s1 s2 s3} {A B M}, type_infer_order A -> type_infer_order M -> type_infer_order {{{ λ r A B M }}}
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
  Ltac clear_defs P :=
    do 2 lazymatch goal with
      | H: (forall (Γ : ctx P) (A : typ P),
               (exists s : P, {{ Γ ⊢ A : Sort@s }}) ->
               forall M : typ P,
                 type_check_order M ->
                 ({ {{ Γ ⊢a M ⟸ A }} } + { ~ {{ Γ ⊢a M ⟸ A }} }))
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall (Γ : ctx P) (A : typ P),
              (exists s : P, {{ Γ ⊢ A : Sort @ s }}) -> forall M : typ P, type_check_order M -> { {{ Γ ⊢a M ⟸ A }} } + { ~ {{ Γ ⊢a M ⟸ A }} })
        |- _ =>
          clear H
      | H: (let H := fixproto in
            forall Γ : ctx P,
              {{ ⊢ Γ }} ->
              forall M : typ P,
                type_infer_order M ->
                ({ B : nf P | {{ Γ ⊢a M ⟹ B }} /\ {{ Γ ⊢aty ^(nf_to_exp B) }} } + { forall C : nf P, ~ {{ Γ ⊢a M ⟹ C }} }))
        |- _ =>
          clear H
      | H: (forall Γ : ctx P,
               {{ ⊢ Γ }} ->
               forall M : typ P,
                 type_infer_order M ->
                 ({ B : nf P | {{ Γ ⊢a M ⟹ B }} /\{{ Γ ⊢aty ^(nf_to_exp B) }} } + { forall C : nf P, ~ {{ Γ ⊢a M ⟹ C }} }))
        |- _ =>
          clear H
    end.

  #[local]
  Ltac clear_redundant_pat :=
    repeat match goal with
      | H: { A | {{ ^?Γ ⊢a ^?M ⟹ A }} /\ (exists s, {{ ^?Γ ⊢a ^(nf_to_exp A) ⟹ Sort@s }}) }
          , H1: {{ ^?Γ ⊢a ^?M ⟹ ^?B }} /\ (exists s, {{ ^?Γ ⊢a ^(nf_to_exp ?B) ⟹ Sort@s }}) |- _ => clear H
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
  Equations type_check {P : PtsSig} (dec_P : DecidableSig P) (Γ : ctx P) A (HA : (exists i, {{ Γ ⊢ A : Sort@i }})) M (H : type_check_order M) : { {{ Γ ⊢a M ⟸ A }} } + { ~ {{ Γ ⊢a M ⟸ A }} } by struct H :=
  | dec_P, Γ, A, HA, M, H =>
      let*o->b (exist _ B _) := type_infer dec_P Γ _ M _ while _ in
      let*b _ := subtyping_impl dec_P Γ (B : nf P) A _ while _ in
      pureb _
  with type_infer {P : PtsSig} (dec_P : DecidableSig P) (Γ : ctx P) (HΓ : {{ ⊢ Γ }}) M (H : type_infer_order M) : { A : nf P | {{ Γ ⊢a M ⟹ A }} /\ {{ Γ ⊢aty A }} } + { forall A, ~ {{ Γ ⊢a M ⟹ A }} } by struct H :=
  | dec_P, Γ, HΓ, M, H with M => {
    | {{{ Sort@s }}} =>
        (* pureo (exist _ n{{{ Sort@(S s) }}} _) *)
        _ 
    | {{{ ℕ }}} =>
        pureo (exist _ n{{{ Sort@0 }}} _)
    | {{{ zero }}} =>
        pureo (exist _ n{{{ ℕ }}} _)
    | {{{ succ M' }}} =>
        let*b->o _ := type_check Γ {{{ ℕ }}} _ M' _ while _ in
        pureo (exist _ n{{{ ℕ }}} _)
    | {{{ rec M' return A' | zero -> MZ | succ -> MS end }}} =>
        let*b->o _ := type_check Γ {{{ ℕ }}} _ M' _ while _ in
        let*o (exist _ UA' _) := type_infer {{{ Γ, ℕ@s }}} _ A' _ while _ in
        let*o (exist _ s' _) :=  get_level_of_sort_nf UA' while _ in
        let*b->o _ := type_check Γ {{{ A'[Id,,zero] }}} _ MZ _ while _ in
        let*b->o _ := type_check {{{ Γ, ℕ@s, A'@s' }}} {{{ A'[Wk∘Wk,,succ #1] }}} _ MS _ while _ in
        let (A'', _) := nbe_ty_impl Γ {{{ A'[Id,,M'] }}} _ in
        pureo (exist _ A'' _)
    | {{{ Π r B C }}} =>
        let*o (exist _ UB _) := type_infer dec_P Γ _ B _ while _ in
        let*o (exist _ s _) :=  get_level_of_sort_nf dec_P UB while _ in
        let*o (exist _ UC _) := type_infer dec_P {{{ Γ, B@s }}} _ C _ while _ in
        let*o (exist _ j _) :=  get_level_of_sort_nf dec_P UC while _ in
        (* pureo (exist _ n{{{ Sort@(max i j) }}} _) *)
        _
    | {{{ λ r A' B' M' }}} =>
        let*o (exist _ UA' _) := type_infer dec_P Γ _ A' _ while _ in
        let*o (exist _ s _) :=  get_level_of_sort_nf dec_P UA' while _ in
        let*o (exist _ B' _) := type_infer dec_P  {{{ Γ, A'@s }}} _ M' _ while _ in
        let (A'', _) := nbe_ty_impl Γ A' _ in
        pureo (exist _ n{{{ Π r A'' B' }}} _)
    | {{{ M' N' }}} =>
        let*o (exist _ C _) := type_infer dec_P Γ _ M' _ while _ in
        let*o (existT _ s1 (existT _ s2 (existT _ s3 (existT _ r (existT _ A (exist _ B _)))))) :=
          get_subterms_of_pi_nf dec_P C while _ in
        let*b->o _ := type_check dec_P Γ (A : nf P) _ N' _ while _ in
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
          solve [firstorder | congruence]
      end.

  #[local]
  Ltac resolve_alg_sound :=
    repeat match goal with
      | H: {{ ^?Γ ⊢a ^?M ⟹ ^?A }} |- _ => assert {{ Γ ⊢ M : A }} by eauto 2 using alg_type_infer_sound; fail_if_dup
      | H: {{ ^?Γ ⊢a ^?M ⟸ ^?A }} |- _ => assert {{ Γ ⊢ M : A }} by eauto 2 using alg_type_check_sound; fail_if_dup
      end.

  #[local]
  Ltac simplify_nbe_order :=
    lazymatch goal with
    | |- nbe_ty_order ?Γ ?A => enough (exists i, {{ Γ ⊢ A : ^(nf_to_exp (nf_typ i)) }}) as [? [? []]%soundness_ty] by eauto 3 using nbe_ty_order_sound
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
            unshelve (eexists; solve [eauto 2]);
            solve [constructor]
        | |- nbe_order ?Γ ?M ?A =>
            simplify_nbe_order;
            solve [eauto 2]
        end
    end.

  #[local]
  Ltac impl_exist_lvl_wf_exp_obl_tac :=
    match goal with
    | |- exists i, {{ ^?Γ ⊢ ^?A : Sort@i }} => enough (exists i, {{ Γ ⊢ A : ^(nf_to_exp (nf_typ i)) }}) by eauto 2
    | |- exists i, {{ ^?Γ ⊢ ^?A : ^(nf_to_exp (nf_typ i)) }} => idtac
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

  Next Obligation. (* exists j, {{ Γ ⊢ A'[Id,,zero] : Sort@j }} *)
    eexists.
    assert {{ ⊢ Γ, ℕ }} by mauto 3.
    resolve_alg_sound.
    mauto 3.
  Qed.

  Next Obligation. (* exists j, {{ Γ, ℕ, A' ⊢ A'[Wk∘Wk,,succ #1] : Sort@i }} *)
    eexists.
    assert {{ ⊢ Γ, ℕ }} by mauto 3.
    resolve_alg_sound.
    mauto 3.
  Qed.

  Next Obligation. (* nbe_ty_order Γ {{{ A'[Id,,M'] }}} *)
    simplify_nbe_order.
    eexists.
    assert {{ Γ ⊢ ℕ : Sort@0 }} by mauto 2.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    resolve_alg_sound.
    mauto 3.
  Qed.

  Next Obligation. (* {{ Γ ⊢a rec M' return A' | zero -> MZ | succ -> MS end ⟹ A'' }} /\ (exists j, {{ Γ ⊢a A'' ⟹ Sort@j }}) *)
    split; [mautosolve 3 |].
    assert {{ Γ ⊢ ℕ : Sort@0 }} by mauto 2.
    assert {{ ⊢ Γ, ℕ }} by mauto 2.
    resolve_alg_sound.
    assert {{ Γ ⊢ A'[Id,,M'] : Sort@i }} by mauto 3.
    assert {{ Γ ⊢ A'[Id,,M'] ≈ A'' : Sort@i }} by eauto 2 using soundness_ty'.
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, {{ Γ ⊢a A'' ⟹ Sort@j }} /\ j <= i) as [? []] by (gen_presups; mauto 3).
    eexists; eauto 2.
  Qed.

  Next Obligation. (* {{ Γ ⊢a λ A' M' ⟹ Π A'' B' }} /\ (exists j, {{ Γ ⊢a Π A'' B' ⟹ Sort@j }}) *)
    split; [mautosolve 3 |].
    resolve_alg_sound.
    assert {{ ⊢ Γ, A' }} by mauto 2.
    assert {{ Γ ⊢ A' ≈ A'' : Sort@i }} by eauto 2 using soundness_ty'.
    assert {{ Γ ⊢ A'' : Sort@i }} by (gen_presups; mauto 2).
    assert {{ ⊢ Γ, ^(A'' : exp) }} by mauto 2.
    resolve_alg_sound.
    assert {{ ⊢ Γ, A' ≈ Γ, ^(A'' : exp) }} by mauto 3.
    eassert {{ Γ, ^(A'' : exp) ⊢ B' : Sort@_ }} by mauto 2.
    assert (user_exp A'') by trivial using user_exp_nf.
    assert (exists j, {{ Γ ⊢a A'' ⟹ Sort@j }} /\ j <= i) as [? []] by (gen_presups; mauto 2).
    assert (user_exp B') by trivial using user_exp_nf.
    eassert (exists k, {{ Γ, ^(A'' : exp) ⊢a B' ⟹ Sort@k }} /\ k <= H1) as [? []] by (gen_presups; mauto 2).
    eexists; mauto 2.
  Qed.

  Next Obligation. (* nbe_ty_order Γ {{{ B[Id,,N'] }}} *)
    simplify_nbe_order.
    progressive_inversion.
    resolve_alg_sound.
    assert {{ ⊢ Γ, ^(A : exp) }} by mauto 2.
    resolve_alg_sound.
    eexists; mauto 3.
  Qed.

  Next Obligation. (* {{ Γ ⊢a M' N' ⟹ B' }} /\ (exists i, {{ Γ ⊢a B' ⟹ Sort@i }}) *)
    progressive_inversion.
    split; [mautosolve 3 |].
    resolve_alg_sound.
    assert {{ ⊢ Γ, ^(A : exp) }} by mauto 2.
    resolve_alg_sound.
    assert {{ Γ ⊢s Id,,N' : Γ, ^(A : exp) }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,N'] : ^n{{{ Sort@j }}} }} by mauto 2.
    assert {{ Γ ⊢ B[Id,,N'] ≈ B' : Sort@j }} by mauto 2 using soundness_ty'.
    assert (user_exp B') by trivial using user_exp_nf.
    assert (exists k, {{ Γ ⊢a B' ⟹ Sort@k }} /\ k <= j) as [? []] by (gen_presups; mauto 2).
    eexists; eauto 2.
  Qed.

  Next Obligation. (* exists i : nat, {{ Γ ⊢ B'[Id,,M1'] : Sort@i }} *)
    progressive_inversion.
    resolve_alg_sound.
    assert {{ ⊢ Γ, A' }} by mauto 2.
    resolve_alg_sound.
    eexists; mauto 2.
    eapply wf_conv'; [eapply wf_exp_sub |]; mauto 3.
  Qed.

  Next Obligation. (* nbe_ty_order {{{ Γ, A' }}} B' *)
    progressive_inversion.
    resolve_alg_sound.
    simplify_nbe_order.
    assert {{ ⊢ Γ, A' }} by mauto 2.
    resolve_alg_sound.
    eauto.
  Qed.

  Next Obligation. (* {{ Γ ⊢a ⟨ M1' : A'; M2' : B' ⟩ ⟹ Σ A'' B'' }} /\ (exists i0 : nat, {{ Γ ⊢a Σ A'' B'' ⟹ Sort@i0 }}) *)
    progressive_inversion.
    split; [mautosolve 3 |].
    resolve_alg_sound.
    assert {{ ⊢ Γ, A' }} by mauto 2.
    resolve_alg_sound.
    assert {{ Γ ⊢ A' ≈ A'' : Sort@i }} by mauto 2 using soundness_ty'.
    assert {{ Γ ⊢ A'' : Sort@i }} by (gen_presups; mauto 2).
    assert {{ Γ , A' ⊢ B' ≈ B'' : Sort@j }} by mauto 2 using soundness_ty'.
    assert {{ Γ , A' ⊢ B'' : Sort@j }} by (gen_presups; mauto 2).
    assert {{ Γ , ^(A'':typ) ⊢ B'' : Sort@j }} by (eapply @ctxeq_exp with (Γ:={{{Γ, A'}}}); mauto 3).
    assert {{ Γ ⊢ Σ A'' B'' : Sort@(max i j) }} by mauto 2.
    assert (user_exp n{{{ Σ A'' B'' }}}) by trivial using user_exp_nf.
    eapply alg_type_infer_typ_complete in H57; mauto 3.
    destruct_all. mauto 3.
  Qed.

  Next Obligation. (* {{ Γ ⊢a fst M' ⟹ A' }} /\ (exists i : nat, {{ Γ ⊢a A' ⟹ Sort@i }}) *)
    progressive_inversion.
    split; [mautosolve 3 |].
    resolve_alg_sound.
    assert (user_exp A') by trivial using user_exp_nf.
    mauto.
  Qed.

  Next Obligation. (* nbe_ty_order Γ {{{ B[Id,,fst M'] }}} *)
    progressive_inversion.
    resolve_alg_sound.
    simplify_nbe_order.
    assert {{ Γ ⊢ fst M' : A' }} by mauto 2.
    assert {{ ⊢ Γ, ^(A':typ) }} by mauto 2.
    resolve_alg_sound.
    eexists.
    eapply wf_conv'; [eapply wf_exp_sub |]; mauto 3.
  Qed.

  Next Obligation.   (* {{ Γ ⊢a snd M' ⟹ B' }} /\ (exists i : nat, {{ Γ ⊢a B' ⟹ Sort@i0 }}) *)
    progressive_inversion.
    split; [mautosolve 3 |].
    resolve_alg_sound.
    mauto.
    assert {{ Γ ⊢ fst M' : A' }} by mauto 2.
    assert {{ ⊢ Γ, ^(A':typ) }} by mauto 2.
    apply wf_sigma_inversion' in H12.
    destruct_all.
    assert {{ Γ ⊢ B[Id,,fst M'] ≈ B' : Sort@(max i j) }} by (eapply soundness_ty'; mauto 3).
    gen_presups.
    assert (user_exp B') by trivial using user_exp_nf.
    eapply alg_type_infer_typ_complete in H18; mauto 3.
    destruct_all. mauto 3.
  Qed.

  Next Obligation. (* {{ Γ ⊢a refl A' M' ⟹ Eq A'' M'' M'' }} /\ (exists i0 : nat, {{ Γ ⊢a Eq A'' M'' M'' ⟹ Sort@i0 }}) *)
    split; [mautosolve 3 |].
    resolve_alg_sound.
    assert {{ Γ ⊢ A' ≈ A'' : Sort@i }} by eauto 2 using soundness_ty'.
    assert {{ Γ ⊢ A' ≈ A'' : Sort@i }} by eauto 2 using soundness_ty'.
    assert {{ Γ ⊢ M' ≈ M'' : A' }} by eauto 2 using soundness'.
    assert {{ Γ ⊢ M' ≈ M'' : A'' }} by mauto 2.
    assert {{ Γ ⊢ Eq A'' M'' M'' : Sort@i }} by (gen_presups; mauto 2).
    assert (user_exp n{{{ Eq A'' M'' M'' }}}) by trivial using user_exp_nf.
    assert (exists k, {{ Γ ⊢a Eq A'' M'' M'' ⟹ Sort@k }} /\ k <= i) as [? []] by (gen_presups; mauto 2).
    eexists; eauto 2.
  Qed.

  Next Obligation. (* {{ ⊢ Γ, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }} *)
    resolve_alg_sound.
    assert {{ Γ, A' ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A' ⊢ A'[Wk] : Sort@i }} by mauto 2.
    assert {{ ⊢ Γ, A', A'[Wk] }} by mauto 3.
    assert {{ Γ, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Sort@i }} by mauto 2.
    mauto 2.
  Qed.

  Next Obligation. (* exists i0 : nat, {{ Γ, A' ⊢ B'[Id,,#0,,refl A'[Wk] #0] : Sort@i0 }} *)
    functional_alg_type_infer_rewrite_clear.
    resolve_alg_sound.
    assert {{ Γ, A' ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A' ⊢ A'[Wk] : Sort@i }} by mauto 2.
    assert {{ ⊢ Γ, A', A'[Wk] }} by mauto 3.
    assert {{ Γ, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Sort@i }} by mauto 2.
    assert {{ Γ, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 ⊢ B' : ^n{{{ Sort@j }}} }} by mauto 3 using alg_type_infer_sound.
    pose proof (@glu_rel_eq_eqrec_synprop_gen_A Γ {{{ Id }}} _ _ A' ltac:(mauto 2) ltac:(eassumption)).
    destruct_all.
    assert {{ Γ, A' ⊢ B'[Id,,#0,,refl A'[Wk] #0] : Sort@j }} by mauto 2.
    eauto.
  Qed.

  Next Obligation. (* nbe_ty_order Γ {{{ B'[Id,,M1',,M2',,N'] }}} *)
    simplify_nbe_order.
    resolve_alg_sound.
    assert {{ Γ ⊢ Eq A' M1' M2' : Sort@i }} by mauto 2.
    resolve_alg_sound.
    assert {{ Γ, A' ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A' ⊢ A'[Wk] : Sort@i }} by mauto 2.
    assert {{ ⊢ Γ, A', A'[Wk] }} by mauto 3.
    assert {{ Γ, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Sort@i }} by mauto 2.
    assert {{ Γ, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 ⊢ B' : ^n{{{ Sort@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢s Id,,M1',,M2',,N' : Γ, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }} by mauto 2.
    eexists; mauto 2.
  Qed.

  Next Obligation. (* {{ Γ ⊢a eqrec N' as Eq A' M1' M2' return B' | refl -> BR' end ⟹ B'' }} /\ (exists i0 : nat, {{ Γ ⊢a B'' ⟹ Sort@i0 }}) *)
    split; [mautosolve 3 |].
    resolve_alg_sound.
    assert {{ Γ ⊢ Eq A' M1' M2' : Sort@i }} by mauto 2.
    resolve_alg_sound.
    assert {{ Γ, A' ⊢s Wk : Γ }} by mauto 3.
    assert {{ Γ, A' ⊢ A'[Wk] : Sort@i }} by mauto 2.
    assert {{ ⊢ Γ, A', A'[Wk] }} by mauto 3.
    assert {{ Γ, A', A'[Wk] ⊢ Eq A'[Wk∘Wk] #1 #0 : Sort@i }} by mauto 2.
    assert {{ Γ, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 ⊢ B' : ^n{{{ Sort@j }}} }} by mauto 3 using alg_type_infer_sound.
    assert {{ Γ ⊢s Id,,M1',,M2',,N' : Γ, A', A'[Wk], Eq A'[Wk∘Wk] #1 #0 }} by mauto 2.
    assert {{ Γ ⊢ B'[Id,,M1',,M2',,N'] : Sort@j }} by mauto 2.
    assert {{ Γ ⊢ B'[Id,,M1',,M2',,N'] ≈ B'' : Sort@j }} by eauto 2 using soundness_ty'.
    assert (user_exp B'') by eauto 2 using user_exp_nf.
    assert (exists k, {{ Γ ⊢a B'' ⟹ Sort@k }} /\ k <= j) as [? []] by (gen_presups; mauto 2).
    eexists; eauto.
  Qed.

  Final Obligation. (* {{ Γ ⊢a #x ⟹ A' }} /\ (exists i, {{ Γ ⊢a A' ⟹ Sort@i }}) *)
    split; [mautosolve 3 |].
    assert (exists i, {{ Γ ⊢ A : Sort@i }}) as [i] by mauto 2.
    resolve_alg_sound.
    assert {{ Γ ⊢ A ≈ A' : Sort@i }} by eauto 2 using soundness_ty'.
    assert (user_exp A') by trivial using user_exp_nf.
    assert (exists j, {{ Γ ⊢a A' ⟹ Sort@j }} /\ j <= i) as [? []] by (gen_presups; mauto 2).
    eexists; eauto 2.
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
