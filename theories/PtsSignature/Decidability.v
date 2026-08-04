From Coq Require Import Program.Equality Logic.PropExtensionality.
From McPTS.PtsSignature Require Import Signatures Adjoint.


Record DecidableSig (P : PtsSig) : Type :=
  mkDecidableSig {
      dec_st_eq : forall (s s' : P), ( {s = s'} + {s <> s'} )%type;
      dec_ax_typ : forall (s : P), ( {s' & Ax_typ P s s'} + {forall s', ~Ax_typ P s s'} )%type;
      dec_st_sub : forall (s s' : P), ({st_subtyp s s'} + {~ st_subtyp s s'})%type;
      dec_ru_pi : forall (s1 s2 : P), ({s3 & Ru_pi P s1 s2 s3} + {forall s3, Ru_pi P s1 s2 s3 -> False})%type;
      dec_ru_pi_eq : forall (s1 s2 s3 : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1 s2 s3),
        ( { r = r'} + {r <> r'} )%type;
      dec_ru_nat : ({s & Ru_nat P s} + {forall s, Ru_nat P s -> False})%type;
    }.
Arguments dec_st_eq {_}.
Arguments dec_ax_typ {_}.
Arguments dec_st_sub {_}.
Arguments dec_ru_pi {_}.
Arguments dec_ru_pi_eq {_}.
Arguments dec_ru_nat {_}.


Section DecidableProperties.
  Context {P : PtsSig} (dec_P : DecidableSig P).

  Definition strong_ru_pi_eq (s1 s1' s2 s2' s3 s3' : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1' s2' s3') :=
      (s1 = s1') /\ (s2 = s2') /\ (s3 = s3') /\ (JMeq r r').
    
  Lemma strong_dec_pi : forall (s1 s1' s2 s2' s3 s3' : P) (r : Ru_pi P s1 s2 s3) (r' : Ru_pi P s1' s2' s3'),
      ({ strong_ru_pi_eq s1 s1' s2 s2' s3 s3' r r' } + {~ strong_ru_pi_eq s1 s1' s2 s2' s3 s3' r r'})%type.
    intros.
    unfold strong_ru_pi_eq.
    destruct (dec_st_eq dec_P s1 s1'); [| right; intuition].
    destruct (dec_st_eq dec_P s2 s2'); [| right; intuition].
    destruct (dec_st_eq dec_P s3 s3'); [| right; intuition].
    subst.
    destruct (dec_ru_pi_eq dec_P s1' s2' s3' r r').
    - left.
      repeat split.
      subst.
      reflexivity.
    - right.
      intros [? [? []]].
      subst.
      eapply n.
      reflexivity.
  Qed.    
End DecidableProperties.


Record DecidableAdjSig (P : AdjSig) : Type :=
  mkDecidableAdjSig {
      dec_mode_eq : forall m1 m2 : Modes P, ({m1 = m2} + {m1 <> m2})%type;
      dec_mode_preorder : forall (m1 m2 : Modes P), ({Mode_preorder P m1 m2} + { ~Mode_preorder P m1 m2})%type;
      dec_sigs : forall m, DecidableSig m;
      dec_ru_upshift_eq : forall (l h : Modes P) (leq : Mode_preorder P l h) (sl : l) (sh : h) (r r' : Ru_upshift P l h leq sl sh),
        ( { r = r'} + {r <> r'} )%type;
    }.

Arguments dec_mode_eq {_}.
Arguments dec_mode_preorder {_}.
Arguments dec_sigs {_}.
Arguments dec_ru_upshift_eq {_}.

Section AdjDecidableProperties.
  Context {P : AdjSig} (dec_P : DecidableAdjSig P).

  Definition strong_ru_upshift_eq (l l' h h' : Modes P) (leq : Mode_preorder P l h) (leq' : Mode_preorder P l' h') sl sl' sh sh' (r : Ru_upshift P l h leq sl sh) (r' : Ru_upshift P l' h' leq' sl' sh') :=
      (l = l') /\ (h = h') /\ (JMeq sl sl') /\ (JMeq sh sh') /\ (JMeq leq leq') /\ (JMeq r r').

  (** NOTE: This proof uses the 'proof_irrelevance' axiom for Prop *)
  Lemma strong_dec_ru_upshift : forall (l l' h h' : Modes P) (leq : Mode_preorder P l h) (leq' : Mode_preorder P l' h') sl sl' sh sh' (r : Ru_upshift P l h leq sl sh) (r' : Ru_upshift P l' h' leq' sl' sh'),
      ({ strong_ru_upshift_eq l l' h h' leq leq' sl sl' sh sh' r r' } + { ~ strong_ru_upshift_eq l l' h h' leq leq' sl sl' sh sh' r r' })%type.
  Proof using dec_P.
    intros.
    unfold strong_ru_upshift_eq.
    destruct (dec_mode_eq dec_P l l'); [| right; intuition].
    destruct (dec_mode_eq dec_P h h'); [| right; intuition].
    subst.
    assert (leq = leq') as -> by (apply proof_irrelevance).
    pose proof (dec_sigs dec_P l') as dec_l'.
    destruct (dec_st_eq dec_l' sl sl'); [| right; intros [? [? [Hsl]]]; inversion Hsl; simpl_existTs; intuition].
    pose proof (dec_sigs dec_P h') as dec_h'.
    destruct (dec_st_eq dec_h' sh sh'); [| right; intros [? [? [? [Hsh]]]]; inversion Hsh; simpl_existTs; intuition].
    subst.
    destruct (dec_ru_upshift_eq dec_P l' h' leq' sl' sh' r r').
    - subst; left; intuition.
    - right; intros [? [? [? [? [? Hr]]]]]; inversion Hr; simpl_existTs; intuition.
  Qed.  
End AdjDecidableProperties.
