From Coq Require Import Program.Equality.
From McPTS.PtsSignature Require Import Signatures.


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
