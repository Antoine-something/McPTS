From Coq Require Import RelationClasses.

Record PtsSig : Type :=
  mkPtsSig {
      St :> Set;
      (** Typing and subtyping axioms *)
      Ax_typ : St -> St -> Prop;
      Ax_sub : St -> St -> Prop;
      (** Rules for type constructors *)
      Ru_pi : St -> St -> St -> Set;
      Ru_nat : St -> Set;
    }.

(** Reflexive transitive close of Ax_sub *)
Inductive st_subtyp {P : PtsSig} : P -> P -> Prop :=
| st_subtyp_refl : forall s, st_subtyp s s
| st_subtyp_trans : forall s1 s2 s3, Ax_sub P s1 s2 -> st_subtyp s2 s3 ->
                                st_subtyp s1 s3.
#[export]
Hint Constructors st_subtyp : mcpts.

#[export]
Instance st_Subtyp_reflexive {P} : Reflexive (@st_subtyp P).
Proof.
  intros x; econstructor.
Qed.

#[export]
Instance st_subtyp_transtive {P} : Transitive (@st_subtyp P).
Proof.
  induction 1; intros; eauto.
  econstructor; eauto.
Qed.

(** Sort options, used in the soundness proof *)
(* We cannot use Rocq's option type because St is defined in Set and 'option' expects something in Type *)
Inductive SortOption (P : PtsSig) : Type :=
| so_None : SortOption P
| so_Some : P -> SortOption P.

Arguments so_None {P}.
Arguments so_Some {P} s.
