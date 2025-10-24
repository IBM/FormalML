Require Import Equivalence EquivDec Eqdep_dec Morphisms.

Require Import LibUtilsCoqLibAdd LibUtilsDigits.

Definition coerce {A B:Type} (pf:A=B) : A -> B.
Proof.
  destruct pf.
  intro a; exact a.
Defined.

Local Existing Instance Equivalence_pullback.

Local Instance EqDec_pullback {A B} (R:A->A->Prop) {eqR:Equivalence R} {decR:EqDec A R} (f:B->A) :
  EqDec B (fun x y : B => R (f x) (f y)).
Proof.
  intros x y.
  destruct (decR (f x) (f y)).
  - left; trivial.
  - right; trivial.
Defined.

Lemma dec_complement {A} {p:A->Prop} (dec_p: forall x, {p x} + {~ p x}) :
  forall x, {~ p x} + {~ ~ p x}.
Proof.
  intros x.
  destruct (dec_p x).
  - right; tauto.
  - left; trivial.
Defined.

Lemma ne_symm {A} (x y : A) : x <> y <-> y <> x.
Proof.
  split; intros.
  * intros Hxy ; symmetry in Hxy ; firstorder.
  * intros Hxy ; symmetry in Hxy ; firstorder.
Qed.

Definition rv_eq {Ts Td:Type} : (Ts -> Td) -> (Ts -> Td) -> Prop
  :=  pointwise_relation Ts eq.

(* This instance is Local, since it is too general *)
Local Instance rv_eq_equiv
         {Ts Td:Type} :
  Equivalence (@rv_eq Ts Td).
Proof.
  typeclasses eauto.
Qed.

Lemma refl_refl {T} {R:T->T->Prop} {refl:Reflexive R} x y : x = y -> R x y.
Proof.
  intros; subst.
  apply refl.
Qed.

Global Instance sigT_eqdec {A} {B:A->Type} (decA:EqDec A eq) (decB:forall x, EqDec (B x) eq) :
  EqDec (sigT B) eq.
Proof.
  intros [x y] [x' y'].
  destruct (decA x x').
  - red in e; subst.
    destruct (decB _ y y').
    + left.
      congruence.
    + right.
      intros HH.
      apply inj_pair2_eq_dec in HH; [| auto].
      congruence.
  - right.
    congruence.
Defined.

Lemma index_pf_irrel n m pf1 pf2 : 
  exist (fun n' : nat => (n' < n)%nat) m pf1 = exist (fun n' : nat => (n' < n)%nat) m pf2.
Proof.
  f_equal.
  apply digit_pf_irrel.
Qed.
