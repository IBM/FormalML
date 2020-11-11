Require Import Equivalence EquivDec.

Require Import LibUtilsCoqLibAdd.

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
