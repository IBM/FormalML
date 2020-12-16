(* Derived from
   https://github.com/arthuraa/poleiro/blob/23854f99cf286087a8c4d3c0f91a99e66eb7f8d0/theories/Quotients.v
with MIT license: https://github.com/arthuraa/poleiro/blob/23854f99cf286087a8c4d3c0f91a99e66eb7f8d0/LICENSE
 *)


(* We do deliberately do not make heavy use of this module, prefering (non-axiomatic) setoid constructions.  Howver, it is needed for interop with librararies that do not generalize to arbitrarty equivalence relations (Coquelicot and LM).
*)

(* begin hide *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.Description.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* end hide *)
(** Quotients are crucial in mathematical practice, and it is a shame that they
are not available in Coq's standard library.  There was a recent discussion on
the #<a href=https://github.com/coq/coq/issues/10871>Coq GitHub page</a># on
this issue and the consequences of implementing quotients like #<a
href=https://leanprover.github.io/>Lean</a># does, where the eliminator for
function types has a reduction rule that breaks pleasant metatheoretic
properties such as subject reduction.
In this post, we are going to define quotients in Coq with three standard
axioms:
- Functional extensionality
- Propositional extensionality
- Constructive definite description (also known as the axiom of unique choice) *)

(*
Check @functional_extensionality_dep :
  ∀ A B (f g : ∀ x : A, B x),
    (∀ x : A, f x = g x) → f = g.

Check @propositional_extensionality :
  ∀ P Q, (P ↔ Q) → P = Q.

Check @constructive_definite_description :
  ∀ A P, (exists! x : A, P x) → {x : A | P x}.

 *)

(** As far as axioms go, these three are relatively harmless.  In particular,
they are valid in any #<a
href=https://en.wikipedia.org/wiki/Topos##Elementary_topoi_(topoi_in_logic)>elementary
topos</a>#, which are generally regarded as a good universe for doing
constructive, higher-order reasoning.  (Naturally, adding axioms in type theory
does not come for free: since they have no useful reduction behavior, our
quotients won't compute.) *)

Section Quotient.

(** We define the quotient of [T] by an equivalence relation [R] as usual: it is
the type of equivalence classes of [R]. *)

Context {T : Type} (R : relation T) {RP : Equivalence R}.

(* begin hide *)
Unset Elimination Schemes.
(* end hide *)
Record quot := Quot_ {
  quot_class  : T → Prop;
  quot_classP : ∃ x, quot_class = R x;
}.
(* begin hide *)
Set Elimination Schemes.
(* end hide *)

(** The projection into the quotient is given by the [Quot] constructor below,
which maps [x] to its equivalence class [R x].  This definition satisfies the
usual properties: [Quot x = Quot y] if and only if [R x y].  The "if" direction
requires the principle of proof irrelevance, which is a consequence of
propositional extensionality. *)

Definition Quot (x : T) : quot :=
  @Quot_ (R x) (ex_intro _ x (eq_refl _)).

Lemma Quot_inj x y : Quot x = Quot y → R x y.
Proof.
  intros e.
  inversion e.
  rewrite H0.
  reflexivity.
Qed.

Lemma eq_Quot x y : R x y → Quot x = Quot y.
Proof.
  intros e.
  assert (eqq:R x = R y).
  {
    apply functional_extensionality; intros z.
    apply propositional_extensionality; rewrite e; tauto.
  }
  unfold Quot.
  generalize (ex_intro (λ x0 : T, R y = R x0) y eq_refl); intros HH.
  generalize HH.
  rewrite <- eqq; intros HH2.
  f_equal.
  apply proof_irrelevance.
Qed.

(** We can also show that [Quot] is surjective by extracting the witness in the
existential. *)
Lemma Quot_inv q : ∃ x, q = Quot x.
Proof.
  destruct q.
  unfold Quot.
  destruct quot_classP0; simpl.
  rewrite e.
  eauto.
Qed.

(** Unique choice comes into play when defining the elimination principles for
the quotient.  In its usual non-dependent form, the principle says that we can
lift a function [f : T → S] to another function [quot → S] provided that [f] is
constant on equivalence classes.  We define a more general dependently typed
version, which allows in particular to prove a property [S q] by proving that [S
(Quot x)] holds for any [x].  The statement of the compatibility condition for
[f] is a bit complicated because it needs to equate terms of different types [S
(Quot x)] and [S (Quot y)], which requires us to transport the left-hand side
along the equivalence [R x y]. *)

Section Elim.

Definition cast A B (e : A = B) : A → B :=
  match e with (eq_refl _) => id end.

Context (S : quot → Type) (f : ∀ x, S (Quot x)).
Context (fP : ∀ x y (exy : R x y), cast (f_equal S (eq_Quot exy)) (f x) = f y).

(** We begin with an auxiliary result that uniquely characterizes the result of
applying the eliminator to an element [q : quot].  Thanks to unique choice, this
allows us to define the eliminator as a function [quot_rect]. *)

Lemma quot_rect_subproof (q : quot) :
  exists! a : S q, ∃ x (exq : Quot x = q), a = cast (f_equal S exq) (f x).
Proof.
  destruct q; simpl.
  destruct quot_classP0 as [x q].
  rewrite q.
  exists (f x).
  split.
  - eauto.
  - intros x' [?[??]].
    subst.
    inversion x1.
    assert (eqq:R x0 x).
    {
      apply Quot_inj; apply eq_Quot.
      rewrite H0; reflexivity.
    } 
    rewrite <- (@fP x0 x eqq).
    do 2 f_equal.
    apply proof_irrelevance.
    Unshelve.
    exact x.
    reflexivity.
Qed.

Definition quot_rect q : S q :=
  proj1_sig (constructive_definite_description _ (quot_rect_subproof q)).

Lemma quot_rectE x : quot_rect (Quot x) = f x.
Proof.
  unfold quot_rect.
  destruct ( (constructive_definite_description
       (λ a : S (Quot x),
          ∃ (x0 : T) (exq : Quot x0 = Quot x), a = cast (f_equal S exq) (f x0))
       (quot_rect_subproof (Quot x)))) as [?[?[??]]]; simpl.
  subst.
  erewrite <- (@fP _ x).
  do 2 f_equal.
  apply proof_irrelevance.
  Unshelve.
  now apply Quot_inj.
Qed.

End Elim.

(** In the non-dependent case, the compatibility condition acquires its usual
form. *)

Section Rec.

Context S (f : T → S) (fP : ∀ x y, R x y → f x = f y).

Definition congr1CE (A B : Type) (b : B) x y (e : x = y) :
  f_equal (λ _ : A, b) e = (eq_refl _) :=
  match e with (eq_refl _) => (eq_refl _) end.

Definition quot_rec : quot -> S :=
  @quot_rect (λ _, S) f
    (λ x y exy, trans_eq
                  (f_equal (λ p, cast p (f x)) (congr1CE S (eq_Quot exy)))
      (fP exy)).

Lemma quot_recE x : quot_rec (Quot x) = f x.
Proof.
  unfold quot_rec.
  now rewrite quot_rectE.
Qed.

End Rec.

End Quotient.


Section Lift.
  Definition quot_lift {T : Type} (R : T->T->Prop)
        {equivR:Equivalence R}
        (f : T -> T) {propR:Proper (R ==> R) f} :
    quot R -> quot R.
  Proof.
    assert (Hpf:forall x0 y : T, R x0 y -> Quot R (f x0) = Quot R (f y)).
    {
      intros.
      apply eq_Quot; trivial.
      rewrite H.
      reflexivity.
    } 
    apply (@quot_rec _ _ equivR (quot R) (fun y => Quot R (f y)) Hpf).
  Defined.

  Global Arguments quot_lift {T} R {equivR} f {propR}.

  Lemma quot_liftE
        {T : Type} (R : T->T->Prop)
        {equivR:Equivalence R}
        (f : T -> T) {propR:Proper (R ==> R) f} :
    forall x, quot_lift R f (Quot R x) = @Quot _ R (f x).
  Proof.
    intros.
    unfold quot_lift.
    now rewrite quot_recE.
  Qed.        
  
  Definition quot_lift2 {T : Type} (R : T->T->Prop)
        {equivR:Equivalence R}
        (f : T -> T -> T) {propR:Proper (R ==> R ==> R) f} :
    quot R -> quot R -> quot R.
  Proof.
    generalize (@quot_rec _ _ equivR)
    ; intros HH.
    specialize (HH (quot R -> quot R)).
    assert (Hpf:forall x, forall x0 y : T, R x0 y -> Quot R (f x x0) = Quot R (f x y)).
    {
      intros.
      apply eq_Quot; trivial.
      rewrite H.
      reflexivity.
    } 
    refine (HH (fun x => (@quot_rec _ _ equivR (quot R) (fun y => Quot R (f x y)) (Hpf x) )) _).
    intros.
    (* we might be able to avoid this, but since quotients use it anyway, it does not really matter *)
    apply FunctionalExtensionality.functional_extensionality; intros.
    destruct (Quot_inv x0); subst.
    repeat rewrite quot_recE.
    apply eq_Quot; trivial.
    rewrite H.
    reflexivity.
  Defined.

  Global Arguments quot_lift2 {T} R {equivR} f {propR}.
    
  Lemma quot_lift2E
        {T : Type} (R : T->T->Prop)
        {equivR:Equivalence R}
        (f : T -> T -> T) {propR:Proper (R ==> R ==> R) f} :
    forall x y, quot_lift2 R f (Quot R x) (Quot R y) = @Quot _ R (f x y).
  Proof.
    intros.
    unfold quot_lift2.
    now repeat rewrite quot_recE.
  Qed.        

End Lift.

