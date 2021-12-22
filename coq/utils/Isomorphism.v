Require Import NArith List Rbase.

Class Isomorphism (A B:Type) :=
  {
    iso_f : A -> B ;
    iso_b : B -> A ;
    iso_f_b : forall b, iso_f (iso_b b) = b ;
    iso_b_f : forall a, iso_b (iso_f a) = a
  }.

(* 
We would like to just declare
Require Import RelationClasses.
Global Instance Isomorphism_equiv : Equivalence Isomorphism.

But this runs into universe issues.
 *)

Global Instance Isomorphism_refl {A} : Isomorphism A A
  := {
      iso_b a := a ;
      iso_f a := a ;
      iso_f_b := @eq_refl A;
      iso_b_f := @eq_refl A
    }.

Instance Isomorphism_symm {A B} (iso:Isomorphism A B) : Isomorphism B A
  := {
      iso_b := iso_f ;
      iso_f := iso_b ;
      iso_f_b := iso_b_f ;
      iso_b_f := iso_f_b
    }.

Program Instance Isomorphism_trans {A B C} (iso1:Isomorphism A B) (iso2:Isomorphism B C) : Isomorphism A C
  := {
      iso_f a := @iso_f _ _ iso2 (@iso_f _ _ iso1 a) ;
      iso_b b := @iso_b _ _ iso1 (@iso_b _ _ iso2 b)
    }.
Next Obligation.
  repeat rewrite iso_f_b; trivial.
Qed.
Next Obligation.
  repeat rewrite iso_b_f; trivial.
Qed.

Program Instance Isomorphism_prod {A B C D} (iso1:Isomorphism A C) (iso2:Isomorphism B D) : Isomorphism (A*B) (C*D)
  := {
      iso_f '(a,c) := (iso_f a, iso_f c) ;
      iso_b '(b,d) := (iso_b b, iso_b d)
    }.
Next Obligation.
  repeat rewrite iso_f_b; trivial.
Qed.
Next Obligation.
  repeat rewrite iso_b_f; trivial.
Qed.

Program Instance Isomorphism_list {A B} (iso1:Isomorphism A B) : Isomorphism (list A) (list B)
  := {
      iso_f := map iso_f ;
      iso_b := map iso_b
    }.
Next Obligation.
  rewrite map_map.
  erewrite map_ext; try apply map_id.
  intros.
  apply iso_f_b.
Qed.
Next Obligation.
  rewrite map_map.
  erewrite map_ext; try apply map_id.
  intros.
  apply iso_b_f.
Qed.

Global Instance nat_to_N_iso : Isomorphism nat N
  := {
      iso_f := N.of_nat ;
      iso_b := N.to_nat ;
      iso_f_b := N2Nat.id ;
      iso_b_f := Nat2N.id ;
    }.

Section nd.
  Lemma iso_b_nodup {A B} {iso:Isomorphism A B} l :
    NoDup l ->
    NoDup (map iso_b l).
  Proof.
    intros.
    apply (NoDup_map_inv (iso_f)).
    rewrite map_map.
    erewrite map_ext; try rewrite map_id; trivial.
    intros.
    now rewrite iso_f_b.
  Qed.

  Lemma iso_f_nodup {A B} {iso:Isomorphism A B} l :
    NoDup l ->
    NoDup (map iso_f l).
  Proof.
    intros.
    apply (NoDup_map_inv (iso_b)).
    rewrite map_map.
    erewrite map_ext; try rewrite map_id; trivial.
    intros.
    now rewrite iso_b_f.
  Qed.

End nd.
