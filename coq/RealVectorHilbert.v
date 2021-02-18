Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
Require Import FunctionalExtensionality.

Require Import hilbert.

Require Export RandomVariableFinite.
Require Import quotient_space.

Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Require Import VectorRandomVariable.

Section stuff.
  Context {n:nat}.

  Definition Rvector_plus (v1 v2:vector R n) : vector R n.
  Admitted.
  
  
  Definition Rvector_AbelianGroup_mixin : AbelianGroup.mixin_of (vector R n)
    := AbelianGroup.Mixin (Vector R n) vector_plus vector_opp vector_zero
                          vector_plus_comm vector_plus_assoc
                          vector_plus_zero vector_plus_inv.
  
  Canonical Rvector_AbelianGroup :=
    AbelianGroup.Pack (vector R n) Rvector_AbelianGroup_mixin (vector R n).

End stuff.
