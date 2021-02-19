Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.

Require Import hilbert.

Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Require Import DVector.

Section Rvector_defs.
  Context {n:nat}.

  Declare Scope Rvector_scope.
  Delimit Scope Rvector_scope with Rvector.
  Bind Scope Rvector_scope with vector R.

  Definition Rvector_zero : vector R n
    := vector_const 0 n.

  Notation "0" := Rvector_zero : Rvector_scope.
  
  Definition Rvector_scale (c:R) (x:vector R n) : vector R n
    := vector_map (fun a => c * a) x.

  Notation "c .* v" := (Rvector_scale (c%R) v) (at level 41, right associativity) : Rvector_scope.

  Definition Rvector_opp (x:vector R n) : vector R n
    := Rvector_scale (-1) x.

  Notation "- v" := (Rvector_opp v) (at level 35, right associativity) : Rvector_scope.
  
  Definition Rvector_plus (x y:vector R n) : vector R n
    := vector_map (fun '(a,b) => a + b) (vector_zip x y).

  Notation "x + y" := (Rvector_plus x y) (at level 50, left associativity) : Rvector_scope.

  Definition Rvector_mult (x y:vector R n) : vector R n
    := vector_map (fun '(a,b) => a * b) (vector_zip x y).

  Notation "x * y" := (Rvector_mult x y) (at level 40, left associativity) : Rvector_scope.

  Definition Rvector_sum (v:vector R n) : R
    := vector_fold_left Rplus v 0.

  Notation "∑ x " := (Rvector_sum (x%Rvector)) (at level 40, left associativity) : Rvector_scope. (* \sum *)

  Definition Rvector_inner (x y:vector R n) : R
    := Rvector_sum (Rvector_plus x y).

  Notation "x · y" := (Rvector_inner x%Rvector y%Rvector) (at level 40, left associativity) : Rvector_scope.  (* \cdot *)

  Local Open Scope Rvector_scope.

  Lemma Rvector_plus_comm (x y:vector R n) : x + y = y + x.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_swap, map_map.
    apply map_ext; intros [??]; simpl.
    lra.
  Qed.

  (* TODO: move *)
  Lemma combine_assoc {A B C} (x:list A) (y:list B) (z:list C):
    combine x (combine y z) = map (fun '(x,y,z) => (x,(y,z))) (combine (combine x y) z).
  Proof.
    revert y z.
    induction x; simpl; trivial.
    destruct y; simpl; trivial.
    destruct z; simpl; trivial.
    now rewrite IHx.
  Qed.

  Lemma combine_const_r {A B} (x:list A) c (y:list B) :
    Forall (fun a => a = c) y ->
    (length x <= length y)%nat ->
    combine x y = map (fun a => (a,c)) x.
  Proof.
    revert y.
    induction x; simpl; trivial; intros.
    destruct y; simpl in *; [lia | ].
    invcs H.
    f_equal.
    apply IHx; trivial.
    lia.
  Qed.

  Lemma Rvector_plus_assoc (x y z:vector R n) : x + (y + z) = (x + y) + z.
  Proof.
    apply vector_eq; simpl.
    rewrite <- (map_id (proj1_sig x)) at 1.
    rewrite <- (map_id (proj1_sig z)) at 2.
    repeat rewrite combine_map, map_map.
    rewrite combine_assoc, map_map.
    apply map_ext; intros [[??]?].
    lra.
  Qed.

  Lemma Rvector_plus_zero (x:vector R n) : x + 0 = x.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_const_r with (c:=0%R).
    - rewrite map_map; simpl.
      erewrite map_ext; try eapply map_id.
      intros; lra.
    - apply vector_const_Forall.
    - now repeat rewrite vector_length.
  Qed.

  Lemma Rvector_plus_inv (x:vector R n) : x + (- x) = 0.
  Proof.
    apply vector_eq; simpl.
    rewrite <- (map_id (proj1_sig x)) at 1.
    repeat rewrite combine_map, combine_self.
    repeat rewrite map_map.
    destruct x; simpl.
    unfold Rvector_zero, vector_const.
    revert x e.
    induction n; simpl
    ; destruct x; simpl in *; trivial; try discriminate
    ; intros.
    invcs e.
    f_equal; auto.
    lra.
  Qed.
  
  Definition Rvector_AbelianGroup_mixin : AbelianGroup.mixin_of (vector R n)
    := AbelianGroup.Mixin (vector R n) Rvector_plus Rvector_opp Rvector_zero
                          Rvector_plus_comm Rvector_plus_assoc
                          Rvector_plus_zero Rvector_plus_inv.
  
  Canonical Rvector_AbelianGroup :=
    AbelianGroup.Pack (vector R n) Rvector_AbelianGroup_mixin (vector R n).

  Lemma Rvector_scale_scale (a b:R) (v:vector R n) :
    a .* (b .* v) = (a * b) .* v.
  Proof.
    apply vector_eq; simpl.
    rewrite map_map.
    apply map_ext; intros.
    lra.
  Qed.

  Lemma Rvector_scale1 (v:vector R n) :
    1 .* v = v.
  Proof.
    apply vector_eq; simpl.
    erewrite map_ext; try eapply map_id; intros; simpl.
    lra.
  Qed.

  Lemma Rvector_scale_plus_l (a:R) (x y:vector R n) :
    a .* (x + y) = a .* x + a .* y.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_map.
    repeat rewrite map_map.
    apply map_ext; intros [??]; simpl.
    lra.
  Qed.

  Lemma Rvector_scale_plus_r (a b:R) (x:vector R n) :
    (a + b) .* x = a .* x + b .* x.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_map, map_map, combine_self, map_map.
    apply map_ext; intros.
    lra.
  Qed.


  Definition Rvector_ModuleSpace_mixin : ModuleSpace.mixin_of R_Ring Rvector_AbelianGroup
        := ModuleSpace.Mixin R_Ring Rvector_AbelianGroup
                             Rvector_scale Rvector_scale_scale Rvector_scale1
                             Rvector_scale_plus_l Rvector_scale_plus_r.

      Canonical Rvector_ModuleSpace :=
        ModuleSpace.Pack R_Ring (vector R n) (ModuleSpace.Class R_Ring (vector R n) Rvector_AbelianGroup_mixin Rvector_ModuleSpace_mixin) (vector R n).
  
End Rvector_defs.
