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

  Definition Rvector_sqr (x:vector R n) : vector R n
    := vector_map (fun a => a²) x.

  Notation "x ²" := (Rvector_sqr x) (at level 1) : Rvector_scope.

  Program Definition Rvector_sum (v:vector R n) : R
    := RealAdd.list_sum v.

  Notation "∑ x " := (Rvector_sum (x%Rvector)) (at level 40, left associativity) : Rvector_scope. (* \sum *)

  Definition Rvector_inner (x y:vector R n) : R
    := Rvector_sum (Rvector_mult x y).

  Notation "x ⋅ y" := (Rvector_inner x%Rvector y%Rvector) (at level 40, left associativity) : Rvector_scope.  (* \cdot *)

  Local Open Scope Rvector_scope.

  Lemma Rvector_plus_comm (x y:vector R n) : x + y = y + x.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_swap, map_map.
    apply map_ext; intros [??]; simpl.
    lra.
  Qed.

  Lemma Rvector_mult_comm (x y:vector R n) : x * y = y * x.
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

  Lemma combine_map_l {A B C : Type} (f : A -> C) (l1 : list A) (l2 : list B) :
    combine (map f l1) l2 = map (fun '(x, y) => (f x, y)) (combine l1 l2).
  Proof.
    rewrite <- (map_id l2) at 1.
    now rewrite combine_map.
  Qed.

  Lemma combine_map_r {A B D : Type} (g : B -> D) (l1 : list A) (l2 : list B) :
    combine l1 (map g l2) = map (fun '(x, y) => (x, g y)) (combine l1 l2).
  Proof.
    rewrite <- (map_id l1) at 1.
    now rewrite combine_map.
  Qed.
  
  Lemma Rvector_plus_assoc (x y z:vector R n) : x + (y + z) = (x + y) + z.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_map_l, combine_map_r.
    repeat rewrite map_map.
    rewrite combine_assoc, map_map.
    apply map_ext; intros [[??]?].
    lra.
  Qed.

  Lemma Rvector_mult_assoc (x y z:vector R n) : x * (y * z) = (x * y) * z.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_map_l, combine_map_r.
    repeat rewrite map_map.
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

  Lemma Rvector_mult_zero (x:vector R n) : x * 0 = 0.
  Proof.
    apply vector_eqs; simpl.
    destruct x; simpl.
    unfold Rvector_zero, vector_const.
    revert x e.
    induction n; simpl; destruct x; simpl in *; trivial; try discriminate; intros.
    invcs e.
    constructor; auto.
    lra.
  Qed.

  Lemma Rvector_plus_inv (x:vector R n) : x + (- x) = 0.
  Proof.
    apply vector_eq; simpl.
    repeat rewrite combine_map_r, combine_self.
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

  Lemma Rvector_inner_comm (x y:vector R n) : x ⋅ y = y ⋅ x.
  Proof.
    unfold Rvector_inner.
    now rewrite Rvector_mult_comm.
  Qed.

  Program Lemma Rvector_sum_pos (x:vector R n) :
    (forall a, In a x -> 0%R <= a) -> 0 <= ∑ x.
  Proof.
    intros.
    apply list_sum_pos_pos'.
    now rewrite Forall_forall.
  Qed.

  Lemma Rvector_sqr_mult (x:vector R n) : x² = x * x.
  Proof.
    apply vector_eq; simpl.
    rewrite combine_self, map_map.
    now unfold Rsqr.
  Qed.

  Program Lemma Rvector_sqr_pos (x:vector R n) : forall a, In a x² -> 0 <= a.
  Proof.
    intros.
    apply in_map_iff in H.
    destruct H as [?[??]].
    subst.
    apply Rle_0_sqr.
  Qed.
  
  Lemma Rvector_inner_pos (x:vector R n) : 0%R <= x ⋅ x.
  Proof.
    unfold Rvector_inner.
    apply Rvector_sum_pos; intros.
    rewrite <- Rvector_sqr_mult in H.
    now apply Rvector_sqr_pos in H.
  Qed.

  Program Lemma Rvector_sum_pos_0 (x:vector R n) :
      (forall a, In a x -> 0%R <= a) ->
      ∑ x = 0%R -> x = 0.
  Proof.
    intros.
    apply vector_const_eq.
    apply list_sum_all_pos_zero_all_zero in H0; trivial.
    rewrite Forall_forall; intros.
    specialize (H _ H1).
    lra.
  Qed.

  Lemma Rvector_sqr_zero_inv (x:vector R n) : x² = 0  -> x = 0.
  Proof.
    intros eqq.
    apply vector_const_eq in eqq.
    apply vector_const_eq.
    rewrite Forall_forall in *; intros a inn.
    specialize (eqq (a ²)%R).
    cut_to eqq.
    - now apply Rsqr_0_uniq.
    - apply in_map_iff.
      eauto.
  Qed.

  Lemma Rvector_inner_zero_inv (x:vector R n) : x ⋅ x = 0%R  -> x = 0.
  Proof.
    unfold Rvector_inner.
    intros.
    rewrite <- Rvector_sqr_mult in H.
    apply Rvector_sum_pos_0 in H.
    - now apply Rvector_sqr_zero_inv.
    - intros.
      eapply Rvector_sqr_pos; eauto.
  Qed.

  Lemma Rvector_scale_mult_l (a:R) (x y:vector R n) :
    ((a .* x) * y) = a .* (x * y).
  Proof.
    apply vector_eq; simpl.
    rewrite combine_map_l.
    repeat rewrite map_map.
    apply map_ext; intros [??]; simpl.
    lra.
  Qed.

  Lemma Rvector_scale_sum (a:R) (x:vector R n) :
    ∑ (a .* x) = Rmult a (∑ x).
  Proof.
    unfold Rvector_sum.
    destruct x; simpl.
    now rewrite list_sum_mult_const, map_id.
  Qed.

  Lemma Rvector_inner_scal (x y:vector R n) (l:R) : (l .* x) ⋅ y = Rmult l (x ⋅ y).
  Proof.
    unfold Rvector_inner.
    now rewrite Rvector_scale_mult_l, Rvector_scale_sum.
  Qed.

  Lemma Rvector_mult_plus_distr_r (x y z:vector R n) :
    (x + y) * z =  (x * z) + (y * z).
  Proof.
    apply vector_eq; simpl.
    repeat rewrite combine_map_l.
    repeat rewrite map_map.
    rewrite (combine_swap  (proj1_sig y) (proj1_sig z)).
    repeat rewrite combine_map_r, map_map.
    rewrite combine_assoc.
    rewrite (combine_swap (combine (proj1_sig x) (proj1_sig z)) (proj1_sig z)).
    rewrite combine_assoc.
    rewrite (combine_swap (combine (proj1_sig z) (proj1_sig x))).
    rewrite combine_assoc.
    rewrite combine_self.
    repeat rewrite combine_map_l, map_map.
    rewrite combine_swap.
    rewrite combine_assoc.
    repeat rewrite map_map.
    apply map_ext; intros [[??]?]; simpl.
    lra.
  Qed.

  Lemma Rvector_sum_plus_distr (x y:vector R n) :
    ∑ (x + y) = (∑ x + ∑ y)%R.
  Proof.
    unfold Rvector_sum, Rvector_plus; simpl.
    destruct x; destruct y; simpl.
    subst.
    revert x0 e0.
    induction x; destruct x0; simpl in *; try discriminate; intros.
    - lra.
    - invcs e0.
      rewrite IHx; trivial.
      lra.
  Qed.

  Lemma Rvector_inner_plus (x y z:vector R n)  : (x + y) ⋅ z = Rplus (x ⋅ z) (y ⋅ z).
  Proof.
    unfold Rvector_inner.
    now rewrite Rvector_mult_plus_distr_r, Rvector_sum_plus_distr.
  Qed.
  
  Definition Rvector_PreHilbert_mixin : PreHilbert.mixin_of (Rvector_ModuleSpace)
    := PreHilbert.Mixin (Rvector_ModuleSpace) Rvector_inner
                        Rvector_inner_comm Rvector_inner_pos Rvector_inner_zero_inv
                        Rvector_inner_scal Rvector_inner_plus.
  
  Canonical Rvector_PreHilbert :=
    PreHilbert.Pack (vector R n) (PreHilbert.Class _ _ Rvector_PreHilbert_mixin) (vector R n).
      
End Rvector_defs.
