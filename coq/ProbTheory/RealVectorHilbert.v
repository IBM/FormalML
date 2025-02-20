Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.

Require Import hilbert.

Require Import utils.Utils.
Require Import List.
Require Coquelicot.Hierarchy.

Set Bullet Behavior "Strict Subproofs".

Require Import DVector.

Section Rvector_defs.
  Context {n:nat}.

  Declare Scope Rvector_scope.
  Delimit Scope Rvector_scope with Rvector.
  Bind Scope Rvector_scope with vector R.

  Lemma vec_Req_EM_T (v1 v2 : vector R n) :
    {v1 = v2} + {v1 <> v2}.
  Proof.
    apply vector_eq_dec.
  Defined.
  
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

  Definition Rvector_abs (x:vector R n) : vector R n
    := vector_map Rabs x.                                                 

  Definition Rvector_max_abs (x:vector R n) : R 
    := vector_fold_left Rmax (Rvector_abs x) 0.

  Definition Rvector_max_sqr (x:vector R n) : R 
    := vector_fold_left Rmax (Rvector_sqr x) 0.

  Definition Rvector_max (x:vector R (S n)) : R 
    := Rmax_list (proj1_sig x).

  Definition Rvector_min (x:vector R (S n)) : R 
    := Rmin_list (proj1_sig x).

  Notation "x ²" := (Rvector_sqr x) (at level 1) : Rvector_scope.

  Program Definition Rvector_sum (v:vector R n) : R
    := RealAdd.list_sum v.

  Notation "∑ x " := (Rvector_sum (x%Rvector)) (at level 40, left associativity) : Rvector_scope. (* \sum *)

  Definition Rvector_inner (x y:vector R n) : R
    := Rvector_sum (Rvector_mult x y).

  Notation "x ⋅ y" := (Rvector_inner x%Rvector y%Rvector) (at level 40, left associativity) : Rvector_scope.  (* \cdot *)

  Local Open Scope Rvector_scope.

  Lemma Rvector_nth_zero i pf : vector_nth i pf Rvector_zero = 0%R.
  Proof.
    apply vector_nth_const.
  Qed.
  
  Lemma Rvector_plus_explode (x y:vector R n) :
    x + y = vector_create 0 n (fun i _ pf => (vector_nth i pf x + vector_nth i pf y)%R).
  Proof.
    unfold Rvector_plus.
    rewrite vector_zip_explode.
    rewrite vector_map_create.
    reflexivity.
  Qed.

  Lemma Rvector_nth_plus (x y:vector R n) i pf :
    vector_nth i pf (x + y) = Rplus (vector_nth i pf x) (vector_nth i pf y).
  Proof.
    rewrite Rvector_plus_explode.
    rewrite vector_nth_create.
    simpl.
    f_equal; apply vector_nth_ext.
  Qed.

  Lemma Rvector_mult_explode (x y:vector R n) :
    x * y = vector_create 0 n (fun i _ pf => (vector_nth i pf x * vector_nth i pf y)%R).
  Proof.
    unfold Rvector_mult.
    rewrite vector_zip_explode.
    rewrite vector_map_create.
    reflexivity.
  Qed.

  Lemma Rvector_nth_mult (x y:vector R n) i pf :
    vector_nth i pf (x * y) = Rmult (vector_nth i pf x) (vector_nth i pf y).
  Proof.
    rewrite Rvector_mult_explode.
    rewrite vector_nth_create.
    simpl.
    f_equal; apply vector_nth_ext.
  Qed.
  
  Lemma Rvector_plus_comm (x y:vector R n) : x + y = y + x.
  Proof.
    repeat rewrite Rvector_plus_explode.
    apply vector_create_ext; intros.
    lra.
  Qed.

  Lemma Rvector_mult_comm (x y:vector R n) : x * y = y * x.
  Proof.
    repeat rewrite Rvector_mult_explode.
    apply vector_create_ext; intros.
    lra.
  Qed.

  Lemma Rvector_nth_scale (c : R) (v : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_scale c v) = (c * vector_nth i pf v)%R.
    Proof.
      apply vector_nth_map.
    Qed.

    Lemma Rvector_nth_opp (v : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_opp v) = (-1 * vector_nth i pf v)%R.
    Proof.
      apply vector_nth_map.
    Qed.

    Lemma Rvector_nth_abs (v : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_abs v) = Rabs (vector_nth i pf v).
    Proof.
      apply vector_nth_map.
    Qed.

    Definition Rvector_minus (x y:vector R n) : vector R n
      := Rvector_plus x (Rvector_opp y).

    Lemma Rvector_nth_minus (v1 v2 : vector R n) (i : nat) (pf : (i < n)%nat):
      vector_nth i pf (Rvector_minus v1 v2) = 
      (vector_nth i pf v1) - (vector_nth i pf v2).
    Proof.
      unfold Rvector_minus.
      rewrite Rvector_nth_plus, Rvector_nth_opp.
      lra.
    Qed.

    Lemma Rvector_plus_eq_compat_l (v v1 v2 : vector R n) :
      v1 = v2 -> Rvector_plus v v1 = Rvector_plus v v2.
    Proof.
      congruence.
    Qed.

    Definition Scaled_Rvector_max_abs  (x y :vector R n) : R :=
      Rvector_max_abs (Rvector_mult x y).
    
    Definition Rvector_inv (x : vector R n) : vector R n :=
      vector_map (fun c => Rinv c) x.
    
    Definition Rinv_mkpos (c : posreal) : posreal :=
      mkposreal _ (Rinv_pos c (cond_pos c)).
    
    Definition Rvector_inv_pos (x : vector posreal n) : vector posreal n :=
      vector_map (fun c => Rinv_mkpos c) x.
    
    Definition Div_scaled_Rvector_max_abs (x y :vector R n) : R :=
      Scaled_Rvector_max_abs x (Rvector_inv y).
    
    Definition pos_Rvector_mult (x : vector R n) (y :vector posreal n) : (vector R n) :=
      Rvector_mult x (vector_map (fun c => pos c) y).
    
    Definition pos_scaled_Rvector_max_abs (x : vector R n) (y :vector posreal n) : R :=
      Rvector_max_abs (pos_Rvector_mult x y).
    
    Definition scaled_norm (x : vector R n) (y :vector posreal n) : R :=
      Rvector_max_abs (pos_Rvector_mult x y).
    
    Definition pos_vec (x : vector posreal n) : vector R n := vector_map pos x.


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
    apply vector_nth_eq; intros.
    rewrite Rvector_nth_plus.
    rewrite Rvector_nth_zero.
    now rewrite Rplus_0_r.
  Qed.

  Lemma Rvector_mult_zero (x:vector R n) : x * 0 = 0.
  Proof.
    rewrite Rvector_mult_explode.
    apply vector_nth_eq; intros.
    rewrite vector_nth_create; simpl.
    unfold Rvector_zero.
    repeat rewrite vector_nth_const.
    lra.
  Qed.

  Lemma Rvector_scale_zero (c : R) :
      Rvector_scale c 0 = 0.
    Proof.
      apply vector_nth_eq.
      unfold Rvector_zero, vector_const.
      unfold Rvector_scale.
      intros.
      rewrite vector_nth_map, vector_nth_create.
      now rewrite Rmult_0_r.
    Qed.

  Lemma Rvector_scale0 (v:vector R n) :
    0 .* v = 0.
  Proof.
    apply vector_nth_eq.
    unfold Rvector_zero, vector_const.
    unfold Rvector_scale.
    intros. rewrite vector_nth_map, vector_nth_create.
    now rewrite Rmult_0_l.
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
    f_equal.
    - lra.
    - rewrite IHn0; trivial.
      apply vector_list_create_const_shift.
  Qed.
  
  Lemma Rvector_inv_plus (x:vector R n) : (- x) + x = 0.
  Proof.
    rewrite Rvector_plus_comm.
    apply Rvector_plus_inv.
  Qed.

  Lemma Rvector_plus_inv' (x:vector R n) : x + (-1 .* x) = 0.
  Proof.
    apply Rvector_plus_inv.
  Qed.

  Lemma Rvector_inv_plus' (x:vector R n) : (-1 .* x) + x = 0.
  Proof.
    apply Rvector_inv_plus.
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
  
  Lemma Rvector_scale_comm (a b : R) (x : vector R n) :
    a .* (b .* x) = b .* (a .* x).
  Proof.
    repeat rewrite Rvector_scale_scale.
    now rewrite Rmult_comm.
  Qed.

  Definition Rvector_ModuleSpace_mixin : ModuleSpace.mixin_of R_Ring Rvector_AbelianGroup
        := ModuleSpace.Mixin R_Ring Rvector_AbelianGroup
                             Rvector_scale Rvector_scale_scale Rvector_scale1
                             Rvector_scale_plus_l Rvector_scale_plus_r.

  Canonical Rvector_ModuleSpace :=
    ModuleSpace.Pack R_Ring (vector R n) (ModuleSpace.Class R_Ring (vector R n) Rvector_AbelianGroup_mixin Rvector_ModuleSpace_mixin) (vector R n).

  Lemma Rvector_scale_inj (c:R) (x y:vector R n) :
    c <> 0%R -> c .* x = c .* y  -> x = y.
  Proof.
    intros.
    apply (f_equal (Rvector_scale (/ c))) in H0.
    repeat rewrite Rvector_scale_scale in H0.
    repeat rewrite Rinv_l in H0 by trivial.
    now repeat rewrite Rvector_scale1 in H0.
  Qed.
  
 Lemma Rvector_scale_not_0 (x:R) (y : vector R n) :
       (x <> 0%R) /\ (y <> Rvector_zero) -> Rvector_scale x y <> Rvector_zero.
 Proof.
   intros.
   unfold not.
   intro zz.
   destruct H.
   rewrite <- Rvector_scale_zero with (c := x) in zz.
   now apply Rvector_scale_inj in zz.
 Qed.

  Lemma Rvector_inner_comm (x y:vector R n) : x ⋅ y = y ⋅ x.
  Proof.
    unfold Rvector_inner.
    now rewrite Rvector_mult_comm.
  Qed.

  Lemma Rvector_sum_const c : ∑ (vector_const c n) = (INR n * c)%R.
  Proof.
    unfold Rvector_sum; simpl.
    generalize (list_sum_map_const (vector_list_create 0 n (fun (m : nat) (_ : (0 <= m)%nat) (_ : (m < n)%nat) => c)) 0%R (fun _ => c%R))
    ; intros HH.
    rewrite vector_list_create_length in HH.
    rewrite <- HH.
    now rewrite vector_list_create_map; simpl.
  Qed.

  Program Lemma Rvector_sum0 : ∑ 0 = 0%R.
  Proof.
    unfold Rvector_zero.
    rewrite Rvector_sum_const.
    lra.
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

  Lemma Rvector_inner_zero (x:vector R n) : x ⋅ 0 = 0%R.
  Proof.
    unfold Rvector_inner; simpl.
    rewrite Rvector_mult_zero.
    apply Rvector_sum0.
  Qed.

  Lemma Rvector_inner_one_r (x:vector R n) : x ⋅ vector_const 1%R n = ∑ x.
  Proof.
    unfold Rvector_inner.
    f_equal.
    apply vector_nth_eq; intros.
    rewrite Rvector_nth_mult.
    rewrite vector_nth_const.
    lra.
  Qed.

  Lemma Rvector_inner_one_l (x:vector R n) : vector_const 1%R n ⋅ x = ∑ x.
  Proof.
    rewrite Rvector_inner_comm.
    apply Rvector_inner_one_r.
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

  Lemma Rvector_scale_mult_r (a:R) (x y:vector R n) :
    (x * (a .* y)) = a .* (x * y).
  Proof.
    apply vector_eq; simpl.
    rewrite combine_map_r.
    repeat rewrite map_map.
    apply map_ext; intros [??]; simpl.
    lra.
  Qed.

  Lemma Rvector_scale_sum (a:R) (x:vector R n) :
    ∑ (a .* x) = Rmult a (∑ x).
  Proof.
    unfold Rvector_sum.
    destruct x; simpl.
    now rewrite list_sum_mult_const.
  Qed.

  Lemma Rvector_inner_scal (x y:vector R n) (l:R) : (l .* x) ⋅ y = Rmult l (x ⋅ y).
  Proof.
    unfold Rvector_inner.
    now rewrite Rvector_scale_mult_l, Rvector_scale_sum.
  Qed.

  Lemma Rvector_scal_one c : c .* vector_const 1 n = vector_const c n.
  Proof.
    apply vector_nth_eq; intros.
    rewrite vector_nth_const.
    unfold Rvector_scale.
    rewrite vector_nth_map, vector_nth_const.
    lra.
  Qed.

  Lemma Rvector_scale_const (c1 c2 : R) :
    c1 .* vector_const c2 n = vector_const (c1 * c2)%R n.
  Proof.
    apply vector_nth_eq; intros.
    rewrite vector_nth_const.
    unfold Rvector_scale.
    rewrite vector_nth_map, vector_nth_const.
    lra.
  Qed.

  Lemma Rvector_inner_const_l (x:vector R n) c : vector_const c n ⋅ x = (c * ∑ x)%R.
  Proof.
    now rewrite <- Rvector_scal_one, Rvector_inner_scal, Rvector_inner_one_l.
  Qed.

  Lemma Rvector_inner_const_r (x:vector R n) c : x ⋅ vector_const c n  = (c * ∑ x)%R.
  Proof.
    rewrite Rvector_inner_comm.
    apply Rvector_inner_const_l.
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

  Lemma Rvector_mult_plus_distr_l (x y z : vector R n) :
    x * (y + z) =  (x * y) + (x * z).
  Proof.
    rewrite Rvector_mult_comm.
    rewrite Rvector_mult_plus_distr_r.
    now repeat rewrite (Rvector_mult_comm x _).
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

  Definition Rvector_filter_part {T} (F:(vector T n -> Prop) -> Prop) i (pf:(i < n)%nat) : (T -> Prop) -> Prop
    := fun (s:T->Prop) =>
         F (fun v => s (vector_nth i pf v)).

  Definition Rvector_lim (F:(vector R n -> Prop) -> Prop) : vector R n
    := vector_create 0 n
                     (fun i _ pf =>
                        Hierarchy.lim (Rvector_filter_part F i pf
                     )).

  Lemma Rvector_filter_part_Filter {T} (F:(vector T n -> Prop) -> Prop) i pf :
    Filter F ->
    Filter (Rvector_filter_part F i pf).
  Proof.
    unfold Rvector_filter_part.
    intros [???].
    constructor; intros; auto.
    - eapply filter_imp; try eapply H0.
      simpl; intros; eauto.
  Qed.
      
  Lemma Rvector_filter_part_ProperFilter {T} (F:(vector T n -> Prop) -> Prop) i pf :
    ProperFilter F ->
    ProperFilter (Rvector_filter_part F i pf).
  Proof.
    unfold Rvector_filter_part.
    intros [??].
    constructor.
    - intros.
      destruct (filter_ex _ H).
      eauto.
    - now apply Rvector_filter_part_Filter.
  Qed.


    Lemma minus_nth (x x0 : vector R n) (i:nat) (pf : (i < n)%nat):
    minus (vector_nth i pf x0) (vector_nth i pf x) =
    vector_nth i pf (minus x0 x).
  Proof.
    unfold minus, plus, opp; simpl.
    rewrite Rvector_plus_explode.
    rewrite vector_nth_create'.
    unfold Rvector_opp, Rvector_scale.
    rewrite vector_nth_map.
    now ring_simplify.
  Qed.
    
  Lemma mult_nth (x x0 : vector R n) (i:nat) (pf : (i < n)%nat):
    ((vector_nth i pf x0) * (vector_nth i pf x))%R =
    vector_nth i pf (Rvector_mult x0 x).
  Proof.
    rewrite Rvector_mult_explode.
    now rewrite vector_nth_create'.
  Qed.

  (* move *) 
  Lemma list_sum_pos_In_le (l:list R) (a:R) 
        (all_pos : forall a : R, In a l -> 0 <= a):
    In a l ->
    a <= RealAdd.list_sum l.
  Proof.
    induction l; simpl; inversion 1; simpl in *.
    - subst.
      generalize (list_sum_pos_pos' l); intros HH.
      cut_to HH.
      + lra.
      + rewrite Forall_forall; eauto.
    - cut_to IHl; trivial.
      + specialize (all_pos a0).
        cut_to all_pos; auto; try lra.
      + eauto. 
  Qed.

  Program Lemma vector_nth_pos_le_pos (v:vector R n) i pf :
    (forall a, In a v -> 0%R <= a) ->
    vector_nth i pf v <= ∑ v.
  Proof.
    unfold vector_nth, proj1_sig.
    destruct v; simpl.
    match_destr; simpl in *.
    intros all_pos.
    symmetry in e0.
    apply nth_error_In in e0.
    unfold Rvector_sum; simpl.
    now apply list_sum_pos_In_le.
  Qed.

  Lemma Hnorm_nth1 (x : vector R n) (eps0 : posreal) (i:nat) (pf : (i < n)%nat):
      Hnorm x < eps0 ->
      abs (vector_nth i pf x) < eps0.
  Proof.
    unfold Hnorm.
    unfold abs; simpl.
    intros.
    eapply Rle_lt_trans; [|apply H].
    rewrite <- sqrt_Rsqr_abs.
    apply sqrt_le_1_alt.
    unfold Rsqr, inner; simpl.
    unfold Rvector_inner.
    rewrite mult_nth.
    apply vector_nth_pos_le_pos; intros.
    rewrite <- Rvector_sqr_mult in H0.
    now apply Rvector_sqr_pos in H0.
  Qed.    
  
  Lemma Hnorm_nth (x x0 : vector R n) (eps0 : posreal) (i:nat) (pf : (i < n)%nat):
      Hnorm (minus x x0) < eps0 ->
      Hierarchy.ball (vector_nth i pf x) eps0 (vector_nth i pf x0).
  Proof.
    intros.
    repeat red.
    rewrite abs_minus.
    rewrite minus_nth.
    now apply Hnorm_nth1.
  Qed.


  Lemma list_sum_bound_const_lt (l : list R)
        (c : R) :
    l <> nil ->
    (forall a : R, In a l -> a < c) ->
    RealAdd.list_sum l < c * INR (length l).
  Proof.
    intros nnil bounded.
    induction l; simpl in *; try congruence.
    destruct l; simpl.
    - ring_simplify.
      auto.
    - simpl in *.
      cut_to IHl; try congruence; auto.
      specialize (bounded a).
      cut_to bounded; auto.
      lra.
  Qed.

  Lemma list_sum_bound_const_le (l : list R)
        (c : R) :
    l <> nil ->
    (forall a : R, In a l -> a <= c) ->
    RealAdd.list_sum l <= c * INR (length l).
  Proof.
    intros nnil bounded.
    induction l; simpl in *; try congruence.
    destruct l; simpl.
    - ring_simplify.
      auto.
    - simpl in *.
      cut_to IHl; try congruence; auto.
      specialize (bounded a).
      cut_to bounded; auto.
      lra.
  Qed.

  Program Lemma Rvector_sum_bound_const_lt (x:vector R n) c :
    n <> 0%nat ->
    (forall a, In a x -> (a < c)%R) ->
    ∑ x < (c * INR n)%R.
  Proof.
    intros.
    unfold Rvector_sum.
    destruct x; simpl in *.
    subst.
    apply list_sum_bound_const_lt; trivial.
    destruct x; simpl in *; congruence.
  Qed.

  Program Lemma Rvector_sum_bound_const_le (x:vector R n) c :
    n <> 0%nat ->
    (forall a, In a x -> (a <= c)%R) ->
    ∑ x <= (c * INR n)%R.
  Proof.
    intros.
    unfold Rvector_sum.
    destruct x; simpl in *.
    subst.
    apply list_sum_bound_const_le; trivial.
    destruct x; simpl in *; congruence.
  Qed.

  Lemma Nth_Hnorm1 (x : vector R n) (eps : posreal) :
    (0 < n)%nat ->
    (forall (i : nat) (pf : (i < n)%nat),
        abs (vector_nth i pf x) < eps / INR n) ->
    Hnorm x < eps.
  Proof.
    unfold Hnorm, abs; simpl; intros.
    unfold inner; simpl.
    unfold Rvector_inner.
    rewrite <- sqrt_Rsqr with (x := eps); [|left; apply cond_pos].
    apply sqrt_lt_1_alt.
    split; [apply Rvector_inner_pos | ].
    assert (INR n <> 0)%R.
    {
    apply Rgt_not_eq.
    now apply lt_0_INR.
    }
    replace (Rsqr eps) with ((Rsqr eps / INR n) * (INR n))%R by
        (unfold Rdiv; rewrite Rmult_assoc, Rinv_l; lra).
    apply Rvector_sum_bound_const_lt; try lia.
    intros.
    apply In_vector_nth_ex in H2.
    destruct H2 as [i [pf H2]].
    rewrite <- H2.
    rewrite <- mult_nth.
    specialize (H0 i pf).
    replace (eps / INR n) with (Rabs (eps / INR n)) in H0.
    apply  Rsqr_lt_abs_1 in H0.
    unfold Rsqr at 1 in H0.
    eapply Rlt_le_trans.
    apply H0.
    unfold Rdiv.
    rewrite Rsqr_mult.
    apply Rmult_le_compat_l; [apply Rle_0_sqr |].
    rewrite Rsqr_inv; trivial.
    apply Rinv_le_contravar; [now apply lt_0_INR |].
    unfold Rsqr; replace (INR n) with ((INR n) * 1)%R at 1 by lra.
    apply Rmult_le_compat_l; [apply pos_INR |].
    assert (1 <= n)%nat by lia.
    now apply le_INR in H3.
    apply Rabs_right.
    unfold Rdiv.
    apply Rle_ge.
    apply Rmult_le_pos.
    left; apply cond_pos.
    left. apply Rinv_pos.
    apply INR_zero_lt; lia.
  Qed.

  Lemma Nth_Hnorm (v x : vector R n) (eps : posreal) :
    (0 < n)%nat ->
    (forall (i : nat) (pf : (i < n)%nat),
        Hierarchy.ball (vector_nth i pf v) (eps / INR n) (vector_nth i pf x)) ->
    Hnorm (minus v x) < eps.
  Proof.
    unfold Hierarchy.ball; simpl.
    unfold AbsRing_ball; simpl.
    intros.
    apply Nth_Hnorm1; trivial.
    intros.
    rewrite <- minus_nth.
    now rewrite (abs_minus (vector_nth i pf v)).
  Qed.

  Lemma Rvector_filter_part_cauchy (F:(PreHilbert_UniformSpace -> Prop) -> Prop) i pf :
    Filter F ->
    cauchy F ->
    cauchy (Rvector_filter_part F i pf).
  Proof.
    unfold Rvector_filter_part.
    unfold cauchy; intros fil cf eps.
    destruct (cf eps).
    exists (vector_nth i pf x).
    apply filter_imp with (P := (fun y : vector R n => Hnorm (minus x y) < eps)).
    intros.
    now apply Hnorm_nth.
    apply H.
  Qed.

  Lemma Rvector_inner_self (x:vector R n) : x ⋅ x = ∑ x².
  Proof.
    unfold Rvector_inner.
    now rewrite <- Rvector_sqr_mult.
  Qed.

  (*
  Lemma Rvector_lim_complete 
             (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (Rvector_lim F) eps).
  Proof.
    intros pff cf eps.
    generalize (fun i pf =>  Hierarchy.complete_cauchy
                            (Rvector_filter_part F i pf)
                            (Rvector_filter_part_ProperFilter F i pf pff)
                            (Rvector_filter_part_cauchy F i pf (Hierarchy.filter_filter) cf)
               )
    ; intros HH.

    unfold Rvector_lim.
    unfold ball.

    unfold Hnorm, inner; simpl.
    eapply filter_imp; intros.
    - rewrite Rvector_inner_self.
      unfold minus, plus; simpl.
      unfold Rvector_filter_part.
      rewrite <- vector_map_create.
      apply H.
    - unfold Rvector_filter_part at 1 in HH.

(*     complete_cauchy : *)

*)

  Lemma Filter_Forall_commute_aux F P :
    Filter F ->
    (forall (i : nat) (pf : (i < n)%nat),
        F (fun v : vector R n =>
             P i pf (vector_nth i pf v))) ->
    forall m (pf2:(m <= n)%nat),
    F (fun v : vector R n =>
         forall (i : nat) (pf : (i < m)%nat),
           P i (lt_le_trans _ _ _ pf pf2) (vector_nth i (lt_le_trans _ _ _ pf pf2) v)).
  Proof.
    intros [???] FA.
    induction m; simpl; intros mle.
    - generalize filter_true.
      apply filter_imp; intros.
      lia.
    - assert (pft:(forall i, i < m -> i < S m)%nat) by lia.
      cut ( F
              (fun v : vector R n =>
                 P m mle (vector_nth m mle v) /\
                 forall (i : nat) (pf : (i < m)%nat),
                   P i (Nat.lt_le_trans i (S m) n (pft _ pf) mle) (vector_nth i (Nat.lt_le_trans i (S m) n (pft _ pf) mle) v))).
      + apply filter_imp; intros.
        generalize (lt_n_Sm_le _ _ pf); intros pf2.
        apply le_lt_or_eq in pf2.
        destruct H.
        destruct pf2.
        * generalize (H0 _ H1).
          now replace ((pft i H1)) with pf by apply le_uniqueness_proof.
        * subst.
          now replace (Nat.lt_le_trans m (S m) n pf mle) with mle by apply le_uniqueness_proof.
      + apply filter_and; trivial.
        assert (pf3:(m <= n)%nat) by lia.
        specialize (IHm pf3).
        revert IHm.
        apply filter_imp; intros.
        specialize (H _ pf).
        now replace ((Nat.lt_le_trans i (S m) n (pft i pf) mle)) with (Nat.lt_le_trans i m n pf pf3)
          by apply le_uniqueness_proof.
  Qed.

  Lemma Filter_Forall_commute F P :
    Filter F ->
    (forall (i : nat) (pf : (i < n)%nat),
        F (fun v : vector R n =>
             P i pf (vector_nth i pf v))) ->
    F (fun v : vector R n =>
         forall (i : nat) (pf : (i < n)%nat),
           P i pf (vector_nth i pf v)).
  Proof.
    intros.
    generalize (Filter_Forall_commute_aux _ _ H H0 n (le_refl n)).
    destruct H.
    apply filter_imp; intros.
    specialize (H i pf).
    now replace  (Nat.lt_le_trans i n n pf (Nat.le_refl n)) with pf in H
      by apply le_uniqueness_proof.
  Qed.
  
  Lemma Rvector_lim_complete_pos (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    (0 < n)%nat ->
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (Rvector_lim F) eps).
  Proof.
    unfold cauchy; intros.
    assert (FF:Filter F).
    {
      destruct H0; trivial.
    } 
      assert (0 < eps/INR n).
      {
        unfold Rdiv.
        apply Rmult_lt_0_compat.
        apply cond_pos.
        apply Rinv_0_lt_compat, lt_0_INR; lia.
      }
      assert (forall i (pf: (i<n)%nat),
                 Rvector_filter_part F i pf (Hierarchy.ball (R_complete_lim (Rvector_filter_part F i pf)) 
                                          (mkposreal _ H2))).
      {
        intros.
        apply R_complete.
        now apply filtermap_proper_filter.
        intros.
        specialize (H1 eps0).
        destruct H1 as [x H1].
        exists (vector_nth i pf x).
        unfold Rvector_filter_part.
        apply filter_imp with (P := (fun y : vector R n => Hnorm (minus x y) < eps0)).
        intros.
        now apply Hnorm_nth.
        apply H1.
      }
      simpl in H3.
      unfold Rvector_lim.
      unfold lim; simpl.
      unfold Rvector_filter_part at 1 in H3.
      generalize (Filter_Forall_commute 
                    F
                    (fun i pf x =>
                       Hierarchy.ball (R_complete_lim (Rvector_filter_part F i pf)) (eps / INR n) x)); trivial; intros HF.
      eapply filter_imp; try eapply HF; intros; trivial.
      unfold ball; simpl.
      unfold Hierarchy.lim; simpl.
      simpl in H4.
      apply Nth_Hnorm; trivial.
      intros.
      specialize (H4 i pf).
      now rewrite vector_nth_create'.
  Qed.

  Lemma vector_zero0 (n0:n = 0%nat) (v:vector R n) : v = 0.
  Proof.
    apply vector_nth_eq; intros; lia.
  Qed.

  Lemma Rvector_lim_complete (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (Rvector_lim F) eps).
  Proof.
    destruct (Nat.eq_dec n 0).
    - intros.
      destruct H as [?[???]].
      generalize filter_true.
      apply filter_imp; intros.
      rewrite (vector_zero0 e (Rvector_lim (fun x : vector R n -> Prop => F x))).
      rewrite (vector_zero0 e x).
      apply ball_center.
    - apply Rvector_lim_complete_pos.
      lia.
  Qed.

Definition Rvector_Hilbert_mixin : Hilbert.mixin_of Rvector_PreHilbert
    := Hilbert.Mixin Rvector_PreHilbert Rvector_lim Rvector_lim_complete.

  Canonical Rvector_Hilbert :=
    Hilbert.Pack (vector R n) (Hilbert.Class _ _ Rvector_Hilbert_mixin) (vector R n).  

End Rvector_defs.

Section more_lemmas.
  
  Lemma Rvector_mult_rsqr {n} (v : vector R n) :
    Rvector_mult v v = vector_map Rsqr v.
  Proof.
    rewrite Rvector_mult_explode.
    apply vector_nth_eq; intros.
    rewrite vector_nth_create; simpl.
    rewrite vector_nth_map.
    rewrite vector_nth_ext with (pf2 := pf).
    now unfold Rsqr.
  Qed.
  
  Lemma rsqr_Rvector_max_abs {n:nat} (v : vector R n) :
    Rsqr (Rvector_max_abs v) = Rvector_max_abs (vector_map Rsqr v).
  Proof.
    unfold Rvector_max_abs.
    destruct v as [l pfl]; simpl in *.
    unfold vector_fold_left, vector_map, Rvector_abs; simpl.
    clear pfl.
    assert (HH:forall a, 0 <= a -> (fold_left Rmax (map Rabs l) a)² = fold_left Rmax (map Rabs (map Rsqr l)) (Rsqr a)).
    - induction l; simpl in *; trivial; intros.
      rewrite IHl.
      f_equal.
      unfold Rmax.
      repeat match_destr.
      + rewrite <- Rsqr_abs.
        now rewrite <- Rabs_sqr.
      + elim n0.
        rewrite <- Rabs_sqr.
        apply Rsqr_le_abs_1.
        now rewrite (Rabs_pos_eq _ H).
      + rewrite <- Rabs_sqr in r.
        apply Rsqr_le_abs_0 in r.
        now rewrite (Rabs_pos_eq _ H) in r.
      + apply Rmax_Rle; eauto.
    - specialize (HH 0).
      rewrite Rsqr_0 in HH.
      apply HH.
      lra.
  Qed.

  Lemma Rvector_max_abs_in_le {n} (v:vector R n) a :
    In a (proj1_sig v) ->
    Rabs a <= Rvector_max_abs v.
  Proof.
    unfold Rvector_max_abs, vector_fold_left.
    destruct v; simpl.
    intros.
    apply fold_left_Rmax_le.
    now apply in_map.
  Qed.

  Lemma Rvector_max_abs_nth_le {n} (v:vector R n) i pf:
    Rabs (vector_nth i pf v) <= Rvector_max_abs v.
  Proof.
    apply Rvector_max_abs_in_le.
    apply vector_nth_In.
  Qed.


  Lemma Rvector_max_abs_in {n} (v:vector R (S n)) :
    In (Rvector_max_abs v) (proj1_sig (vector_map Rabs v)).
  Proof.
    destruct v; simpl.
    destruct x; simpl; try discriminate.
    unfold Rvector_max_abs, vector_fold_left; simpl.
    clear e.
    induction x using rev_ind; simpl.
    - unfold Rmax.
      match_destr; eauto.
      elim n0.
      apply Rabs_pos.
    - rewrite map_app.
      rewrite fold_left_app.
      destruct IHx.
      + rewrite <- H.
        simpl.
        unfold Rmax.
        match_destr.
        * right.
          apply in_app_iff; simpl; eauto.
        * eauto.
      + simpl.
        right.
        unfold Rmax at 1.
        match_destr.
        * apply in_app_iff; simpl; eauto.
        * apply in_app_iff; simpl; eauto.
  Qed.

  Lemma Rvector_max_abs_nth_in {n} (v:vector R (S n)) :
    exists i pf, Rvector_max_abs v = Rabs (vector_nth i pf v).
  Proof.
    generalize (Rvector_max_abs_in v)
    ; intros HH.
    apply In_vector_nth_ex in HH.
    destruct HH as [?[? eqq]].
    symmetry in eqq.
    rewrite vector_nth_map in eqq.
    eauto.
  Qed.

  Lemma Rvector_max_abs_le {n} (v1 v2 : vector R (S n)) :
    (forall i pf, Rabs (vector_nth i pf v1) <= Rabs (vector_nth i pf v2)) ->
    Rvector_max_abs v1 <= Rvector_max_abs v2.
  Proof.
    intros.
    destruct (Rvector_max_abs_nth_in v1) as [? [??]].
    rewrite H0.
    eapply Rle_trans.
    apply H.
    apply Rvector_max_abs_nth_le.
  Qed.

  Lemma Rvector_max_abs_const {n} (c : R) :
    Rvector_max_abs (vector_const c (S n)) = Rabs c.
  Proof.
    destruct (Rvector_max_abs_nth_in (vector_const c (S n))) as [?[? eqq]].
    rewrite eqq.
    now rewrite vector_nth_const.
  Qed.

  Program Lemma Rvector_sum_pos_in_le {n} x (v : vector R n) :
    (forall a, In a v -> 0%R <= a) ->
    In x v ->
    x <= Rvector_sum v.
  Proof.
    unfold Rvector_sum.
    destruct v as [l lpf]; simpl.
    apply list_sum_pos_In_le.
  Qed.

  
  Lemma Rvector_max_abs_nth_Rabs_le {n} (v : vector R (S n)) (c:R) :
    Rvector_max_abs v <= c <->
    forall (i : nat) (pf : (i < S n)%nat),
      Rabs (vector_nth i pf v) <= c.
  Proof.
    split; intros.
    - eapply Rle_trans.
      apply Rvector_max_abs_nth_le.
      apply H.
    - destruct (Rvector_max_abs_nth_in v) as [? [? ?]].
      rewrite H0.
      apply H.
  Qed.
    
  Lemma Rvector_max_abs_nonneg {n} (v: vector R n) : 0 <= Rvector_max_abs v.
  Proof.
    unfold Rvector_max_abs, vector_fold_left.
    destruct v as [l lpf]; simpl; clear lpf.
    apply fold_left_Rmax_init_le.
  Qed.

  Lemma Rabs_Rvector_max_abs {n} (v : vector R n) :
    Rabs (Rvector_max_abs v) = Rvector_max_abs v.
  Proof.
    rewrite Rabs_right; trivial.
    apply Rle_ge.
    apply Rvector_max_abs_nonneg.
  Qed.

  Lemma sqr_max_abs_le_inner {n:nat} (v : vector R n) :
    (Rvector_max_abs v)² <= Rvector_inner v v.
  Proof.
    rewrite rsqr_Rvector_max_abs.
    unfold Rvector_inner.
    rewrite <- Rvector_sqr_mult.
    unfold Rvector_sqr.
    destruct n.
    - destruct v.
      destruct x; simpl in *; try discriminate.
      vm_compute; eauto.
    - apply Rvector_sum_pos_in_le.
      + intros.
        apply In_vector_nth_ex in H.
        destruct H as [?[??]]; subst.
        rewrite vector_nth_map.
        apply Rle_0_sqr.
      + generalize (Rvector_max_abs_in (vector_map Rsqr v))
        ; intros inn.
        rewrite vector_map_map in inn.
        erewrite (vector_map_ext' (fun x : R => Rabs x²)) in inn
        ; try eapply inn; intros; simpl.
        now rewrite <- Rabs_sqr.
  Qed.

  Lemma inner_le_sqr_max_abs {n:nat} (v : vector R n) :
    Rvector_inner v v <= INR n * (Rvector_max_abs v)².
  Proof.
    rewrite rsqr_Rvector_max_abs.
    unfold Rvector_inner.
    rewrite <- Rvector_sqr_mult.
    unfold Rvector_sqr.
    rewrite Rmult_comm.
    destruct n.
    - destruct v.
      destruct x; simpl in *; try discriminate.
      vm_compute; lra.
    - apply Rvector_sum_bound_const_le.
      + congruence.
      + intros.
        eapply Rle_trans; try eapply Rle_abs.
        now apply Rvector_max_abs_in_le.
  Qed.        

  Lemma inner_le_mult_max_abs {n:nat} (v w : vector R n) :
    Rvector_inner v w <= (Rvector_max_abs v) * (Rvector_max_abs w) * INR n.
  Proof.
    unfold Rvector_inner.
    destruct n.
    - destruct v; destruct w.
      destruct x; simpl; unfold Rvector_sum, Rvector_mult; simpl; try rewrite Rabs_R0; try lra.
      generalize (length_zero_iff_nil (r :: x) ); intros.
      destruct H.
      specialize (H e).
      discriminate.
    - apply Rvector_sum_bound_const_le; try lia.
      intros.
      eapply Rle_trans; try eapply Rle_abs.      
      unfold Rvector_mult in H.
      simpl in H.
      apply in_map_iff in H.
      destruct H as [? [? ?]].
      destruct x.
      rewrite <- H.
      rewrite Rabs_mult.
      apply Rmult_le_compat; try apply Rabs_pos.
      + generalize (in_combine_l _ _ _ _ H0); intros.
        now apply Rvector_max_abs_in_le.
      + generalize (in_combine_r _ _ _ _ H0); intros.      
        now apply Rvector_max_abs_in_le.      
  Qed.        

  Lemma abs_inner_le_mult_max_abs {n:nat} (v w : vector R n) :
    Rabs (Rvector_inner v w) <= (Rvector_max_abs v) * (Rvector_max_abs w) * INR n.
  Proof.
    destruct (Rle_dec 0 (Rvector_inner v w)).
    - rewrite Rabs_right; try lra.
      apply inner_le_mult_max_abs.
    - rewrite Rabs_left; try lra.
      replace (- Rvector_inner v w) with ((-1) * Rvector_inner v w) by lra.
      rewrite <- Rvector_inner_scal.
      assert (Rvector_max_abs (Rvector_scale (-1) v) = Rvector_max_abs v).
      {
        unfold Rvector_max_abs.
        f_equal.
        unfold Rvector_abs, Rvector_scale.
        rewrite vector_map_map.
        apply vector_map_ext.
        intros.
        rewrite Rabs_mult.
        replace (-1) with (Ropp 1) by lra.
        rewrite Rabs_Ropp, Rabs_R1; lra.
      }
      rewrite <- H.
      apply inner_le_mult_max_abs.      
  Qed.        

  Lemma max_abs_le_sqrt_inner {n:nat} (v : vector R n) :
    (Rvector_max_abs v) <= Rsqrt (mknonnegreal (Rvector_inner v v) (Rvector_inner_pos v)).
  Proof.
    replace (Rvector_max_abs v) with
        (nonneg (mknonnegreal (Rvector_max_abs v) (Rvector_max_abs_nonneg v))) by reflexivity.
    apply Rsqr_le_to_Rsqrt; simpl.
    apply sqr_max_abs_le_inner.
  Qed.

  Lemma vector_nth_sum_n {n:nat} i pf k (f:nat->vector R n) :
    vector_nth i pf (sum_n f k) =
    sum_n (fun j => vector_nth i pf (f j)) k.
  Proof.
    unfold sum_n, sum_n_m, Iter.iter_nat, plus, zero; simpl.
    generalize (0%nat).
    induction k; simpl; intros.
    - now rewrite Rvector_nth_plus, Rvector_nth_zero. 
    - rewrite Rvector_nth_plus.
      now rewrite IHk.
  Qed.
  
  Lemma Rvector_max_abs_zero {n} (v : vector R n) :
    Rvector_max_abs v = 0 <-> v = Rvector_zero.
  Proof.
    split; intros HH.
    - apply vector_nth_eq; intros.
      generalize (vector_nth_In v i pf); intros HH2.
      generalize (Rvector_max_abs_in_le _ _ HH2).
      rewrite HH; intros HH3.
      rewrite Rvector_nth_zero.
      assert (Rabs (vector_nth i pf v)=0).
      {
        apply antisymmetry; trivial.
        apply Rabs_pos.
      }
      now apply Rabs_eq_0 in H.
    - destruct n.
      + rewrite (vector0_0 v); reflexivity.
      + destruct (Rvector_max_abs_nth_in v) as [?[? eqq]].
        rewrite eqq, HH.
        rewrite Rvector_nth_zero.
        now rewrite Rabs_R0.
  Qed.

 Lemma Rvector_max_abs_nzero {n} (v : vector R n) :
   v <> Rvector_zero -> Rvector_max_abs v <> 0.
 Proof.
   unfold not.
   intros.
   apply Rvector_max_abs_zero in H0.
   now apply H in H0.
 Qed.

  Lemma Rvector_max_abs_scale {n} c (v : vector R n) :
    Rvector_max_abs (Rvector_scale c v) = Rabs c * Rvector_max_abs v.
  Proof.
    destruct v.
    unfold Rvector_scale, vector_map, Rvector_max_abs, vector_fold_left; simpl.
    clear e.
    cut (forall s,
            0 <= s ->
             fold_left Rmax (map Rabs (map (fun a : R => c * a) x)) (Rabs c * s) =
               Rabs c * fold_left Rmax (map Rabs x) s).
    {
      intros.
      rewrite <- H by lra.
      now rewrite Rmult_0_r.
    }
    induction x; simpl; trivial; intros.
    rewrite Rabs_mult.
    rewrite <- IHx.
    - now rewrite <- Rmult_max_distr_l by apply Rabs_pos.
    - rewrite H.
      apply Rmax_l.
  Qed.

  Lemma Rvector_max_abs_scale_nneg {n} (c:nonnegreal) (v : vector R n) :
    Rvector_max_abs (Rvector_scale c v) = c * Rvector_max_abs v.
  Proof.
    rewrite (Rvector_max_abs_scale c v).
    rewrite Rabs_pos_eq; trivial.
    apply cond_nonneg.
  Qed.

  Lemma Rvector_max_abs_triang {n} (v1 v2 : vector R n) :
    Rvector_max_abs (Rvector_plus v1 v2) <= Rvector_max_abs v1 + Rvector_max_abs v2.
  Proof.
    destruct n.
    - rewrite (vector0_0 _).
      rewrite (vector0_0 v1).
      rewrite (vector0_0 v2).
      vm_compute; lra.
    - destruct (Rvector_max_abs_nth_in (Rvector_plus v1 v2)) as [?[? eqq]].
      rewrite eqq, Rvector_nth_plus, Rabs_triang.
      apply Rplus_le_compat
      ; apply Rvector_max_abs_nth_le.
  Qed.

  Lemma Rvector_max_abs_triang_inv {n} (v1 v2 : vector R n) :
    Rvector_max_abs v1 - Rvector_max_abs v2 <= Rvector_max_abs (Rvector_minus v1 v2).
  Proof.
    generalize (Rvector_max_abs_triang (Rvector_minus v1 v2) v2); intros.
    replace (Rvector_plus (Rvector_minus v1 v2) v2) with v1 in H; try lra.
    unfold Rvector_minus.
    rewrite <- Rvector_plus_assoc.
    rewrite Rvector_inv_plus.
    now rewrite Rvector_plus_zero.
  Qed.

  Lemma Rvector_max_abs_plus_nneg {n} (v : vector R (S n)) (c : R) :
    0 <= c ->
    Rvector_max_abs (Rvector_plus (Rvector_abs v) (vector_const c (S n))) =
      Rvector_max_abs v + c.
  Proof.
    intros c_nneg.
    unfold Rvector_max_abs, Rvector_abs, vector_fold_left; simpl.
    destruct v; simpl.
    destruct x; [discriminate |].
    simpl.
    assert (length x = n) by auto with arith.
    clear e.
    rewrite <- H.
    clear H.
    repeat rewrite fold_symmetric by apply Rmax_assoc || apply Rmax_comm.
    induction x; simpl.
    - repeat rewrite Rmax_right by apply Rabs_pos.
      apply Rabs_pos_eq.
      generalize (Rabs_pos r).
      lra.
    - rewrite vector_list_create_const_shift with (start2:=1%nat).
      replace (vector_list_create 1 (length x)
                 (fun (m : nat) (_ : (1 <= m)%nat) (_ : (m < 1 + length x)%nat) => c))
        with (vector_list_create 1 (length x)
                (fun (m : nat) (_ : (1 <= m)%nat) (_ : (m < S (length x))%nat) => c))
      by now apply vector_list_create_ext.
      rewrite IHx.
      generalize (fold_right Rmax (Rmax 0 (Rabs r)) (map Rabs x)); intros.
      rewrite (Rabs_pos_eq (Rabs a + c)).
      + now rewrite Rplus_max_distr_r.
      + generalize (Rabs_pos a).
        lra.
  Qed.

  Lemma Rvector_max_abs_sqr {n} (v : vector R n) :
    Rvector_max_sqr v = Rsqr (Rvector_max_abs v).
  Proof.
    unfold Rvector_max_sqr, Rvector_max_abs, Rvector_sqr, Rvector_abs.
    destruct v; simpl.
    unfold vector_fold_left, vector_map; simpl.
    clear e.
    rewrite <- Rsqr_0 at 1.
    assert (0 <= 0) by lra.
    revert H.
    generalize 0 at 2 3 4.
    induction x; simpl; trivial.
    intros.
    rewrite <- IHx.
    - f_equal.
      rewrite max_abs_sqr.
      rewrite Rabs_right; trivial.
      lra.
    - rewrite H.
      apply Rmax_l.
  Qed.
  
  Lemma Rvector_max_abs_opp {n} (v : vector R n) :
    Rvector_max_abs (Rvector_opp v) = Rvector_max_abs v.
  Proof.
    unfold Rvector_opp.
    rewrite Rvector_max_abs_scale.
    rewrite Rabs_m1.
    lra.
  Qed.

    Lemma Rvector_max_spec {n} (v : vector R (S n)) :
      forall i pf,
        vector_nth i pf v <= Rvector_max v.
   Proof.
     intros.
     apply Rmax_spec.
     apply vector_nth_In.
   Qed.

  Lemma Rvector_min_spec {n} (v : vector R (S n)) :
      forall i pf,
        vector_nth i pf v >= Rvector_min v.
   Proof.
     intros.
     apply Rmin_spec.
     apply vector_nth_In.
   Qed.

  Lemma Rvector_max_in {n} (v:vector R (S n)) :
    In (Rvector_max v) (proj1_sig v).
  Proof.
    unfold Rvector_max.
    apply Rmax_list_In.
    destruct v; simpl.
    destruct x; simpl; try discriminate.
  Qed.

  Lemma Rvector_min_in {n} (v:vector R (S n)) :
    In (Rvector_min v) (proj1_sig v).
  Proof.
    unfold Rvector_min.
    apply Rmin_list_In.
    destruct v; simpl.
    destruct x; simpl; try discriminate.
  Qed.

  Lemma Rvector_max_nth_in {n} (v:vector R (S n)) :
    exists i pf, Rvector_max v = vector_nth i pf v.
  Proof.
    generalize (Rvector_max_in v)
    ; intros HH.
    apply In_vector_nth_ex in HH.
    destruct HH as [?[? eqq]].
    symmetry in eqq.
    eauto.
  Qed.

  Lemma Rvector_min_nth_in {n} (v:vector R (S n)) :
    exists i pf, Rvector_min v = vector_nth i pf v.
  Proof.
    generalize (Rvector_min_in v)
    ; intros HH.
    apply In_vector_nth_ex in HH.
    destruct HH as [?[? eqq]].
    symmetry in eqq.
    eauto.
  Qed.

  Lemma vector_max_min {n} (l1 l2 : vector R (S n)) : 
    Rabs ((Rvector_min l1) - (Rvector_min l2)) <=
      Rvector_max (vector_map (fun '(x,y) => Rabs(x - y)) (vector_zip l1 l2)).
  Proof.
    unfold Rvector_min, Rvector_max.
    destruct l1; destruct l2; simpl.
    apply max_min_list2.
    - destruct x; simpl in *; congruence.
    - congruence.
  Qed.


End more_lemmas.

Section rvinner_stuff.
  Context {n : nat}.
  Canonical Rvector_NormedModule := @PreHilbert_NormedModule (@Rvector_PreHilbert n).

   Lemma rv_inner_plus_l (x y z : vector R n) :
     Rvector_inner (Rvector_plus x y) z = 
     (Rvector_inner x z) + (Rvector_inner y z).
   Proof.
     apply (inner_plus_l x y z).
   Qed.

    Lemma rv_inner_plus_r (x y z : vector R n) :
     Rvector_inner x (Rvector_plus y z) = 
     (Rvector_inner x y) + (Rvector_inner x z).
    Proof.
      apply (inner_plus_r x y z).
    Qed.
   
   Lemma rv_inner_scal_l (x y : vector R n) (l : R) :
     Rvector_inner (Rvector_scale l x) y = l * Rvector_inner x y.
   Proof.
     apply (inner_scal_l x y l).
   Qed.

   Lemma rv_inner_scal_r (x y : vector R n) (l : R) :
     Rvector_inner x (Rvector_scale l y) = l * Rvector_inner x y.
   Proof.
     apply (inner_scal_r x y l).
   Qed.

   Lemma rv_inner_sym (x y : vector R n) :
     Rvector_inner x y = Rvector_inner y x.
   Proof.
     apply (inner_sym x y).
   Qed.

   Lemma rv_inner_ge_0 (x : vector R n) :
      0 <= Rvector_inner x x.
   Proof.
     apply (inner_ge_0 x).
   Qed.

End rvinner_stuff.

Section veclim.
  
  Lemma lim_seq_maxabs0 {n} (X : nat -> vector R n) :
    is_lim_seq (fun m => Rvector_max_abs (X m)) 0 ->
    forall i pf,
      is_lim_seq (fun m => vector_nth i pf (X m)) 0.
  Proof.
    intros.
    apply is_lim_seq_abs_0.
    apply is_lim_seq_le_le with 
      (u := const 0) 
      (w := fun m : nat => Rvector_max_abs (X m))
    ; trivial; [| apply is_lim_seq_const].
    intros.
    split.
    + unfold const; apply Rabs_pos.
    + apply Rvector_max_abs_nth_le.
  Qed.

  Lemma lim_seq_maxabs0_b {n} (X : nat -> vector R n) :
    (forall i pf,
      is_lim_seq (fun m => vector_nth i pf (X m)) 0) ->
    is_lim_seq (fun m => Rvector_max_abs (X m)) 0.
  Proof.
    intros.
    apply is_lim_seq_spec.
    intros eps.
    assert (HH:forall (i : nat) (pf : (i < n)%nat),
               eventually (fun m : nat => Rabs (vector_nth i pf (X m)) < eps)).
    {
      intros i pf.
      specialize (H i pf).
      apply is_lim_seq_spec in H.
      specialize (H eps).
      simpl in H.
      revert H.
      apply eventually_impl, all_eventually; intros.
      now rewrite Rminus_0_r in H.
    }
    apply bounded_nat_ex_choice_vector in HH.
    destruct HH as [v HH].
    exists (list_max (proj1_sig v)).
    intros n0 n0ge.
    destruct n.
    - destruct (Rvector_max_abs_zero (X n0)) as [? HH2].
      rewrite HH2.
      + rewrite Rminus_0_r, Rabs_R0.
        apply cond_pos.
      + apply vector_eq; simpl.
        now rewrite (vector0_0 (X n0)); simpl.
    - destruct (Rvector_max_abs_nth_in (X n0)) as [?[? eqq]].
      rewrite Rminus_0_r.
      rewrite eqq.
      rewrite Rabs_Rabsolu.
      apply HH.
      rewrite <- n0ge.
      generalize (list_max_upper (proj1_sig v)); intros HH2.
      rewrite Forall_forall in HH2.
      apply HH2.
      apply vector_nth_In.
  Qed.
  
  Lemma lim_seq_maxabs {n} (X : nat -> vector R n) (x: vector R n) :
    is_lim_seq (fun m => Rvector_max_abs (Rvector_minus (X m) x)) 0 <->
    forall i pf,
      is_lim_seq (fun m => vector_nth i pf (X m)) (vector_nth i pf x).
  Proof.
    split; intros.
    - generalize (lim_seq_maxabs0 (fun m => Rvector_minus (X m) x) H i pf); intros.
      generalize (is_lim_seq_const (vector_nth i pf x)); intros.
      generalize (is_lim_seq_plus' _ _ _ _  H0 H1); intros.
      rewrite Rplus_0_l in H2.
      revert H2.
      apply is_lim_seq_ext.
      intros.
      rewrite Rvector_nth_minus.
      lra.
    - apply lim_seq_maxabs0_b.
      intros.
      specialize (H i pf).
      generalize (is_lim_seq_const (vector_nth i pf x)); intros.
      generalize (is_lim_seq_minus' _ _ _ _  H H0); intros.
      setoid_rewrite Rvector_nth_minus.
      now rewrite Rminus_eq_0 in H1.
  Qed.

End veclim.
