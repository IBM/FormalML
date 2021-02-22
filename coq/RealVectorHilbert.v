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

  Lemma Rvector_plus_explode (x y:vector R n) :
    x + y = vector_create 0 n (fun i _ pf => (vector_nth i pf x + vector_nth i pf y)%R).
  Proof.
    unfold Rvector_plus.
    rewrite vector_zip_explode.
    rewrite vector_map_create.
    reflexivity.
  Qed.

  Lemma Rvector_mult_explode (x y:vector R n) :
    x * y = vector_create 0 n (fun i _ pf => (vector_nth i pf x * vector_nth i pf y)%R).
  Proof.
    unfold Rvector_mult.
    rewrite vector_zip_explode.
    rewrite vector_map_create.
    reflexivity.
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
    rewrite Rvector_plus_explode.
    apply vector_nth_eq; intros.
    rewrite vector_nth_create; simpl.
    unfold Rvector_zero.
    rewrite vector_nth_const.
    rewrite Rplus_0_r.
    apply vector_nth_ext.
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

  Program Lemma In_vector_nth_ex {T} {x:vector T n} a :
    In a x ->
    exists i pf, vector_nth i pf x = a.
  Proof.
    intros inn.
    apply In_nth_error in inn.
    destruct inn as [i eqq].
    destruct x; simpl in *.
    destruct (lt_dec i (length x)).
    - subst.
      exists i, l.
      unfold vector_nth, proj1_sig.
      repeat match_destr.
      simpl in *.
      congruence.
    - assert (HH:(length x <= i)%nat) by lia.
      apply nth_error_None in HH.
      congruence.
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
    now rewrite abs_minus with (x0 := (vector_nth i pf v)).
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
  Definition Rvector_lim_complete 
             (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
    ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (Rvector_lim F) eps).
  Proof.
    intros pff cf eps.
    generalize (fun i pf =>  Hierarchy.complete_cauchy
                            (Rvector_filter_part F i pf)
                            (Rvector_filter_part_ProperFilter F i pf pff)
                            (Rvector_filter_part_cauchy F i pf pff cf)
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
*)
(*     complete_cauchy :
  Admitted.

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
  
  Lemma Rvector_lim_complete_nneg (F : (PreHilbert_UniformSpace -> Prop) -> Prop) :
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
    - apply Rvector_lim_complete_nneg.
      lia.
  Qed.

Definition Rvector_Hilbert_mixin : Hilbert.mixin_of Rvector_PreHilbert
    := Hilbert.Mixin Rvector_PreHilbert Rvector_lim Rvector_lim_complete.

  Canonical Rvector_Hilbert :=
    Hilbert.Pack (vector R n) (Hilbert.Class _ _ Rvector_Hilbert_mixin) (vector R n).  

End Rvector_defs.
