Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Ranalysis_reg.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import SeqProp.
Require Import Coquelicot.Coquelicot.

Require Import Lra Lia.
Require Import Utils.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Implicit Type f : R -> R.

Lemma RiemannInt_p1 f (a:R) (pr1:Riemann_integrable f a (a+1)) :
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt pr1 <= f a .
Proof.
  intros.
  assert (pr2:Riemann_integrable (fun _ : R => f a) a (a + 1)).
  { apply continuity_implies_RiemannInt.
    - lra.
    - intros.
      apply continuity_pt_const.
      red; trivial.
  } 
  generalize (@RiemannInt_P19 f (fun x => f a) a (a+1) pr1 pr2); intros HH.
  cut_to HH.
  - generalize (RiemannInt_P15 pr2).
    unfold fct_cte; intros eqq; rewrite eqq in HH; clear eqq.
    replace (f a * (a + 1 - a)) with (f a) in HH by lra.
    trivial.
  - lra.
  - intros.
    apply H; lra.
Qed.

Lemma RiemannInt_p2 f (a:R) (pr1:Riemann_integrable f a (a+1)) :
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt pr1 >= f (a+1).
Proof.
  intros.
  assert (pr2:Riemann_integrable (fun _ : R => f (a+1)) a (a + 1)).
  { apply continuity_implies_RiemannInt.
    - lra.
    - intros.
      apply continuity_pt_const.
      red; trivial.
  } 
  generalize (RiemannInt_P19 pr2 pr1); intros HH.
  cut_to HH.
  - generalize (RiemannInt_P15 pr2).
    unfold fct_cte; intros eqq; rewrite eqq in HH; clear eqq.
    replace (f (a+1) * (a + 1 - a)) with (f (a+1)) in HH by lra.
    lra.
  - lra.
  - intros.
    apply H; lra.
Qed.

Lemma RiemannInt_pn1 f (n:nat) (pr1:Riemann_integrable f 1 (2 + INR n)) :
    (forall x y :R, 1 <= x -> y <= 2 + (INR n) -> x<=y -> f y <= f x)
    -> RiemannInt pr1 <= sum_f 1 (n+1) (fun j:nat => f (INR j)).
Proof.
  revert pr1.
  induction n; simpl.
  - assert (eqq:(2 + 0)=2) by (compute; lra).
    rewrite eqq.
    intros.
    generalize (RiemannInt_p1 _ _ pr1); intros.
    cut_to H0.
    + auto.
    + intros.
      apply H; lra.
  - intros.
    replace (match n with
                                    | 0%nat => 1
                                    | S _ => INR n + 1
             end) with (INR n + 1) in *
      by repeat (destruct n; simpl; try lra).
    assert (leqs:1 <= (2 + INR n) <= (2 + match n with
                                    | 0%nat => 1
                                    | S _ => INR n + 1
                      end)).
    { destruct n.
      - simpl; split; intros; lra.
      - rewrite <- Rplus_assoc.
        split; intros; [ | lra].
        replace 1 with (1+0) by lra.
        apply Rplus_le_compat; [lra | ].
        apply pos_INR.
    }
    generalize (RiemannInt_P22 pr1 leqs); intros pr2.
    specialize (IHn pr2).
    cut_to IHn.
    + unfold sum_f in *.
      replace ((S (n + 1) - 1)%nat) with ((S n)%nat) by lia.
      replace ((n + 1 - 1)%nat) with (n%nat) in IHn by lia.
      simpl.
      assert (eqn:match n with
                  | 0%nat => 1
                  | S _ => INR n + 1
                  end = INR n + 1).
      { destruct n; trivial; simpl; lra. }
      assert (pr3:Riemann_integrable f (2 + INR n)
        (2 + match n with 
             | 0%nat => 1
             | S _ => INR n + 1
             end)).
      {
        apply (@RiemannInt_P23 f 1  (2 + match n with
                                        | 0%nat => 1
                                        | S _ => INR n + 1
                                         end)); trivial.
      } 
      generalize (RiemannInt_P26 pr2 pr3 pr1); intros eqr.
      rewrite <- eqr.
      clear pr1 eqr.
      apply Rplus_le_compat; trivial.
      revert pr3 H; clear.
      assert (eqn:2 + match n with
                  | 0%nat => 1
                  | S _ => INR n + 1
                  end = (2 + INR n) + 1).
      { destruct n.
        - simpl; lra.
        - lra.
      }
      rewrite eqn.
      intros pr3 H.
      replace (match (n + 1)%nat with
                      | 0%nat => 1
                      | S _ => INR (n + 1) + 1
               end) with (2 + INR n).
      * apply (RiemannInt_p1 _ _ pr3).
        intros.
        apply H; try lra.
        eapply Rle_trans; [| eapply H0].
        replace 1 with (1 + 0) by lra.
        apply Rplus_le_compat; try lra.
        apply pos_INR.
      * { assert (forall x, match x%nat with
              | 0%nat => 1
              | S _ => INR x + 1
                            end = INR x+1).
          { destruct x; [simpl | ]; lra. }
          rewrite H0.
          rewrite plus_INR.
          simpl; lra.
        } 
    + intros.
      apply H; lra.
Qed.

Lemma RiemannInt_pn2 f (n:nat) (pr1:Riemann_integrable f 1 (2 + INR n)) :
    (forall x y :R, 1 <= x -> y <= (2 + INR n) -> x<=y -> f y <= f x)
    -> RiemannInt pr1 >= sum_f 2 (2+n) (fun j:nat => f (INR j)).
Proof.
  revert pr1.
  induction n; simpl.
  - assert (eqq:(2 + 0)=2) by (compute; lra).
    rewrite eqq.
    intros.
    generalize (RiemannInt_p2 _ _ pr1); intros.
    cut_to H0.
    + auto.
    + intros.
      apply H; trivial.
  - intros.
    replace (match n with
                                    | 0%nat => 1
                                    | S _ => INR n + 1
             end) with (INR n + 1) in *
      by repeat (destruct n; simpl; try lra).
    assert (leqs:1 <= (2 + INR n) <= (2 + match n with
                                    | 0%nat => 1
                                    | S _ => INR n + 1
                      end)).
    { destruct n.
      - simpl; split; intros; lra.
      - rewrite <- Rplus_assoc.
        split; intros; [ | lra].
        replace 1 with (1+0) by lra.
        apply Rplus_le_compat; [lra | ].
        apply pos_INR.
    }
    generalize (RiemannInt_P22 pr1 leqs); intros pr2.
    specialize (IHn pr2).
    cut_to IHn.
    + unfold sum_f in *.
      replace ( (S (S (S n)) - 2))%nat with ((S n)%nat) by lia.
      replace ((2 + n - 2)%nat) with (n%nat) in IHn by lia.
      simpl.
      assert (eqn:match (n + 2)%nat with
                  | 0%nat => 1
                  | S _ => INR (n + 2) + 1
                  end = INR (n + 2) + 1).
      { destruct n; simpl; lra. }
      assert (pr3:Riemann_integrable f (2 + INR n)
        (2 + match n with 
             | 0%nat => 1
             | S _ => INR n + 1
             end)).
      {
        apply (@RiemannInt_P23 f 1  (2 + match n with
                                        | 0%nat => 1
                                        | S _ => INR n + 1
                                         end)); trivial.
      } 
      generalize (RiemannInt_P26 pr2 pr3 pr1); intros eqr.
      rewrite <- eqr.
      clear pr1 eqr.
      apply Rplus_ge_compat; trivial.
      revert pr3 H; clear.
      assert (eqn:2 + match n with
                  | 0%nat => 1
                  | S _ => INR n + 1
                  end = (2 + INR n) + 1).
      { destruct n.
        - simpl; lra.
        - lra.
      }
      rewrite eqn.
      intros pr3 H.
      replace (match (n + 2)%nat with
                      | 0%nat => 1
                      | S _ => INR (n + 2) + 1
               end) with ((2 + INR n) + 1).
      * apply (RiemannInt_p2 _ _ pr3).
        intros.
        apply H; try lra.
        eapply Rle_trans; [| eapply H0].
        replace 1 with (1 + 0) by lra.
        apply Rplus_le_compat; try lra.
        apply pos_INR.
      * { assert (forall x, match x%nat with
              | 0%nat => 1
              | S _ => INR x + 1
                            end = INR x+1).
          { destruct x; [simpl | ]; lra. }
          rewrite H0.
          rewrite plus_INR.
          simpl; lra.
        } 
    + intros.
      apply H; lra.
Qed.

Lemma RiemannInt_pn f (n:nat) (pr1:Riemann_integrable f 1 (2 + INR n)) :
    (forall x y :R, 1 <= x -> y <= 2 + (INR n) -> x<=y -> f y <= f x)
    -> sum_f 2 (2+n) (fun j:nat => f (INR j))
       <= RiemannInt pr1 <= 
       sum_f 1 (n+1) (fun j:nat => f (INR j)).
Proof.
  split.
  - apply Rge_le.
    apply RiemannInt_pn2; trivial.
  - apply RiemannInt_pn1; trivial.
Qed.

Lemma ale21 n : 1 <= 2 + INR n.
Proof.
  generalize (pos_INR n); intros.
  lra.
Qed.

Lemma RiemannInt_cont_pn1 f (n:nat) :
  forall (C0:forall x:R, 1 <= x <= 2 + (INR n) -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= 2 + (INR n) -> x<=y -> f y <= f x)
    -> RiemannInt (@continuity_implies_RiemannInt f 1 (2 + (INR n)) (ale21 n) C0) <= 
       sum_f 1 (n+1) (fun j:nat => f (INR j)).
Proof.
  intros.
  apply RiemannInt_pn1; trivial.
Qed.
  
Lemma RiemannInt_cont_pn2 f (n:nat): 
  forall (C0:forall x:R, 1 <= x <= 2 + (INR n) -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= (2 + INR n) -> x<=y -> f y <= f x)
    -> RiemannInt (@continuity_implies_RiemannInt f 1 (2 + (INR n)) (ale21 n) C0) >=
       sum_f 2 (2+n) (fun j:nat => f (INR j)).
Proof.
  intros.
  apply RiemannInt_pn2; trivial.
Qed.

Lemma RiemannInt_cont_pn f (n:nat): 
  forall (C0:forall x:R, 1 <= x <= 2 + (INR n) -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= (2 + INR n) -> x<=y -> f y <= f x)
    ->  sum_f 2 (2+n) (fun j:nat => f (INR j))
        <= RiemannInt (@continuity_implies_RiemannInt f 1 (2 + (INR n)) (ale21 n) C0) <=
        sum_f 1 (n+1) (fun j:nat => f (INR j)).
Proof.
  split.
  - apply Rge_le.
    apply RiemannInt_cont_pn2; trivial.
  - apply RiemannInt_cont_pn1; trivial.
Qed.

Lemma sum_bound_22 n : 0 <= n -> 0 <= 2-1/(n+2) - (2-1/(n+1)) - 1/((n+2)*(n+2)).
Proof.
  intros.
  replace (2 - 1 / (n + 2) - (2 - 1 / (n + 1)) - 1 / ((n + 2) * (n + 2)))
                              with (1 / (n + 1) - 1 / (n + 2) - 1 / ((n + 2) * (n + 2))) by lra.
  field_simplify (1 / (n + 1) - 1 / (n + 2) - 1 / ((n + 2) * (n + 2))); try lra.
  rewrite (Fdiv_def Rfield).
  destruct H.
  - left.
      apply Rmult_lt_0_compat; [lra | ].
      apply Rinv_0_lt_compat.
      replace 0 with (0 + 0 + 0 + 0) by lra.
      repeat try apply Rplus_lt_compat.
      * simpl pow.
        repeat (apply Rmult_lt_0_compat; trivial).
        lra.
      * simpl pow.
        repeat (apply Rmult_lt_0_compat; trivial)
        ; lra.
      * lra.
      * lra.
  - subst. 
    simpl pow.
    lra.
Qed.

Lemma sum_f_bound n : sum_f_R0 (fun i => 1 / Rsqr (INR i+1)) n <= 2 - 1 / (INR (n + 1)).
Proof.
  induction n.
  - simpl.
    unfold Rsqr.
    lra.
  - simpl.
    replace ((match n with
       | 0%nat => 1
       | S _ => INR n + 1
              end)) with (INR n + 1).
    + replace (match (n + 1)%nat with
          | 0%nat => 1
          | S _ => INR (n + 1) + 1
               end) with (INR (n + 1) + 1).
      * replace (2 - 1 / (INR (n + 1) + 1)) with (2 - 1 / INR (n + 1) + ((2 - 1 / (INR (n + 1) + 1)) - (2 - 1 / INR (n + 1)))) by lra.
        apply Rplus_le_compat; trivial.
        generalize (sum_bound_22 (INR n)); intros sb.
        cut_to sb; [| apply pos_INR].
        replace ((INR n + 1 + 1)²) with ((INR n + 2) * (INR n + 2)); [| unfold Rsqr; lra].
        { replace (INR (n + 1) + 1) with (INR (n+2)).
          - apply (Rplus_le_compat_r (1 / ((INR n + 2) * (INR n + 2)))) in sb.
            rewrite Rplus_0_l in sb.
            eapply Rle_trans; [eapply sb |].
            clear.
            replace ( 2 - 1 / (INR n + 2) - (2 - 1 / (INR n + 1)) - 1 / ((INR n + 2) * (INR n + 2)) +
                      1 / ((INR n + 2) * (INR n + 2)) ) with
                                  (( 2 - 1 / (INR n + 2) - (2 - 1 / (INR n + 1)))) by lra.
            unfold Rminus.
            repeat rewrite Rplus_assoc.
            apply Rplus_le_compat_l.
            repeat rewrite plus_INR.
            apply Rplus_le_compat_l.
            simpl; lra.
          - repeat rewrite plus_INR; simpl; lra.
        } 
      * destruct n; simpl; trivial.
    + destruct n; simpl; trivial; lra.
Qed.

Definition f_inv := (fun x : R =>  / x).
Definition f_inv_sq := (fun x : R => / Rsqr x).

Lemma continuity_pt_inv_x a : 0 < a -> continuity_pt f_inv a.
Proof.
  intros.
  apply continuity_pt_inv.
  apply derivable_continuous_pt.
  apply derivable_pt_id.
  apply Rgt_not_eq.
  apply Rlt_gt; trivial.
Qed.

Lemma continuity_pt_inv_xsq a : 0 < a -> continuity_pt f_inv_sq a.
Proof.
  intros.
  apply continuity_pt_inv. 
  apply derivable_continuous_pt.
  apply derivable_pt_Rsqr.
  apply Rmult_integral_contrapositive; lra.
Qed.

Lemma integrable_inv a : 1 <= a -> Riemann_integrable f_inv 1 a.
Proof.
  intros.
  apply continuity_implies_RiemannInt; trivial.
  intros.
  apply continuity_pt_inv_x; lra.
Qed.

Lemma integrable_inv_sq a : 1 <= a -> Riemann_integrable f_inv_sq 1 a.
Proof.  
  intros.
  apply continuity_implies_RiemannInt; trivial.
  intros.
  apply continuity_pt_inv_xsq; lra.
Qed.

Lemma ub_sum_inv_sq (n:nat) :
   sum_f 2 (2+n) (fun j:nat => f_inv_sq (INR j))
        <= RiemannInt (@integrable_inv_sq (2 + (INR n)) (ale21 n)).
Proof.
   apply Rge_le.
   apply RiemannInt_pn2.
   intros.
   unfold f_inv_sq.
   apply Rinv_le_contravar; trivial.
   apply Rmult_lt_0_compat; lra.
   apply Rmult_le_compat; lra.
Qed.

Lemma lb_sum_inv (n:nat) :
   RiemannInt (@integrable_inv (2 + (INR n)) (ale21 n))
       <= sum_f 1 (n+1) (fun j:nat => f_inv (INR j)).
Proof.  
   apply RiemannInt_pn1.
   intros.
   unfold f_inv.
   apply Rinv_le_contravar; lra.
Qed.

Lemma ln_int_unbounded : forall x:R, 0 < x -> { y | ln y - ln 1 > x}.
Proof.
  intros.
  exists (exp(x+1)).
  rewrite ln_1.
  rewrite ln_exp.
  rewrite <- (Rplus_0_r x) at 2.
  replace (1-0) with 1; lra.
Qed.

Lemma inv_int_bounded : forall x:R, 0 < x -> 1 - (/ x) < 1.
Proof. 
  intros.
  rewrite <- (Rplus_0_r 1) at 2.
  apply Rplus_lt_compat_l.
  apply Ropp_lt_gt_0_contravar.
  apply Rinv_0_lt_compat; trivial.
Qed.

Lemma is_RInt_inv (b:R) (pr:1 <= b) :
    is_RInt Rinv 1 b ((ln b) - (ln 1)).
Proof.
  apply (@is_RInt_derive).
  rewrite Rmin_left by lra.
  rewrite Rmax_right; intuition.
  apply is_derive_Reals.
  apply derivable_pt_lim_ln; lra.
  rewrite Rmin_left by lra.
  rewrite Rmax_right; intuition.
  unfold continuous.
  apply continuity_pt_filterlim.
  apply continuity_pt_inv; try lra.
  apply continuity_pt_id.
Qed.

Lemma is_lim_RInt_inv0:
  is_lim (fun b => (ln b) - (ln 1)) p_infty p_infty.
Proof.
  apply is_lim_minus with (lf := p_infty) (lg := 0).
  apply is_lim_ln_p.
  apply (is_lim_ext (fun _ =>  0)).
  rewrite ln_1; trivial.
  apply is_lim_const.
  unfold is_Rbar_minus.
  simpl.
  replace (- 0) with (0) by lra.
  unfold is_Rbar_plus.
  now unfold Rbar_plus'.
Qed.

Lemma is_lim_RInt_inv:
  is_lim (fun b => (RInt Rinv 1 b)) p_infty p_infty.
Proof.
  apply (is_lim_ext_loc (fun b => (ln b) - (ln 1))).
  exists 2.
  intros.
  symmetry.
  apply is_RInt_unique.
  apply is_RInt_inv; lra.
  apply is_lim_RInt_inv0.
Qed.

Lemma is_RInt_inv_Rsqr (b:R) (pr:1 <= b) :
    is_RInt (fun x:R => / Rsqr x) 1 b (1 - 1 / b).
Proof.
  replace (1 - 1/b) with ((- Rinv b) - (- Rinv 1)).
  apply (@is_RInt_derive) with (f:= fun x => - Rinv x).
  rewrite Rmin_left by lra.
  rewrite Rmax_right by lra.
  intros.
  replace (/ (Rsqr x)) with (- (- 1 / x^2)).
  apply is_derive_opp with (f := fun x => / x).
  apply is_derive_inv with (f := id).
  apply (@is_derive_id).
  unfold id; lra.
  unfold Rsqr.
  field_simplify; trivial; lra.
  rewrite Rmin_left by lra.
  rewrite Rmax_right; intuition.
  unfold continuous.
  apply (continuity_pt_filterlim (fun x => / (Rsqr x))).
  apply continuity_pt_inv.  
  unfold Rsqr.
  apply continuity_pt_mult.
  apply continuity_pt_id.
  apply continuity_pt_id.
  apply Rgt_not_eq.
  apply Rmult_gt_0_compat; lra.
  field_simplify; trivial; lra.
Qed.

Lemma is_lim_Rint_inv_Rsqr0 :
  is_lim (fun b => (1 - 1 / b)) p_infty 1.
Proof.
  apply is_lim_minus with (lf := 1) (lg := 0).
  apply is_lim_const.
  apply (is_lim_ext Rinv).
  intros.
  lra.
  replace (Finite 0) with (Rbar_inv p_infty).
  apply is_lim_inv.
  apply is_lim_id.
  discriminate.
  unfold Rbar_inv; trivial.
  compute.
  apply f_equal.
  replace (Rplus R1 (Ropp R0)) with (R1); trivial; lra.
Qed.

Lemma is_lim_Rint_inv_Rsqr :
  is_lim (fun b => RInt (fun x:R => / Rsqr x) 1 b) p_infty 1.
Proof.
  apply (is_lim_ext_loc (fun b => 1 - 1/b)).
  exists 2.
  intros.
  symmetry.
  apply is_RInt_unique.
  apply is_RInt_inv_Rsqr.
  lra.
  apply is_lim_Rint_inv_Rsqr0.
Qed.  

Lemma is_RInt_gen_inv_Rsqr :
  is_RInt_gen (fun x:R => / Rsqr x) (at_point 1) (Rbar_locally' p_infty) 1.  
Proof.
  apply (is_RInt_gen_ext (Derive (fun x => - / x))).
  - exists (fun a => a=1) (fun b => b>1000).
      now unfold at_point.
      unfold Rbar_locally'.
      now exists 1000.
      unfold fst, snd. 
      intros.
      subst.
      rewrite Rmin_left in H1 by lra.
      rewrite Rmax_right in H1 by lra.
      assert (x0 <> 0).
      apply Rgt_not_eq; lra.
      rewrite Derive_opp.
      rewrite Derive_inv; try lra.
      rewrite Derive_id.
      unfold Rsqr.
      field_simplify; try lra.
      now auto_derive.
  - replace (1) with (0 - (-1)) at 2 by lra.
    apply is_RInt_gen_Derive.
    + exists (fun a => a=1) (fun b => b>1000).
      now unfold at_point.
      unfold Rbar_locally'.
      now exists 1000.
      intros.
      unfold fst, snd in H1.
      subst.
      rewrite Rmin_left in H1 by lra.
      rewrite Rmax_right in H1 by lra.
      assert (x0 <> 0).
      apply Rgt_not_eq; lra.
      auto_derive; try lra.
    + exists (fun a => a=1) (fun b => b>1000).
      now unfold at_point.
      unfold Rbar_locally'.
      now exists 1000.
      intros.
      unfold fst, snd in H1.
      subst.
      rewrite Rmin_left in H1 by lra.
      rewrite Rmax_right in H1 by lra.
      assert (x0 <> 0).
      apply Rgt_not_eq; lra.
      apply continuous_continuous_on with (D:=fun x => x>0).
      assert (0 < 1/2) by lra.
      exists (mkposreal (1/2) H2).
      intros.
      cut (Rabs (y0-x0) < 1/2).
      unfold Rabs.
      destruct (Rcase_abs (y0-x0)); lra.
      apply -> ball_Rabs; trivial.
      apply (continuous_on_ext (fun x => x > 0) (fun x => / Rsqr x)).
      * intros.
        assert (x <> 0).
        apply Rgt_not_eq; lra.
        rewrite Derive_opp.
        rewrite Derive_inv; try lra.
        rewrite Derive_id.
        unfold Rsqr.
        field_simplify; try lra.
        apply ex_derive_id.
      * apply continuous_on_forall.
        intros.
        apply (@ex_derive_continuous).
        auto_derive.
        apply Rgt_not_eq.
        now apply Rmult_gt_0_compat. 
    + unfold filterlim, filter_le.
      intros.
      unfold filtermap, at_point.
      replace (- / 1) with (-1) by lra.
      now apply locally_singleton.
    + replace (filterlim (fun x : R => - / x) (Rbar_locally' p_infty) (locally 0)) with 
          (is_lim (fun x : R => - / x) p_infty 0).
      replace (Finite 0) with (Rbar_opp 0).
      * apply is_lim_opp.
        replace (Finite 0) with (Rbar_inv p_infty).
        -- apply is_lim_inv.
           apply is_lim_id.
           discriminate.
        -- now compute.
      * compute; f_equal; lra.
      * unfold is_lim; trivial.
Qed.

(* this proves sum 1/i^2 converges to a finite limit  *)
Lemma sum_inv_sqr_bounded : 
  ex_finite_lim_seq (fun n => sum_f_R0 (fun i => 1 / Rsqr (INR i + 1)) n).
Proof.
  apply ex_finite_lim_seq_incr with (M := 2).
  intros.
  simpl.
  cut (0 <
       1 / (match n with
       | 0%nat => 1
       | S _ => INR n + 1
       end + 1)²).
  lra.
  unfold Rdiv.
  rewrite (Rmult_1_l).
  apply Rinv_0_lt_compat.
  destruct n.
  compute; lra.
  replace (INR (S n) + 1 + 1) with (INR (S n) + 2) by lra.
  apply Rlt_0_sqr.
  apply Rgt_not_eq.
  cut (0 <= INR (S n)); try lra.
  apply pos_INR.
  intros.
  apply Rle_trans with (r2 := 2 - 1 / INR (n+1)) (r3 := 2).
  apply sum_f_bound.
  apply Rminus_le.
  ring_simplify.
  apply Rge_le.
  apply Ropp_0_le_ge_contravar.
  apply Rlt_le.
  unfold Rdiv.
  rewrite (Rmult_1_l).
  replace (n+1)%nat with (S n).
  rewrite S_INR.
  apply RinvN_pos.
  intuition.
Defined.

Lemma converges_2harmonic :
  exists sum:R, infinite_sum (fun i => 1 / Rsqr (INR i + 1)) sum.
Proof.
  assert (ex_finite_lim_seq (fun n => sum_f_R0 (fun i => 1 / Rsqr (INR i + 1)) n)).
  apply sum_inv_sqr_bounded.  
  destruct H.
  exists x.
  apply infinite_sum_is_lim_seq; trivial.
Qed.
