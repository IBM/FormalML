Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Arith.
Require Export Rlimit.
Require Export Rderiv.
Require Import Ranalysis_reg.
Require Import Reals.Integration.

Require Import Lra Omega.
Require Import BasicTactics Sums.


Local Open Scope R_scope.
Implicit Type f : R -> R.

Definition lb_interval (lb x:R) : Prop := x >= lb.

Definition positive_lb f (lb:R) : Prop := forall x:R, x >= lb -> f x > 0.

Definition continuity_lb f (lb:R) : Prop := forall x:R, x >= lb -> continuity_pt f x.

Definition decreasing_lb f (lb:R) : Prop := forall x y:R, x>=lb -> x <= y -> f y <= f x.

(* sum from 1 to n of f:R -> R *)
Definition sum_f1 (n:nat) f := sum_f 1 n (fun j:nat => f (INR j)).

Definition Newton_integrable (f:R -> R) (a b:R) : Type :=
  { g:R -> R | antiderivative f g a b \/ antiderivative f g b a }.

Definition NewtonInt (f:R -> R) (a b:R) (pr:Newton_integrable f a b) : R :=
  let (g,_) := pr in g b - g a.

Definition integ_f1 (b:R) f (pr:Newton_integrable f R1 b) : R :=  NewtonInt f R1 b pr.

(*
Lemma continuity_implies_RiemannInt :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) -> Riemann_integrable f a b.
Admitted.
*)
(*
Lemma RiemannInt_P19 :
  forall (f g:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
    a <= b ->
    (forall x:R, a < x < b -> f x <= g x) -> RiemannInt pr1 <= RiemannInt pr2.
Admitted.
*)

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

Lemma ale (a:R) : a <= a + 1.
Proof.
  lra.
Qed.
  
Lemma RiemannInt_cont_p1 f (a:R) :
  forall (C0:forall x:R, a <= x <= a+1 -> continuity_pt f x),
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt (continuity_implies_RiemannInt (ale a) C0) <= f a .
Proof.
  intros.
  apply RiemannInt_p1; trivial.
Qed.

Lemma RiemannInt_cont_p2 :
  forall f (a:R)
    (C0:forall x:R, a <= x <= a+1 -> continuity_pt f x),
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt (continuity_implies_RiemannInt (ale a) C0) >= f (a+1) .
Proof.
  intros.
  apply RiemannInt_p2; trivial.
Qed.

Lemma ale2 n : 1 <= 1 + (INR n).
Proof.
  generalize (pos_INR n); intros.
  lra.
Qed.

Lemma Riemann_integrable_nil f a b : a = b -> Riemann_integrable f a b.
Proof.
  intros.
  subst.
  apply RiemannInt_P7.
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
      replace ((S (n + 1) - 1)%nat) with ((S n)%nat) by omega.
      replace ((n + 1 - 1)%nat) with (n%nat) in IHn by omega.
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
      replace ( (S (S (S n)) - 2))%nat with ((S n)%nat) by omega.
      replace ((2 + n - 2)%nat) with (n%nat) in IHn by omega.
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





