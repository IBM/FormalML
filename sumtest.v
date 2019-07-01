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
      *
Admitted.

Lemma RiemannInt_pn1 f (n:nat) (pr1:Riemann_integrable f 1 (2 + INR n)) :
  forall (C0:forall x:R, 1 <= x <= 2 + (INR n) -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= 2 + (INR n) -> x<=y -> f y <= f x)
    -> RiemannInt pr1 <= sum_f 1 (n+1) (fun j:nat => f (INR j)).
Proof.
  intros.
  induction n; simpl.
  - assert (eqq:(2 + INR 0)=2) by (compute; lra).
    generalize pr1; intros pr1'.
    rewrite eqq in pr1.
    
    generalize (RiemannInt_p1 _ _ pr1); intros.
    cut_to H0.
    + Opaque RiemannInt.
      compute.
      Transparent RiemannInt.
      eapply Rle_trans; [| eapply H0].
      clear.
      revert pr1 pr1'.
Admitted.

Lemma RiemannInt_cont_pn1 f (n:nat) :
  forall (C0:forall x:R, 1 <= x <= 1 + (INR n) -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= 1 + (INR n) -> x<=y -> f y <= f x)
    -> RiemannInt (@continuity_implies_RiemannInt f 1 (1 + (INR n)) (ale2 n) C0) <= 
       sum_f 1 n (fun j:nat => f (INR j)).
Proof.
  intros.
  
  
Qed.
  

Lemma RiemannInt_cont_pn2 :
  forall f (n:nat) (h:0 < INR n)
    (C0:forall x:R, 1 <= x <= INR n -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= INR n -> x<=y -> f y <= f x)
    -> (f 1) + RiemannInt (@continuity_implies_RiemannInt f 1 (INR n) h C0) >= 
       sum_f 1 n (fun j:nat => f (INR j)).
Admitted.

(* then take limits as n-> \infty *)
  
(* 
S n = sum_{k=1}^n f(k), I n = integ_1^n f(x)dx
positive_lb f 1 /\ continuity_lb f 1 /\ decreasing_lb f 1 ->
    I (n+1) <= S n <= f(1) + I n 
*)








