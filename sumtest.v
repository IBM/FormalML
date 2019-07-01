Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Arith.
Require Export Rlimit.
Require Export Rderiv.
Require Import Ranalysis_reg.
Require Import Reals.Integration.

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


Lemma continuity_implies_RiemannInt :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall x:R, a <= x <= b -> continuity_pt f x) -> Riemann_integrable f a b.
Admitted.

(*
Lemma RiemannInt_P19 :
  forall (f g:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b),
    a <= b ->
    (forall x:R, a < x < b -> f x <= g x) -> RiemannInt pr1 <= RiemannInt pr2.
Admitted.
*)

Lemma RiemannInt_p1 :
  forall f (a:R) (pr1:Riemann_integrable f a (a+1)),
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt pr1 <= f a .
Admitted.

Lemma RiemannInt_p2 :
  forall f (a:R) (pr1:Riemann_integrable f a (a+1)),
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt pr1 >= f (a+1) .
Admitted.  

Lemma RiemannInt_cont_p1 :
  forall f (a:R) (h:a <= a+1)
    (C0:forall x:R, a <= x <= a+1 -> continuity_pt f x),
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt (continuity_implies_RiemannInt f a (a+1) h C0) <= f a .
Admitted.

Lemma RiemannInt_cont_p2 :
  forall f (a:R) (h:a <= a+1)
    (C0:forall x:R, a <= x <= a+1 -> continuity_pt f x),
    (forall x y :R, a <= x -> y <= a+1 -> x<=y -> f y <= f x)
    -> RiemannInt (continuity_implies_RiemannInt f a (a+1) h C0) >= f (a+1) .
Admitted.

Lemma RiemannInt_cont_pn1 :
  forall f (n:nat) (h:1 <= 1 + (INR n))
    (C0:forall x:R, 1 <= x <= 1 + (INR n) -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= 1 + (INR n) -> x<=y -> f y <= f x)
    -> RiemannInt (continuity_implies_RiemannInt f 1 (1 + (INR n)) h C0) <= 
       sum_f 1 n (fun j:nat => f (INR j)).
Admitted.

Lemma RiemannInt_cont_pn2 :
  forall f (n:nat) (h:1 <= INR n)
    (C0:forall x:R, 1 <= x <= INR n -> continuity_pt f x),
    (forall x y :R, 1 <= x -> y <= INR n -> x<=y -> f y <= f x)
    -> (f 1) + RiemannInt (continuity_implies_RiemannInt f 1 (INR n) h C0) >= 
       sum_f 1 n (fun j:nat => f (INR j)).
Admitted.

(* then take limits as n-> \infty *)
  
(* 
S n = sum_{k=1}^n f(k), I n = integ_1^n f(x)dx
positive_lb f 1 /\ continuity_lb f 1 /\ decreasing_lb f 1 ->
    I (n+1) <= S n <= f(1) + I n 
*)








