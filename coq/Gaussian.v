Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.RInt.
Require Import Coquelicot.Continuity.


Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Reals.R_sqrt.
Require Import Streams.
Require Import Ranalysis_reg.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import Rtrigo1.
Require Import Ranalysis1.
Require Import Lra Omega.


Require Import Utils.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Implicit Type f : R -> R.

(* following PDF has mean 0 and variance .5, CDF = erf(x) *)
(* integrating from -infinity to infinity *)
Definition Gaussian_PDF := fun t => (/ (sqrt PI)) * exp(-t^2).

(* generates 2 gaussian samples from 2 uniform samples *)
(* with mean 0 and variance .5 *)
Definition Box_Muller (uniform1 uniform2: R) : (R * R) :=
  let r := sqrt (-2 * (ln uniform1)) in
  let theta := 2 * PI * uniform2 in
  (r * cos theta, r * sin theta).

CoFixpoint mkGaussianStream (uniformStream : Stream R) : Stream R :=
  let u1 := hd uniformStream in
  let ust2 := tl uniformStream in
  let u2 := hd ust2 in
  let ust3 := tl ust2 in
  let '(g1,g2) := Box_Muller u1 u2 in
  Cons g1 (Cons g2 (mkGaussianStream ust3)).


Lemma continuity_id : continuity id.
Proof.
  apply derivable_continuous.    
  apply derivable_id.
Qed.

Lemma continuity_Gaussian_PDF : continuity Gaussian_PDF.
Proof.
  unfold Gaussian_PDF.
  apply continuity_mult.
  apply continuity_const.
  unfold constant; trivial.
  apply continuity_comp  with (f2 := fun x => exp x).
  apply continuity_opp.
  apply continuity_mult.
  apply continuity_id.
  apply continuity_mult.
  apply continuity_id.
  apply continuity_const.
  unfold constant; trivial.
  apply derivable_continuous.  
  unfold derivable.
  intros.
  unfold derivable_pt.
  unfold derivable_pt_abs.
  exists (exp x).
  apply derivable_pt_lim_exp.
Qed.

(* SearchAbout continuity_pt.*)

Lemma continuous_Gaussian_PDF :
  forall (x:R), continuous Gaussian_PDF x.
Proof.
  intros.
  apply continuity_pt_filterlim.
  assert (continuity Gaussian_PDF).
  apply continuity_Gaussian_PDF.
  unfold continuity in *.
  trivial.
Qed.  


Lemma Riemann_integrable_Gaussian_PDF (a b:R) :
    a <= b -> Riemann_integrable Gaussian_PDF a b.
Proof.
  intros.
  apply continuity_implies_RiemannInt; trivial.
  intros.
  apply continuity_Gaussian_PDF.
Qed.

Lemma ex_RInt_Gaussian_PDF (a b:R) :
    a <= b -> ex_RInt Gaussian_PDF a b.
Proof.
  intros.
  apply ex_RInt_continuous with (f:=Gaussian_PDF).
  intros.
  apply continuous_Gaussian_PDF.
Qed.


Lemma continuity_Gaussian_mean_PDF : continuity (fun t => t * (Gaussian_PDF t)).
Proof.  
  apply continuity_mult.
  apply continuity_id.
  apply continuity_Gaussian_PDF.
Qed.

Lemma continuous_Gaussian_mean_PDF : 
  forall (x:R), continuous (fun t => t * (Gaussian_PDF t)) x.
Proof.  
  intros.
  apply continuous_scal with (f:=Gaussian_PDF).
  apply continuous_id.
  apply continuous_Gaussian_PDF.
Qed.

Lemma continuous_Gaussian_variance_PDF : 
  forall (x:R), continuous (fun t => t^2 * (Gaussian_PDF t)) x.
Proof.  
  intros.
  apply continuous_scal with  (f:=Gaussian_PDF).
  unfold pow.
  apply continuous_scal with  (f:=fun y=> y*1).
  apply continuous_id.
  apply continuous_scal with  (f:=fun y=> 1).
  apply continuous_id.
  apply continuous_const.
  apply continuous_Gaussian_PDF.
Qed.


Lemma Riemann_integrable_Gaussian_mean_PDF (a b:R) :
    a <= b -> Riemann_integrable (fun t => t * (Gaussian_PDF t)) a b.
Proof.
  intros.
  apply continuity_implies_RiemannInt; trivial.
  intros.
  apply continuity_Gaussian_mean_PDF.
Qed.

Lemma ex_RInt_Gaussian_mean_PDF (a b:R) :
    a <= b -> ex_RInt (fun t => t * (Gaussian_PDF t)) a b.
Proof.
  intros.
  apply ex_RInt_continuous with (f := fun t => t * (Gaussian_PDF t)).
  intros.
  apply continuous_Gaussian_mean_PDF.
Qed.


Lemma Riemann_integrable_Gaussian_PDF_sym (t:R) :
  Riemann_integrable Gaussian_PDF (-t) t.
Proof.
  destruct (Rle_dec (-t) t).
  apply Riemann_integrable_Gaussian_PDF; trivial.  
  apply RiemannInt_P1.  
  apply Riemann_integrable_Gaussian_PDF;lra.
Qed.

Definition erf (t:R) := RiemannInt (Riemann_integrable_Gaussian_PDF_sym t).

Lemma ex_RInt_Gaussian_PDF_sym (t:R) :
  ex_RInt Gaussian_PDF (-t) t.
Proof.
  destruct (Rle_dec (-t) t).
  apply ex_RInt_Gaussian_PDF; trivial.
  apply ex_RInt_swap.
  apply ex_RInt_Gaussian_PDF; lra.
Qed.

Definition erf2 (t:R) := RInt Gaussian_PDF (-t) t.

Definition oddfun (f : R -> R) : Prop := forall x:R, f(-x) = - f (x).

Lemma odd_mean_gaussian : oddfun (fun t => t * (Gaussian_PDF t)).
Proof.
  unfold oddfun.
  intros.
  rewrite Ropp_mult_distr_l.
  apply Rmult_eq_compat_l with (r1 := Gaussian_PDF (-x)) (r2 := Gaussian_PDF x).
  unfold Gaussian_PDF.
  apply Rmult_eq_compat_l.
  cut ((- (-x)^2) = -x^2).
  intuition.
  lra.
Qed.

(*SearchAbout ex_RInt.*)

Lemma RInt_comp_opp (f : R -> R) (a b : R) :
  ex_RInt f (-a) (-b) ->
  RInt f (-a) (-b) = RInt (fun y => - (f (- y))) a b.
Proof.
  intros.
  symmetry.
  apply is_RInt_unique.
  apply: is_RInt_comp_opp.
  exact: RInt_correct.    
Qed.

Lemma negate_arg (t:R) (f:R -> R): 
  ex_RInt f 0 (-t) -> 
  RInt (fun t => - (f (- t))) 0 t = RInt f 0 (-t).
Proof.  
  intros.
  symmetry.
  replace (0) with (- 0) at 1 by lra.
  apply RInt_comp_opp with (a:=0) (b:=t) (f := f).
  ring_simplify.
  trivial.
Qed.

(* SearchAbout ex_RInt.*)

Lemma odd_integral (t:R) (f : R-> R):
  0 <= t ->
  ex_RInt f (-t) t ->
  oddfun f -> RInt f (-t) t = 0.
Proof.  
  unfold oddfun.
  intros.
  assert(le_chain:- t <= 0 <= t) by lra.
  assert (fneg: ex_RInt f (- t) 0).
  {  apply ex_RInt_Chasles_1 with (a := -t) (b := 0) (c := t) (f0 := f); trivial. }
  assert (fpos:ex_RInt f 0 t).
  {  apply ex_RInt_Chasles_2 with (a := -t) (b := 0) (c := t) (f0 := f); trivial. }
  assert (fnegswap: ex_RInt f 0 (- t)).
  {  apply ex_RInt_swap. trivial. }
  assert (fopp: ex_RInt (fun x : R => f (- x)) 0 t).
  { apply ex_RInt_ext with (g:=(fun x => f (-x))) (a:=0) (b:=t) (f0 := (fun x => - f x)).
    - intuition.
    - apply ex_RInt_opp with (f0 := f) (a := 0) (b := t).  trivial.
  }
  rewrite <- RInt_Chasles with (b := 0) by trivial.
  rewrite <- opp_RInt_swap by trivial.
  rewrite <- negate_arg by trivial.
  rewrite RInt_opp; trivial.
  rewrite opp_opp.
  rewrite <- RInt_plus by trivial.
  rewrite -> RInt_ext with (g:=(fun x => 0)).
  - rewrite RInt_const; intuition.
  - intros. rewrite H1. intuition.
Qed.

(* proves that normalized gaussian has zero mean *)
Lemma zero_mean_gaussian (t:R):
  0 <= t -> RInt (fun t => t * (Gaussian_PDF t)) (-t) t = 0.
Proof.
  intros.
  apply odd_integral; trivial.
  apply ex_RInt_Gaussian_mean_PDF; lra.
  apply odd_mean_gaussian.
Qed.
