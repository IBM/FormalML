Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.RInt.
Require Import Coquelicot.RInt_analysis.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Derive.

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

SearchAbout Derive.

Definition erf' (x:R) := (2 / sqrt PI) * exp(-x^2).
Definition erf (x:R) := RInt erf' 0 x.
Lemma erf_pinfty : erf (p_infty) = 1.
Admitted.
Lemma erf_minfty : erf (m_infty) = -1.
Admitted.

(* following is standard normal density, i.e. has mean 0 and std=1 *)
(* CDF(x) = RInt Standard_Gaussian_PDF -infty x *)
Definition Standard_Gaussian_PDF (t:R) := (/ (sqrt (2*PI))) * exp (-t^2/2).

(* general gaussian density with mean = mu and std = sigma *)
Definition General_Gaussian_PDF (mu sigma t : R) :=
   (/ (sigma * (sqrt (2*PI)))) * exp (- (t - mu)^2/(2*sigma^2)).

  
Lemma gen_from_std (mu sigma : R) :
   sigma > 0 -> forall x:R,  General_Gaussian_PDF mu sigma x = 
                             / sigma * Standard_Gaussian_PDF ((x-mu)/sigma).
Proof.
  intros.
  assert (sigma <> 0).
  apply Rgt_not_eq; trivial.
  assert (PI > 0).
  apply PI_RGT_0.
  assert (sqrt(2*PI) <> 0).
  apply Rgt_not_eq.
  apply sqrt_lt_R0.
  lra.
  unfold General_Gaussian_PDF.
  unfold Standard_Gaussian_PDF.
  field_simplify.
  unfold Rdiv.
  apply Rmult_eq_compat_r.
  apply f_equal.
  field_simplify; trivial.
  lra.
  lra.
Qed.  

(* standard normal distribution *)
Definition Standard_Gaussian_CDF (t:R) := RInt Standard_Gaussian_PDF m_infty t.

Lemma std_from_erf :
  forall x:R, Standard_Gaussian_CDF x = (/ 2) * (1 + erf (x/sqrt 2)).
Proof.
  intros.
  unfold Standard_Gaussian_CDF.
  unfold erf.
  unfold Standard_Gaussian_PDF.
  unfold erf'.
  Admitted.

(* generates 2 gaussian samples from 2 uniform samples *)
(* with mean 0 and variance 1 *)
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

Lemma continuous_Standard_Gaussian_PDF :
  forall (x:R), continuous Standard_Gaussian_PDF x.
Proof.
  intros.
  unfold Standard_Gaussian_PDF.
  apply continuous_mult with (f:= fun t => / sqrt (2*PI)) (g:=fun t=> exp(-t^2/2)).
  apply continuous_const.
  apply continuous_comp with (g := exp).
  unfold Rdiv.
  apply continuous_mult with (f := fun t => -t^2) (g := fun t => /2).
  apply continuous_opp with (f := fun t =>  t^2).
  apply continuous_mult with (f := id).
  apply continuous_id.
  apply continuous_mult with (f := id).
  apply continuous_id.
  apply continuous_const.
  apply continuous_const.  
  apply ex_derive_continuous with (f := exp) (x0 := -x^2/2).
  apply ex_derive_Reals_1.
  unfold derivable_pt.
  unfold derivable_pt_abs.
  exists (exp (- x ^ 2 / 2)).
  apply derivable_pt_lim_exp.
Qed.

Lemma ex_RInt_Standard_Gaussian_PDF (a b:R) :
    a <= b -> ex_RInt Standard_Gaussian_PDF a b.
Proof.
  intros.
  apply ex_RInt_continuous with (f:=Standard_Gaussian_PDF).
  intros.
  apply continuous_Standard_Gaussian_PDF.
Qed.

Lemma continuous_Standard_Gaussian_mean_PDF : 
  forall (x:R), continuous (fun t => t * (Standard_Gaussian_PDF t)) x.
Proof.  
  intros.
  apply continuous_scal with (f:=Standard_Gaussian_PDF).
  apply continuous_id.
  apply continuous_Standard_Gaussian_PDF.
Qed.

Lemma continuous_Standard_Gaussian_variance_PDF : 
  forall (x:R), continuous (fun t => t^2 * (Standard_Gaussian_PDF t)) x.
Proof.  
  intros.
  apply continuous_scal with  (f:=Standard_Gaussian_PDF).
  unfold pow.
  apply continuous_scal with  (f:=fun y=> y*1).
  apply continuous_id.
  apply continuous_scal with  (f:=fun y=> 1).
  apply continuous_id.
  apply continuous_const.
  apply continuous_Standard_Gaussian_PDF.
Qed.

Lemma ex_RInt_Standard_Gaussian_mean_PDF (a b:R) :
    a <= b -> ex_RInt (fun t => t * (Standard_Gaussian_PDF t)) a b.
Proof.
  intros.
  apply ex_RInt_continuous with (f := fun t => t * (Standard_Gaussian_PDF t)).
  intros.
  apply continuous_Standard_Gaussian_mean_PDF.
Qed.

Lemma ex_RInt_Standard_Gaussian_variance_PDF (a b:R) :
    a <= b -> ex_RInt (fun t => t^2 * (Standard_Gaussian_PDF t)) a b.
Proof.
  intros.
  apply ex_RInt_continuous with (f := fun t => t^2 * (Standard_Gaussian_PDF t)).
  intros.
  apply continuous_Standard_Gaussian_variance_PDF.
Qed.

Definition oddfun (f : R -> R) : Prop := forall x:R, f(-x) = - f (x).

Lemma odd_mean_standard_gaussian : oddfun (fun t => t * (Standard_Gaussian_PDF t)).
Proof.  
  unfold oddfun.
  intros.
  rewrite Ropp_mult_distr_l.
  apply Rmult_eq_compat_l with (r1 := Standard_Gaussian_PDF (-x)) (r2 := Standard_Gaussian_PDF x).  
  unfold Standard_Gaussian_PDF.
  apply Rmult_eq_compat_l.
  replace ((-x)^2) with (x^2) by lra.
  trivial.
Qed.

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
  0 <= t -> RInt (fun t => t * (Standard_Gaussian_PDF t)) (-t) t = 0.
Proof.
  intros.
  apply odd_integral; trivial.
  apply ex_RInt_Standard_Gaussian_mean_PDF; lra.
  apply odd_mean_standard_gaussian.
Qed.

Lemma variance_exint0 (a b:Rbar) :
  a <= b ->
  ex_RInt (fun t => (t^2-1)*Standard_Gaussian_PDF t) a b.
Proof.
  intros.
  assert (ex_RInt (fun t => t^2*Standard_Gaussian_PDF t - Standard_Gaussian_PDF t) a b).
  apply ex_RInt_minus with (f := fun t=> t^2*Standard_Gaussian_PDF t)
                           (g := Standard_Gaussian_PDF).
  apply ex_RInt_Standard_Gaussian_variance_PDF; trivial.
  apply ex_RInt_Standard_Gaussian_PDF; trivial.
  apply ex_RInt_ext with (f := (fun t : R => t ^ 2 * Standard_Gaussian_PDF t - Standard_Gaussian_PDF t)) (g := (fun t : R => (t ^ 2 - 1) * Standard_Gaussian_PDF t)).
  intros.
  lra.
  trivial.
Qed.  

Lemma variance_int0 (a b:Rbar) :
  a <= b -> 
  RInt (fun t => t^2*Standard_Gaussian_PDF t) a b =
  RInt (fun t => (t^2-1)*Standard_Gaussian_PDF t) a b +
  RInt (fun t => Standard_Gaussian_PDF t) a b.
Proof.
  intros.
  replace (RInt (fun t : R => t ^ 2 * Standard_Gaussian_PDF t) a b) with
      (RInt (fun t : R => (t^2-1)*Standard_Gaussian_PDF t + Standard_Gaussian_PDF t) a b).
  apply RInt_plus with (f := (fun t => (t^2-1)*Standard_Gaussian_PDF t))
                       (g := (fun t => Standard_Gaussian_PDF t)).
  apply variance_exint0; trivial.
  apply ex_RInt_Standard_Gaussian_PDF; trivial.
  apply RInt_ext.
  intros.
  lra.
Qed.

Lemma derivable_pt_std_nmean (x:R) : 
  derivable_pt (fun t => -t*Standard_Gaussian_PDF t) x.
Proof.  
  apply derivable_pt_mult.
  apply derivable_pt_opp.
  apply derivable_pt_id.
  unfold Standard_Gaussian_PDF.
  apply derivable_pt_mult.
  apply derivable_pt_const.
  apply derivable_pt_comp with (f1 := (fun t => -t^2/2)).
  apply derivable_pt_div.
  apply derivable_pt_opp.
  apply derivable_pt_mult.
  apply derivable_pt_id.
  apply derivable_pt_mult.
  apply derivable_pt_id.
  apply derivable_pt_const.
  apply derivable_pt_const.    
  lra.
  apply derivable_pt_exp.
Qed.

SearchAbout PI.

Lemma variance_derive (x:R) : 
      Derive (fun t => -t*Standard_Gaussian_PDF t) x = (x^2-1)*Standard_Gaussian_PDF x.
Proof.
  assert (PI > 0).
  apply PI_RGT_0.         
  assert (sqrt(2*PI) <> 0).
  apply Rgt_not_eq.
  apply sqrt_lt_R0.
  lra.
  rewrite -> Derive_mult with (f := fun t => -t) (g := Standard_Gaussian_PDF).
  rewrite Derive_opp.
  rewrite Derive_id.
  ring_simplify.
  unfold Rminus.
  rewrite -> Rplus_comm with (r1 := Standard_Gaussian_PDF x * x ^ 2).
  apply Rplus_eq_compat_l.
  unfold Standard_Gaussian_PDF.
  rewrite Derive_mult.
  rewrite Derive_const.
  ring_simplify.
  rewrite Derive_comp.
  rewrite Derive_div.
  rewrite Derive_const.
  rewrite Derive_opp.
  rewrite Derive_mult.
  rewrite Derive_mult.
  rewrite Derive_id.
  rewrite Derive_const.
  field_simplify.
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (-x^2/2)).
  rewrite derive_pt_exp.
  field_simplify.
  reflexivity.
  lra.
  assert (ex_derive (fun x => x * 1) x).
  apply ex_derive_mult.    
  apply ex_derive_id.
  apply ex_derive_const.
  trivial.
  trivial.
  trivial.
  apply ex_derive_id.
  apply ex_derive_const.
  apply ex_derive_id.
  apply ex_derive_mult.    
  apply ex_derive_id.
  apply ex_derive_const.
  apply ex_derive_opp with (f:=fun y => y^2).
  apply ex_derive_mult.
  apply ex_derive_id.
  apply ex_derive_mult.
  apply ex_derive_id.
  apply ex_derive_const.
  apply ex_derive_const.  
  lra.
Admitted.
  
Lemma variance_int1 (x:R):
  RInt (fun t => (t^2*exp(-t^2/2))) 0 x = 
  -x*exp(-x^2/2) + RInt (fun t => exp(-t^2/2)) 0 x.
Admitted.


Lemma limxexp_inf : is_lim (fun t => t*exp(-t^2/2)) p_infty 0.
Proof.
   unfold is_lim.
  unfold filterlim.
  unfold filter_le.
  unfold filtermap.
  intros.
  unfold Rbar_locally'.
  unfold Rbar_locally.
  unfold locally.
  unfold ball.
  intros.
  destruct H.
  unfold UniformSpace.ball in H.
Admitted.
  
Lemma limxexp_minf : is_lim (fun t => t*exp(-t^2/2)) m_infty 0.
Admitted.


