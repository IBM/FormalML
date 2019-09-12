Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.RInt.
Require Import Coquelicot.RInt_gen.
Require Import Coquelicot.RInt_analysis.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Derive.
Require Import Coquelicot.AutoDerive.
Require Import Coquelicot.ElemFct.

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

Definition erf' (x:R) := (2 / sqrt PI) * exp(-x^2).
Definition erf (x:R) := RInt erf' 0 x.

Axiom erf_pinfty : Lim erf p_infty = 1.
Axiom erf_minfty : Lim erf m_infty = -1.
Axiom erf_ex_lim : forall (x:Rbar), ex_lim erf x.

(* following is standard normal density, i.e. has mean 0 and std=1 *)
(* CDF(x) = RInt_gen Standard_Gaussian_PDF (Rbar_locally m_infty) (Rbar_locally x) *)
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
  generalize sqrt_2PI_nzero; intros.

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

Definition Standard_Gaussian_CDF (t:R) := 
  RInt_gen Standard_Gaussian_PDF (Rbar_locally m_infty) (at_point t).

Definition General_Gaussian_CDF (mu sigma : R) (t:R) := 
  RInt_gen (General_Gaussian_PDF mu sigma) (Rbar_locally m_infty) (at_point t).

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
  ex_RInt Standard_Gaussian_PDF a b.
Proof.
  intros.
  apply ex_RInt_continuous with (f:=Standard_Gaussian_PDF).
  intros.
  apply continuous_Standard_Gaussian_PDF.
Qed.

Lemma derive_xover_sqrt2 (x:R):
  Derive (fun x => x/sqrt 2) x = /sqrt 2.
Proof.
  generalize sqrt2_neq0; intros.
  unfold Rdiv.
  rewrite Derive_mult.
  rewrite Derive_id.
  rewrite Derive_const.
  field_simplify; trivial.
  apply ex_derive_id.
  apply ex_derive_const.
Qed.
  
Lemma continuous_erf' :
  forall (x:R), continuous erf' x.
Proof.
  intros.
  unfold erf'.
  apply continuous_mult with (f := fun x => 2 / sqrt PI).
  apply continuous_const.
  apply continuous_comp with (g := exp).
  apply continuous_opp with (f := fun x => x^2).
  apply continuous_mult with (f:=id).
  apply continuous_id.
  apply continuous_mult with (f:=id).
  apply continuous_id.
  apply continuous_const.
  apply ex_derive_continuous with (f := exp).
  apply ex_derive_Reals_1.
  apply derivable_pt_exp.
Qed.

Lemma std_pdf_from_erf' (x:R):
  Standard_Gaussian_PDF x = / (2*sqrt 2) * (erf' (x / sqrt 2)).
Proof.
  unfold Standard_Gaussian_PDF.
  unfold erf'.
  field_simplify.
  replace (sqrt (2*PI)) with (sqrt(2)*sqrt(PI)).
  unfold Rdiv.
  apply Rmult_eq_compat_r.
  apply f_equal.
  field_simplify.
  replace (sqrt 2 ^ 2) with (2); trivial.
  rewrite <- Rsqr_pow2.  
  rewrite -> Rsqr_sqrt with (x:=2); trivial; lra.
  apply sqrt2_neq0.
  rewrite sqrt_mult_alt; trivial; lra.
  split.
  assert (PI > 0) by apply PI_RGT_0.
  apply Rgt_not_eq.
  apply sqrt_lt_R0; lra.
  apply sqrt2_neq0.
  apply sqrt_2PI_nzero.
Qed.

Lemma std_pdf_from_erf (x:R):
  Derive (fun t=> erf (t/sqrt 2)) x = 2 * Standard_Gaussian_PDF x.
Proof.
  generalize sqrt2_neq0; intros.
  assert (PI > 0) by apply PI_RGT_0.
  assert (sqrt PI <> 0).
  apply Rgt_not_eq.
  apply sqrt_lt_R0; lra.
  unfold erf.
  assert (forall y:R, ex_RInt erf' 0 y).
  intros.
  apply (@ex_RInt_continuous R_CompleteNormedModule).
  intros.
  apply continuous_erf'.
  rewrite Derive_comp.
  rewrite Derive_RInt.
  rewrite derive_xover_sqrt2.
  rewrite std_pdf_from_erf'.
  field_simplify; trivial.
  apply locally_open with (D:=fun _ => True); trivial.
  apply open_true.
  apply continuous_erf'.
  unfold ex_derive.
  exists (erf' (x / sqrt 2)).
  apply is_derive_RInt with (a:=0).
  apply locally_open with (D:=fun _ => True); trivial.
  apply open_true.
  intros.
  apply RInt_correct with (f:=erf') (a:=0) (b:=x0); trivial.
  apply continuous_erf'.
  unfold Rdiv.
  apply ex_derive_mult.
  apply ex_derive_id.
  apply ex_derive_const.
Qed.

Lemma scale_mult (a x : R) : (scal a x) = (a * x).
Proof.
  reflexivity.
Qed.

Hint Resolve Rlt_sqrt2_0 sqrt2_neq0 Rinv_pos : Rarith.

Lemma std_from_erf0 (x:R) : 
  RInt Standard_Gaussian_PDF 0 x = / 2 * erf(x/sqrt 2).
Proof.
  unfold erf.
  replace (/ 2 * RInt erf' 0 (x / sqrt 2)) with (scal (/ 2) (RInt erf' 0 (x / sqrt 2))).
  - rewrite <- RInt_scal with (l := /2) (f:=erf') (a := 0) (b := x / sqrt 2).
    + replace (0) with (/ sqrt 2 * 0 + 0) at 2 by lra.
      replace (x / sqrt 2) with (/ sqrt 2 * x + 0) by lra.
      rewrite <- RInt_comp_lin with (v:=0) (u:=/sqrt 2) (a:=0) (b:=x).
      * apply RInt_ext.
        intros.
        rewrite std_pdf_from_erf'.
        { replace (erf'(/ sqrt 2 * x0 + 0)) with (erf' (x0/sqrt 2)).
          - repeat rewrite scale_mult.
            field_simplify; auto with Rarith.
          - f_equal.
            field_simplify; auto with Rarith.
        }
      * apply ex_RInt_scal with (f := erf').
        field_simplify; auto with Rarith.
        apply ex_RInt_continuous with (f := erf') (a:=0 / sqrt 2) (b := x /sqrt 2).
        intros.
        apply continuous_erf'.
    + apply ex_RInt_continuous with (f := erf') (a:=0) (b := x /sqrt 2).  
      intros.
      apply continuous_erf'.
  - reflexivity.
Qed.

(* next 4 lemmas move between Lim RInt and RInt_gen when only one endpoint is infinite *)
Lemma lim_rint_gen_p_infty (f : R->R) (a:R) (l:R):
  (forall x y, ex_RInt f x y) ->
  is_lim (fun x => RInt f a x) p_infty l -> is_RInt_gen f (at_point a) (Rbar_locally p_infty) l.
Proof.
  intros fex.
  unfold is_lim.
  intros.
  unfold filterlim in H.
  unfold filter_le in H.
  unfold filtermap in H.
  simpl in *.
  intros P Plocal.
  specialize (H P Plocal).
  destruct H as [M PltM].
  eexists (fun x => x=a) (fun y => _); try easy.
  - simpl.
    eauto.
  - simpl.
    intros.
    subst.
    simpl in *.
    exists (RInt f a y).  
    split; trivial.
    apply (@RInt_correct R_CompleteNormedModule); trivial.
Qed.

Lemma lim_rint_gen_m_infty (f : R->R) (a:R) (l:R):
  (forall x y, ex_RInt f x y) ->
  is_lim (fun x => RInt f a x) m_infty l -> is_RInt_gen f (at_point a) (Rbar_locally m_infty) l.
Proof.
  intros fex.
  unfold is_lim.
  intros.
  unfold filterlim in H.
  unfold filter_le in H.
  unfold filtermap in H.
  simpl in *.
  intros P Plocal.
  specialize (H P Plocal).
  destruct H as [M PltM].
  eexists (fun x => x=a) (fun y => _); try easy.
  - simpl.
    eauto.
  - simpl.
    intros.
    subst.
    simpl in *.
    exists (RInt f a y).  
    split; trivial.
    apply (@RInt_correct R_CompleteNormedModule); trivial.
Qed.

Lemma rint_gen_lim_p_infty {f : R->R} {a:R} {l:R} :
  is_RInt_gen f (at_point a) (Rbar_locally p_infty) l -> is_lim (fun x => RInt f a x) p_infty l.
Proof.
  intros H P HP.
  specialize (H _ HP).
  destruct H as [Q R Qa Rb H].
  simpl in H.
  destruct Rb as [M Rb].
  exists M.
  intros x xlt.
  destruct (H a x Qa (Rb _ xlt))
    as [y [yis iP]].
  now rewrite (is_RInt_unique _ _ _ _ yis).
Qed.

Lemma rint_gen_lim_m_infty {f : R->R} {a:R} {l:R} :
  is_RInt_gen f (at_point a) (Rbar_locally m_infty) l -> is_lim (fun x => RInt f a x) m_infty l.
Proof.
  intros H P HP.
  specialize (H _ HP).
  destruct H as [Q R Qa Rb H].
  simpl in H.
  destruct Rb as [M Rb].
  exists M.
  intros x xlt.
  destruct (H a x Qa (Rb _ xlt))
    as [y [yis iP]].
  now rewrite (is_RInt_unique _ _ _ _ yis).
Qed.

Lemma Rbar_mult_p_infty_pos (z:R) :
  0 < z -> Rbar_mult p_infty z = p_infty.
Proof.
  intros.
  apply is_Rbar_mult_unique.
  apply is_Rbar_mult_p_infty_pos.
  simpl; auto.
Qed.    

Lemma Rbar_mult_m_infty_pos (z:R) :
  0 < z -> Rbar_mult m_infty z = m_infty.
Proof.
  intros.
  apply is_Rbar_mult_unique.
  apply is_Rbar_mult_m_infty_pos.
  simpl; auto.
Qed.

Lemma Rbar_mult_p_infty_neg (z:R) :
  0 > z -> Rbar_mult p_infty z = m_infty.
Proof.
  intros.
  apply is_Rbar_mult_unique.
  apply is_Rbar_mult_p_infty_neg.
  simpl; auto.
Qed.    

Lemma Rbar_mult_m_infty_neg (z:R) :
  0 > z -> Rbar_mult m_infty z = p_infty.
Proof.
  intros.
  apply is_Rbar_mult_unique.  
  apply is_Rbar_mult_m_infty_neg.
  simpl; auto.
Qed.

Lemma erf0_limit_p_infty : Lim (fun x => erf(x/sqrt 2)) p_infty = 1.
Proof.
  assert (A1:Lim (fun x : R => x / sqrt 2) p_infty = p_infty).
  {
    unfold Rdiv.
    rewrite Lim_scal_r.
    rewrite Lim_id.
    apply Rbar_mult_p_infty_pos.
    auto with Rarith.
  }
  rewrite (Lim_comp erf (fun x => x / sqrt 2)).
  - rewrite A1 erf_pinfty; trivial.
  - rewrite A1.
    apply erf_ex_lim.
  - apply ex_lim_scal_r.
    apply ex_lim_id.
  - rewrite A1.
    red.
    exists 0; intros.
    discriminate.
Qed.

Lemma erf0_limit_m_infty : Lim (fun x => erf(x/sqrt 2)) m_infty = -1.
Proof.
  assert (A1:Lim (fun x : R => x / sqrt 2) m_infty = m_infty).
  {
    unfold Rdiv.
    rewrite Lim_scal_r.
    rewrite Lim_id.
    apply Rbar_mult_m_infty_pos.
    auto with Rarith.
  }
  rewrite (Lim_comp erf (fun x => x / sqrt 2)).
  - rewrite A1 erf_minfty; trivial.
  - rewrite A1.
    apply erf_ex_lim.
  - apply ex_lim_scal_r.
    apply ex_lim_id.
  - rewrite A1.
    red.
    exists 0; intros.
    discriminate.
Qed.

Lemma ex_lim_Standard_Gaussian_PDF :
  ex_lim (fun a : R => RInt Standard_Gaussian_PDF 0 a) m_infty.
Proof.
  apply ex_lim_ext with (f := fun a => (/2) * erf (/sqrt 2 * a + 0)).
  intros.
  symmetry.
  replace (erf(/sqrt 2 * y + 0) ) with (erf(y/sqrt 2)).
  apply std_from_erf0.
  apply f_equal.
  field.
  apply sqrt2_neq0.
  apply ex_lim_comp_lin with (f := fun x => /2 * erf x) (a := /sqrt 2) (b := 0).
  apply ex_lim_scal_l with (a:=/2). 
  apply erf_ex_lim.
Qed.


Lemma Rint_lim_gen_m_infty_p_infty f (l:R) :
  (forall x y, ex_RInt f x y) ->
  filterlim (fun x => RInt f (fst x) (snd x))
            (filter_prod (Rbar_locally' m_infty) (Rbar_locally' p_infty))
            (Rbar_locally l) ->
  is_RInt_gen (V:=R_CompleteNormedModule) f (Rbar_locally m_infty) (Rbar_locally p_infty) l.
Proof.
  intros fex.
  unfold is_RInt_gen.
  unfold filterlimi, filterlim.
  unfold filtermap, filtermapi.
  unfold filter_le; intros.
  simpl in *.
  specialize (H P H0).
  replace (Rbar_locally' m_infty) with (Rbar_locally m_infty)  in * by reflexivity.
  replace (Rbar_locally' p_infty) with (Rbar_locally p_infty)  in * by reflexivity.
  revert H.
  apply filter_prod_ind; intros.
  eapply Filter_prod; eauto.
  intros.
  eexists; split; try eapply H2; eauto.
  apply RInt_correct.
  simpl.
  auto.
Qed.

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

  repeat first [
           apply derivable_pt_mult
         | apply derivable_pt_opp
         | apply derivable_pt_id
         | apply derivable_pt_const
         | apply derivable_pt_div
         | apply derivable_pt_comp with (f1 := (fun t => -t^2/2))
         | apply derivable_pt_exp
         ].
Qed.


Ltac solve_derive := try solve [auto_derive; trivial | lra].

Lemma variance_derive (x:R) : 
      Derive (fun t => -t*Standard_Gaussian_PDF t) x = (x^2-1)*Standard_Gaussian_PDF x.
Proof.

  generalize sqrt_2PI_nzero; intros.

  rewrite -> Derive_mult with (f := fun t => -t) (g := Standard_Gaussian_PDF)
  ; try solve [unfold Standard_Gaussian_PDF; solve_derive].
  rewrite Derive_opp.
  rewrite Derive_id.
  ring_simplify.
  unfold Rminus.
  rewrite -> Rplus_comm with (r1 := Standard_Gaussian_PDF x * x ^ 2).
  apply Rplus_eq_compat_l.
  unfold Standard_Gaussian_PDF.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_const; solve_derive.
  ring_simplify.
  rewrite Derive_comp; solve_derive.
  rewrite Derive_div; solve_derive.
  rewrite Derive_const.
  rewrite Derive_opp.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_id.
  rewrite Derive_const.
  field_simplify; try lra. 
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (-x^2/2)).
  rewrite derive_pt_exp.
  field_simplify; lra.
Qed.

Lemma limxexp_inv_inf : is_lim (fun t => exp(t^2/2) / t) p_infty p_infty.
Proof.
  eapply is_lim_le_p_loc; [idtac | apply is_lim_div_exp_p].
  unfold Rbar_locally'.
  exists 3; intros.
  apply Rmult_le_compat_r.
  - left.
    apply Rinv_0_lt_compat.
    lra.
  - left.
    apply exp_increasing.
    simpl.
    replace x with (x*1) at 1 by lra.
    unfold Rdiv.
    repeat rewrite Rmult_assoc.
    apply Rmult_lt_compat_l; lra.
Qed.
  
Lemma limxexp_inf : is_lim (fun t => t*exp(-t^2/2)) p_infty 0.
Proof.
  generalize (limxexp_inv_inf); intros HH.
  apply is_lim_inv in HH; try discriminate.
  simpl in HH.
  eapply is_lim_ext_loc; try apply HH.
  intros.
  simpl.
  exists 0.
  intros x xpos.
  replace (- (x * (x * 1)) / 2) with (- ((x * (x * 1)) / 2)) by lra.
  rewrite exp_Ropp.
  field.
  split; try lra.
  generalize (exp_pos (x * (x * 1) / 2)).
  lra.
Qed.

Lemma limxexp_minf : is_lim (fun t => t*exp(-t^2/2)) m_infty 0.
Proof.
  generalize limxexp_inf; intros HH.
  generalize (is_lim_comp (fun t => t*exp(-t^2/2)) Ropp m_infty 0 p_infty HH); intros HH2.
  cut_to HH2.
  - apply is_lim_opp in HH2.
    simpl in HH2.
    replace (- 0) with 0 in HH2 by lra.
    eapply is_lim_ext; try eapply HH2.
    intros; simpl.
    field_simplify.
    do 3 f_equal.
    lra.
  - generalize (is_lim_id m_infty); intros HH3.
    apply is_lim_opp in HH3.
    simpl in HH3.
    apply HH3.
  - simpl.
    exists 0; intros; discriminate.
Qed.

Lemma continuous_derive_gaussian_opp_mean x :
  continuous (Derive (fun t : R => - t * Standard_Gaussian_PDF t)) x.
Proof.
  apply (continuous_ext (fun t => (t^2-1)*Standard_Gaussian_PDF t)).
  intros.
  rewrite variance_derive; trivial.
  apply continuous_mult with (f := fun t => t^2-1).
  apply continuous_minus with (f := fun t => t^2).
  apply continuous_mult with (f:=id).
  apply continuous_id.
  apply continuous_mult with (f:=id).
  apply continuous_id.
  apply continuous_const.
  apply continuous_const.
  apply continuous_Standard_Gaussian_PDF.
Qed.

Lemma plim_gaussian_opp_mean : is_lim (fun t => - t*(Standard_Gaussian_PDF t)) p_infty 0.
Proof.
  replace (0) with ((- / sqrt (2*PI)) * 0) by lra.  
  unfold Standard_Gaussian_PDF.
  apply (is_lim_ext (fun t : R => (- / sqrt (2 * PI)) * (t * exp (- t ^ 2 / 2)))).
  intros.
  field_simplify; trivial.
  apply sqrt_2PI_nzero.
  apply sqrt_2PI_nzero.
  apply is_lim_scal_l with (a:=- / sqrt (2 * PI)) (l := 0).
  apply limxexp_inf.  
Qed.  

Lemma mlim_gaussian_opp_mean : is_lim (fun t => - t*(Standard_Gaussian_PDF t)) m_infty 0.
Proof.
  replace (0) with ((- / sqrt (2*PI)) * 0) by lra.  
  unfold Standard_Gaussian_PDF.
  apply (is_lim_ext (fun t : R => (- / sqrt (2 * PI)) * (t * exp (- t ^ 2 / 2)))).
  intros.
  field_simplify; trivial.
  apply sqrt_2PI_nzero.
  apply sqrt_2PI_nzero.
  apply is_lim_scal_l with (a:=- / sqrt (2 * PI)) (l := 0).
  apply limxexp_minf.  
Qed.

Lemma variance_int1_middle :
  is_RInt_gen (fun t => (t^2-1)*Standard_Gaussian_PDF t) (Rbar_locally m_infty) (Rbar_locally p_infty) 0.
Proof.
  apply (is_RInt_gen_ext (Derive (fun t : R => - t * Standard_Gaussian_PDF t))).
  - simpl.
    eapply (Filter_prod _ _ _ (fun _ => True) (fun _ => True))
    ; simpl; eauto.
    intros.
    rewrite variance_derive; trivial.
  - replace 0 with (0 - 0) by lra.
    apply is_RInt_gen_Derive.
    + eapply (Filter_prod _ _ _ (fun _ => True) (fun _ => True))
      ; simpl; eauto.
      intros; simpl.
      unfold Standard_Gaussian_PDF.
      auto_derive; trivial.
    + eapply (Filter_prod _ _ _ (fun _ => True) (fun _ => True))
      ; simpl; eauto.
      intros; simpl.
      apply continuous_derive_gaussian_opp_mean.
    + apply mlim_gaussian_opp_mean.
    + apply plim_gaussian_opp_mean.
  Unshelve.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
Qed.

Lemma Standard_Gaussian_PDF_int1_pinf : 
  is_RInt_gen Standard_Gaussian_PDF (at_point 0) (Rbar_locally p_infty)  (/2).
Proof.
  apply lim_rint_gen_p_infty.
  apply ex_RInt_Standard_Gaussian_PDF.
  apply is_lim_ext with (f := (fun x => / 2 * erf(x/sqrt 2))).
  intros.
  symmetry.
  apply std_from_erf0.
  replace (Finite (/ 2)) with (Rbar_mult (/ 2) (Finite 1)).
  apply is_lim_scal_l with (a:=/2) (f:= fun x:R => erf(x/sqrt 2)) (l := 1).
  replace (Finite 1) with (Lim (fun x : R => erf (x / sqrt 2)) p_infty).
  apply Lim_correct.
  apply ex_lim_ext with (f := fun x => erf ((/ sqrt 2) * x + 0)).
  intros.
  apply f_equal; lra.
  apply ex_lim_comp_lin with (f := erf) (a := / sqrt 2) (b:=0).
  apply erf_ex_lim.
  apply erf0_limit_p_infty.
  apply Rbar_finite_eq; lra.
Qed.

Lemma Standard_Gaussian_PDF_int1_minf : 
  is_RInt_gen Standard_Gaussian_PDF (at_point 0) (Rbar_locally m_infty)  (-/2).
Proof.
  apply lim_rint_gen_m_infty.
  apply ex_RInt_Standard_Gaussian_PDF.
  apply is_lim_ext with (f := (fun x => / 2 * erf(x/sqrt 2))).
  intros.
  symmetry.
  apply std_from_erf0.
  replace (Finite (-/ 2)) with (Rbar_mult (/ 2) (Finite (-1))).
  apply is_lim_scal_l with (a:=/2) (f:= fun x:R => erf(x/sqrt 2)) (l := -1).
  replace (Finite (-1)) with (Lim (fun x : R => erf (x / sqrt 2)) m_infty).
  apply Lim_correct.
  apply ex_lim_ext with (f := fun x => erf ((/ sqrt 2) * x + 0)).
  intros.
  apply f_equal; lra.
  apply ex_lim_comp_lin with (f := erf) (a := / sqrt 2) (b:=0).
  apply erf_ex_lim.
  apply erf0_limit_m_infty.
  apply Rbar_finite_eq; lra.
Qed.

Lemma std_CDF_from_erf0 :
  forall x:R, is_RInt_gen Standard_Gaussian_PDF (Rbar_locally m_infty) (at_point x)  ((/ 2) + (/2)*erf (x/sqrt 2)).
Proof.
  intros.
  apply (@is_RInt_gen_Chasles R_CompleteNormedModule) with (b := 0) (l1 := /2) (l2 := /2 * erf (x / sqrt 2)).
  apply Rbar_locally_filter.
  apply at_point_filter.
  replace (/2) with (opp (- /2)).
  apply (@is_RInt_gen_swap R_CompleteNormedModule).
  apply Rbar_locally_filter.
  apply at_point_filter.
  apply Standard_Gaussian_PDF_int1_minf.
  compute; field_simplify; auto.
  rewrite is_RInt_gen_at_point.
  replace (/ 2 * erf (x / sqrt 2)) with (RInt Standard_Gaussian_PDF 0 x).
  apply RInt_correct.
  apply ex_RInt_Standard_Gaussian_PDF.
  apply std_from_erf0.
Qed.

Lemma std_CDF_from_erf :
  forall x:R, Standard_Gaussian_CDF x =  (/ 2) + (/2)*erf (x/sqrt 2).
Proof.
  intros.
  unfold Standard_Gaussian_CDF.
  apply is_RInt_gen_unique.
  apply std_CDF_from_erf0.
Qed.

Lemma Standard_Gaussian_PDF_normed : 
  is_RInt_gen Standard_Gaussian_PDF (Rbar_locally m_infty) (Rbar_locally p_infty) 1.
Proof.  
  replace (1) with (plus (/ 2) (/ 2)).
  apply (@is_RInt_gen_Chasles R_CompleteNormedModule) with (b := 0) (l1 := /2) (l2 := /2).  
  apply Rbar_locally_filter.
  apply Rbar_locally_filter.  
  replace (/ 2) with (opp (opp (/2))).
  apply (@is_RInt_gen_swap R_CompleteNormedModule) with (l := (opp (/2))).
  apply Rbar_locally_filter.  
  apply at_point_filter.
  apply Standard_Gaussian_PDF_int1_minf.
  apply opp_opp.
  apply Standard_Gaussian_PDF_int1_pinf.
  compute; lra.
Qed.

Lemma variance_standard_gaussian0 :
  is_RInt_gen (fun t => (t^2-1)*Standard_Gaussian_PDF t + Standard_Gaussian_PDF t) (Rbar_locally m_infty) (Rbar_locally p_infty) 1.
Proof.
  intros.
  replace (1) with (0 + 1) at 1 by lra.
  apply is_RInt_gen_plus with 
      (f:=(fun t => (t^2-1)*Standard_Gaussian_PDF t)) (lf :=0)
      (g:=(fun t => Standard_Gaussian_PDF t)) (lg := 1).
  apply variance_int1_middle.
  apply Standard_Gaussian_PDF_normed.
Qed.

Lemma variance_standard_gaussian :
  is_RInt_gen (fun t => t^2*Standard_Gaussian_PDF t) 
           (Rbar_locally m_infty) (Rbar_locally p_infty) 1.
Proof.
  eapply is_RInt_gen_ext; try eapply variance_standard_gaussian0.
  eapply (Filter_prod _ _ _ (fun _ => True) (fun _ => True))
  ; simpl; eauto.
  intros; simpl.
  unfold Standard_Gaussian_PDF.
  lra.
  Unshelve.
  exact 0.
  exact 0.
Qed.

Lemma limexp_inf : is_lim (fun t => exp(t^2/2)) p_infty p_infty.
Proof.
  eapply is_lim_le_p_loc; [idtac | apply is_lim_exp_p].
  unfold Rbar_locally'.
  exists 2; intros.
  left.
  apply exp_increasing.
  simpl.
  replace (x) with (x*1) at 1 by lra.
  replace (x * (x * 1) / 2) with (x * (x / 2)) by lra.
  apply Rmult_lt_compat_l; lra.
Qed.

Lemma limexp_neg_inf : is_lim (fun t => exp(-t^2/2)) p_infty 0.
Proof.
  apply (is_lim_ext (fun t => / exp(t^2/2))).
  intros.
  symmetry.
  replace (- y^2/2) with (- (y^2/2)).
  apply exp_Ropp with (x:=y^2/2).
  lra.
  replace (Finite 0) with (Rbar_inv p_infty).
  apply is_lim_inv.
  apply limexp_inf.
  discriminate.
  compute; trivial.
Qed.

Lemma limexp_neg_minf : is_lim (fun t => exp(-t^2/2)) m_infty 0.
Proof.
  replace (0) with ((-1) * 0 + 0).
  apply (is_lim_ext (fun t => exp(-(-1*t+0)^2/2))).
  intros.
  apply f_equal.
  field_simplify; trivial.
  apply is_lim_comp_lin with (a := -1) (b := 0) (f := fun t => exp(-t^2/2)).
  replace (Rbar_plus (Rbar_mult (-1) m_infty) 0) with (p_infty).
  replace (-1 * 0 + 0) with (0) by lra.
  apply limexp_neg_inf.
  rewrite Rbar_plus_0_r.
  symmetry.
  rewrite Rbar_mult_comm.
  apply is_Rbar_mult_unique.
  apply is_Rbar_mult_m_infty_neg.
  compute; lra.
  apply Rlt_not_eq; lra.
  compute.
  field_simplify.
  reflexivity.
Qed.

Lemma Derive_opp_Standard_Gaussian_PDF (x:R):
  Derive (fun t => - Standard_Gaussian_PDF t) x = x*Standard_Gaussian_PDF x.
Proof.
  rewrite Derive_opp.
  unfold Standard_Gaussian_PDF.
  rewrite Derive_scal.
  rewrite Derive_comp.
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (-x^2/2)).
  rewrite derive_pt_exp.
  unfold Rdiv at 1.
  rewrite Derive_scal_l.
  rewrite Derive_opp.
  rewrite Derive_pow.
  simpl.
  rewrite Derive_id.
  field_simplify.
  unfold Rdiv at 1.
  unfold Rdiv at 2.
  replace (2 * x * exp (- (x * (x * 1)) / 2) * / (2 * sqrt (2 * PI))) with (x * exp (- (x * (x * 1)) / 2) * (2 * / (2 * sqrt (2 * PI)))) by lra.
  apply Rmult_eq_compat_l.
  field_simplify.
  reflexivity.
  apply sqrt_2PI_nzero.
  apply sqrt_2PI_nzero.
  apply sqrt_2PI_nzero.
  apply sqrt_2PI_nzero.  
  apply ex_derive_id.
  solve_derive.
  solve_derive.  
Qed.
  
Lemma ex_derive_opp_Standard_Gaussian_PDF (x:R):
  ex_derive (fun t => - Standard_Gaussian_PDF t) x.
Proof.
  unfold Standard_Gaussian_PDF.
  solve_derive.
Qed.

Lemma continuous_Derive_opp_Standard_Gaussian_PDF (x:R):
  continuous (Derive (fun t => - Standard_Gaussian_PDF t)) x.
Proof.
  apply continuous_ext with (f:=fun t => t*Standard_Gaussian_PDF t).
  symmetry.
  apply Derive_opp_Standard_Gaussian_PDF.
  apply (@continuous_mult R_CompleteNormedModule).
  apply continuous_id.
  apply continuous_Standard_Gaussian_PDF.
Qed.

Lemma mean_standard_gaussian :
  is_RInt_gen (fun t => t*Standard_Gaussian_PDF t) 
           (Rbar_locally m_infty) (Rbar_locally p_infty) 0.
Proof.  
  replace (0) with (0 - 0) by lra.
  apply (is_RInt_gen_ext (Derive (fun t => - Standard_Gaussian_PDF t))).
  apply filter_forall.
  intros; trivial.
  apply Derive_opp_Standard_Gaussian_PDF.
  apply is_RInt_gen_Derive with (f := fun t => - Standard_Gaussian_PDF t) (la := 0) (lb := 0).
  apply filter_forall.  
  intros; trivial.
  apply ex_derive_opp_Standard_Gaussian_PDF.
  apply filter_forall.
  intros; trivial.
  apply continuous_Derive_opp_Standard_Gaussian_PDF.
  replace (filterlim (fun t : R => - Standard_Gaussian_PDF t) (Rbar_locally m_infty) (locally 0)) with (is_lim (fun t : R => - Standard_Gaussian_PDF t) m_infty 0).
  unfold Standard_Gaussian_PDF.
  apply (is_lim_ext (fun t : R => (- / sqrt (2 * PI)) *  exp (- t ^ 2 / 2))).
  intros.
  field_simplify; trivial.
  apply sqrt_2PI_nzero.
  apply sqrt_2PI_nzero. 
  replace (0) with ((- / sqrt (2*PI)) * 0) by lra.  
  apply is_lim_scal_l with (a:=- / sqrt (2 * PI)) (l := 0).
  apply limexp_neg_minf.
  unfold is_lim.
  reflexivity.
  replace (filterlim (fun t : R => - Standard_Gaussian_PDF t) (Rbar_locally p_infty) (locally 0)) with (is_lim (fun t : R => - Standard_Gaussian_PDF t) p_infty 0).
  unfold Standard_Gaussian_PDF.
  apply (is_lim_ext (fun t : R => (- / sqrt (2 * PI)) *  exp (- t ^ 2 / 2))).
  intros.
  field_simplify; trivial.
  apply sqrt_2PI_nzero.
  apply sqrt_2PI_nzero. 
  replace (0) with ((- / sqrt (2*PI)) * 0) by lra.  
  apply is_lim_scal_l with (a:=- / sqrt (2 * PI)) (l := 0).
  apply limexp_neg_inf.
  unfold is_lim.
  reflexivity.
Qed.

(* main results:
  Definition Standard_Gaussian_PDF (t:R) := (/ (sqrt (2*PI))) * exp (-t^2/2).

  Lemma Standard_Gaussian_PDF_normed : 
     is_RInt_gen Standard_Gaussian_PDF (Rbar_locally m_infty) (Rbar_locally p_infty) 1.

  Definition Standard_Gaussian_CDF (t:Rbar) := 
      RInt_gen Standard_Gaussian_PDF (Rbar_locally m_infty) (at_point t).

  Lemma std_CDF_from_erf :
     forall x:R, Standard_Gaussian_CDF x = (/ 2) + (/2)*erf (x/sqrt 2).

  Lemma mean_standard_gaussian :
     is_RInt_gen (fun t => t*Standard_Gaussian_PDF t) 
           (Rbar_locally m_infty) (Rbar_locally p_infty) 0.
   
  Lemma variance_standard_gaussian :
     is_RInt_gen (fun t => t^2*Standard_Gaussian_PDF t) 
           (Rbar_locally m_infty) (Rbar_locally p_infty) 1.

  CoFixpoint mkGaussianStream (uniformStream : Stream R) : Stream R
*)

Lemma lim_rint_gen_R (f : R->R) (a:R) (b:R) (l:R):
  (forall x y, ex_RInt f x y) ->
  is_lim (fun x => RInt f a x) b l -> is_RInt_gen f (at_point a) (Rbar_locally' b) l.
Proof.
  intros fex.
  unfold is_lim.
  intros.
  unfold filterlim in H.
  unfold filter_le in H.
  unfold filtermap in H.
  simpl in *.
  intros P Plocal.
  specialize (H P Plocal).
  destruct H as [M PltM].
  eexists (fun x => x=a) (fun y => P (RInt f a y)); try easy.
  - simpl.
    unfold locally', within, locally in *.
    eauto.
  - simpl.
    intros.
    subst.
    simpl in *.
    exists (RInt f a y).  
    split; trivial.
    now apply (@RInt_correct R_CompleteNormedModule).
Qed.

Lemma lim_rint_gen (f : R->R) (a:R) (b:Rbar) (l:R):
  (forall x y, ex_RInt f x y) ->
  is_lim (fun x => RInt f a x) b l -> is_RInt_gen f (at_point a) (Rbar_locally' b) l.
Proof.
  intros fex isl.
  destruct b.
  - now apply lim_rint_gen_R.
  - now apply lim_rint_gen_p_infty.
  - now apply lim_rint_gen_m_infty.
Qed.
