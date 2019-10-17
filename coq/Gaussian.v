Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.

Require Import Reals Coquelicot.Coquelicot.
Require Import Streams.

Require Import Lra Omega.

Require Import Utils.

Set Bullet Behavior "Strict Subproofs".

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

  Lemma General_Gaussian_PDF_normed (mu sigma:R) : 
     sigma>0 ->
     ex_RInt_gen Standard_Gaussian_PDF (Rbar_locally' m_infty) (at_point (- mu / sigma)) ->
     ex_RInt_gen Standard_Gaussian_PDF (at_point (- mu / sigma)) (Rbar_locally' p_infty) ->
     is_RInt_gen (General_Gaussian_PDF mu sigma) (Rbar_locally' m_infty) (Rbar_locally' p_infty) 1.

  Lemma mean_general_gaussian (mu sigma:R) :
    sigma > 0 ->
    ex_RInt_gen Standard_Gaussian_PDF (Rbar_locally' m_infty) (at_point (- mu / sigma)) ->
    ex_RInt_gen Standard_Gaussian_PDF (at_point (- mu / sigma)) (Rbar_locally' p_infty) ->

    is_RInt_gen (fun t => t*General_Gaussian_PDF mu sigma t) 
                           (Rbar_locally' m_infty) (Rbar_locally' p_infty) mu.
 
  Lemma variance_general_gaussian (mu sigma : R) :
    sigma > 0 ->
    ex_RInt_gen (fun t : R => sigma ^ 2 * t ^ 2 * Standard_Gaussian_PDF t)
              (Rbar_locally' m_infty) (at_point (- mu / sigma)) ->
    ex_RInt_gen (fun t : R => sigma ^ 2 * t ^ 2 * Standard_Gaussian_PDF t)
              (at_point (- mu / sigma)) (Rbar_locally' p_infty) ->
    is_RInt_gen (fun t => (t-mu)^2*General_Gaussian_PDF mu sigma t) 
              (Rbar_locally' m_infty) (Rbar_locally' p_infty) (sigma^2).

  Lemma Uniform_normed (a b:R) :
    a < b -> is_RInt_gen (Uniform_PDF a b) (Rbar_locally' m_infty) (Rbar_locally' p_infty) 1.

  Lemma Uniform_mean (a b:R) :
    a < b -> is_RInt_gen (fun t => t*(Uniform_PDF a b t)) (Rbar_locally' m_infty) (Rbar_locally' p_infty) ((b+a)/2).

  Lemma Uniform_variance (a b:R) :
    a < b -> is_RInt_gen (fun t => (t-(b+a)/2)^2*(Uniform_PDF a b t)) (Rbar_locally' m_infty) (Rbar_locally' p_infty) ((b-a)^2/12).

*)

Ltac solve_derive := try solve [auto_derive; trivial | lra].

Local Open Scope R_scope.
Implicit Type f : R -> R.

Definition inf_sign (r:Rbar) :=
  match r with
  | p_infty => 1
  | m_infty => -1
  | _ => 0
  end.                

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
  now apply Rgt_not_eq.
  generalize sqrt_2PI_nzero; intros.

  unfold General_Gaussian_PDF.
  unfold Standard_Gaussian_PDF.
  field_simplify.
  unfold Rdiv.
  apply Rmult_eq_compat_r.
  f_equal; now field_simplify.
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
  apply (@ex_derive_continuous).
  now auto_derive.
Qed.

Lemma ex_RInt_Standard_Gaussian_PDF (a b:R) :
  ex_RInt Standard_Gaussian_PDF a b.
Proof.
  intros.
  apply (@ex_RInt_continuous).
  intros.
  apply continuous_Standard_Gaussian_PDF.
Qed.

Lemma derive_xover_sqrt2 (x:R):
  Derive (fun x => x/sqrt 2) x = /sqrt 2.
Proof.
  generalize sqrt2_neq0; intros.
  unfold Rdiv.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_id.
  rewrite Derive_const.
  now field_simplify.
Qed.
  
Lemma continuous_erf' :
  forall (x:R), continuous erf' x.
Proof.
  intros.
  unfold erf'.
  apply (@ex_derive_continuous).
  now auto_derive.
Qed.

Lemma std_pdf_from_erf' (x:R):
  Standard_Gaussian_PDF x = / (2*sqrt 2) * (erf' (x / sqrt 2)).
Proof.
  unfold Standard_Gaussian_PDF.
  unfold erf'.
  field_simplify.
  rewrite sqrt_mult_alt; trivial; try lra.
  unfold Rdiv.
  apply Rmult_eq_compat_r.
  f_equal; field_simplify.
  replace (sqrt 2 ^ 2) with (2); trivial.
  rewrite <- Rsqr_pow2.  
  rewrite -> Rsqr_sqrt with (x:=2); trivial; lra.
  apply sqrt2_neq0.
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
  apply (@ex_RInt_continuous).
  intros.
  apply continuous_erf'.
  rewrite Derive_comp; solve_derive.
  rewrite Derive_RInt.
  rewrite derive_xover_sqrt2.
  rewrite std_pdf_from_erf'.
  now field_simplify.
  apply locally_open with (D:=fun _ => True); trivial.
  apply open_true.
  apply continuous_erf'.
  unfold ex_derive.
  exists (erf' (x / sqrt 2)).
  apply is_derive_RInt with (a:=0).
  apply locally_open with (D:=fun _ => True); trivial.
  apply open_true.
  intros.
  now apply RInt_correct with (f:=erf') (a:=0) (b:=x0).
  apply continuous_erf'.
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
          - f_equal; field_simplify; auto with Rarith.
        }
      * apply ex_RInt_scal with (f := erf').
        field_simplify; auto with Rarith.
        apply (@ex_RInt_continuous).
        intros.
        apply continuous_erf'.
    + apply (@ex_RInt_continuous).
      intros.
      apply continuous_erf'.
  - reflexivity.
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
  - now rewrite A1 erf_pinfty.
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
  - now rewrite A1 erf_minfty.
  - rewrite A1.
    apply erf_ex_lim.
  - apply ex_lim_scal_r.
    apply ex_lim_id.
  - rewrite A1.
    red.
    exists 0; intros.
    discriminate.
Qed.

(*
Lemma ex_lim_Standard_Gaussian_PDF :
  ex_lim (fun a : R => RInt Standard_Gaussian_PDF 0 a) m_infty.
Proof.
  apply ex_lim_ext with (f := fun a => (/2) * erf (/sqrt 2 * a + 0)).
  intros.
  symmetry.
  replace (erf(/sqrt 2 * y + 0) ) with (erf(y/sqrt 2)).
  apply std_from_erf0.
  f_equal.
  field.
  apply sqrt2_neq0.
  apply ex_lim_comp_lin with (f := fun x => /2 * erf x) (a := /sqrt 2) (b := 0).
  apply ex_lim_scal_l with (a:=/2). 
  apply erf_ex_lim.
Qed.
*)

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

Lemma ex_RInt_Standard_Gaussian_mean_PDF (a b:R) :
    ex_RInt (fun t => t * (Standard_Gaussian_PDF t)) a b.
Proof.
  intros.
  apply (@ex_RInt_continuous).
  intros.
  apply (@continuous_scal).
  apply continuous_id.
  apply continuous_Standard_Gaussian_PDF.
Qed.

  Ltac cont_helper
    :=
      repeat (match goal with
  | [|- continuous (fun _ => _ * _ ) _ ] => apply @continuous_scal
  | [|- continuous (fun _ => _ ^ 2 ) _ ] => apply @continuous_scal
  | [|- continuous (fun _ => Hierarchy.mult _ _ ) _ ] => apply @continuous_mult
  | [|- continuous (fun _ => _ + _ ) _ ] => apply @continuous_plus
  | [|- continuous (fun _ => _ - _ ) _ ] => apply @continuous_minus
  end
 || apply continuous_id
 || apply continuous_const
 || apply continuous_Standard_Gaussian_PDF).


  Lemma ex_RInt_Standard_Gaussian_variance_PDF (a b:R) :
    ex_RInt (fun t => t^2 * (Standard_Gaussian_PDF t)) a b.
Proof.
  intros.
  apply (@ex_RInt_continuous).
  intros.

  cont_helper.
Qed.

Lemma variance_exint0 (a b:Rbar) :
  ex_RInt (fun t => (t^2-1)*Standard_Gaussian_PDF t) a b.
Proof.
  intros.
  assert (ex_RInt (fun t => t^2*Standard_Gaussian_PDF t - Standard_Gaussian_PDF t) a b).
  apply ex_RInt_minus with (f := fun t=> t^2*Standard_Gaussian_PDF t)
                           (g := Standard_Gaussian_PDF).
  now apply ex_RInt_Standard_Gaussian_variance_PDF.
  now apply ex_RInt_Standard_Gaussian_PDF.
  apply ex_RInt_ext with (f := (fun t : R => t ^ 2 * Standard_Gaussian_PDF t - Standard_Gaussian_PDF t)) (g := (fun t : R => (t ^ 2 - 1) * Standard_Gaussian_PDF t)).
  intros.
  lra.
  assumption.
Qed.  

Lemma variance_int0 (a b:Rbar) :
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
  now apply ex_RInt_Standard_Gaussian_PDF.
  apply RInt_ext.
  intros.
  lra.
Qed.

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
    apply Rinv_0_lt_compat; lra.
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
  rewrite exp_Ropp; field.
  split; try lra.
  generalize (exp_pos (x * (x * 1) / 2)); lra.
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
    intros; simpl; field_simplify.
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
  now rewrite variance_derive.
  cont_helper.
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
    now rewrite variance_derive.
  - replace 0 with (0 - 0) by lra.
    apply is_RInt_gen_Derive.
    + eapply (Filter_prod _ _ _ (fun _ => True) (fun _ => True))
      ; simpl; eauto.
      intros; simpl.
      unfold Standard_Gaussian_PDF.
      now auto_derive.
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
  is_RInt_gen Standard_Gaussian_PDF (at_point 0) (Rbar_locally' p_infty)  (/2).
Proof.
  apply lim_rint_gen_Rbar.
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
  f_equal; lra.
  apply ex_lim_comp_lin with (f := erf) (a := / sqrt 2) (b:=0).
  apply erf_ex_lim.
  apply erf0_limit_p_infty.
  apply Rbar_finite_eq; lra.
Qed.

Lemma Standard_Gaussian_PDF_int1_minf : 
  is_RInt_gen Standard_Gaussian_PDF (at_point 0) (Rbar_locally' m_infty)  (-/2).
Proof.
  apply lim_rint_gen_Rbar.
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
  f_equal; lra.
  apply ex_lim_comp_lin with (f := erf) (a := / sqrt 2) (b:=0).
  apply erf_ex_lim.
  apply erf0_limit_m_infty.
  apply Rbar_finite_eq; lra.
Qed.

Lemma std_CDF_from_erf0 :
  forall x:R, is_RInt_gen Standard_Gaussian_PDF (Rbar_locally' m_infty) (at_point x)  ((/ 2) + (/2)*erf (x/sqrt 2)).
Proof.
  intros.
  apply (@is_RInt_gen_Chasles) with (b := 0) (l1 := /2) (l2 := /2 * erf (x / sqrt 2)).  
  apply Rbar_locally'_filter.
  apply at_point_filter.
  replace (/2) with (opp (- /2)).
  apply (@is_RInt_gen_swap).
  apply Rbar_locally'_filter.
  apply at_point_filter.
  apply Standard_Gaussian_PDF_int1_minf.
  compute; field_simplify; auto.
  rewrite is_RInt_gen_at_point.
  replace (/ 2 * erf (x / sqrt 2)) with (RInt Standard_Gaussian_PDF 0 x).
  apply (@RInt_correct).
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
  apply (@is_RInt_gen_Chasles) with (b := 0) (l1 := /2) (l2 := /2).
  apply Rbar_locally_filter.
  apply Rbar_locally_filter.  
  replace (/ 2) with (opp (opp (/2))).
  apply (@is_RInt_gen_swap) with (l := (opp (/2))).
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
  now compute.
Qed.

Lemma limexp_neg_minf : is_lim (fun t => exp(-t^2/2)) m_infty 0.
Proof.
  replace (0) with ((-1) * 0 + 0).
  apply (is_lim_ext (fun t => exp(-(-1*t+0)^2/2))).
  intros.
  f_equal; now field_simplify.
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
  lra.
Qed.

Lemma Derive_opp_Standard_Gaussian_PDF (x:R):
  Derive (fun t => - Standard_Gaussian_PDF t) x = x*Standard_Gaussian_PDF x.
Proof.
  rewrite Derive_opp.
  unfold Standard_Gaussian_PDF.
  rewrite Derive_scal.
  rewrite Derive_comp; solve_derive.
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (-x^2/2)).
  rewrite derive_pt_exp.
  unfold Rdiv at 1.
  rewrite Derive_scal_l.
  rewrite Derive_opp.
  rewrite Derive_pow; solve_derive.
  simpl.
  rewrite Derive_id.
  apply Rminus_diag_uniq; field_simplify; try lra.
  apply sqrt_2PI_nzero.
Qed.
  
Lemma ex_derive_opp_Standard_Gaussian_PDF (x:R):
  ex_derive (fun t => - Standard_Gaussian_PDF t) x.
Proof.
  unfold Standard_Gaussian_PDF.
  now auto_derive.
Qed.

Lemma continuous_Derive_opp_Standard_Gaussian_PDF (x:R):
  continuous (Derive (fun t => - Standard_Gaussian_PDF t)) x.
Proof.
  apply continuous_ext with (f:=fun t => t*Standard_Gaussian_PDF t).
  symmetry.
  apply Derive_opp_Standard_Gaussian_PDF.
  cont_helper.
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
  now ring_simplify.
  replace (0) with ((- / sqrt (2*PI)) * 0) by lra.    
  apply is_lim_scal_l with (a:=- / sqrt (2 * PI)) (l := 0).
  apply limexp_neg_minf.
  now unfold is_lim.
  replace (filterlim (fun t : R => - Standard_Gaussian_PDF t) (Rbar_locally p_infty) (locally 0)) with (is_lim (fun t : R => - Standard_Gaussian_PDF t) p_infty 0).
  unfold Standard_Gaussian_PDF.
  apply (is_lim_ext (fun t : R => (- / sqrt (2 * PI)) *  exp (- t ^ 2 / 2))).
  intros.
  now ring_simplify.
  replace (0) with ((- / sqrt (2*PI)) * 0) by lra.  
  apply is_lim_scal_l with (a:=- / sqrt (2 * PI)) (l := 0).
  apply limexp_neg_inf.
  now unfold is_lim.
Qed.

Lemma Positive_General_Gaussian_PDF (mu sigma x : R):
  sigma > 0 -> General_Gaussian_PDF mu sigma x > 0.
Proof.  
  intros.
  unfold General_Gaussian_PDF.
  apply Rmult_gt_0_compat.
  apply Rinv_0_lt_compat.
  apply Rmult_gt_0_compat; trivial.
  apply sqrt_lt_R0.
  apply Rmult_gt_0_compat.
  apply Rle_lt_0_plus_1; lra.
  apply PI_RGT_0.
  apply exp_pos.
Qed.

Lemma Derive_General_Gaussian_PDF (mu sigma x:R):
  sigma > 0 -> Derive (General_Gaussian_PDF mu sigma) x = / (sigma^2)*(mu-x)*General_Gaussian_PDF mu sigma x.
Proof.
  intros.
  assert (sigma <> 0).
  now apply Rgt_not_eq.
  unfold General_Gaussian_PDF.
  rewrite Derive_scal.
  rewrite Derive_comp; solve_derive.
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (-(x-mu)^2/(2*sigma^2))).
  rewrite derive_pt_exp.
  unfold Rdiv at 1.
  rewrite Derive_scal_l.
  rewrite Derive_opp.
  rewrite Derive_pow; solve_derive.
  rewrite Derive_minus; solve_derive.
  rewrite Derive_id.
  rewrite Derive_const.
  apply Rminus_diag_uniq; simpl; field_simplify; try lra.
  split.
  apply sqrt_2PI_nzero.
  trivial.
Qed.  

Lemma ex_derive_General_Gaussian_PDF (mu sigma:R) (x:R):
  sigma > 0 -> ex_derive (General_Gaussian_PDF mu sigma) x.
Proof.
  intros.
  unfold General_Gaussian_PDF.
  now auto_derive.
Qed.

Lemma continuous_Derive_General_Gaussian_PDF (mu sigma x:R):
  sigma > 0 -> continuous (Derive (General_Gaussian_PDF mu sigma)) x.
Proof.
  intros.
  apply (continuous_ext (fun x => / (sigma^2)*((mu-x)*General_Gaussian_PDF mu sigma x))).
  intros.
  rewrite Derive_General_Gaussian_PDF.
  now rewrite Rmult_assoc.
  trivial.
  unfold General_Gaussian_PDF.
  apply (@ex_derive_continuous).
  now auto_derive.
Qed.

Lemma General_Gaussian_PDF_normed (mu sigma:R) : 
  sigma>0 ->
  ex_RInt_gen Standard_Gaussian_PDF (Rbar_locally' m_infty) (at_point (- mu / sigma)) ->
  ex_RInt_gen Standard_Gaussian_PDF (at_point (- mu / sigma)) (Rbar_locally' p_infty) ->
  is_RInt_gen (General_Gaussian_PDF mu sigma) (Rbar_locally' m_infty) (Rbar_locally' p_infty) 1.
Proof.
  intros.
  assert (Rbar_plus (Rbar_mult (/ sigma) m_infty) (- mu / sigma) = m_infty).
  rewrite Rbar_mult_comm.
  rewrite Rbar_mult_m_infty_pos.
  now compute.
  apply Rinv_0_lt_compat; lra.  
  assert (Rbar_plus (Rbar_mult (/ sigma) p_infty) (- mu / sigma) = p_infty).
  rewrite Rbar_mult_comm.
  rewrite Rbar_mult_p_infty_pos.
  now compute.
  apply Rinv_0_lt_compat; lra.  
  
  apply (is_RInt_gen_ext (fun x =>  / sigma * Standard_Gaussian_PDF (/sigma *x + (-mu/sigma)))).
  apply filter_forall.
  intros.
  rewrite gen_from_std.
  apply Rmult_eq_compat_l.
  f_equal; lra.
  trivial.
  apply is_RInt_gen_comp_lin with (u := /sigma) (v := -mu/sigma) 
                                  (f:=Standard_Gaussian_PDF).
  apply Rinv_neq_0_compat.
  now apply Rgt_not_eq.
  replace (Rbar_plus (Rbar_mult (/ sigma) m_infty) (- mu / sigma)) with
          (m_infty).
  replace (/ sigma * 0 + - mu / sigma) with (-mu/sigma) by lra.
  trivial.
  replace (/ sigma * 0 + - mu / sigma) with (-mu/sigma) by lra.  
  replace (Rbar_plus (Rbar_mult (/ sigma) p_infty) (- mu / sigma)) with
          (p_infty).
  trivial.
  apply ex_RInt_Standard_Gaussian_PDF.
  replace (Rbar_plus (Rbar_mult (/ sigma) m_infty) (- mu / sigma)) with
          (m_infty).
  replace (Rbar_plus (Rbar_mult (/ sigma) p_infty) (- mu / sigma)) with
          (p_infty).
  apply Standard_Gaussian_PDF_normed.
Qed.  

Lemma mean_general_gaussian (mu sigma:R) :
  sigma > 0 ->
    ex_RInt_gen Standard_Gaussian_PDF (Rbar_locally' m_infty) (at_point (- mu / sigma)) ->
    ex_RInt_gen Standard_Gaussian_PDF (at_point (- mu / sigma)) (Rbar_locally' p_infty) ->

    is_RInt_gen (fun t => t*General_Gaussian_PDF mu sigma t) 
                           (Rbar_locally' m_infty) (Rbar_locally' p_infty) mu.
Proof.
  intros.
  assert (sigma <> 0).
  now apply Rgt_not_eq.
  apply (is_RInt_gen_ext (fun t => mu*General_Gaussian_PDF mu sigma t - (mu-t)*General_Gaussian_PDF mu sigma t)). 
  apply filter_forall.
  intros.
  apply Rminus_diag_uniq; lra.
  replace (mu) with (mu*1 - 0) at 1 by lra.
  apply (@is_RInt_gen_minus).
  apply Rbar_locally'_filter.
  apply Rbar_locally'_filter.  
  apply (@is_RInt_gen_scal).
  apply Rbar_locally'_filter.
  apply Rbar_locally'_filter.  
  now apply General_Gaussian_PDF_normed.
  apply (is_RInt_gen_ext (fun t => sigma^2 * Derive (General_Gaussian_PDF mu sigma) t)).
  apply filter_forall.
  intros.
  rewrite Derive_General_Gaussian_PDF.
  apply Rminus_diag_uniq; field_simplify; lra.
  assumption.
  replace (0) with (sigma^2 * 0) by lra.
  apply (@is_RInt_gen_scal).
  apply Rbar_locally'_filter.
  apply Rbar_locally'_filter.    
  replace (0) with (0 - 0) by lra.
  apply is_RInt_gen_Derive.
  apply filter_forall.
  intros.
  now apply ex_derive_General_Gaussian_PDF.
  apply filter_forall.
  intros.
  apply continuous_Derive_General_Gaussian_PDF.
  now unfold General_Gaussian_PDF.
  replace (0) with ( / (sigma * sqrt (2*PI)) * 0) by lra.  
  apply is_lim_scal_l with (a:= / (sigma * sqrt (2 * PI))) (l := 0).
  apply (is_lim_ext (fun t => exp(-((/sigma * t)+ (-mu/sigma))^2/2))).
  intros.
  f_equal; now field_simplify.
  apply is_lim_comp_lin with (f := fun t => exp(-t^2/2)) (a := /sigma) (b:= -mu/sigma).
  replace (Rbar_plus (Rbar_mult (/ sigma) m_infty) (- mu / sigma)) with (m_infty).
  apply limexp_neg_minf.
  rewrite Rbar_mult_comm.
  rewrite Rbar_mult_m_infty_pos.
  now compute.
  apply Rinv_0_lt_compat; lra.
  now apply Rinv_neq_0_compat.
  unfold General_Gaussian_PDF.
  replace (0) with ( / (sigma * sqrt (2*PI)) * 0) by lra.  
  apply is_lim_scal_l with (a:= / (sigma * sqrt (2 * PI))) (l := 0).
  apply (is_lim_ext (fun t => exp(-((/sigma * t)+ (-mu/sigma))^2/2))).
  intros.
  f_equal; now field_simplify.
  apply is_lim_comp_lin with (f := fun t => exp(-t^2/2)) (a := /sigma) (b:= -mu/sigma).
  replace (Rbar_plus (Rbar_mult (/ sigma) p_infty) (- mu / sigma)) with (p_infty).  
  apply limexp_neg_inf.
  rewrite Rbar_mult_comm.
  rewrite Rbar_mult_p_infty_pos.
  now compute.
  apply Rinv_0_lt_compat; lra.
  now apply Rinv_neq_0_compat.
Qed.
  
Lemma variance_general_gaussian (mu sigma : R) :
  sigma > 0 ->
  ex_RInt_gen (fun t : R => sigma ^ 2 * t ^ 2 * Standard_Gaussian_PDF t)
              (Rbar_locally' m_infty) (at_point (- mu / sigma)) ->
  ex_RInt_gen (fun t : R => sigma ^ 2 * t ^ 2 * Standard_Gaussian_PDF t)
              (at_point (- mu / sigma)) (Rbar_locally' p_infty) ->
  is_RInt_gen (fun t => (t-mu)^2*General_Gaussian_PDF mu sigma t) 
              (Rbar_locally' m_infty) (Rbar_locally' p_infty) (sigma^2).
Proof.
  intros.
  assert (sigma <> 0).
  now apply Rgt_not_eq.
  assert (Rbar_plus (Rbar_mult (/ sigma) m_infty) (- mu / sigma) = m_infty).
  rewrite Rbar_mult_comm.
  rewrite Rbar_mult_m_infty_pos.
  now compute.
  apply Rinv_0_lt_compat; lra.  
  assert (Rbar_plus (Rbar_mult (/ sigma) p_infty) (- mu / sigma) = p_infty).
  rewrite Rbar_mult_comm.
  rewrite Rbar_mult_p_infty_pos.
  now compute.
  apply Rinv_0_lt_compat; lra.  
  apply (is_RInt_gen_ext (fun t => /sigma * (sigma^2 * (/sigma * t + (-mu/sigma))^2 * Standard_Gaussian_PDF(/sigma*t + (-mu/sigma))))).
  apply filter_forall.
  intros.
  rewrite gen_from_std.
  replace (/sigma * x0 + - mu/sigma) with ((x0-mu)/sigma) by lra.
  apply Rminus_diag_uniq; field_simplify; lra.
  lra.
  apply is_RInt_gen_comp_lin with (u := /sigma) (v := -mu/sigma) 
                                  (f:=fun t => sigma^2 * t^2 * Standard_Gaussian_PDF t).
  now apply Rinv_neq_0_compat.
  replace (Rbar_plus (Rbar_mult (/ sigma) m_infty) (- mu / sigma)) with
          (m_infty).
  replace (/ sigma * 0 + - mu / sigma) with (-mu/sigma) by lra.
  assumption.
  replace (/ sigma * 0 + - mu / sigma) with (-mu/sigma) by lra.
  replace (Rbar_plus (Rbar_mult (/ sigma) p_infty) (- mu / sigma)) with
          (p_infty).
  assumption.
  intros.
  apply (ex_RInt_ext (fun t => sigma^2 * (t^2 * Standard_Gaussian_PDF t))).
  intros.
  lra.
  apply (@ex_RInt_scal) with (k := sigma^2) (f := fun t => t^2 * Standard_Gaussian_PDF t).
  apply ex_RInt_Standard_Gaussian_variance_PDF.
  replace (sigma^2) with (sigma^2 * 1) at 1 by lra.
  apply (is_RInt_gen_ext (fun t=>sigma^2 * (t^2 * Standard_Gaussian_PDF t))).
  apply filter_forall.
  intros.
  lra.
  apply (@is_RInt_gen_scal).
  apply Rbar_locally'_filter.
  apply Rbar_locally'_filter.      
  replace (Rbar_plus (Rbar_mult (/ sigma) m_infty) (- mu / sigma)) with 
      (m_infty).
  replace (Rbar_plus (Rbar_mult (/ sigma) p_infty) (- mu / sigma)) with 
      (p_infty).
  apply variance_standard_gaussian.
Qed.

Definition Indicator (a b t:R) :=
  (if Rlt_dec t a then 0 else 
     (if Rgt_dec t b then 0 else 1)).

Definition Uniform_PDF (a b t:R) := 
  (/ (b-a)) * Indicator a b t.

Lemma Uniform_normed0 (a b:R) :
  a < b -> is_RInt (fun t => (/ (b-a))) a b 1.
Proof.  
  intros.
  replace (1) with (scal (b-a) (/ (b-a))).
  apply (@is_RInt_const).
  compute; field_simplify; lra.
Qed.

Lemma Indicator_left (a b:R) (f : R -> R) :
  a < b -> is_RInt_gen (fun t => (f t) * (Indicator a b t)) (Rbar_locally' m_infty) (at_point a) 0.
Proof.  
  - intros.
    unfold Indicator.
    apply (is_RInt_gen_ext (fun _ =>  0)).
    + exists (fun y => y<a) (fun x => x=a).
      unfold Rbar_locally'.
      exists (a).
      intros; assumption.
      now unfold at_point.
      intros x y H0 H1.
      unfold fst, snd.
      subst.
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros.
      replace (is_left (Rlt_dec x0 a)) with true.
      lra.
      now destruct (Rlt_dec x0 a).
    + apply (is_RInt_gen_ext (Derive (fun _ => 0))).
      * apply filter_forall.
        intros.
        apply Derive_const.
      * replace (0) with (0 - 0) at 1 by lra.
        apply is_RInt_gen_Derive with (f0 := fun _ => 0) (la := 0) (lb := 0).
        ++ apply filter_forall.
           intros.
           apply ex_derive_const.
        ++ apply filter_forall.
           intros.
           apply continuous_const.
        ++ apply filterlim_const.
        ++ apply filterlim_const.
Qed.

Lemma Indicator_right (a b:R) (f : R -> R) :
  a < b -> is_RInt_gen (fun t => (f t) * (Indicator a b t)) (at_point b) (Rbar_locally' p_infty)  0.
Proof.  
  - intros.
    unfold Indicator.
    apply (is_RInt_gen_ext (fun _ =>  0)).
    + exists (fun x => x=b) (fun y => b<y).
      now unfold at_point.
      unfold Rbar_locally'.
      exists (b).
      intros; trivial.
      intros x y H0 H1.
      unfold fst, snd.
      subst.
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros.
      replace (is_left (Rlt_dec x a)) with false.
      replace (is_left (Rgt_dec x b)) with true.
      lra.
      destruct (Rgt_dec x b).
      intuition.
      intuition.
      destruct (Rlt_dec x a).
      lra.
      intuition.
    + apply (is_RInt_gen_ext (Derive (fun _ => 0))).
      apply filter_forall.
      intros.
      apply Derive_const.
      replace (0) with (0 - 0) at 1 by lra.
      apply is_RInt_gen_Derive with (f0 := fun _ => 0) (la := 0) (lb := 0).
      * apply filter_forall.
        intros.
        apply ex_derive_const.
      * apply filter_forall.
        intros.
        apply continuous_const.
      * apply filterlim_const.
      * apply filterlim_const.
Qed.

Lemma Indicator_full (a b:R) (f : R -> R) (l:R):
  a < b -> is_RInt f a b l -> is_RInt_gen (fun t => (f t) * (Indicator a b t)) (Rbar_locally' m_infty) (Rbar_locally' p_infty) l.
Proof.
  - intros.
    replace (l) with (0 + l) by lra.
    apply (@is_RInt_gen_Chasles) with (b:=a).
    + apply Rbar_locally'_filter.
    + apply Rbar_locally'_filter.    
    + apply (is_RInt_gen_ext (fun t => (f t) * (Indicator a b t))).
      * apply filter_forall.
        intros.
        now apply Rmult_eq_compat_l.
      * now apply Indicator_left with (f := f).
    + replace (l) with (l + 0) by lra.
      apply (@is_RInt_gen_Chasles) with (b:=b).
      * apply at_point_filter.
      * apply Rbar_locally'_filter.  
      * apply is_RInt_gen_at_point.
        apply (is_RInt_ext f).
        rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros.
        ++ unfold Indicator.
           replace (is_left (Rlt_dec x a)) with false.
           replace (is_left (Rgt_dec x b)) with false.
           lra.
           destruct (Rgt_dec x b).
           lra.
           tauto.
           destruct (Rlt_dec x a).
           lra.
           tauto.
        ++ trivial.
      * now apply Indicator_right.
Qed.

Lemma Uniform_full (a b:R) (f : R -> R) (l:R):
  a < b -> is_RInt (fun t => (f t)*(/ (b-a))) a b l -> is_RInt_gen (fun t => (f t) * (Uniform_PDF a b t)) (Rbar_locally' m_infty) (Rbar_locally' p_infty) l.
Proof.
  intros.
  apply (is_RInt_gen_ext (fun t => (f t) * (/ (b-a)) * Indicator a b t)).
  apply filter_forall.
  intros.
  unfold Uniform_PDF.
  now ring_simplify.
  now apply Indicator_full with (f := fun t => f t * (/ (b - a))).
Qed.

Lemma Uniform_PDF_non_neg (a b t :R) :
  a < b -> Uniform_PDF a b t >= 0.
Proof.  
  intros.
  unfold Uniform_PDF.
  replace (0) with ((/ (b-a)) * 0) by lra.
  apply Rmult_ge_compat_l with (r2 := 0).
  left.
  apply Rinv_0_lt_compat; lra.
  unfold Indicator.
  destruct (is_left (Rlt_dec t a)); try lra.
  destruct (is_left (Rgt_dec t b)); try lra.
Qed.

Lemma Uniform_normed (a b:R) :
  a < b -> is_RInt_gen (Uniform_PDF a b) (Rbar_locally' m_infty) (Rbar_locally' p_infty) 1.
Proof.
  intros.
  apply (is_RInt_gen_ext (fun t => 1 * (Uniform_PDF a b t))).
  apply filter_forall.
  intros.
  lra.
  apply Uniform_full with (f := fun _ => 1) (l := 1); try lra.
  apply (is_RInt_ext (fun t => (/ (b-a)))).
  intros.
  now ring_simplify.
  now apply Uniform_normed0.
Qed.

Lemma Uniform_mean0 (a b:R) :
  a < b -> is_RInt (fun t => t*(/ (b-a))) a b ((b+a)/2).
Proof.  
  - intros.
    replace ((b+a)/2) with  (/(b-a)*(b^2/2) - (/(b-a)*(a^2/2))).
    + apply (@is_RInt_derive) with (f := fun t => (/(b-a))*(t^2/2)).      
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros.
      replace (x * (/ (b-a))) with (/(b-a) * x) by lra.
      apply is_derive_scal with (k := /(b-a)) (f:= (fun t => t^2/2)).
      apply (is_derive_ext (fun t => t * ((/2) * t))).
      intros.
      now field_simplify.
      replace (x) with (1 * (/2 * x) + x * /2) at 2 by lra.
      apply (@is_derive_mult) with (f := id) (g:= fun t => (/2) * t).
      apply (@is_derive_id).
      replace (/2) with (/2 * 1) at 1 by lra.
      apply (@is_derive_scal).
      apply (@is_derive_id).
      intros.
      apply Rmult_comm.
      intros.
      apply (@continuous_scal_l).
      apply continuous_id.
    + apply Rminus_diag_uniq; field_simplify; lra.
Qed.

Lemma Uniform_mean (a b:R) :
  a < b -> is_RInt_gen (fun t => t*(Uniform_PDF a b t)) (Rbar_locally' m_infty) (Rbar_locally' p_infty) ((b+a)/2).
Proof.
  intros.
  apply Uniform_full with (f := fun t => t); trivial.
  now apply Uniform_mean0.
Qed.

Lemma Uniform_variance0 (a b:R) :
  a < b -> is_RInt (fun t => (/ (b-a)) * (t-(b+a)/2)^2) a b ((b-a)^2/12).
Proof.
  - intros.
    replace ((b-a)^2/12) with (scal (/(b-a)) ((b-a)^3/12)).
    + apply (@is_RInt_scal) with (k := /(b-a)) (f := fun t => (t - (b+a)/2)^2) (If := (b-a)^3/12).
      apply (is_RInt_ext (fun t => t^2 - (b+a)*t + (b+a)^2/4)).
      * intros.
        now field_simplify.
      * replace ((b-a)^3/12) with ((a-b)*(b^2+4*a*b+a^2)/6 + ((b+a)^2/4)*(b-a)).
        apply is_RInt_plus with (f:= fun t=> t^2 - (b+a)*t) (g := fun t=> (b+a)^2/4).
        -- replace ((a - b) * (b ^ 2 + 4 * a * b + a ^ 2) / 6) with ((b^3/3-a^3/3) - (b-a)*(b+a)^2/2).
           apply is_RInt_minus with (f := fun t => t^2) (g := fun t => (b+a)*t).
           apply (@is_RInt_derive) with (f := fun t => t^3/3).
           ++ intros.
              apply (is_derive_ext (fun t => (/3) * t^3)).
              intros; now field_simplify.
              replace (x^2) with (/3 * (INR(3%nat) * 1 * x^2)).
              apply is_derive_scal.
              apply is_derive_pow with (f:=id) (n := 3%nat) (l:=1).
              apply (@is_derive_id).
              simpl; now field_simplify.
           ++ rewrite Rmax_right; try lra.
              rewrite Rmin_left; try lra.
              intros.
              cont_helper.
           ++ replace ((b - a) * (b + a) ^ 2 / 2) with ((b+a)*((b^2/2-a^2/2))).
              apply (@is_RInt_scal).
              apply is_RInt_derive with (f:=fun x => x^2/2).
              rewrite Rmax_right; try lra.
              rewrite Rmin_left; try lra.
              ** intros.
                 apply (is_derive_ext (fun t => (/2) * t^2)).
                 intros.
                 now field_simplify.
                 replace (x) with (/2 * (2 * x)) at 2 by lra.
                 apply is_derive_scal.
                 replace (2 * x) with (INR(2%nat) * 1 * x^1) by
                 (simpl; field_simplify; lra).
                 apply is_derive_pow with (f:=id) (n := 2%nat) (l:=1).
                 apply (@is_derive_id).
              ** rewrite Rmax_right; try lra.
                 rewrite Rmin_left; try lra.
                 intros.
                 apply continuous_id.
              ** now field_simplify.
           ++ apply Rminus_diag_uniq; compute; field_simplify; lra.
        -- replace ((b + a) ^ 2 / 4 * (b - a)) with (scal (b-a) ((b+a)^2/4)).
           apply (@is_RInt_const).
           compute; now field_simplify.
        -- apply Rminus_diag_uniq; field_simplify; lra.
    + compute; field_simplify; lra.
Qed.

Lemma Uniform_variance (a b:R) :
  a < b -> is_RInt_gen (fun t => (t-(b+a)/2)^2*(Uniform_PDF a b t)) (Rbar_locally' m_infty) (Rbar_locally' p_infty) ((b-a)^2/12).
Proof.
  intros.
  apply Uniform_full with (f := (fun t => (t-(b+a)/2)^2)); trivial.
  apply (is_RInt_ext (fun t => (/ (b-a)) * (t-(b+a)/2)^2)).
  intros.
  now ring_simplify.
  now apply Uniform_variance0.
Qed.

Axiom Fubini:
  forall (a b c d: R) (f: R -> R -> R) (x y: R), 
    a < x < b -> c < y < d -> 
    continuity_2d_pt f x y -> 
    RInt (fun u => RInt (fun v => f u v) a b) c d =
    RInt (fun v => RInt (fun u => f u v) c d) a b.

(* the iterated integrals below are equal in the sense either they are both infinite, or they are both finite with the same value *)

Axiom Fubini_gen :
  forall (Fa Fb Fc Fd: (R -> Prop) -> Prop)
         (f: R -> R -> R) ,
  filter_prod Fa Fb
    (fun ab => forall (x : R), Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) ->
           filter_prod Fc Fd
                       (fun bc => forall (y : R), 
                            Rmin (fst bc) (snd bc) <= y <= Rmax (fst bc) (snd bc) -> 
                            continuity_2d_pt f x y)) ->
  filter_prod Fa Fb
    (fun ab => forall (x : R), 
         Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) ->
         filter_prod Fc Fd
                     (fun bc => forall (y : R), 
                          Rmin (fst bc) (snd bc) <= y <= Rmax (fst bc) (snd bc) ->
                          f x y >= 0)) ->    
  ex_RInt_gen (fun u => RInt_gen (fun v => f u v) Fa Fb) Fc Fd ->
  ex_RInt_gen (fun v => RInt_gen (fun u => f u v) Fc Fd) Fa Fb ->
  RInt_gen (fun u => RInt_gen (fun v => f u v) Fa Fb) Fc Fd =
    RInt_gen (fun v => RInt_gen (fun u => f u v) Fc Fd) Fa Fb.

Lemma sqr_plus1_gt (x:R):
  x^2 + 1 > 0.
Proof.
  intros.
  apply Rplus_le_lt_0_compat.
  apply pow2_ge_0.
  lra.
Qed.  

Lemma sqr_plus1_neq (x:R):
  x^2 + 1 <> 0.
Proof.
  apply Rgt_not_eq.  
  apply sqr_plus1_gt.
Qed.

Lemma deriv_erf00 (x0 x2:R) :
  Derive (fun u : R => - / (2 * x0 ^ 2 + 2) * exp (- (u ^ 2 + (u * x0) ^ 2))) x2 =
    x2 * exp (- (x2 ^ 2 + (x2 * x0) ^ 2)). 
Proof.
  rewrite Derive_scal; solve_derive.
  rewrite Derive_comp; solve_derive.
  rewrite Derive_opp; solve_derive.
  rewrite Derive_plus; solve_derive.
  rewrite Derive_pow; solve_derive.
  rewrite Derive_id; solve_derive.
  rewrite Derive_pow; solve_derive.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_id.
  rewrite Derive_const.
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (- (x2 ^ 2 + (x2 * x0) ^ 2))).
  rewrite derive_pt_exp.
  simpl.
  apply Rminus_diag_uniq; field_simplify; try lra.
  replace (2*(x0 * x0) + 2) with (2*(x0^2 + 1)) by lra.
  apply Rmult_integral_contrapositive_currified; try lra.
  apply sqr_plus1_neq.
Qed.

Lemma atan_tan_inv (x:R) :
  -PI/2 < x < PI/2 -> atan (tan x) = x.
Proof.
  intros.
  unfold atan.
  destruct (pre_atan (tan x)) as [y [yrang yinv]].
  now apply tan_is_inj in yinv.
Qed.

Lemma lim_atan_inf:
  is_lim atan p_infty (PI/2).
Proof.
  apply is_lim_spec.
  unfold is_lim'.
  intros.
  assert(atan_upper:forall x, atan x < PI/2)
    by apply atan_bound.
  unfold Rbar_locally'.
  destruct (Rlt_dec (PI/2-eps) 0).
  - exists (0).
    intros.
    rewrite Rabs_left.
    + assert (atan 0 < atan x)
             by now apply atan_increasing.
      rewrite atan_0 in H0; try lra.
    + now apply Rlt_minus.
  - exists (tan (PI/2 - eps)).
    assert (eps > 0)
      by now destruct eps.
    intros.
    rewrite Rabs_left; try lra.
    + assert (atan (tan (PI/2 - eps)) < atan x)
       by now apply atan_increasing.
      rewrite atan_tan_inv in H1; try lra.
    + now apply Rlt_minus.
Qed.
                                          
Lemma erf_atan:
  is_RInt_gen (fun s : R => / (2 * s ^ 2 + 2)) (at_point 0) 
              (Rbar_locally' p_infty) (PI / 4).
Proof.
    + apply (is_RInt_gen_ext (Derive (fun s => /2 * atan s))).
      * apply filter_forall.
        intros.
        replace (/ (2 * x0^2 + 2)) with ( (/2) * (/ (x0^2+1))).
        rewrite Derive_scal.
        apply Rmult_eq_compat_l.
        rewrite <- Derive_Reals with (pr := derivable_pt_atan x0).
        rewrite derive_pt_atan.
        unfold Rsqr.
        replace (1+x0*x0) with (x0^2+1) by lra.
        unfold Rdiv.
        lra.
        field.
        split.
        replace (2*x0^2 + 2) with (2*(x0^2+1)) by lra.
        apply Rmult_integral_contrapositive.
        split.
        lra.
        apply sqr_plus1_neq.
        apply sqr_plus1_neq.
      * replace (PI/4) with (PI/4 - 0) by lra.
        apply is_RInt_gen_Derive.
        - apply filter_forall.
           intros.
           apply ex_derive_scal.
           apply ex_derive_Reals_1.
           apply derivable_pt_atan.
        - apply filter_forall.
           intros.
           apply (continuous_ext (fun s => /2 * /(s^2+1))).
           intros.
           symmetry.
           replace (/ (x1^2+1)) with (Derive atan x1).
           apply Derive_scal with (f := atan ) (k := /2) (x := x1).
           rewrite <- Derive_Reals with (pr := derivable_pt_atan x1).
           rewrite derive_pt_atan.
           unfold Rsqr.
           replace (1 + x1*x1) with (x1^2 + 1) by lra; lra.
           apply (@ex_derive_continuous).
           auto_derive.
           apply sqr_plus1_neq.
        - unfold filterlim, filter_le.
          intros.
          unfold filtermap, at_point.
          replace (/2 * atan 0) with (0).
          now apply locally_singleton.
          rewrite atan_0; lra.
        - replace (filterlim (fun s : R => / 2 * atan s) (Rbar_locally' p_infty) (locally (PI / 4))) with (is_lim (fun s : R => / 2 * atan s) p_infty (Rbar_mult (/2) (PI/2))).
           apply is_lim_scal_l with (a := /2) (f := atan).
           apply lim_atan_inf.
           unfold is_lim.
           replace (Rbar_locally (Rbar_mult (/2) (PI/2))) with (Rbar_locally (PI/4)).
           reflexivity.
           f_equal; simpl; f_equal; field.
Qed.

Lemma erf_exp0 (x0:R) :
   is_RInt_gen (fun u : R => u * exp (- (u ^ 2 + (u * x0) ^ 2))) 
               (at_point 0) (Rbar_locally' p_infty) (/ (2 * x0 ^ 2 + 2)).
Proof.
      replace (/ (2*x0^2+2)) with (0 - (- / (2*x0^2+2))).
      * apply (is_RInt_gen_ext (Derive (fun u => -/(2*x0^2+2) * exp(-(u^2+(u*x0)^2))))).
        -- apply filter_forall.
           intros.
           apply deriv_erf00.
        -- apply is_RInt_gen_Derive with (f := fun u => -/(2*x0^2+2)* exp(-(u^2+(u*x0)^2))) (lb:=0) (la := - / (2*x0^2+2)).
           ++ apply filter_forall.
              intros.
              solve_derive.
           ++ apply filter_forall.
              intros.
              apply (continuous_ext (fun x2 => x2 * exp (- (x2 ^ 2 + (x2 * x0) ^ 2)))).
              ** intros.
                 symmetry.
                 apply deriv_erf00.
              ** apply (@ex_derive_continuous).
                 solve_derive.
           ++ unfold filterlim, filter_le.
              intros.
              unfold filtermap, at_point.
              replace (- / (2 * x0 ^ 2 + 2) * exp (- (0 ^ 2 + (0 * x0) ^ 2))) with (- / (2 * x0 ^ 2 + 2)).
              now apply locally_singleton.
              replace (- (0 ^ 2 + (0 * x0) ^ 2)) with (0) by lra.
              rewrite exp_0; lra.
           ++ replace (filterlim (fun u : R => - / (2 * x0 ^ 2 + 2) * exp (- (u ^ 2 + (u * x0) ^ 2)))
                                 (Rbar_locally' p_infty) (locally 0)) with 
                  (is_lim (fun u : R => - / (2 * x0 ^ 2 + 2) * exp (- (u ^ 2 + (u * x0) ^ 2))) p_infty 0).
              ** replace  (Finite 0) with (Rbar_mult  (- / (2 * x0 ^ 2 + 2)) 0).
                 apply is_lim_scal_l with (a := - / (2 * x0 ^ 2 + 2) ).
                 apply is_lim_comp with (l:=m_infty).
                 apply is_lim_exp_m.
                 replace (m_infty) with (Rbar_opp p_infty).
                 apply is_lim_opp.
                 apply (is_lim_ext (fun y => y * y * (1 + Rsqr x0))).
                 intros.
                 unfold Rsqr.
                 now ring_simplify.
                 replace (p_infty) with (Rbar_mult (Rbar_mult p_infty p_infty) (1 + Rsqr x0)) at 2.
                 apply is_lim_mult.
                 apply is_lim_mult.
                 apply is_lim_id.
                 apply is_lim_id.
                 now compute.
                 apply is_lim_const.
                 compute.
                 replace (x0 * x0) with (x0^2) by lra.
                 rewrite Rplus_comm.
                 apply sqr_plus1_neq.
                 replace (Rbar_mult p_infty p_infty) with (p_infty).
                 apply is_Rbar_mult_unique.
                 apply is_Rbar_mult_p_infty_pos.                 
                 simpl.
                 rewrite Rsqr_pow2.
                 rewrite Rplus_comm.
                 apply sqr_plus1_gt.
                 now compute.
                 now compute.
                 unfold Rbar_locally'.
                 exists x0.
                 intros.
                 discriminate.
                 simpl; f_equal; ring.
              ** now unfold is_lim.
      * now ring_simplify.
Qed.

Lemma erf_int00 : 
  is_RInt_gen (fun s => RInt_gen (fun u => u*exp(-(u^2+(u*s)^2))) (at_point 0)  (Rbar_locally' p_infty)) (at_point 0) (Rbar_locally' p_infty) (PI / 4).
Proof.
  - apply (is_RInt_gen_ext (fun s => / (2*s^2+2))).
    apply filter_forall.
    + intros.
      symmetry.
      apply is_RInt_gen_unique.
      apply erf_exp0.
    + apply erf_atan.
Qed.

Lemma erf_ex_RInt0 (x0:R):
  ex_RInt_gen
   (fun v : R =>
    (if  (Rlt_dec v 1) then 1 else v * exp (- v ^ 2)) * exp (- x0 ^ 2))
   (at_point 0) (Rbar_locally' p_infty).
Proof.
  unfold ex_RInt_gen.
  exists (exp(-x0^2) + / (2* exp 1) * exp(-x0^2)).
  apply is_RInt_gen_Chasles with (b:=1) (l1 := exp(-x0^2)) (l2 := / (2 * exp 1) * exp(-x0^2))
                                 (f :=    (fun v : R =>
    (if (Rlt_dec v 1) then 1 else v * exp (- v ^ 2)) * exp (- x0 ^ 2))).
  apply is_RInt_gen_at_point.
  apply (is_RInt_ext (fun v => exp(-x0^2))).
  intros.
  rewrite Rmin_left in H; try lra.
  rewrite Rmax_right in H; try lra.
  destruct (Rlt_dec x 1).
  unfold is_left; lra.
  lra.
  replace (exp(-x0^2)) with ((1 - 0) * (exp(-x0^2))) at 1.
  apply (@is_RInt_const).
  lra.
  apply (is_RInt_gen_ext (fun v => v* exp(-v^2)*exp(-x0^2))).  
  exists (fun a => a = 1) (fun b => b>1000).
  now unfold at_point.
  unfold Rbar_locally'; now exists 1000.
  intros.
  subst.
  unfold fst, snd in H1.
  rewrite Rmin_left in H1; try lra.
  rewrite Rmax_right in H1; try lra.
  destruct (Rlt_dec x1 1); try lra.
  now unfold is_left.
  apply (is_RInt_gen_ext (Derive (fun v => -(/2)*exp(-x0^2) * exp(-v^2)))).  
  apply filter_forall.
  intros.
  rewrite Derive_scal.  
  rewrite Derive_comp; solve_derive.
  rewrite Derive_opp; solve_derive.
  rewrite Derive_mult; solve_derive.    
  rewrite Derive_id.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_id.
  rewrite Derive_const.
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (- (x1 ^ 2))).
  rewrite derive_pt_exp.
  ring_simplify; try lra.
  replace  (/ (2 * exp 1) * exp (- x0 ^ 2)) with (0 - -  (/ (2 * exp 1) * exp (- x0 ^ 2))) by lra.
  apply is_RInt_gen_Derive.
  apply filter_forall.
  intros.
  now auto_derive.
  apply filter_forall.  
  intros.
  apply (continuous_ext (fun v => exp(-x0^2)*v*exp(-v^2))).
  intros.
  rewrite Derive_scal.
  rewrite Derive_comp; solve_derive.  
  rewrite Derive_opp; solve_derive.
  rewrite Derive_mult; solve_derive.    
  rewrite Derive_id.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_id.
  rewrite Derive_const.
  rewrite <- Derive_Reals with (pr := derivable_pt_exp (- (x2 ^ 2))).
  rewrite derive_pt_exp.
  ring_simplify; try lra.
  apply (@ex_derive_continuous).
  now auto_derive.
  unfold filterlim, filter_le.
  intros.
  unfold filtermap, at_point.
  apply locally_singleton.
  replace (- / 2 * exp (- x0 ^ 2) * exp (- 1 ^ 2)) with (- (/ (2 * exp 1) * exp (- x0 ^ 2))); trivial.
  apply Rminus_diag_uniq; field_simplify.
  replace (exp (-1^2)) with (/ exp 1).
  field_simplify; try lra.
  apply Rgt_not_eq.  
  apply exp_pos.
  replace (-1^2) with (-1) by lra.
  rewrite exp_Ropp.
  now unfold IPR.
  apply Rgt_not_eq.  
  apply exp_pos.
  replace (filterlim (fun v : R => - / 2 * exp (- x0 ^ 2) * exp (- v ^ 2))
    (Rbar_locally' p_infty) (locally 0)) with (is_lim (fun v : R => - / 2 * exp (- x0 ^ 2) * exp (- v ^ 2)) p_infty 0).
  replace (Finite 0) with (Rbar_mult (-/2 * exp(-x0^2)) 0).
  apply is_lim_scal_l.
  apply (is_lim_ext (fun t => / exp(t^2))).
  intros.
  symmetry.
  apply exp_Ropp.
  replace (Finite 0) with (Rbar_inv p_infty).
  apply is_lim_inv.
  eapply is_lim_le_p_loc; [idtac | apply is_lim_exp_p].
  unfold Rbar_locally'.
  exists 2; intros.
  left.
  apply exp_increasing.
  replace (x) with (x*1) at 1 by lra.
  replace (x^2) with (x*x) by lra.
  apply Rmult_lt_compat_l; lra.
  discriminate.
  now compute.
  apply Rbar_mult_0_r.
  now unfold is_lim.
Qed.

Lemma erf_ex_RInt1 (x0:R):
  ex_RInt_gen
   (fun v : R => exp(-(x0^2 + v^2)))
   (at_point 0) (Rbar_locally' p_infty).
Proof.
    apply (ex_RInt_gen_ext (fun v => exp(-(x0^2))*exp(-v^2))).
    apply filter_forall.
    intros.
    replace (-(x0^2 + x1^2)) with ((-x0^2) + (-x1^2)) by lra.
    symmetry.
    apply exp_plus.
    apply ex_RInt_gen_bound with (g := fun v => (if (Rlt_dec v 1) then 1 else v*exp(-v^2))*exp(-x0^2)).
    apply at_point_filter.
    apply Rbar_locally'_filter.
    unfold filter_Rlt.
    exists 1.
    exists (fun x => x=0) (fun y => y>1000).
    now unfold at_point.
    unfold Rbar_locally'; now exists 1000.
    intros.
    subst.
    unfold fst, snd.
    lra.
    apply erf_ex_RInt0.
    exists (fun x => x=0) (fun y => y>1000).
    now unfold at_point.    
    unfold Rbar_locally'; now exists 1000.
    intros.
    subst.
    unfold fst, snd.
    split.
    intros.
    split.
    rewrite <- exp_plus.
    left.
    apply exp_pos.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r.
    left.
    apply exp_pos.
    destruct (Rlt_dec x 1).
    unfold is_left.
    rewrite exp_Ropp.
    replace (1) with (/ 1) by lra.
    apply Rinv_le_contravar; try lra.
    replace (1) with (exp 0).
    left.
    apply exp_increasing.
    replace (x ^ 2) with (Rsqr x).
    apply Rlt_0_sqr; lra.
    simpl.
    unfold Rsqr; lra.
    apply exp_0.
    unfold is_left.
    replace (exp(-x^2)) with (1 * exp(-x^2)) at 1 by lra.
    apply  Rmult_le_compat_r.
    left.
    apply exp_pos.
    lra.
    apply (@ex_RInt_continuous).
    intros.
    apply (@ex_derive_continuous).
    now auto_derive.
Qed.

Lemma erf_ex_RInt2:
  ex_RInt_gen
   (fun v : R => exp(-v^2))
   (at_point 0) (Rbar_locally' p_infty).
Proof.
  apply (ex_RInt_gen_ext (fun v => exp(-(0^2 + v^2)))).  
  apply filter_forall.
  intros.
  f_equal; lra.
  apply erf_ex_RInt1.
Qed.  

Lemma erf_ex_bound1 (u:R) :
  u>=0 -> exp (- (u ^ 2)) <= /(1+u^2).
Proof.
  intros.
  rewrite exp_Ropp.
  destruct H.
  left.
  apply Rinv_1_lt_contravar.
  apply Rplus_le_reg_l with (r:=-1).
  replace (-1 + 1) with (0) by lra.
  replace (-1 + (1 + u^2)) with (u^2) by lra.
  apply pow2_ge_0.
  apply exp_ineq1.
  apply pow2_gt_0; lra.  
  subst.
  replace (0^2) with (0) by lra.
  replace (1 + 0) with (1) by lra.
  rewrite exp_0; lra.
Qed.
  
Lemma erf_ex_bound2 (u v:R) :
  u*v>=0 -> exp (- ((u*v) ^ 2)) <= /(1+(u*v)^2).
Proof.
  intros.
  now apply erf_ex_bound1 with (u:=u*v).
Qed.

Lemma erf_ex_bound3 (u v:R) :
  u>=0 -> v>=0 -> u * exp (- (u ^ 2 + (u * v) ^ 2)) <= u * ( / (1+u^2) * /(1 + (u*v)^2)).
Proof.
  intros.
  apply Rmult_le_compat_l; try lra.
  replace (exp(-(u^2+(u*v)^2))) with (exp(-u^2)*exp(-(u*v)^2)).
  apply Rmult_le_compat.
  left.
  apply exp_pos.
  left.
  apply exp_pos.
  now apply erf_ex_bound1.
  apply erf_ex_bound2.
  replace (0) with (u * 0) by lra.
  now apply Rmult_ge_compat_l.
  rewrite <- exp_plus.
  f_equal; ring.
Qed.

Lemma int_bound3 (u:R) :
  u>0 -> is_RInt_gen (fun v : R =>   u / (1+u^2) * /(1 + (u*v)^2)) 
                      (at_point 0) (Rbar_locally' p_infty) (PI/(2*(u^2+1))).
Proof.
  intros.
  assert (forall x1 : R_UniformSpace,
      / (1 + (u * x1) ^ 2) = Derive (fun y : R => atan (u * y) / u) x1).
  intros.
  symmetry.
  rewrite Derive_div; solve_derive.
  rewrite Derive_const.
  rewrite Derive_comp; solve_derive.
  rewrite Derive_mult; solve_derive.
  rewrite Derive_const.
  rewrite Derive_id.
  rewrite <- Derive_Reals with (pr := derivable_pt_atan (u * x1)).
  rewrite derive_pt_atan.
  unfold Rsqr.
  field_simplify; trivial.
  apply Rgt_not_eq.
  apply plus_Rsqr_gt_0.
  split.
  replace (u*x1*(u*x1)) with ((u*x1)^2).
  apply Rgt_not_eq.
  apply plus_Rsqr_gt_0.
  now ring_simplify.
  lra.
  replace (PI/(2*(u^2+1))) with ((u/(1+u^2)) * (PI/(2*u))).
  apply (@is_RInt_gen_scal).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply (is_RInt_gen_ext (Derive (fun y => atan(u*y)/u))).
  exists (fun a => a=0) (fun b => b>1000).
  now unfold at_point.
  unfold Rbar_locally'; now exists 1000.
  intros.
  symmetry.
  apply H0.
  replace (PI / (2*u)) with ((PI/(2*u)) - 0) by lra.
  apply is_RInt_gen_Derive.
  apply filter_forall.
  intros.
  solve_derive.
  apply filter_forall.
  intros.
  apply (continuous_ext (fun y =>  / (1 + (u * y) ^ 2))).
  apply H0.
  apply (@ex_derive_continuous).  
  auto_derive.
  replace (u*x0*(u*x0*1)) with ((u*x0)^2).
  apply Rgt_not_eq.
  apply plus_Rsqr_gt_0.
  now ring_simplify.
  unfold filterlim, filter_le.
  intros.
  unfold filtermap, at_point.
  replace (u * 0) with (0) by lra.
  rewrite atan_0.
  replace (0 / u) with (0) by lra.
  now apply locally_singleton.
  replace (filterlim (fun y : R => atan (u * y) / u) (Rbar_locally' p_infty)
                     (locally (PI / (2 * u)))) with
          (is_lim (fun y : R => atan (u * y) / u) p_infty (PI / (2 * u))).
  apply (is_lim_ext (fun y => /u * atan(u*y+0))).
  intros.
  unfold Rdiv.
  replace (u*y+0) with (u*y) by lra.
  now rewrite Rmult_comm.
  replace (Finite (PI / (2*u))) with (Rbar_mult (/u) (PI/2)).
  apply (@is_lim_scal_l).
  apply is_lim_comp_lin .
  rewrite Rbar_plus_0_r.
  rewrite Rbar_mult_comm.
  rewrite Rbar_mult_p_infty_pos.
  apply lim_atan_inf.
  lra.
  now apply Rgt_not_eq.
  simpl.
  f_equal; field_simplify; trivial.
  now apply Rgt_not_eq.
  now apply Rgt_not_eq.
  unfold is_lim.
  reflexivity.
  field_simplify; trivial.
  apply sqr_plus1_neq.
  split.
  now apply Rgt_not_eq.
  rewrite Rplus_comm.
  now apply sqr_plus1_neq.  
Qed.

Lemma erf_ex_RInt33 (u:R) :
  u >= 0 -> ex_RInt_gen (fun v : R => u * exp (- (u ^ 2 + (u * v) ^ 2))) (at_point 0)
                       (Rbar_locally' p_infty).
Proof.
  intros.
  destruct H.
  apply ex_RInt_gen_bound with (g:=(fun v : R =>   u / (1+u^2) * /(1 + (u*v)^2))).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply filter_Rlt_at_point_p_infty.
  unfold ex_RInt_gen.
  exists (PI/(2*(u^2+1))).
  now apply int_bound3.
  exists (fun a => a=0) (fun b => b>1000).
  now unfold at_point.
  unfold Rbar_locally'; now exists 1000.
  intros.
  split.
  intros.
  split.
  replace (0) with (u * 0) by lra.
  apply Rmult_le_compat_l; try lra.
  left; apply exp_pos.
  unfold Rdiv.
  rewrite Rmult_assoc.
  apply erf_ex_bound3; try lra.
  unfold fst in H2; lra.
  unfold fst, snd.
  apply (@ex_RInt_continuous).
  intros.
  apply (@ex_derive_continuous).
  solve_derive.
  subst.
  apply (ex_RInt_gen_ext (Derive (fun v => 0))).
  apply filter_forall.
  intros.
  rewrite Derive_const; lra.
  unfold ex_RInt_gen.
  exists (0 - 0).
  apply is_RInt_gen_Derive.
  apply filter_forall.
  intros.
  solve_derive.
  apply filter_forall.
  intros.
  apply (continuous_ext (fun _ => 0)).
  intros.
  now rewrite Derive_const.
  apply (@ex_derive_continuous).
  solve_derive.
  unfold filterlim, filter_le.
  intros.
  unfold filtermap, at_point.
  now apply locally_singleton.
  unfold filterlim, filter_le.
  intros.
  unfold filtermap, Rbar_locally'.
  exists 0.
  intros.
  now apply locally_singleton.
Qed.  

Lemma erf_decr_RInt30 (b:R):
   b >= 0 ->
   interval_decreasing (fun u : R => RInt_gen (fun v : R => exp (- (u ^ 2 + v ^ 2))) (at_point 0) (Rbar_locally' p_infty)) 0 b.
Proof.
  intros.
  unfold interval_decreasing.
  intros.
  apply is_RInt_gen_Rle with (fl := RInt_gen (fun v : R => exp (- (y ^ 2 + v ^ 2)))
                                             (at_point 0) (Rbar_locally' p_infty))
                             (gl := RInt_gen (fun v : R => exp (- (x ^ 2 + v ^ 2)))
                                             (at_point 0) (Rbar_locally' p_infty))                             
                             (f := (fun v : R => exp (- (y ^ 2 + v ^ 2))))
                             (g := (fun v : R => exp (- (x ^ 2 + v ^ 2))))           
                             (F:= at_point 0) (G:= Rbar_locally' p_infty).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply filter_Rlt_at_point_p_infty.  
  apply (@RInt_gen_correct).
  apply Proper_StrongProper, at_point_filter.
  apply Proper_StrongProper, Rbar_locally'_filter.
  apply erf_ex_RInt1.
  apply (@RInt_gen_correct).
  apply Proper_StrongProper, at_point_filter.
  apply Proper_StrongProper, Rbar_locally'_filter.
  apply erf_ex_RInt1.
  exists (fun a => a=0) (fun b => b>1000).
  now unfold at_point.
  unfold Rbar_locally'; now exists 1000.
  intros.
  destruct H2.
  left.
  apply exp_increasing.
  apply Ropp_gt_lt_contravar.
  apply Rplus_lt_compat_r.
  rewrite <- Rsqr_pow2; rewrite <- Rsqr_pow2.  
  apply Rsqr_incrst_1; lra; lra.
  subst; lra.
Qed.

Lemma erf_ex_RInt3_bound (u:R) :
  u > 0 ->
  ex_RInt_gen (fun v : R => u * exp (- (u ^ 2 + (u * v) ^ 2))) 
              (at_point 0) (Rbar_locally' p_infty)  ->
  RInt_gen (fun v : R => u * exp (- (u ^ 2 + (u * v) ^ 2)))
           (at_point 0) (Rbar_locally' p_infty) <= (PI/(2*(u^2+1))).
Proof.
  intros.
  apply is_RInt_gen_Rle with (fl := RInt_gen (fun v : R => u * exp (- (u ^ 2 + (u * v) ^ 2)))
                                             (at_point 0) (Rbar_locally' p_infty))
                             (gl := (PI/(2*(u^2+1))))
                             (f := (fun v : R => u * exp (- (u ^ 2 + (u * v) ^ 2))))
                             (g := (fun v =>   u / (1+u^2) * /(1 + (u*v)^2)) )
                             (F:= at_point 0) (G:= Rbar_locally' p_infty).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply filter_Rlt_at_point_p_infty.  
  now apply int_bound3.
  apply (@RInt_gen_correct).
  apply Proper_StrongProper, at_point_filter.
  apply Proper_StrongProper, Rbar_locally'_filter.
  trivial.
  exists (fun a => a = 0) (fun b => b>1000).
  now unfold at_point.
  unfold Rbar_locally'; now exists 1000.
  intros.
  subst.
  unfold Rdiv.
  rewrite Rmult_assoc.
  apply erf_ex_bound3; try lra.
  unfold fst in H3; try lra.
Qed.

Lemma erf_ex_RInt3_bound_int :
  is_RInt_gen (fun u : R => PI/(2*(u^2+1))) (at_point 0) (Rbar_locally' p_infty) (PI^2/4).
Proof.
  apply (is_RInt_gen_ext (Derive (fun u => (PI/2) * atan u))).
  apply filter_forall.
  intros.
  rewrite Derive_scal.
  rewrite <- Derive_Reals with (pr := derivable_pt_atan (x0)).
  rewrite derive_pt_atan.
  unfold Rsqr.
  field_simplify; trivial.
  apply Rgt_not_eq.  
  now apply sqr_plus1_gt.  
  replace (1 + x0*x0) with (x0^2+1).
  now apply sqr_plus1_neq.  
  ring.
  replace (PI^2/4) with (PI^2/4 - 0).
  apply is_RInt_gen_Derive.
  apply filter_forall.
  intros.
  solve_derive.
  apply filter_forall.
  intros.
  apply (continuous_ext (fun u => (PI/(2*(u^2+1))))).
  intros.
  rewrite Derive_scal.
  rewrite <- Derive_Reals with (pr := derivable_pt_atan (x1)).
  rewrite derive_pt_atan.
  unfold Rsqr.
  field_simplify; trivial.
  replace (1+x1*x1) with (x1^2+1).
  now apply sqr_plus1_neq.  
  ring.
  now apply sqr_plus1_neq.  
  apply (@ex_derive_continuous).
  auto_derive.
  apply Rgt_not_eq.  
  ring_simplify.
  replace (2 * x0 ^ 2 + 2) with (2*(x0^2+1)) by lra.
  apply Rmult_gt_0_compat; try lra.
  now apply sqr_plus1_gt.  
  unfold filterlim, filter_le.
  intros.
  unfold filtermap, at_point.
  replace (PI/2 * atan 0) with (0).
  now apply locally_singleton.
  rewrite atan_0.
  ring.
  replace (filterlim (fun u : R => PI / 2 * atan u) (Rbar_locally' p_infty) (locally (PI ^ 2 / 4))
) with (is_lim (fun u : R => PI / 2 * atan u) p_infty (PI^2/4)).
  replace (Finite (PI^2/4)) with (Rbar_mult (PI/2) (PI/2)).
  apply is_lim_scal_l.
  apply lim_atan_inf.
  simpl.
  f_equal; now field_simplify.
  unfold is_lim.
  reflexivity.
  now field_simplify.
Qed.

Lemma erf_ex_RInt3 :
  ex_RInt_gen
    (fun u : R =>
     RInt_gen (fun v : R => u * exp (- (u ^ 2 + (u * v) ^ 2))) 
              (at_point 0) (Rbar_locally' p_infty)) (at_point 0) (Rbar_locally' p_infty).
Proof.  
  apply ex_RInt_gen_bound with (g:=(fun u : R => (PI/(2*(u^2+1))))).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply filter_Rlt_at_point_p_infty.
  unfold ex_RInt_gen.
  exists (PI^2/4).
  apply erf_ex_RInt3_bound_int.
  exists (fun a => a=0) (fun b => b>1000).
  now unfold at_point.
  unfold Rbar_locally'; now exists 1000.
  intros.
  split.
  intros.
  split.
  apply RInt_gen_Rle0.
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply filter_Rlt_at_point_p_infty.
  apply erf_ex_RInt33.
  unfold fst in H1; try lra.
  exists (fun a => a=0) (fun b => b>1000).
  now unfold at_point.
  unfold Rbar_locally'; now exists 1000.
  intros.
  unfold fst in H1.
  left.
  apply Rmult_lt_0_compat; try lra.
  apply exp_pos.
  apply erf_ex_RInt3_bound.
  unfold fst in H1; try lra.
  apply erf_ex_RInt33.
  unfold fst in H1; try lra.
  unfold fst, snd.
  subst.
  apply (ex_RInt_ext (fun u : R =>
     RInt_gen (fun w : R => exp (- (u ^ 2 + w ^ 2))) (at_point 0)
       (Rbar_locally' p_infty))).
  intros.
  rewrite Rmin_left in H; try lra.
  rewrite Rmax_right in H; try lra.
  symmetry.
  apply is_RInt_gen_unique.
  apply is_RInt_gen_comp_lin_point_0 with (u := x) (f := fun v => exp(-(x^2+v^2))).
  lra.
  intros.
  apply (@ex_RInt_continuous).
  intros.
  apply (@ex_derive_continuous).
  solve_derive.
  replace (x*0) with (0) by lra.
  replace (Rbar_mult x p_infty) with (p_infty).
  apply (@RInt_gen_correct).
  apply Proper_StrongProper, at_point_filter.
  apply Proper_StrongProper, Rbar_locally'_filter.
  apply erf_ex_RInt1.
  symmetry.
  apply Rbar_mult_p_infty_pos; try lra.
  apply ex_RInt_Reals_1.
  apply RiemannInt_decreasing; try lra.
  apply erf_decr_RInt30; try lra.
Qed.

Lemma erf_int1  :
  is_RInt_gen (fun u => RInt_gen (fun v => exp(-(u^2+v^2))) (at_point 0)  (Rbar_locally' p_infty)) (at_point 0) (Rbar_locally' p_infty) (PI / 4).
Proof.
  apply (is_RInt_gen_ext (fun u => RInt_gen (fun v => u*exp(-(u^2+(u*v)^2))) (at_point 0) (Rbar_locally' p_infty))).
  - exists (fun x => x=0) (fun y => y>1000).
    + now unfold at_point.
    + unfold Rbar_locally'; now exists 1000.
    + intros.
      unfold fst, snd in H1.
      subst.
      rewrite Rmin_left in H1; try lra.
      rewrite Rmax_right in H1; try lra.
      apply is_RInt_gen_unique.
      apply is_RInt_gen_comp_lin_point_0 with (f := fun v => exp(-(x0^2 + v^2))); try lra.
      * intros.
        apply (@ex_RInt_continuous).
        intros.
        apply (@ex_derive_continuous).
        now auto_derive.
      * replace (x0*0) with (0) by lra.
        replace (Rbar_mult x0 p_infty) with (p_infty).
        ++ apply (@RInt_gen_correct).
           apply Proper_StrongProper, at_point_filter.
           apply Proper_StrongProper, Rbar_locally'_filter.
           apply erf_ex_RInt1.
        ++ rewrite Rbar_mult_comm.
           now rewrite Rbar_mult_p_infty_pos.
  - replace (PI/4) with 
        (RInt_gen
           (fun u : R =>
              RInt_gen (fun v : R => u * exp (- (u ^ 2 + (u * v) ^ 2))) 
                       (at_point 0) (Rbar_locally' p_infty)) (at_point 0) (Rbar_locally' p_infty)).
    + apply RInt_gen_correct.
      apply erf_ex_RInt3.
    + rewrite -> Fubini_gen with (Fa := at_point 0) (Fc := at_point 0) (Fb := Rbar_locally' p_infty) (Fd := Rbar_locally' p_infty) (f := fun u => fun v => u* exp (- (u^2 + (u*v) ^ 2))).
      * apply is_RInt_gen_unique.
        apply erf_int00.
      * apply filter_forall.  
        intros.
        apply filter_forall.  
        intros.
        apply continuity_2d_pt_mult.
        apply continuity_2d_pt_id1.
        apply continuity_1d_2d_pt_comp.
        apply derivable_continuous_pt.
        apply derivable_pt_exp.
        repeat first [
               apply continuity_2d_pt_opp
             | apply continuity_2d_pt_plus
             | apply continuity_2d_pt_mult
             | apply continuity_2d_pt_id1
             | apply continuity_2d_pt_id2
             | apply continuity_2d_pt_const
             ].
      * eapply Filter_prod with (Q:=(eq 0)) (R:=fun x => x > 1000).
        -- now red.
        -- simpl;
             now exists 1000.
        -- intros.
           simpl in *.
           subst.
           eapply Filter_prod with (Q:=(eq 0)) (R:=fun x => x > 1000).
           now red.
           simpl;
             now exists 1000.
           intros.
           simpl in *.
           subst.
           rewrite Rmin_left in H1; try lra.
           apply Rle_ge.
           apply Rmult_le_pos; try lra.
           left.
           apply exp_pos.
      * apply erf_ex_RInt3.
      * unfold ex_RInt_gen.
        exists (PI/4).
        apply erf_int00.
Qed.

Lemma erf_int_sq :
  Rsqr (RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' p_infty)) = PI/4.
Proof.
  unfold Rsqr.
  rewrite <- RInt_gen_scal.
  rewrite <- (RInt_gen_ext (fun u => RInt_gen (fun v => exp(-(u^2+v^2))) (at_point 0)  (Rbar_locally' p_infty)) ).
  apply is_RInt_gen_unique.
  apply erf_int1.
  apply filter_forall.
  intros.
  rewrite scale_mult.
  rewrite Rmult_comm.
  rewrite <- RInt_gen_scal.
  symmetry.
  rewrite <- (RInt_gen_ext (fun y => exp (-(x0^2 + y^2)))).
  reflexivity.
  apply filter_forall.
  intros.
  rewrite scale_mult.
  replace (-(x0^2 + x2^2)) with ((-x0^2)+(-x2^2)).
  apply exp_plus.
  lra.
  apply erf_ex_RInt1.
  apply erf_ex_RInt2.  
  unfold ex_RInt_gen.
  exists (PI/4).
  apply erf_int1.
  apply erf_ex_RInt2.  
Qed.

Lemma erf_int2: 
  RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' p_infty) = (sqrt PI/2).
Proof.
  replace (sqrt PI/2) with (Rabs (sqrt PI/2)).
  replace ( RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' p_infty)) with
      (Rabs ( RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' p_infty))).
  apply Rsqr_eq_abs_0.
  replace (Rsqr (sqrt PI/2)) with (PI/4).
  apply erf_int_sq.
  rewrite Rsqr_div.
  rewrite Rsqr_sqrt.
  unfold Rsqr; lra.
  left; apply PI_RGT_0.
  lra.
  rewrite Rabs_pos_eq; trivial.
  apply RInt_gen_Rle0.
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply filter_Rlt_at_point_p_infty.
  apply erf_ex_RInt2.
  apply filter_forall.
  intros.
  left; apply exp_pos.
  rewrite Rabs_pos_eq; trivial.
  apply Rle_div_r; try lra.
  replace (0 * 2) with (0) by lra.
  left; apply sqrt_lt_R0.
  apply PI_RGT_0.
Qed.

Lemma erf_int21: 
  is_RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' p_infty) (sqrt PI/2).
Proof.
  replace (sqrt PI/2) with (RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' p_infty)).
  apply (@RInt_gen_correct).
  apply Proper_StrongProper, at_point_filter.
  apply Proper_StrongProper, Rbar_locally'_filter.
  apply erf_ex_RInt2.
  apply erf_int2.
Qed.

Lemma erf_int31: 
  is_RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' m_infty) ( -sqrt PI/2).
Proof.
  apply (is_RInt_gen_ext (fun y => (-1) * ((-1) * (exp (-(-1*y)^2))))).
  apply filter_forall.
  intros.
  replace ((-1*x0)^2) with (x0^2).
  now ring_simplify.
  now ring_simplify.
  replace (-sqrt PI/2) with (scal  (-1) (sqrt PI/2)).
  apply (@is_RInt_gen_scal).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply is_RInt_gen_comp_lin_point_0 with (f := fun y => exp(-y^2)).
  lra.
  intros.
  apply (@ex_RInt_continuous).
  intros.
  apply (@ex_derive_continuous).
  now auto_derive.
  replace (-1*0) with (0) by lra.
  replace (Rbar_mult (-1) m_infty) with (p_infty).
  apply erf_int21.
  symmetry.
  rewrite Rbar_mult_comm.
  apply Rbar_mult_m_infty_neg; lra.
  replace (- sqrt PI/2) with ((-1)*(sqrt PI/2)).
  apply scale_mult.
  lra.
Qed.

Lemma erf_int3 (r:Rbar): 
  r = p_infty \/ r= m_infty ->
  is_RInt_gen (fun u => exp(-(u^2))) (at_point 0) (Rbar_locally' r) ( inf_sign r * sqrt PI/2).
Proof.
  intros.
  destruct H.
  subst.
  unfold inf_sign.
  replace (1 * sqrt PI /2) with (sqrt PI / 2) by lra.
  apply erf_int21.
  subst.
  unfold inf_sign.
  replace (-1 * sqrt PI /2) with (-sqrt PI / 2) by lra.  
  apply erf_int31.
Qed.

Lemma erf_p_infty : 
  is_RInt_gen erf' (at_point 0) (Rbar_locally' p_infty) 1.
Proof.
  unfold erf'.
  replace (1) with ((2 / sqrt PI)*(sqrt PI/2)).
  apply (@is_RInt_gen_scal).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply erf_int21.
  field_simplify; try lra.
  apply sqrt_PI_neq0.
Qed.

Lemma erf_m_infty : 
  is_RInt_gen erf' (at_point 0) (Rbar_locally' m_infty) (-1).
Proof.
  unfold erf'.
  replace (-1) with ((2 / sqrt PI)*(-sqrt PI/2)).
  apply (@is_RInt_gen_scal).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  apply erf_int31.
  apply Rminus_diag_uniq; field_simplify; try lra.
  apply sqrt_PI_neq0.
Qed.

Lemma Standard_Gaussian_PDF_int1_pm (r : Rbar): 
  r = p_infty \/ r = m_infty -> is_RInt_gen Standard_Gaussian_PDF (at_point 0) (Rbar_locally' r)  (inf_sign r * /2).
Proof.
  intros.
  unfold Standard_Gaussian_PDF.
  apply (is_RInt_gen_ext (fun y => /(sqrt 2) * ( (/sqrt PI) * exp (- ((/sqrt 2)*y)^2)))).
  apply filter_forall.
  intros.
  apply Rminus_diag_uniq.
  replace (/sqrt(2*PI)) with (/sqrt(2)*/sqrt(PI)).
  replace (-(/ sqrt 2 * x0) ^ 2) with (-x0^2/2).
  now ring_simplify.
  rewrite Rpow_mult_distr.
  replace ((/ sqrt 2)^2) with (/2).
  now field_simplify.
  rewrite <- Rsqr_pow2.
  rewrite Rsqr_inv.
  rewrite Rsqr_sqrt; try easy.
  lra.
  apply sqrt2_neq0.
  rewrite sqrt_mult_alt.
  symmetry; apply Rinv_mult_distr.
  apply sqrt2_neq0.
  apply sqrt_PI_neq0.
  lra.
  apply is_RInt_gen_comp_lin_point_0 with (f := fun y => (/ sqrt PI) * exp (- y^2)).
  apply Rinv_neq_0_compat.
  apply sqrt2_neq0.
  intros.
  apply (@ex_RInt_continuous).
  intros.
  apply (@ex_derive_continuous).
  now auto_derive.
  replace (/sqrt 2 * 0) with (0) by lra.
  replace (Rbar_mult (/ sqrt 2) r) with (r).
  replace (inf_sign r * /2) with (/ sqrt PI * (inf_sign r * sqrt PI/2)).
  apply (@is_RInt_gen_scal).
  apply at_point_filter.
  apply Rbar_locally'_filter.
  now apply erf_int3.
  apply Rminus_diag_uniq; field_simplify; try lra.
  apply sqrt_PI_neq0.
  symmetry.
  rewrite Rbar_mult_comm.
  assert (0 < / sqrt 2).
  apply Rgt_lt.
  apply Rinv_0_lt_compat.
  apply sqrt_lt_R0; lra.
  destruct H.
  subst.
  now apply Rbar_mult_p_infty_pos.
  subst.
  now apply Rbar_mult_m_infty_pos.  
Qed.
