Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Coquelicot.Coquelicot.
Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Reals.R_sqrt.
Require Import Rtrigo_def.
Require Import Rtrigo1.
Require Import Reals.Rtrigo_calc.
Require Import Lra.

Require Import LibUtils.

Set Bullet Behavior "Strict Subproofs".

Lemma sqrt2_neq0 :
  sqrt 2 <> 0.
Proof.
  apply Rgt_not_eq.
  apply Rlt_gt.
  apply Rlt_sqrt2_0.
Qed.

Lemma sqrt_2PI_nzero : sqrt(2*PI) <> 0.
Proof.
  assert (PI > 0) by apply PI_RGT_0.

  apply Rgt_not_eq.
  apply sqrt_lt_R0.
  lra.
Qed.

Lemma ex_Rbar_plus_Finite_l x y : ex_Rbar_plus (Finite x) y.
  destruct y; simpl; trivial.
Qed.

Lemma ex_Rbar_plus_Finite_r x y : ex_Rbar_plus x (Finite y).
  destruct x; simpl; trivial.
Qed.

Lemma ex_Rbar_minus_Finite_l x y : ex_Rbar_minus (Finite x) y.
  destruct y; simpl; trivial.
Qed.

Lemma ex_Rbar_minus_Finite_r x y : ex_Rbar_minus x (Finite y).
  destruct x; simpl; trivial.
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

Lemma lim_rint_gen_Rbar (f : R->R) (a:R) (b:Rbar) (l:R):
  (forall y, ex_RInt f a y) ->
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
  destruct b.
  - destruct H as [M PltM].
    eexists (fun x => x=a) (fun y => P (RInt f a y)); try easy.
    + simpl.
      unfold locally', within, locally in *.
      eauto.
    + simpl.
      intros.
      subst.
      simpl in *.
      exists (RInt f a y).  
      split; trivial.
      now apply (@RInt_correct R_CompleteNormedModule).
  - destruct H as [M PltM].
    eexists (fun x => x=a) (fun y => _); try easy.
    + simpl.
      eauto.
    + simpl.
      intros.
      subst.
      simpl in *.
      exists (RInt f a y).  
      split; trivial.
      apply (@RInt_correct R_CompleteNormedModule); trivial.
  - destruct H as [M PltM].
    eexists (fun x => x=a) (fun y => _); try easy.
    + simpl.
      eauto.
    + simpl.
      intros.
      subst.
      simpl in *.
      exists (RInt f a y).  
      split; trivial.
      apply (@RInt_correct R_CompleteNormedModule); trivial.
Qed.
  
Lemma rint_gen_lim_Rbar {f : R->R} {a:R} {b:Rbar} {l:R} :
  is_RInt_gen f (at_point a) (Rbar_locally' b) l -> is_lim (fun x => RInt f a x) b l.
Proof.
  intros H P HP.
  specialize (H _ HP).
  destruct H as [Q R Qa Rb H].
  simpl in H.
  destruct b.
  - destruct Rb as [M Rb].
    exists M.
    intros x xlt xne.
    destruct (H a x Qa (Rb _ xlt xne))
      as [y [yis iP]].
    now rewrite (is_RInt_unique _ _ _ _ yis).
  - destruct Rb as [M Rb].
    exists M.
    intros x xlt.
    destruct (H a x Qa (Rb _ xlt))
      as [y [yis iP]].
    now rewrite (is_RInt_unique _ _ _ _ yis).
  - destruct Rb as [M Rb].
    exists M.
    intros x xlt.
    destruct (H a x Qa (Rb _ xlt))
      as [y [yis iP]].
    now rewrite (is_RInt_unique _ _ _ _ yis).
Qed.

Lemma is_RInt_gen_comp_lin0
  (f : R -> R) (u v : R) (a:R) (b : Rbar) (l : R) :
  u<>0 -> (forall x y, ex_RInt f x y) ->
  is_RInt_gen f (at_point (u * a + v)) (Rbar_locally'  (Rbar_plus (Rbar_mult u b) v)) l
    -> is_RInt_gen (fun y => scal u (f (u * y + v))) (at_point a) (Rbar_locally' b) l.
Proof.
  intros.
  apply lim_rint_gen_Rbar.
  intros.
  apply (@ex_RInt_comp_lin R_CompleteNormedModule); trivial.
  apply (is_lim_ext (fun x : R => RInt f (u*a+v) (u*x+v))).
  intros.
  rewrite RInt_comp_lin; trivial.
  apply is_lim_comp_lin.
  apply rint_gen_lim_Rbar; trivial.
  trivial.
Qed.  

Lemma RInt_gen_Chasles {Fa Fc : (R -> Prop) -> Prop}
  {FFa : ProperFilter' Fa} {FFc : ProperFilter' Fc}
  (f : R -> R) (b : R):
  ex_RInt_gen f Fa (at_point b) -> ex_RInt_gen f (at_point b) Fc ->
  plus (RInt_gen f Fa (at_point b)) (RInt_gen f (at_point b) Fc) = RInt_gen f Fa Fc.
Proof.
  intros.
  apply sym_eq.
  apply (@is_RInt_gen_unique R_CompleteNormedModule).
  trivial.
  trivial.
  apply (@is_RInt_gen_Chasles R_CompleteNormedModule) with (b:=b).
  apply filter_filter'.
  apply filter_filter'.
  now apply RInt_gen_correct.
  now apply RInt_gen_correct.  
Qed.

Lemma is_RInt_gen_comp_lin
  (f : R -> R) (u v : R) (a b : Rbar) (ll : R) :
  u<>0 -> ex_RInt_gen f (Rbar_locally' (Rbar_plus (Rbar_mult u a) v)) (at_point (u*0+v)) ->
  ex_RInt_gen f (at_point (u*0+v)) (Rbar_locally' (Rbar_plus (Rbar_mult u b) v)) ->
  (forall (x y :R), ex_RInt f x y) ->
  is_RInt_gen f (Rbar_locally'  (Rbar_plus (Rbar_mult u a) v)) (Rbar_locally'  (Rbar_plus (Rbar_mult u b) v)) ll
  -> is_RInt_gen (fun y => scal u (f (u * y + v))) (Rbar_locally' a) (Rbar_locally' b) ll.
Proof.  
  intros.
  replace (ll) with (plus (RInt_gen f (Rbar_locally' (Rbar_plus (Rbar_mult u a) v))  (at_point (u*0+v)))
                         (RInt_gen f (at_point (u*0+v)) (Rbar_locally' (Rbar_plus (Rbar_mult u b) v)))).
  apply (@is_RInt_gen_Chasles R_CompleteNormedModule) with (b := 0) 
        (l1 := (RInt_gen f (Rbar_locally' (Rbar_plus (Rbar_mult u a) v))  (at_point (u*0+v))))
        (l2 := (RInt_gen f (at_point (u*0+v)) (Rbar_locally' (Rbar_plus (Rbar_mult u b) v)))).
  apply Rbar_locally'_filter.
  apply Rbar_locally'_filter.
  replace (RInt_gen f (Rbar_locally' (Rbar_plus (Rbar_mult u a) v)) (at_point (u * 0 + v))) with
      (opp (opp (RInt_gen f (Rbar_locally' (Rbar_plus (Rbar_mult u a) v)) (at_point (u * 0 + v))))).
  apply (@is_RInt_gen_swap R_CompleteNormedModule) with 
      (l := (opp (RInt_gen f (Rbar_locally' (Rbar_plus (Rbar_mult u a) v)) (at_point (u * 0 + v))))).
  apply Rbar_locally'_filter.
  apply at_point_filter.
  apply is_RInt_gen_comp_lin0; trivial.
  apply (@is_RInt_gen_swap R_CompleteNormedModule) with 
      (l := (RInt_gen f (Rbar_locally' (Rbar_plus (Rbar_mult u a) v)) (at_point (u * 0 + v)))).
  apply at_point_filter.  
  apply Rbar_locally'_filter.
  apply RInt_gen_correct.
  trivial.
  rewrite opp_opp; trivial.
  apply is_RInt_gen_comp_lin0; trivial.
  apply (@RInt_gen_correct R_CompleteNormedModule).
  apply Proper_StrongProper.
  apply at_point_filter.
  apply Proper_StrongProper.
  apply Rbar_locally'_filter.
  trivial.
  rewrite RInt_gen_Chasles.
  apply is_RInt_gen_unique; trivial.
  trivial.
  trivial.
Qed.  
