Require Import Reals utils.RealAdd.
Require Import Coquelicot.Hierarchy.
Require Import Morphisms Equivalence.
Require Import Lra.
Require Import utils.Utils.
Require Import List.
(* For const *)
Require Export Program.Basics.
Require Import Coquelicot.Coquelicot.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R.
Section rels.
  Context {Ts:Type}.

  Definition rv_le :=
    pointwise_relation Ts Rle.

  Global Instance rv_le_pre : PreOrder rv_le.
  Proof.
    unfold rv_le.
    constructor; intros.
    - intros ??; lra.
    - intros ??????.
      eapply Rle_trans; eauto.
  Qed.

  Global Instance rv_le_part : PartialOrder rv_eq rv_le.
  Proof.
    intros ??.
    split; intros eqq.
    - repeat red.
      repeat red in eqq.
      split; intros ?; rewrite eqq; lra.
    - destruct eqq as [le1 le2].
      intros y.
      specialize (le1 y).
      specialize (le2 y).
      lra.
  Qed.

  Definition Rbar_rv_le := pointwise_relation Ts Rbar_le.

  Global Instance Rbar_rv_le_pre : PreOrder Rbar_rv_le.
  Proof.
    unfold Rbar_rv_le.
    constructor; intros.
    - intros ??; apply Rbar_le_refl.
    - intros ??????.
      eapply Rbar_le_trans; eauto.
  Qed.

  Global Instance Rbar_rv_le_part : PartialOrder rv_eq Rbar_rv_le.
  Proof.
    intros ??.
    split; intros eqq.
    - repeat red.
      repeat red in eqq.
      split; intros ?; rewrite eqq; apply Rbar_le_refl.
    - destruct eqq as [le1 le2].
      intros y.
      specialize (le1 y).
      specialize (le2 y).
      now apply Rbar_le_antisym.
  Qed.

End rels.

Section defs.
  Context {Ts:Type}.

  Section funs.

    (* const is defined in Program.Basics *)

    Definition EventIndicator {P : Ts->Prop} (dec:forall x, {P x} + {~ P x}) : Ts -> R
      := fun omega => if dec omega then 1 else 0.

    Definition rvplus (rv_X1 rv_X2 : Ts -> R) :=
      (fun omega =>  (rv_X1 omega) + (rv_X2 omega)).

    Definition rvsum (Xn : nat -> Ts -> R) (n : nat) :=
      (fun omega => sum_n (fun n0 => Xn n0 omega) n).

    Definition rvscale (c:R) (rv_X : Ts -> R) :=
      fun omega => c * (rv_X omega).

    Definition rvopp (rv_X : Ts -> R) := rvscale (-1) rv_X.

    Definition rvminus (rv_X1 rv_X2 : Ts -> R) :=
      rvplus rv_X1 (rvopp rv_X2).

    Definition rvmult (rv_X1 rv_X2 : Ts -> R) := 
      fun omega => (rv_X1 omega) * (rv_X2 omega).

    Definition rvsqr (rv_X : Ts -> R) := fun omega => Rsqr (rv_X omega).
    Definition rvsqrt (rv_X : Ts -> R) := fun omega => sqrt (rv_X omega).    

    Definition rvpow (rv_X : Ts -> R) (n:nat) := fun omega => pow (rv_X omega) n.

    Definition rvpower (rv_X1 rv_X2 : Ts -> R) := fun omega => power (rv_X1 omega) (rv_X2 omega).

    Definition rvabs  (rv_X : Ts -> R) := fun omega => Rabs (rv_X omega).

    Lemma rvabs_pos (rv_X : Ts -> R) :
      rv_le (const 0) (rvabs rv_X).
    Proof.
      intro x.
      unfold const, rvabs.
      apply Rabs_pos.
    Qed.

    Definition rvchoice (c:Ts -> bool) (rv_X1 rv_X2 : Ts -> R)
      := fun omega => if c omega then  rv_X1 omega else rv_X2 omega.

    Definition bvmin_choice (rv_X1 rv_X2:Ts -> R) : Ts -> bool
      := fun omega => if Rle_dec (rv_X1 omega) (rv_X2 omega) then true else false.

    Definition bvmax_choice (rv_X1 rv_X2:Ts -> R) : Ts -> bool
      := fun omega => if Rle_dec (rv_X1 omega) (rv_X2 omega) then false else true.

    Definition rvmax  (rv_X1 rv_X2 : Ts -> R)
      := fun omega => Rmax (rv_X1 omega) (rv_X2 omega).

    Definition rvmin  (rv_X1 rv_X2 : Ts -> R)
      := fun omega => Rmin (rv_X1 omega) (rv_X2 omega). 


    Program Definition pos_fun_part {Ts:Type} (f : Ts -> R) : (Ts -> nonnegreal) :=
      fun x => mknonnegreal (Rmax (f x) 0) _.
    Next Obligation.
      apply Rmax_r.
    Defined.
    
    Program Definition neg_fun_part {Ts:Type} (f : Ts -> R) : (Ts -> nonnegreal) :=
      fun x => mknonnegreal (Rmax (- f x) 0) _.
    Next Obligation.
      apply Rmax_r.
    Defined.

    Definition rvclip {Ts:Type} (f : Ts -> R) (c : nonnegreal) : Ts -> R
      := fun x => if Rgt_dec (f x) c then c else
                    (if Rlt_dec (f x) (-c) then (-c) else f x).

    Lemma rvclip_le_c (rv_X : Ts -> R) (c : nonnegreal) :
      rv_le (rvclip rv_X c) (const c).
    Proof.
      intro x0.
      unfold rvclip, const.
      assert (0 <= c) by apply (cond_nonneg c).
      match_destr; [lra |].
      match_destr; lra.
    Qed.
    
    Lemma rvclip_negc_le (rv_X : Ts -> R) (c : nonnegreal) :
      rv_le (const (-c)) (rvclip rv_X c).
    Proof.
      intro x0.
      unfold rvclip, const.
      assert (0 <= c) by apply (cond_nonneg c).
      match_destr; [lra |].
      match_destr; lra.
    Qed.

    Lemma rvclip_abs_bounded rv_X c :
      forall omega : Ts, Rabs ((rvclip rv_X c) omega) <= c.
    Proof.
      intros.
      assert (0 <= c) by apply (cond_nonneg c).
      unfold rvclip.
      match_destr.
      rewrite Rabs_pos_eq; lra.
      match_destr.
      rewrite Rabs_Ropp.
      rewrite Rabs_pos_eq; lra.      
      apply Rabs_le.
      lra.
    Qed.

    Lemma rvclip_abs_le_c (rv_X : Ts -> R) (c : nonnegreal) :
      rv_le (rvabs (rvclip rv_X c)) (const c).
    Proof.
      intro x.
      unfold rvabs, const.
      apply rvclip_abs_bounded.
    Qed.

  End funs.

  Section eqs.
    Existing Instance rv_eq_equiv.

    Global Instance rvplus_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvplus.
    Proof.
      unfold rv_eq, rvplus, pointwise_relation.
      intros ???????.
      now rewrite H, H0.
    Qed.

    Global Instance rvscale_proper : Proper (eq ==> rv_eq ==> rv_eq ) rvscale.
    Proof.
      unfold rv_eq, rvopp, Proper, rvscale, respectful, pointwise_relation.
      intros ??? x y eqq z.
      subst.
      now rewrite eqq.
    Qed.

    Global Instance rvopp_proper : Proper (rv_eq ==> rv_eq ) rvopp.
    Proof.
      unfold rv_eq, rvopp, Proper, rvscale, respectful, pointwise_relation.
      intros x y eqq z.
      now rewrite eqq.
    Qed.

    Global Instance rvminus_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvminus.
    Proof.
      unfold rv_eq, rvminus, rvplus, rvopp, rvscale, pointwise_relation.
      intros ???????.
      now rewrite H, H0.
    Qed.
    
    Global Instance rvmult_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvmult.
    Proof.
      unfold rv_eq, rvmult.
      intros ???????.
      now rewrite H, H0.
    Qed.

    Global Instance rvsqr_proper : Proper (rv_eq ==> rv_eq) rvsqr.
    Proof.
      unfold rv_eq, rvsqr, Proper, respectful, pointwise_relation.
      intros x y eqq z.
      unfold Rsqr.
      rewrite eqq.
      trivial.
    Qed.

    Global Instance rvpow_proper : Proper (rv_eq ==> eq ==> rv_eq) rvpow.
    Proof.
      unfold rv_eq, rvpow, Proper, respectful, pointwise_relation.
      intros x y eqq z ???.
      subst.
      rewrite eqq.
      trivial.
    Qed.

    Global Instance rvpower_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvpower.
    Proof.
      unfold rv_eq, rvpower, Proper, respectful, pointwise_relation.
      intros x y eqq1 z ? eqq2 ?.
      subst.
      now rewrite eqq1, eqq2.
    Qed.

    Global Instance rvabs_proper : Proper (rv_eq ==> rv_eq) rvabs.
    Proof.
      unfold rv_eq, rvabs, Proper, respectful, pointwise_relation.
      intros x y eqq z.
      unfold Rabs.
      rewrite eqq.
      trivial.
    Qed.

    Global Instance rvmax_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvmax.
    Proof.
      unfold rv_eq, rvmax.
      intros ???????.
      now rewrite H, H0.
    Qed.

    Global Instance rvmin_proper : Proper (rv_eq ==> rv_eq ==> rv_eq) rvmin.
    Proof.
      unfold rv_eq, rvmin.
      intros ???????.
      now rewrite H, H0.
    Qed.

    Local Open Scope equiv_scope.
    Lemma rv_pos_neg_id (rv_X:Ts->R) : rv_X === rvplus (pos_fun_part rv_X) (rvopp (neg_fun_part rv_X)).
    Proof.
      intros x.
      unfold rvplus, rvopp, pos_fun_part, neg_fun_part, rvscale; simpl.
      unfold Rmax, Rmin.
      repeat match_destr; lra.
    Qed.

    Lemma rvmult_assoc
          (rv_X1 rv_X2 rv_X3 : Ts -> R) :
      (rvmult (rvmult rv_X1 rv_X2) rv_X3) === (rvmult rv_X1 (rvmult rv_X2 rv_X3)).
    Proof.
      intros x.
      unfold rvmult.
      lra.
    Qed.

    Lemma rvmult_comm
          (rv_X1 rv_X2 : Ts -> R) :
      (rvmult rv_X1 rv_X2)  === (rvmult rv_X2 rv_X1).
    Proof.
      intros x.
      unfold rvmult.
      lra.
    Qed.

    Lemma rvmult_rvadd_distr
          (rv_X1 rv_X2 rv_X3 : Ts -> R) :
      (rvmult rv_X1 (rvplus rv_X2 rv_X3)) ===  
                                          (rvplus (rvmult rv_X1 rv_X2) (rvmult rv_X1 rv_X3)).
    Proof.
      intros x.
      unfold rvmult, rvplus.
      lra.
    Qed.

    Lemma pos_fun_part_le rv_X : rv_le (fun x : Ts => pos_fun_part rv_X x) (rvabs rv_X).
    Proof.
      intros ?.
      unfold rvabs, pos_fun_part, Rabs, Rmax; simpl.
      repeat match_destr; lra.
    Qed.

    Lemma neg_fun_part_le rv_X : rv_le (fun x : Ts => (neg_fun_part rv_X x)) (rvabs rv_X).
    Proof.
      intros ?.
      unfold rvabs, rvopp, rvscale, neg_fun_part, Rabs, Rmax; simpl.
      repeat match_destr; lra.
    Qed.

    Lemma rv_le_pos_fun_part rv_X1 rv_X2 :
      rv_le rv_X1 rv_X2 ->
      rv_le (fun x : Ts => pos_fun_part rv_X1 x) (fun x : Ts => pos_fun_part rv_X2 x).
    Proof.
      intros le12 a.
      simpl.
      now apply Rle_max_compat_r.
    Qed.

    Lemma rv_le_neg_fun_part rv_X1 rv_X2 :
      rv_le rv_X1 rv_X2 ->
      rv_le (fun x : Ts => neg_fun_part rv_X2 x) (fun x : Ts => neg_fun_part rv_X1 x).
    Proof.
      intros le12 a.
      simpl.
      replace 0 with (- 0) by lra.
      repeat rewrite Rcomplements.Rmax_opp_Rmin.
      apply Ropp_le_contravar.
      now apply Rle_min_compat_r.
    Qed.
    
    Lemma rvmax_unfold (f g:Ts->R) :
      rvmax f g === rvscale (/2) (rvplus (rvplus f g) (rvabs (rvminus f g))).
    Proof.
      intro x.
      unfold rvmax, rvminus, rvscale, rvabs, rvopp, rvscale, rvplus.
      unfold Rmax, Rabs.
      repeat match_destr; lra.
    Qed.

    Lemma rvmin_unfold (f g:Ts->R) :
      rvmin f g === rvscale (/2) (rvminus (rvplus f g) (rvabs (rvminus f g))).
    Proof.
      intro x.
      unfold rvmin, rvminus, rvscale, rvabs, rvopp, rvscale, rvplus.
      unfold Rmin, Rabs.
      repeat match_destr; lra.
    Qed.

    Lemma rvmult_unfold (f g:Ts->R) :
      rvmult f g === rvscale (1/4) (rvminus (rvsqr (rvplus f g))
                                            (rvsqr (rvminus f g))).
    Proof.
      intros x.
      unfold rvmult, rvminus, rvplus,rvsqr, rvopp, rvscale.
      replace (1 / 4 * ((f x + g x)² + -1 * (f x + -1 * g x)²)) with ((f x)*(g x)) by (unfold Rsqr; lra).
      intuition.
    Qed.

    Lemma rvsqr_unfold (f:Ts->R) :
      rvsqr f === rvpow f 2.
    Proof.
      intros x.
      unfold rvpow, rvsqr, Rsqr; simpl.
      lra.
    Qed.

    Lemma rvpower_abs2_unfold (f:Ts->R) :
      rvpower (rvabs f) (const 2) === rvsqr f.
    Proof.
      intros x.
      apply power_abs2_sqr.
    Qed.

    Lemma rvpower_abs_scale c (X:Ts->R) n :
      rvpower (rvscale (Rabs c) (rvabs X)) (const n) === rvscale (power (Rabs c) n) (rvpower (rvabs X) (const n)).
    Proof.
      intros x.
      unfold rvpower, rvscale.
      rewrite power_mult_distr; trivial.
      - apply Rabs_pos.
      - apply rvabs_pos.
    Qed.

    Lemma rv_abs_abs (rv_X:Ts->R) :
      rv_eq (rvabs (rvabs rv_X)) (rvabs rv_X).
    Proof.
      intros a.
      unfold rvabs.
      now rewrite Rabs_Rabsolu.
    Qed.
    
    Lemma rvpowabs_choice_le c (rv_X1 rv_X2 : Ts -> R) p :
      rv_le (rvpower (rvabs (rvchoice c rv_X1 rv_X2)) (const p))
            (rvplus (rvpower (rvabs rv_X1) (const p)) (rvpower (rvabs rv_X2) (const p))).
    Proof.
      intros a.
      unfold rvpower, rvabs, rvchoice, rvplus, const; simpl.
      match_destr.
      - assert (0 <= power (Rabs (rv_X2 a)) p) by apply power_nonneg.
        lra.
      - assert (0 <= power (Rabs (rv_X1 a)) p) by apply power_nonneg.
        lra.
    Qed.
    
    Lemma pos_fun_part_unfold (f : Ts->R) :
      (fun x => nonneg (pos_fun_part f x)) === rvmax f (const 0).
    Proof.
      intros x.
      reflexivity.
    Qed.

    Lemma neg_fun_part_unfold (f : Ts->R) :
      (fun x => nonneg (neg_fun_part f x)) === rvmax (rvopp f) (const 0).
    Proof.
      intros x.
      unfold neg_fun_part, rvopp, const, rvscale, rvmax; simpl.
      f_equal.
      lra.
    Qed.

    Lemma rvmin_choice (rv_X1 rv_X2 : Ts -> R)
      : rvmin rv_X1 rv_X2 === rvchoice (bvmin_choice rv_X1 rv_X2) rv_X1 rv_X2.
    Proof.
      intros a.
      unfold rvmin, rvchoice, bvmin_choice, Rmin.
      match_destr.
    Qed.

    Lemma rvmax_choice (rv_X1 rv_X2 : Ts -> R)
      : rvmax rv_X1 rv_X2 === rvchoice (bvmax_choice rv_X1 rv_X2) rv_X1 rv_X2.
    Proof.
      intros a.
      unfold rvmax, rvchoice, bvmax_choice, Rmax.
      match_destr.
    Qed.

    Lemma rvchoice_le_max (c:Ts->bool) (rv_X1 rv_X2 : Ts -> R)
      : rv_le (rvchoice c rv_X1 rv_X2) (rvmax rv_X1 rv_X2).
    Proof.
      intros a.
      unfold rvchoice, rvmax, Rmax.
      repeat match_destr; lra.
    Qed.

    Lemma rvchoice_le_min (c:Ts->bool) (rv_X1 rv_X2 : Ts -> R)
      : rv_le (rvmin rv_X1 rv_X2) (rvchoice c rv_X1 rv_X2).
    Proof.
      intros a.
      unfold rvchoice, rvmin, Rmin.
      repeat match_destr; lra.
    Qed.

    Lemma rvminus_self (x:Ts->R) : rv_eq (rvminus x x) (const 0).
    Proof.
      intros a.
      unfold rvminus, rvplus, rvopp, rvscale, const.
      lra.
    Qed.

    Lemma rvminus_unfold (x y : Ts -> R)
      : rv_eq (rvminus x y)  (fun a => x a - y a).
    Proof.
      unfold rvminus, rvplus, rvopp, rvscale.
      intros a.
      lra.
    Qed.

    Lemma rvabs_rvminus_sym (x y : Ts -> R) :
      rv_eq (rvabs (rvminus x y)) (rvabs (rvminus y x)).
    Proof.
      repeat rewrite rvminus_unfold.
      unfold rvabs.
      intros a.
      apply Rabs_minus_sym.
    Qed.

    Lemma rvabs_pow1 (x:Ts->R) : rv_eq (rvpower (rvabs x) (const 1)) (rvabs x).
    Proof.
      intros a.
      unfold rvpower, rvabs, const.
      apply power_1.
      apply Rabs_pos.
    Qed.

    Lemma rv_abs_scale_eq (c:R) (rv_X:Ts->R) :
      rv_eq (rvabs (rvscale c rv_X)) (rvscale (Rabs c) (rvabs rv_X)).
    Proof.
      intros a.
      unfold rvabs, rvscale.
      apply Rabs_mult.
    Qed.
    
    Lemma rv_abs_const_eq (c:R)  :
      rv_eq (Ts:=Ts) (rvabs (const c)) (const (Rabs c)).
    Proof.
      intros a.
      reflexivity.
    Qed.
    
    Lemma rvpow_mult_distr (x y:Ts->R) n :
      rv_eq (rvpow (rvmult x y) n) (rvmult (rvpow x n) (rvpow y n)).
    Proof.
      intros a.
      unfold rvpow, rvmult.
      apply Rpow_mult_distr.
    Qed.

    Lemma rvpow_scale c (X:Ts->R) n :
      rv_eq (rvpow (rvscale c X) n) (rvscale (pow c n) (rvpow X n)).
    Proof.
      intros x.
      unfold rvpow, rvscale.
      apply Rpow_mult_distr.
    Qed.

    Lemma rvpow_const c n :
      rv_eq (Ts:=Ts) (rvpow (const c) n) (const (pow c n)).
    Proof.
      intros x.
      reflexivity.
    Qed.

    Lemma rvpower_const b e :
      rv_eq (Ts:=Ts) (rvpower (const b) (const e)) (const (power b e)).
    Proof.
      reflexivity.
    Qed.

    Lemma fold_right_rvplus c (l:list (Ts->R)) (a:Ts) :
      fold_right rvplus (const c) l a =
      fold_right Rplus c (map (fun x => x a) l).
    Proof.
      unfold rvplus, const.
      induction l; simpl; trivial.
      now rewrite IHl.
  Qed.

      Lemma rvabs_bound (rv_X : Ts -> R) :
    rv_le (rvabs rv_X) (rvplus (rvsqr rv_X) (const 1)).
  Proof.
    assert (forall x, 0 <= (rvsqr (rvplus (rvabs rv_X) (const (-1)))) x) by (intros; apply Rle_0_sqr).

    assert (rv_eq (rvsqr (rvplus (rvabs rv_X) (const (-1))))
                  (rvplus 
                     (rvplus (rvsqr (rvabs rv_X)) (rvscale (-2) (rvabs rv_X)))
                     (const 1))).
    {
      intro x.
      unfold rvsqr, rvplus, rvscale, rvabs, const, Rsqr.
      now ring_simplify.
    }
    intros x.
    specialize (H x).
    rewrite H0 in H.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, rvabs, const in *.
    rewrite Rsqr_abs.
    unfold Rsqr in *.
    apply Rplus_le_compat_l with (r := 2 * Rabs (rv_X x)) in H.
    ring_simplify in H.
    generalize (Rabs_pos (rv_X x)); intros.
    lra.
  Qed.

  Lemma rvabs_sqr (rv_X : Ts -> R) :
    rv_eq (rvabs (rvsqr rv_X)) (rvsqr rv_X).
    Proof.
      intro x.
      unfold rvabs, rvsqr.
      apply Rabs_pos_eq.
      apply Rle_0_sqr.
    Qed.
      
  Lemma rvsqr_abs (rv_X : Ts -> R) :
    rv_eq (rvsqr (rvabs rv_X)) (rvsqr rv_X).
    Proof.
      intro x.
      unfold rvabs, rvsqr.
      now rewrite <- Rsqr_abs.
    Qed.

    Lemma rvmult_abs (rv_X1 rv_X2 : Ts -> R):
      rv_eq (rvabs (rvmult rv_X1 rv_X2)) (rvmult (rvabs rv_X1) (rvabs rv_X2)).
    Proof.
      intro x.
      unfold rvmult, rvabs.
      apply Rabs_mult.
    Qed.
    
    Lemma rvprod_bound (rv_X1 rv_X2 : Ts->R) :
      rv_le (rvscale 2 (rvmult rv_X1 rv_X2))
            (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
    Proof.
      assert (forall x, 0 <= (rvsqr (rvminus rv_X1 rv_X2)) x) by (intros; apply Rle_0_sqr).
      assert (rv_eq (rvsqr (rvminus rv_X1 rv_X2)) 
                  (rvplus (rvplus (rvsqr rv_X1) (rvopp (rvscale 2 (rvmult rv_X1 rv_X2))))
                          (rvsqr rv_X2))).
    { 
      intro x.
      unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr.
      now ring_simplify.
    }
    intros x; specialize (H x).
    rewrite H0 in H; clear H0.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr in *.
    lra.
  Qed.  
  
  Lemma rvprod_abs_bound (rv_X1 rv_X2 : Ts->R) :
    rv_le (rvscale 2 (rvabs (rvmult rv_X1 rv_X2)))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
  Proof.
    generalize (rvprod_bound (rvabs rv_X1) (rvabs rv_X2)); intros.
    do 2 rewrite rvsqr_abs in H.
    now rewrite rvmult_abs.
  Qed.

  Lemma rvsum_sqr_bound (rv_X1 rv_X2 : Ts->R) :
    rv_le (rvsqr (rvplus rv_X1 rv_X2)) 
                          (rvscale 2 (rvplus (rvsqr rv_X1) (rvsqr rv_X2))).
  Proof.
    assert (forall x, 0 <= (rvsqr (rvminus rv_X1 rv_X2)) x) by (intros; apply Rle_0_sqr).
    assert (rv_eq (rvsqr (rvminus rv_X1 rv_X2)) 
                  (rvplus (rvplus (rvsqr rv_X1) (rvopp (rvscale 2 (rvmult rv_X1 rv_X2))))
                          (rvsqr rv_X2))).
    { 
      intro x.
      unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr.
      now ring_simplify.
    }
    intros x; specialize (H x).
    rewrite H0 in H; clear H0.
    unfold rvsqr, rvminus, rvplus, rvmult, rvopp, rvscale, Rsqr in *.
    apply Rplus_le_compat_l with (r:= ((rv_X1 x + rv_X2 x) * (rv_X1 x + rv_X2 x))) in H.
    ring_simplify in H.
    ring_simplify.
    apply H.
  Qed.    

  Lemma rvsqr_eq (x:Ts->R): rv_eq (rvsqr x) (rvmult x x).
  Proof.
    intros ?.
    reflexivity.
  Qed.

  Lemma rvprod_abs1_bound (rv_X1 rv_X2 : Ts->R) :
    rv_le (rvabs (rvmult rv_X1 rv_X2))
                          (rvplus (rvsqr rv_X1) (rvsqr rv_X2)).
  Proof.
    generalize (rvprod_abs_bound rv_X1 rv_X2).
    unfold rv_le, rvscale, rvabs, rvmult, rvsqr, Rsqr; intros H x.
    specialize (H x).
    assert (Rabs (rv_X1 x * rv_X2 x) <= 2 * Rabs (rv_X1 x * rv_X2 x)).
    apply Rplus_le_reg_l with (r := - Rabs(rv_X1 x * rv_X2 x)).
    ring_simplify.
    apply Rabs_pos.
    lra.
  Qed.

    Lemma Rbar_Rabs_lim_sum_le0 (f : nat -> Ts -> R) (x : Ts) :
    is_finite (Lim_seq (sum_n (fun n=> Rabs (f n x)))) ->
    Rbar_le
      (Rbar_abs (Lim_seq (fun n => (rvsum f) n x)))
      (Rbar_abs (Lim_seq (fun n => (rvsum (fun n0 => (rvabs (f n0))) n x)))).
  Proof.
    intros.
    apply series_abs_bounded in H.
    generalize H; intros HH.
    generalize (ex_series_Rabs (fun n => (f n x)) H); intros.
    generalize (Series_Rabs (fun n => (f n x)) H); intros.
    unfold rvsum, rvabs.
    apply ex_series_Lim_seq in H.
    apply ex_series_Lim_seq in H0.
    replace (Lim_seq
               (fun n : nat => sum_n (fun n0 : nat => f n0 x) n))
      with (Finite ( Series (fun n : nat => f n x))).
    replace (Lim_seq
          (fun n : nat =>
             sum_n (fun n0 : nat => Rabs (f n0 x)) n))
      with (Finite (Series (fun n : nat => Rabs (f n x)))).
    simpl.
    apply Rge_le.
    rewrite Rabs_right.
    apply Rle_ge, H1.
    apply Rle_ge, Series_nonneg; trivial.
    intros.
    apply Rabs_pos.
  Qed.

  Lemma Rabs_lim_sum_le0 (f : nat -> Ts -> R) (x : Ts) :
    is_finite (Lim_seq (sum_n (fun n=> Rabs (f n x)))) ->
    Rbar_le
      (Rbar_abs (Finite (real (Lim_seq (fun n => (rvsum f) n x)))))
      (Rbar_abs (Lim_seq (fun n => (rvsum (fun n0 => (rvabs (f n0))) n x)))).
  Proof.
    intros.
    apply series_abs_bounded in H.
    generalize H; intros HH.
    generalize (ex_series_Rabs (fun n => (f n x)) H); intros.
    generalize (Series_Rabs (fun n => (f n x)) H); intros.
    unfold rvsum, rvabs.
    apply ex_series_Lim_seq in H.
    apply ex_series_Lim_seq in H0.
    replace (Lim_seq
               (fun n : nat => sum_n (fun n0 : nat => f n0 x) n))
      with (Finite ( Series (fun n : nat => f n x))).
    replace (Lim_seq
          (fun n : nat =>
             sum_n (fun n0 : nat => Rabs (f n0 x)) n))
      with (Finite (Series (fun n : nat => Rabs (f n x)))).
    simpl.
    apply Rge_le.
    rewrite Rabs_right.
    apply Rle_ge, H1.
    apply Rle_ge, Series_nonneg; trivial.
    intros.
    apply Rabs_pos.
  Qed.

    Lemma Rbar_Rabs_lim_sum_le (f : nat -> Ts -> R) (x : Ts) :
    Rbar_le
      (Rbar_abs (Lim_seq (fun n => (rvsum f) n x)))
      (Rbar_abs (Lim_seq (fun n => (rvsum (fun n0 => (rvabs (f n0))) n x)))).
  Proof.
    case_eq (Lim_seq
          (fun n : nat =>
           rvsum (fun n0 : nat => rvabs (f n0)) n x)); intros.
    - rewrite <- H.
      apply Rbar_Rabs_lim_sum_le0.
      unfold rvsum, rvabs in H.
      replace  (Lim_seq (sum_n (fun n : nat => Rabs (f n x))))
        with
           (Lim_seq
              (fun n : nat =>
                 sum_n (fun n0 : nat => Rabs (f n0 x)) n)).
      now rewrite H.
      apply Lim_seq_ext.
      intros; trivial.
    - destruct (Lim_seq (fun n : nat => rvsum f n x)); now simpl.
    - assert (Rbar_le 0 (Lim_seq
        (fun n : nat =>
         rvsum (fun n0 : nat => rvabs (f n0)) n x))).
      + apply Lim_seq_pos.
        intros.
        unfold rvsum, rvabs.
        apply sum_n_nneg.
        intros.
        apply Rabs_pos.
      + rewrite H in H0.
        now simpl in H0.
  Qed.


  Lemma Rabs_lim_sum_le (f : nat -> Ts -> R) (x : Ts) :
    Rbar_le
      (Rbar_abs (Finite (real (Lim_seq (fun n => (rvsum f) n x)))))
      (Rbar_abs (Lim_seq (fun n => (rvsum (fun n0 => (rvabs (f n0))) n x)))).
  Proof.
    case_eq (Lim_seq
          (fun n : nat =>
           rvsum (fun n0 : nat => rvabs (f n0)) n x)); intros.
    - rewrite <- H.
      apply Rabs_lim_sum_le0.
      unfold rvsum, rvabs in H.
      replace  (Lim_seq (sum_n (fun n : nat => Rabs (f n x))))
        with
           (Lim_seq
              (fun n : nat =>
                 sum_n (fun n0 : nat => Rabs (f n0 x)) n)).
      now rewrite H.
      apply Lim_seq_ext.
      intros; trivial.
    - destruct (Lim_seq (fun n : nat => rvsum f n x)); now simpl.
    - assert (Rbar_le 0 (Lim_seq
        (fun n : nat =>
         rvsum (fun n0 : nat => rvabs (f n0)) n x))).
      + apply Lim_seq_pos.
        intros.
        unfold rvsum, rvabs.
        apply sum_n_nneg.
        intros.
        apply Rabs_pos.
      + rewrite H in H0.
        now simpl in H0.
  Qed.

  End eqs.
End defs.

Ltac rv_unfold := unfold
                    const,
                  id,
                  compose,
                  EventIndicator,
                  rvsqr,
                  rvpow,
                  rvpower,
                  rvabs,
                  rvmax, 
                  rvmin,
                  rvchoice,
                  bvmin_choice,
                  bvmax_choice,
                  pos_fun_part,
                  neg_fun_part,
                  rvminus,
                  rvopp,
                  rvscale,
                  rvplus,
                  rvmult in *.
