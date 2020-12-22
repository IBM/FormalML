Require Import Reals.
Require Import Morphisms Equivalence.
Require Import Lra.
Require Import utils.Utils.
(* For const *)
Require Export Program.Basics.

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

End rels.

Section defs.
  Context {Ts:Type}.

  Section funs.

    (* const is defined in Program.Basics *)

    Definition EventIndicator {P : Ts->Prop} (dec:forall x, {P x} + {~ P x}) : Ts -> R
      := fun omega => if dec omega then 1 else 0.

    Definition rvplus (rv_X1 rv_X2 : Ts -> R) :=
      (fun omega =>  (rv_X1 omega) + (rv_X2 omega)).

    Definition rvscale (c:R) (rv_X : Ts -> R) :=
      fun omega => c * (rv_X omega).

    Definition rvopp (rv_X : Ts -> R) := rvscale (-1) rv_X.

    Definition rvminus (rv_X1 rv_X2 : Ts -> R) :=
      rvplus rv_X1 (rvopp rv_X2).

    Definition rvmult (rv_X1 rv_X2 : Ts -> R) := 
      fun omega => (rv_X1 omega) * (rv_X2 omega).

    Definition rvsqr (rv_X : Ts -> R) := fun omega => Rsqr (rv_X omega).

    Definition rvabs  (rv_X : Ts -> R) := fun omega => Rabs (rv_X omega).

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
      unfold pos_fun_part; simpl.
      now apply Rle_max_compat_r.
    Qed.

    Lemma rv_le_neg_fun_part rv_X1 rv_X2 :
      rv_le rv_X1 rv_X2 ->
      rv_le (fun x : Ts => neg_fun_part rv_X2 x) (fun x : Ts => neg_fun_part rv_X1 x).
    Proof.
      intros le12 a.
      unfold pos_fun_part; simpl.
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

  End eqs.
End defs.
