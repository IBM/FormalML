Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Reals.
Require Import Classical.

Require Import BorelSigmaAlgebra.
Require Import ProbSpace.
Require Import RandomVariable.
Require Import RealRandomVariable.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R.

Class HasEventEq {Td:Type} (cod:SigmaAlgebra Td)
  := sa_event_eq :
       forall {Ts} {dom:SigmaAlgebra Ts} (r1 r2:Ts->Td)
         {rv1:RandomVariable dom cod r1}
         {rv2:RandomVariable dom cod r2},
         sa_sigma (fun x => r1 x = r2 x).

Global Instance borel_haseqs : HasEventEq borel_sa.
Proof.
  red; intros.
  eapply sa_proper
  ; [| apply (sa_preimage_singleton (rvminus r1 r2) 0)].
  red; intros.
  unfold pre_event_preimage, pre_event_singleton, rvminus, rvplus, rvopp, rvscale.
  split; lra.
Qed.

Section almost_eq.
  Context {Ts:Type} {Td:Type}
          {dom: SigmaAlgebra Ts}
          {cod: SigmaAlgebra Td}
          {has_eq:HasEventEq cod}
          (prts: ProbSpace dom).

  Definition event_eq (r1 r2:Ts -> Td)
         {rv1:RandomVariable dom cod r1}
         {rv2:RandomVariable dom cod r2}
    : event dom
    := exist _ _ (sa_event_eq r1 r2).

  Definition rv_almost_eq (r1 r2:Ts -> Td)
             {rv1:RandomVariable dom cod r1}
             {rv2:RandomVariable dom cod r2}
    := ps_P (event_eq r1 r2) = 1.

  Lemma rv_almost_eq_eq (r1 r2:Ts -> Td)
             {rv1:RandomVariable dom cod r1}
             {rv2:RandomVariable dom cod r2} :
    rv_eq r1 r2 ->
    rv_almost_eq r1 r2.
  Proof.
    unfold rv_almost_eq; intros eqq.
    erewrite ps_proper; try eapply ps_one.
    unfold Ω, pre_Ω.
    split; simpl; trivial.
  Qed.
  
  Lemma rv_almost_eq_alt_eq
        {r1 r2:Ts->Td}
        {rv1:RandomVariable dom cod r1}
        {rv2:RandomVariable dom cod r2} 
    : ps_P (event_eq r1 r2) = 1 <-> ps_P (event_complement (event_eq r1 r2)) = 0.
  Proof.
    rewrite ps_complement.
    split; auto with real.
  Qed.

Lemma rv_almost_eq_rv_refl
      (x : Ts -> Td)
      {rvx : RandomVariable dom cod x} :
  rv_almost_eq x x.
Proof.
  unfold rv_almost_eq.
  erewrite ps_proper.
  - apply ps_one.
  - unfold event_eq, Ω, pre_Ω.
    intros ?; simpl.
    intuition.
Qed.

Lemma rv_almost_eq_rv_sym
      {r1 r2:Ts->Td}
      {rv1:RandomVariable dom cod r1}
      {rv2:RandomVariable dom cod r2} :
  rv_almost_eq r1 r2 -> rv_almost_eq r2 r1.
Proof.
  unfold rv_almost_eq.
  intros eqq.
  rewrite <- eqq.
  eapply ps_proper.
  intros ?; simpl.
  intuition.
Qed.

Lemma rv_almost_eq_rv_trans
      (x y z: Ts -> Td)
      {rvx : RandomVariable dom cod x} 
      {rvy : RandomVariable dom cod y} 
      {rvz : RandomVariable dom cod z} :
  rv_almost_eq x y ->
  rv_almost_eq y z ->
  rv_almost_eq x z.
Proof.
  unfold rv_almost_eq.
  intros ps1 ps2.
  simpl in *.
  generalize (ps_union prts (event_complement (event_eq x y)) (event_complement (event_eq y z)))
  ; intros HH.
  rewrite rv_almost_eq_alt_eq in ps1 by eauto with prob.
  rewrite rv_almost_eq_alt_eq in ps2 by eauto with prob.
  rewrite rv_almost_eq_alt_eq by eauto with prob.
  rewrite ps1,ps2 in HH.
  field_simplify in HH.
  assert (HH2 : ps_P
                  (event_inter (event_complement (event_eq x y))
                               (event_complement (event_eq y z))) = 0).
  {
    assert (HH3:ps_P
                  (event_union (event_complement (event_eq x y))
                               (event_complement (event_eq y z))) 
                +
                ps_P
                  (event_inter (event_complement (event_eq x y))
                               (event_complement (event_eq y z))) = 0)
           by (unfold event_complement, pre_event_complement in *; lra).
    rewrite Rplus_comm in HH3.
    apply Rplus_eq_0_l in HH3; trivial
    ; apply ps_pos
    ; eauto 6 with prob.
  }
  rewrite HH2, Ropp_0 in HH.

  assert (ele:event_sub
                (event_complement (event_eq x z))
                (event_union (event_complement (event_eq x y))
                             (event_complement (event_eq y z)))).
  {
    unfold event_complement, pre_event_complement in *; simpl in *.
    intros ?; simpl; intros.
    apply not_and_or.
    intros [??].
    congruence.
  }

  apply (@ps_sub _ _ prts) in ele; trivial.
  * rewrite HH in ele.
    apply Rle_antisym; trivial.
    apply ps_pos; trivial.
Qed.

End almost_eq.

Section borel_almost_eq.
  
Lemma rv_almost_eq_plus_proper
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x1 x2 y1 y2 : Ts -> R)
      {rvx1 : RandomVariable dom borel_sa x1}
      {rvx2: RandomVariable dom borel_sa x2}
      (eqqx : rv_almost_eq prts x1 x2)
      {rvy1 : RandomVariable dom borel_sa y1}
      {rvy2 : RandomVariable dom borel_sa y2}
      (eqqy : rv_almost_eq prts y1 y2) :
  rv_almost_eq prts (rvplus x1 y1) (rvplus x2 y2).
Proof.
  unfold rv_almost_eq in *.
  assert (event_sub (event_inter (event_eq x1 x2)
                                 (event_eq y1 y2))
                    (event_eq (rvplus x1 y1) (rvplus x2 y2))).
  - intros ? [??]; simpl in *.
    unfold rvplus.
    congruence.
  - assert (ps_P (event_inter (event_eq x1 x2) (event_eq y1 y2)) = 1).
    + apply ps_one_inter; trivial.
    + generalize (ps_sub prts (event_inter (event_eq x1 x2) (event_eq y1 y2))
                         (event_eq (rvplus x1 y1) (rvplus x2 y2))); intros.
      rewrite H0 in H1.
      apply Rle_antisym.
      * apply ps_le1.
      * apply H1; trivial.
Qed.


Lemma rv_almost_eq_mult_proper
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x1 x2 y1 y2 : Ts -> R)
      {rvx1 : RandomVariable dom borel_sa x1}
      {rvx2: RandomVariable dom borel_sa x2}
      (eqqx : rv_almost_eq prts x1 x2)
      {rvy1 : RandomVariable dom borel_sa y1}
      {rvy2 : RandomVariable dom borel_sa y2}
      (eqqy : rv_almost_eq prts y1 y2) :
  rv_almost_eq prts (rvmult x1 y1) (rvmult x2 y2).
Proof.
  unfold rv_almost_eq in *.
  assert (event_sub (event_inter (event_eq x1 x2)
                                 (event_eq y1 y2))
                    (event_eq (rvmult x1 y1) (rvmult x2 y2))).
  - intros ? [??]; simpl in *.
    unfold rvmult.
    congruence.
  - assert (ps_P (event_inter (event_eq x1 x2) (event_eq y1 y2)) = 1).
    + apply ps_one_inter; trivial.
    + generalize (ps_sub prts (event_inter (event_eq x1 x2) (event_eq y1 y2))
                         (event_eq (rvmult x1 y1) (rvmult x2 y2))); intros.
      rewrite H0 in H1.
      apply Rle_antisym.
      * apply ps_le1.
      * apply H1; trivial.
Qed.


Lemma rv_almost_eq_sub
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x1 x2: Ts -> R)
      (f:(Ts->R)->Ts->R)
      {rvx1 : RandomVariable dom borel_sa x1}
      {rvx2: RandomVariable dom borel_sa x2}
      {rvfx1 : RandomVariable dom borel_sa (f x1)}
      {rvfx2: RandomVariable dom borel_sa (f x2)}
      (eqqx : rv_almost_eq prts x1 x2)
      (fpres: forall x y a, x a = y a -> f x a = f y a)
:
  rv_almost_eq prts (f x1) (f x2).
Proof.
  red in eqqx.
  red.
  apply Rle_antisym.
  - apply ps_le1.
  - generalize (ps_sub prts (event_eq x1 x2) (event_eq (f x1) (f x2)))
    ; intros HH.
    rewrite eqqx in HH.
    apply HH.
    + intros a ?; simpl in *.
      auto.
Qed.
                                                         
  
Lemma rv_almost_eq_pow_abs_proper
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x1 x2: Ts -> R)
      n
      {rvx1 : RandomVariable dom borel_sa x1}
      {rvx2: RandomVariable dom borel_sa x2}
      (eqqx : rv_almost_eq prts (rvabs x1) (rvabs x2)) :
  rv_almost_eq prts (rvpow (rvabs x1) n) (rvpow (rvabs x2) n).
Proof.
  apply (rv_almost_eq_sub prts (rvabs x1) (rvabs x2) (fun x => rvpow x n)); trivial.
  intros.
  now unfold rvpow; rewrite H.
Qed.
      
Lemma rv_almost_eq_power_abs_proper
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x1 x2: Ts -> R)
      n
      {rvx1 : RandomVariable dom borel_sa x1}
      {rvx2: RandomVariable dom borel_sa x2}
      (eqqx : rv_almost_eq prts (rvabs x1) (rvabs x2)) :
  rv_almost_eq prts (rvpower (rvabs x1) (const n)) (rvpower (rvabs x2) (const n)).
Proof.
  apply (rv_almost_eq_sub prts (rvabs x1) (rvabs x2) (fun x => rvpower x (const n))); trivial.
  intros.
  now unfold rvpower; rewrite H.
Qed.

Lemma rv_almost_eq_abs_proper
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x1 x2: Ts -> R)
      {rvx1 : RandomVariable dom borel_sa x1}
      {rvx2: RandomVariable dom borel_sa x2}
      (eqqx : rv_almost_eq prts x1 x2) :
  rv_almost_eq prts (rvabs x1) (rvabs x2).
Proof.
  eapply rv_almost_eq_sub; eauto; try typeclasses eauto.
  intros.
  unfold rvabs.
  now rewrite H.
Qed.

End borel_almost_eq.

