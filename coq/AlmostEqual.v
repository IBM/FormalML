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

Section almost_eq.
  Context {Ts:Type} {Td:Type}
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Definition rv_almost_eq (r1 r2:Ts -> Td) :=
    ps_P (fun x => r1 x = r2 x) = 1.

  Global Instance rv_almost_eq_eq : subrelation rv_eq rv_almost_eq.
  Proof.
    unfold subrelation, rv_almost_eq; intros x y eqq.
    erewrite ps_proper; try eapply ps_one.
    unfold Ω.
    split; trivial.
  Qed.
  
  Lemma rv_almost_eq_alt_eq {r1 r2:Ts->Td} (Hsigma:sa_sigma (fun x => r1 x = r2 x))
    : ps_P (fun x => r1 x = r2 x) = 1 <-> ps_P (fun x => r1 x <> r2 x) = 0.
  Proof.
    generalize (ps_complement prts _ Hsigma)
    ; unfold event_complement
    ; intros HH
    ; rewrite HH.
    split; auto with real.
  Qed.

  Instance rv_almost_eq_equiv (Hsigma:forall r1 r2:Ts -> Td, sa_sigma (fun x => r1 x = r2 x)): Equivalence rv_almost_eq.
  Proof.
    unfold rv_almost_eq.
    constructor; red.
    - intros x.
      assert (eqq:event_equiv (fun x0 : Ts => x x0 = x x0) Ω)
        by firstorder.
      rewrite eqq.
      eauto with prob.
    - intros x y ps1.
      rewrite ps_proper; try eassumption.
      firstorder.
    - intros x y z ps1 ps2.
      rewrite rv_almost_eq_alt_eq in ps1 by auto.
      rewrite rv_almost_eq_alt_eq in ps2 by auto.
      rewrite rv_almost_eq_alt_eq by auto.
      generalize (ps_union prts _ _ (sa_complement _ (Hsigma x y)) (sa_complement _ (Hsigma y z)))
      ; intros HH.
      unfold event_complement in HH.
      rewrite ps1,ps2 in HH.
      field_simplify in HH.

      assert (HH2 : ps_P
                      (event_inter (event_complement (fun x0 : Ts => x x0 = y x0))
                                   (event_complement (fun x : Ts => y x = z x))) = 0).
      {
        assert (HH3:ps_P
                      (event_union (event_complement (fun x0 : Ts => x x0 = y x0))
                                   (event_complement (fun x : Ts => y x = z x))) 
                    +
                    ps_P
                      (event_inter (event_complement (fun x0 : Ts => x x0 = y x0))
                                   (event_complement (fun x : Ts => y x = z x))) = 0)
          by (unfold event_complement; lra).
        rewrite Rplus_comm in HH3.
        apply Rplus_eq_0_l in HH3; trivial
        ; apply ps_pos
        ; auto with prob.
      }
      unfold event_complement in HH2.
      rewrite HH2, Ropp_0 in HH.
      unfold event_union in HH2.

      assert (ele:event_sub
                    (event_complement (fun x0 : Ts => x x0 = z x0))
                    (event_union (event_complement (fun x1 : Ts => x x1 = y x1))
                                 (event_complement (fun x : Ts => y x = z x)))).
      {
        unfold event_complement.
        red; intros.
        apply not_and_or.
        intros [??].
        congruence.
      }

      apply (@ps_sub _ _ prts) in ele; trivial.
      * unfold event_complement in ele.
        rewrite HH in ele.
        apply Rle_antisym; trivial.
        apply ps_pos; trivial.
        apply sa_complement.
        apply Hsigma.
      * auto with prob.
      * apply sa_union; auto with prob.
  Qed.

End almost_eq.

Lemma Hsigma_borel_eq_pf
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) : forall r1 r2 : Ts -> R,
    RandomVariable dom borel_sa r1 ->
    RandomVariable dom borel_sa r2 ->
    sa_sigma (fun x0 : Ts => r1 x0 = r2 x0).
Proof.
  intros.
  assert (sa_sigma (fun x => (rvminus r1 r2) x = 0)).
  {
    apply sa_le_pt
    ; intros.
    apply borel_sa_preimage2
    ; intros.
    apply measurable_rv; trivial.
    apply minus_measurable; now apply rv_measurable.
  }
  eapply sa_proper; try eassumption.
  red; intros.
  unfold rvminus, rvplus, rvopp, rvscale.
  split; lra.
Qed.

Lemma rv_almost_eq_rv_refl
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x : Ts -> R)
      {rvx : RandomVariable dom borel_sa x} :
  rv_almost_eq prts x x.
Proof.
  unfold rv_almost_eq.
  assert (eqq:event_equiv (fun x0 : Ts => x x0 = x x0) Ω)
    by firstorder.
  rewrite eqq.
  eauto with prob.
Qed.

Global Instance rv_almost_eq_rv_sym {Ts Td:Type} {dom: SigmaAlgebra Ts} (prts: ProbSpace dom) :
  Symmetric (rv_almost_eq prts (Td:=Td)).
Proof.
  unfold rv_almost_eq.
  intros x y ps1; simpl in *.
  rewrite ps_proper; try eassumption.
  red; intros.
  split; congruence.
Qed.

Hint Resolve Hsigma_borel_eq_pf : prob.

Lemma rv_almost_eq_rv_trans
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x y z: Ts -> R)
      {rvx : RandomVariable dom borel_sa x} 
      {rvy : RandomVariable dom borel_sa y} 
      {rvz : RandomVariable dom borel_sa z} :
  rv_almost_eq prts x y ->
  rv_almost_eq prts y z ->
  rv_almost_eq prts x z.
Proof.
  unfold rv_almost_eq.
  intros ps1 ps2.
  simpl in *.
  rewrite rv_almost_eq_alt_eq in ps1 by eauto with prob.
  rewrite rv_almost_eq_alt_eq in ps2 by eauto with prob.
  rewrite rv_almost_eq_alt_eq by eauto with prob.
  generalize (ps_union prts _ _ (sa_complement _ (Hsigma_borel_eq_pf _ x y _ _)) (sa_complement _ (Hsigma_borel_eq_pf _ y z _ _)))
  ; intros HH.
  unfold event_complement in HH.
  rewrite ps1,ps2 in HH.
  field_simplify in HH.

  assert (HH2 : ps_P
                  (event_inter (event_complement (fun x0 : Ts => x x0 = y x0))
                               (event_complement (fun x : Ts => y x = z x))) = 0).
  {
    assert (HH3:ps_P
                  (event_union (event_complement (fun x0 : Ts => x x0 = y x0))
                               (event_complement (fun x : Ts => y x = z x))) 
                +
                ps_P
                  (event_inter (event_complement (fun x0 : Ts => x x0 = y x0))
                               (event_complement (fun x : Ts => y x = z x))) = 0)
      by (unfold event_complement; lra).
    rewrite Rplus_comm in HH3.
    apply Rplus_eq_0_l in HH3; trivial
    ; apply ps_pos
    ; eauto 6 with prob.
  }
  unfold event_complement in HH2.
  rewrite HH2, Ropp_0 in HH.
  unfold event_union in HH2.

  assert (ele:event_sub
                (event_complement (fun x0 : Ts => x x0 = z x0))
                (event_union (event_complement (fun x1 : Ts => x x1 = y x1))
                             (event_complement (fun x : Ts => y x = z x)))).
  {
    unfold event_complement.
    red; intros.
    apply not_and_or.
    intros [??].
    congruence.
  }

  apply (@ps_sub _ _ prts) in ele; trivial.
  * unfold event_complement in ele.
    rewrite HH in ele.
    apply Rle_antisym; trivial.
    apply ps_pos; trivial.
    apply sa_complement.
    eauto with prob.
  * eauto with prob.
  * apply sa_union; eauto with prob.
Qed.

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
  assert (event_sub (event_inter (fun x : Ts => x1 x = x2 x)
                                 (fun x : Ts => y1 x = y2 x))
                    (fun x : Ts => rvplus x1 y1 x = rvplus x2 y2 x)).
  - unfold event_sub, event_inter, rvplus.
    intros.
    destruct H.
    now rewrite H, H0.
  - assert (ps_P (event_inter (fun x : Ts => x1 x = x2 x) (fun x : Ts => y1 x = y2 x)) = 1).
    + apply ps_one_inter; trivial
      ; eapply Hsigma_borel_eq_pf; eauto.
    + generalize (ps_sub prts (event_inter (fun x : Ts => x1 x = x2 x) (fun x : Ts => y1 x = y2 x))
                         (fun x : Ts => rvplus x1 y1 x = rvplus x2 y2 x)); intros.
      rewrite H0 in H1.
      apply Rle_antisym.
      * apply ps_le1.
        apply (Hsigma_borel_eq_pf prts); now apply rvplus_rv.
      * apply H1; trivial.
        -- apply sa_inter; now apply (Hsigma_borel_eq_pf prts).
        -- apply (Hsigma_borel_eq_pf prts); now apply rvplus_rv.
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
  unfold rvmult.
  assert (event_sub (event_inter (fun x : Ts => x1 x = x2 x)
                                 (fun x : Ts => y1 x = y2 x))
                    (fun x : Ts => rvmult x1 y1 x = rvmult x2 y2 x)).
  - unfold event_sub, event_inter, rvmult.
    intros.
    destruct H.
    now rewrite H, H0.
  - assert (ps_P (event_inter (fun x : Ts => x1 x = x2 x) (fun x : Ts => y1 x = y2 x)) = 1).
    + apply ps_one_inter; trivial
      ; eapply Hsigma_borel_eq_pf; eauto.
    + generalize (ps_sub prts (event_inter (fun x : Ts => x1 x = x2 x) (fun x : Ts => y1 x = y2 x))
                         (fun x : Ts => rvmult x1 y1 x = rvmult x2 y2 x)); intros.
      rewrite H0 in H1.
      apply Rle_antisym.
      * apply ps_le1.
        apply (Hsigma_borel_eq_pf prts); now apply rvmult_rv.
      * apply H1; trivial.
        -- apply sa_inter; now apply (Hsigma_borel_eq_pf prts).
        -- apply (Hsigma_borel_eq_pf prts); now apply rvmult_rv.
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
    apply Hsigma_borel_eq_pf; eauto.
  - generalize (ps_sub prts (fun x : Ts => x1 x = x2 x) (fun x : Ts => f x1 x = f x2 x))
    ; intros HH.
    rewrite eqqx in HH.
    apply HH.
    + apply Hsigma_borel_eq_pf; eauto.
    + apply Hsigma_borel_eq_pf; eauto.
    + intros a ?.
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
  apply rv_almost_eq_sub; eauto; try typeclasses eauto.
  intros.
  unfold rvabs.
  now rewrite H.
Qed.
