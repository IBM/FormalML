Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Reals.
Require Import Classical.

Require Import BorelSigmaAlgebra.
Require Import ProbSpace.
Require Import RandomVariable.

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
    RandomVariable prts borel_sa r1 ->
    RandomVariable prts borel_sa r2 ->
    sa_sigma (fun x0 : Ts => r1 x0 = r2 x0).
Proof.
  intros.
  assert (sa_sigma (fun x => (rvminus r1 r2) x = 0)).
  {
    apply sa_le_pt
    ; intros.
    apply borel_sa_preimage2
    ; intros.
    now apply rv_preimage.
  }
  eapply sa_proper; try eassumption.
  red; intros.
  unfold rvminus, rvplus, rvopp, rvscale.
  split; lra.
Qed.

Lemma rv_almost_eq_plus_proper
      {Ts:Type} 
      {dom: SigmaAlgebra Ts}
      (prts: ProbSpace dom) 
      (x1 x2 y1 y2 : Ts -> R)
      {rvx1 : RandomVariable prts borel_sa x1}
      {rvx2: RandomVariable prts borel_sa x2}
      (eqqx : rv_almost_eq prts x1 x2)
      {rvy1 : RandomVariable prts borel_sa y1}
      {rvy2 : RandomVariable prts borel_sa y2}
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

