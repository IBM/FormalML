Require Import Coquelicot.Coquelicot.
Require Import ProbSpace SigmaAlgebras.
Require Import Reals.
Require Import Lra Lia.
Require Import Utils.
Require Import NumberIso.
Require Import Equivalence.
Require Import Program.
Require Import QArith.

Set Bullet Behavior "Strict Subproofs".

(* specialized for R *)

Instance open_borel_sa : SigmaAlgebra R
  := generated_sa open_set.

Instance borel_sa : SigmaAlgebra R
  := generated_sa (fun (s:R->Prop) => exists r, forall m, m <= r <-> s m)%R.

Section Borel.

Local Open Scope R.

Context {Ts:Type}
        {dom : SigmaAlgebra Ts}.

Lemma borel_sa_preimage
      (rvx: Ts -> R)
      (pf_pre: forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r)%R) :
  (forall B: event borel_sa, sa_sigma (event_preimage rvx B)).
Proof.
  intros.
  unfold event_preimage.
  destruct B; simpl.
  apply generated_sa_closure in s.
  simpl in *.  
  dependent induction s.
  - apply sa_all.
  - destruct H as [??].
    generalize (pf_pre x).
    apply sa_proper; intros xx.
    specialize (H (rvx xx)).
    tauto.
  - apply sa_countable_union. 
    eauto.
  - apply sa_complement; eauto.
Qed.

Lemma borel_sa_preimage2 
      (rvx: Ts -> R):
  (forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r)%R) <-> 
  (forall B: event borel_sa, (sa_sigma (event_preimage rvx B))).
Proof.
  split; intros.
  - now apply borel_sa_preimage.
  - unfold event_preimage in *.
    refine (H (exist _  (fun x => x <= r)%R _)).
    apply generated_sa_sub.
    exists r; intuition.
Qed.

Lemma open_borel_sa_preimage
      (rvx: Ts -> R)
      (pf_pre: forall B:pre_event R, open_set B -> sa_sigma (pre_event_preimage rvx B)%R) :
  (forall B: event open_borel_sa, sa_sigma (event_preimage rvx B)).
Proof.
  intros.
  unfold event_preimage.
  destruct B; simpl in *.
  apply generated_sa_closure in s.
  simpl in *.  
  dependent induction s.
  - apply sa_all.
  - generalize (pf_pre q); intros.
    apply H0.
    now unfold open_set.
  - apply sa_countable_union. 
    eauto.
  - apply sa_complement; eauto.
Qed.

Lemma open_borel_sa_preimage2 
      (rvx: Ts -> R):
  (forall B:pre_event R, open_set B -> sa_sigma (pre_event_preimage rvx B)%R) <->
  (forall B:event open_borel_sa, sa_sigma (event_preimage rvx B)).
Proof.
  split; intros.
  - now apply open_borel_sa_preimage.
  -  unfold event_preimage, pre_event_preimage in *.
     refine (H (exist _ B _)).
    now apply generated_sa_sub.
Qed.

  Lemma equiv_le_lt (f : Ts -> R) (r:R) :
    pre_event_equiv (fun omega : Ts => f omega < r)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => f omega <= r - / (1 + INR n)))).
  Proof.
    unfold pre_event_equiv, pre_union_of_collection.
    intros.
    split ; intros.
    + generalize (archimed_cor1 (r - f x)) ; intros.
      assert (r - f x > 0) by lra. specialize (H0 H1).
      clear H1.
      destruct H0 as [N [HNf HN]].
      exists N. left.
      replace (1 + INR N) with (INR (S N)) by (apply S_O_plus_INR).
      assert (f x < r - / INR N) by lra.
      eapply Rlt_trans ; eauto.
      unfold Rminus.
      apply Rplus_lt_compat_l. apply Ropp_lt_contravar.
      apply Rinv_lt_contravar.
      rewrite <-mult_INR. apply lt_0_INR ; lia.
      apply lt_INR ; lia.
    + destruct H.
      assert (0 < / INR (S x0)).
      apply Rinv_0_lt_compat.
      apply  lt_0_INR; lia.
      replace (1 + INR x0) with (INR (S x0)) in H by (apply S_O_plus_INR).
      lra.
  Qed.

  Lemma equiv_ge_gt (f : Ts -> R) (r:R) :
    pre_event_equiv (fun omega : Ts => f omega > r)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => f omega >= r + / (1 + INR n)))).
  Proof.
    unfold event_equiv, union_of_collection.
    intros.
    split ; intros.
    + generalize (archimed_cor1 (f x - r )) ; intros.
      assert (0 < f x - r) by lra. 
      specialize (H0 H1).
      clear H1.
      destruct H0 as [N [HNf HN]].
      exists N. left.
      replace (1 + INR N) with (INR (S N)) by (apply S_O_plus_INR).
      assert (f x > r + / INR N) by lra.
      eapply Rlt_trans ; eauto.
      unfold Rminus.
      apply Rplus_lt_compat_l.
      apply Rinv_lt_contravar.
      rewrite <-mult_INR. apply lt_0_INR ; lia.
      apply lt_INR ; lia.
    + destruct H.
      assert (0 < / INR (S x0)).
      apply Rinv_0_lt_compat.
      apply  lt_0_INR; lia.
      replace (1 + INR x0) with (INR (S x0)) in H by (apply S_O_plus_INR).
      lra.
  Qed.

  Lemma sa_le_gt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega > r)).
  Proof. 
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega > r)
                        (pre_event_complement (fun omega : Ts => f omega <= r))).
    - intro x.
      unfold pre_event_complement.
      split; intros; lra.
    - rewrite H0.
      now apply sa_complement.
  Qed.

  Lemma sa_ge_lt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega < r)).
  Proof. 
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega < r)
                        (pre_event_complement (fun omega : Ts => f omega >= r))).
    - intro x.
      unfold pre_event_complement.
      split; intros; lra.
    - rewrite H0.
      now apply sa_complement.
  Qed.

  Lemma sa_le_ge (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega >= r)
                        (pre_event_complement (fun omega : Ts => f omega < r))).
    {
      intro x.
      unfold pre_event_complement.
      split; intros; lra.
    }
      rewrite H0.
      apply sa_complement.
      rewrite equiv_le_lt.
      apply sa_countable_union.
      intros.
      apply H.
  Qed.

  Lemma sa_ge_le (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega <= r)
                        (pre_event_complement (fun omega : Ts => f omega > r))).
    {
      intro x.
      unfold pre_event_complement.
      split; intros; lra.
    }
      rewrite H0.
      apply sa_complement.
      rewrite equiv_ge_gt.
      apply sa_countable_union.
      intros.
      apply H.
  Qed.
  
  Lemma sa_le_lt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega < r)).
  Proof. 
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega < r)
                        (pre_event_complement (fun omega : Ts => f omega >= r))).
    - intro x.
      unfold pre_event_complement.
      split; intros; lra.
    - rewrite H0.
      apply sa_complement.
      now apply sa_le_ge.
  Qed.

  Lemma sa_ge_gt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega > r)).
  Proof. 
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega > r)
                        (pre_event_complement (fun omega : Ts => f omega <= r))).
    - intro x.
      unfold pre_event_complement.
      split; intros; lra.
    - rewrite H0.
      apply sa_complement.
      now apply sa_ge_le.
  Qed.

  Lemma sa_closed_intervals (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (l r:R), sa_sigma (fun omega : Ts => l <= f omega <= r)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => l <= f omega <= r) 
                        (pre_event_inter (fun omega : Ts => l <= f omega) 
                                     (fun omega : Ts => f omega <= r))).
    now unfold pre_event_equiv, pre_event_inter.
    rewrite H0.
    apply sa_inter; trivial.
    assert (pre_event_equiv (fun omega : Ts => l <= f omega)
                        (fun omega : Ts => f omega >= l)).
    red; intros; intuition.
    rewrite H1.
    now apply sa_le_ge.
  Qed.

  Lemma sa_open_intervals (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (l r:R), sa_sigma (fun omega : Ts => l < f omega < r)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => l < f omega < r) 
                        (pre_event_inter (fun omega : Ts => l < f omega) 
                                     (fun omega : Ts => f omega < r))).
    now unfold pre_event_equiv, pre_event_inter.
    rewrite H0.
    apply sa_inter; trivial.
    assert (pre_event_equiv (fun omega : Ts => l < f omega)
                        (fun omega : Ts => f omega > l)).
    red; intros; intuition.
    rewrite H1.
    now apply sa_le_gt.
    now apply sa_le_lt.
  Qed.

  Lemma sa_le_pt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (pt:R), sa_sigma (fun omega : Ts => f omega = pt)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega = pt)
                        (pre_event_inter (fun omega : Ts => f omega <= pt)
                                     (fun omega : Ts => f omega >= pt))).
    - unfold pre_event_equiv, pre_event_inter; intros.
      intuition.
    - rewrite H0.
      apply sa_inter; trivial.
      now apply sa_le_ge.
  Qed.

  Definition Q_interval (l r : Q) (x:R) : Prop :=
    Qreals.Q2R l < x < Qreals.Q2R r.  
  
  Lemma Q_neighborhood_included (D:R -> Prop) (x:R) :
        neighbourhood D x -> 
        exists (l r : Q), Q_interval l r x /\
                          included (Q_interval l r) D.
    Proof.
      unfold neighbourhood, included, disc; intros.
      destruct H as [eps H].
      generalize (cond_pos eps); intros.
      assert (x < x+eps)%R by lra.
      assert (x - eps < x)%R by lra.
      generalize (Q_dense (x-eps) x H2); intros.
      generalize (Q_dense x (x + eps) H1); intros.
      destruct H3 as [l0 H3].      
      destruct H4 as [r0 H4].
      exists l0; exists r0.
      unfold Q_interval.
      split; [lra | ].
      intros;  apply H.
      rewrite Rcomplements.Rabs_lt_between'; lra.
    Qed.

    Lemma Q_open_set (D:R -> Prop) :
      open_set D <->
      (forall x:R, D x ->
        exists (l r : Q), Q_interval l r x /\
                          included (Q_interval l r) D).
    Proof.
      unfold open_set.
      split; intros.
      - apply Q_neighborhood_included.
        now apply H.
      - unfold neighbourhood.
        specialize (H x H0).
        destruct H as [l0 H]; destruct H as [r0 H].
        destruct H.
        unfold included,disc,Q_interval in *.
        assert (0 < Rmin (x - Qreals.Q2R l0) (Qreals.Q2R r0 - x))%R.
        + apply Rmin_pos; lra.
        + exists (mkposreal _ H2); intros; apply H1.
          rewrite Rcomplements.Rabs_lt_between in H3; simpl in H3.
          destruct H3.
          apply Ropp_lt_contravar in H3.
          rewrite Ropp_involutive in H3.
          apply Rmin_Rgt_l in H3.
          apply Rmin_Rgt_l in H4.        
          lra.
     Qed.

    Lemma sa_le_open_set (f : Ts -> R) :
      (forall (r:R),  sa_sigma (fun omega : Ts => (f omega <= r)%R)) ->      
      (forall B: pre_event R, open_set B -> sa_sigma (pre_event_preimage f B)).
    Proof.
      unfold pre_event_preimage; intros.
      generalize (Q_open_set B); intros.
      destruct H1.
      assert (pre_event_equiv (fun omega : Ts => B (f omega))
                          (pre_union_of_collection
                             (fun (n:nat) => 
                                let n12 := (@iso_b _ _ nat_pair_encoder) n in
                                let qint := Q_interval (iso_b (fst n12)) (iso_b (snd n12)) in
                                fun omega : Ts => (qint (f omega)) /\
                                                  (included qint B)))).
      - unfold pre_event_equiv, union_of_collection; intros.
        split; intros.
        + specialize (H1 H0 (f x) H3).
          destruct H1 as [l0 [r0 H1]].
          exists (iso_f ((iso_f l0), (iso_f r0)) ).
          rewrite iso_b_f.
          unfold fst, snd.
          now do 2 rewrite iso_b_f.
        + destruct H3.
          unfold included in H3.
          destruct H3.
          now specialize (H4 (f x) H3).
      - rewrite H3.
        apply sa_countable_union; intros.
        generalize (sa_open_intervals f H); intros.
        unfold Q_interval.
        specialize (H4 (Qreals.Q2R (iso_b (fst (@iso_b _ nat nat_pair_encoder n))))
                       (Qreals.Q2R (iso_b (snd (@iso_b _ nat nat_pair_encoder n))))).
        apply sa_inter; trivial.
        apply sa_sigma_const_classic.
    Qed.
      
    Lemma sa_open_set_le (f : Ts -> R) :
      (forall B: pre_event R, open_set B -> sa_sigma (pre_event_preimage f B)) ->
      (forall (r:R),  sa_sigma (fun omega : Ts => (f omega <= r)%R)).
    Proof.
      intros.
      assert (pre_event_equiv (fun omega : Ts => (f omega <= r)%R)
                          (pre_event_complement (fun omega : Ts => (f omega > r)%R))).
      - unfold pre_event_equiv, pre_event_complement.
        intros.
        lra.
      - rewrite H0.
        apply sa_complement.
        apply H.
        unfold open_set, neighbourhood.
        intros; unfold disc.
        unfold included.
        assert (0 < (x-r)/2)%R.
        lra.
        exists (mkposreal _ H2); intros.
        simpl in *.
        apply Rabs_def2 in H3.
        lra.
    Qed.

    Lemma sa_open_iff_le (f : Ts -> R) :
      (forall B: pre_event R, open_set B -> sa_sigma (pre_event_preimage f B)) <->
      (forall (r:R),  sa_sigma (fun omega : Ts => (f omega <= r)%R)).
    Proof.
      split.
      apply sa_open_set_le.
      apply sa_le_open_set.
    Qed.

End Borel.

Local Open Scope equiv_scope.

Lemma sa_borel_open_le_sub1 : sa_sub open_borel_sa borel_sa.
Proof.
  generalize (sa_open_iff_le id).
  unfold pre_event_preimage, id.
  intros HH.
  intros e; simpl.
  intros.
  apply H.
  unfold all_included; intros.
  apply HH; trivial.
  intros.
  red in H0.
  apply borel_sa_preimage2.
  unfold event_preimage.
  simpl; intros.
  destruct B; simpl.
  auto.
Qed.

Lemma sa_borel_open_le_sub2 : sa_sub borel_sa open_borel_sa.
Proof.
  intros e; simpl; intros Hs.
  apply generated_sa_closure in Hs.
  intros.
  simpl in *.
  dependent induction Hs.
  - apply sa_all.
  - destruct H as [r Hr].
    assert (eqq:pre_event_equiv q (fun m => (m <= r)%R)).
    { red; intros; symmetry; trivial. }
    rewrite eqq.
    clear Hr eqq.
    assert (HH2:(pre_event_equiv (fun m : R => m <= r)
                             (pre_event_complement (fun m => m > r)))%R).
    {
      unfold pre_event_complement; intros x.
      intuition lra.
    }
    rewrite HH2; clear HH2.
    apply sa_complement.
    apply H0.
    intros x xgt.
    red.
    unfold included, disc.
    assert (HH:(0 < (x-r)/2)%R) by lra.
    exists (mkposreal _ HH); intros.
    simpl in *.
    apply Rabs_def2 in H.
    lra.
  - apply sa_countable_union; eauto.
  - apply sa_complement; eauto.
Qed.  

Theorem sa_borel_open_le_equiv : open_borel_sa === borel_sa.
Proof.
  split; intros.
  - now apply sa_borel_open_le_sub1.
  - now apply sa_borel_open_le_sub2.
Qed.

Local Open Scope R.


  Section RbarBorel.
    
  Instance Rbar_borel_sa : SigmaAlgebra Rbar
    := generated_sa (fun (s:Rbar->Prop) => exists r, forall m, Rbar_le m r <-> s m).

  Context {Ts:Type}
    {dom: SigmaAlgebra Ts}.

    (* For the Rbar_borel_sa, this is an equivalent definition *)
  Class RbarMeasurable (f: Ts -> Rbar)
      := rbarmeasurable : forall (r:Rbar), 
          sa_sigma (fun omega : Ts => Rbar_le (f omega) r).

  Lemma Rbar_borel_sa_preimage
      (rvx: Ts -> Rbar)
      (pf_pre: forall r:Rbar, sa_sigma (fun omega:Ts => Rbar_le (rvx omega) r)) :
  (forall B: event Rbar_borel_sa, sa_sigma (event_preimage rvx B)).
  Proof.
    intros.
    unfold event_preimage.
    destruct B; simpl.
    apply generated_sa_closure in s.
    simpl in *.  
    dependent induction s.
    - apply sa_all.
    - destruct H as [??].
      generalize (pf_pre x).
      apply sa_proper; intros xx.
      specialize (H (rvx xx)).
      tauto.
    - apply sa_countable_union. 
      eauto.
    - apply sa_complement; eauto.
  Qed.

  Lemma Rbar_borel_sa_preimage2 
      (rvx: Ts -> Rbar):
  (forall r:Rbar, sa_sigma (fun omega:Ts => Rbar_le (rvx omega) r)) <-> 
  (forall B: event Rbar_borel_sa, (sa_sigma (event_preimage rvx B))).
Proof.
  split; intros.
  - now apply Rbar_borel_sa_preimage.
  - unfold event_preimage in *.
    refine (H (exist _  (fun x => Rbar_le x r) _)).
    apply generated_sa_sub.
    exists r; intuition.
Qed.

  Lemma Rbar_equiv_le_lt (f : Ts -> Rbar) (r:R) :
    pre_event_equiv (fun omega : Ts => Rbar_lt (f omega) r)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => 
                                      Rbar_le (f omega) 
                                              (Rbar_minus r  (/ (1 + INR n)))))).
  Proof.
    unfold pre_event_equiv, pre_union_of_collection.
    intros.
    split ; intros.
    - case_eq (f x); intros.
      + rewrite H0 in H; simpl in H.
        generalize (archimed_cor1 (r - r0)) ; intros.
        assert (r - r0 > 0) by lra.
        specialize (H1 H2).
        clear H2.
        destruct H1 as [N [HNf HN]].
        exists N. left.
        replace (1 + INR N) with (INR (S N)) by (apply S_O_plus_INR).
        assert (r0 < r - / INR N) by lra.
        eapply Rlt_trans ; eauto.
        unfold Rminus.
        apply Rplus_lt_compat_l, Ropp_lt_contravar.
        apply Rinv_lt_contravar.
        rewrite <-mult_INR. apply lt_0_INR ; lia.
        apply lt_INR ; lia.
      + rewrite H0 in H; now simpl in H.
      + exists (0%nat); now simpl.
   - destruct H.
     assert (0 < / INR (S x0)).
     { 
       apply Rinv_0_lt_compat.
       apply  lt_0_INR; lia.
     }
     replace (1 + INR x0) with (INR (S x0)) in H by (apply S_O_plus_INR).
     eapply Rbar_le_lt_trans.
     apply H.
     simpl; simpl in H0; lra.
   Qed.

  Definition Rbar_ge (x y : Rbar) := Rbar_le y x.

  Lemma Rbar_sa_le_ge (f : Ts -> Rbar) :
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_le (f omega) r)) ->
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_ge (f omega) r)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => Rbar_ge (f omega) r)
                        (pre_event_complement (fun omega : Ts => Rbar_lt (f omega) r))).
    {
      intro x.
      unfold pre_event_complement.
      split; intros.
      - now apply Rbar_le_not_lt.
      - now apply Rbar_not_lt_le in H0.
    }
    destruct r.
    - rewrite H0.
      apply sa_complement.
      rewrite Rbar_equiv_le_lt.
      apply sa_countable_union.
      intros.
      apply H.
    - rewrite H0.
      apply sa_complement.
      assert (pre_event_equiv 
                (fun omega : Ts => Rbar_lt (f omega) p_infty)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => 
                                      Rbar_le (f omega) (INR n))))).
      { 
        intro x.
        unfold pre_union_of_collection.
        destruct (f x).
        - split; intros.
          + destruct (Rle_dec 0 r).
            * exists (Z.to_nat (up r)).
              rewrite INR_up_pos; try lra.
              simpl.
              left.
              apply archimed.
            * exists (0%nat).
              simpl; lra.
          + now simpl.
        - split; intros.
          + now simpl in H1.
          + destruct H1; now simpl in H1.
        - split; intros.
          + exists (0%nat); now simpl.
          + now simpl.
      }
      rewrite H1.
      apply sa_countable_union.
      intros.
      apply H.
    - assert (pre_event_equiv (fun omega : Ts => Rbar_ge (f omega) m_infty)
                              (fun omega => True)).
      {
        intro x.
        now simpl.
      }
      rewrite H1.
      apply sa_all.
   Qed.

  Lemma Rbar_sa_le_lt (f : Ts -> Rbar) :
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_le (f omega) r)) ->
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_lt (f omega) r)).
  Proof. 
    intros.
    assert (pre_event_equiv (fun omega : Ts => Rbar_lt (f omega) r)
                        (pre_event_complement (fun omega : Ts => Rbar_ge (f omega) r))).
    - intro x.
      unfold pre_event_complement.
      split; intros.
      + unfold Rbar_ge.
        now apply Rbar_lt_not_le.
      + unfold Rbar_ge in H0.
        now apply Rbar_not_le_lt in H0.
    - rewrite H0.
      apply sa_complement.
      now apply Rbar_sa_le_ge.
  Qed.

  Definition Rbar_gt (x y : Rbar) := Rbar_lt y x.

   Lemma Rbar_sa_le_gt (f : Ts -> Rbar) :
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_le (f omega) r)) ->
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_gt (f omega) r)).
  Proof. 
    intros.
    assert (pre_event_equiv (fun omega : Ts => Rbar_gt (f omega) r)
                        (pre_event_complement (fun omega : Ts => Rbar_le (f omega) r))).
    - intro x.
      unfold pre_event_complement.
      split; intros.
      + unfold Rbar_le.
        now apply Rbar_lt_not_le.
      + unfold Rbar_le in H0.
        now apply Rbar_not_le_lt in H0.
    - rewrite H0.
      now apply sa_complement.
  Qed.

  Lemma Rbar_equiv_ge_gt (f : Ts -> Rbar) (r:R) :
    pre_event_equiv (fun omega : Ts => Rbar_gt (f omega) r)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => Rbar_ge (f omega) (r + / (1 + INR n))))).
  Proof.
    unfold event_equiv, union_of_collection.
    intros.
    split ; intros.
    - case_eq (f x); intros.
      + rewrite H0 in H; simpl in H.
        generalize (archimed_cor1 (f x - r )) ; intros.
        assert (0 <  r0 - r) by lra. 
        rewrite H0 in H1.
        specialize (H1 H2).
        clear H2.
        destruct H1 as [N [HNf HN]].
        exists N.
        rewrite H0; simpl; left.
        replace (1 + INR N) with (INR (S N)) by (apply S_O_plus_INR).
        simpl in HNf.
        assert (r0 > r + / INR N) by lra.
        eapply Rlt_trans ; eauto.
        unfold Rminus.
        apply Rplus_lt_compat_l.
        apply Rinv_lt_contravar.
        rewrite <-mult_INR. apply lt_0_INR ; lia.
        apply lt_INR ; lia.
      + exists 0%nat.
        rewrite H0.
        now simpl.
      + rewrite H0 in H.
        now simpl in H.
    - destruct H.
      assert (0 < / INR (S x0)).
      apply Rinv_0_lt_compat.
      apply  lt_0_INR; lia.
      replace (1 + INR x0) with (INR (S x0)) in H by (apply S_O_plus_INR).
      unfold Rbar_gt; unfold Rbar_ge in H.
      eapply Rbar_lt_le_trans.
      shelve.
      apply H.
      Unshelve.
      red.
      lra.
  Qed.

  Lemma Rbar_sa_ge_le (f : Ts -> Rbar) :
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_ge (f omega) r)) ->
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_le (f omega) r)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => Rbar_le (f omega) r)
                        (pre_event_complement (fun omega : Ts => Rbar_gt (f omega) r))).
    {
      intro x.
      unfold pre_event_complement.
      unfold Rbar_gt.
      split; intros.
      - now apply Rbar_le_not_lt.
      - now apply Rbar_not_lt_le in H0.
    }
    destruct r.  
    - rewrite H0.
      apply sa_complement.
      rewrite Rbar_equiv_ge_gt.
      apply sa_countable_union.
      intros.
      apply H.
    - assert (pre_event_equiv (fun omega : Ts => Rbar_le (f omega) p_infty)
                              (fun omega => True)).
      {
        intro x.
        unfold Rbar_le.
        match_destr; easy.
      }
      rewrite H1.
      apply sa_all.
    - rewrite H0.
      apply sa_complement.
      assert (pre_event_equiv 
                (fun omega : Ts => Rbar_gt (f omega) m_infty)
                (pre_union_of_collection
                   (fun (n:nat) => (fun omega : Ts => 
                                      Rbar_ge (f omega) (- (INR n)))))).
      { 
        intro x.
        unfold pre_union_of_collection.
        destruct (f x).
        - split; intros.
          + destruct (Rle_dec r 0).
            * exists (Z.to_nat (up (- r))).
              rewrite INR_up_pos; try lra.
              simpl.
              left.
              generalize (archimed (-r)); intros.
              lra.
            * exists (0%nat).
              simpl; lra.
          + now simpl.
        - split; intros.
          + exists 0%nat; now simpl.
          + now simpl.
        - split; intros.
          + now simpl in H1.
          + destruct H1.
            now simpl in H1.
      }
      rewrite H1.
      apply sa_countable_union.
      intros.
      apply H.
  Qed.

  Lemma Rbar_sa_le_pt (f : Ts -> Rbar) :
    (forall (r:Rbar),  sa_sigma (fun omega : Ts => Rbar_le (f omega) r)) ->
    (forall (pt:Rbar), sa_sigma (fun omega : Ts => f omega = pt)).
  Proof.
    intros.
    assert (pre_event_equiv (fun omega : Ts => f omega = pt)
                        (pre_event_inter (fun omega : Ts => Rbar_le (f omega) pt)
                                     (fun omega : Ts => Rbar_ge (f omega) pt))).
    - unfold pre_event_equiv, pre_event_inter; intros.
      unfold Rbar_ge.
      split; intros.
      + rewrite H0; simpl.
        split; apply Rbar_le_refl.
      + destruct H0.
        now apply Rbar_le_antisym.
    - rewrite H0.
      apply sa_inter; trivial.
      now apply Rbar_sa_le_ge.
   Qed.

 End RbarBorel.
 Section RbarBorel2.

  Context {Ts:Type}
    {dom: SigmaAlgebra Ts}.

  Lemma Rbar_borel_singleton (c:Rbar) :
    sa_sigma (SigmaAlgebra:=Rbar_borel_sa) (pre_event_singleton c).
  Proof.
    apply Rbar_sa_le_pt.
    apply Rbar_borel_sa_preimage2; intros.
    destruct B.
    unfold event_preimage.
    simpl.
    apply s.
  Qed.

  End RbarBorel2.
  
