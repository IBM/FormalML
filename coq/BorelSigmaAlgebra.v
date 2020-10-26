Require Import ProbSpace SigmaAlgebras.
Require Import Reals.
Require Import Lra Lia.
Require Import Utils.
Require Import NumberIso.

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
  (forall B: event R, sa_sigma B -> sa_sigma (event_preimage rvx B)).
Proof.
Admitted.


Lemma borel_sa_preimage2 
      (rvx: Ts -> R):
  (forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r)%R) <-> 
  (forall B: event R, sa_sigma B -> (sa_sigma (event_preimage rvx B))).
Proof.
  split; intros.
  - now apply borel_sa_preimage.
  - unfold event_preimage in *.
    simpl in H.
    apply (H (fun x => x <= r)%R).
    apply generated_sa_sub.
    exists r; intuition.
Qed.

  Lemma equiv_le_lt (f : Ts -> R) (r:R) :
    event_equiv (fun omega : Ts => f omega < r)
                (union_of_collection
                   (fun (n:nat) => (fun omega : Ts => f omega <= r - / (1 + INR n)))).
  Proof.
    unfold event_equiv, union_of_collection.
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

  Lemma sa_le_gt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega > r)).
  Proof. 
    intros.
    assert (event_equiv (fun omega : Ts => f omega > r)
                        (event_complement (fun omega : Ts => f omega <= r))).
    - intro x.
      unfold event_complement.
      split; intros; lra.
    - rewrite H0.
      now apply sa_complement.
  Qed.

  Lemma sa_le_ge (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => f omega >= r)
                        (event_complement (fun omega : Ts => f omega < r))).
    {
      intro x.
      unfold event_complement.
      split; intros; lra.
    }
      rewrite H0.
      apply sa_complement.
      rewrite equiv_le_lt.
      apply sa_countable_union.
      intros.
      apply H.
  Qed.

  Lemma sa_le_lt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega < r)).
  Proof. 
    intros.
    assert (event_equiv (fun omega : Ts => f omega < r)
                        (event_complement (fun omega : Ts => f omega >= r))).
    - intro x.
      unfold event_complement.
      split; intros; lra.
    - rewrite H0.
      apply sa_complement.
      now apply sa_le_ge.
  Qed.

  Lemma sa_closed_intervals (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (l r:R), sa_sigma (fun omega : Ts => l <= f omega <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => l <= f omega <= r) 
                        (event_inter (fun omega : Ts => l <= f omega) 
                                     (fun omega : Ts => f omega <= r))).
    now unfold event_equiv, event_inter.
    rewrite H0.
    apply sa_inter; trivial.
    assert (event_equiv (fun omega : Ts => l <= f omega)
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
    assert (event_equiv (fun omega : Ts => l < f omega < r) 
                        (event_inter (fun omega : Ts => l < f omega) 
                                     (fun omega : Ts => f omega < r))).
    now unfold event_equiv, event_inter.
    rewrite H0.
    apply sa_inter; trivial.
    assert (event_equiv (fun omega : Ts => l < f omega)
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
    assert (event_equiv (fun omega : Ts => f omega = pt)
                        (event_inter (fun omega : Ts => f omega <= pt)
                                     (fun omega : Ts => f omega >= pt))).
    - unfold event_equiv, event_inter; intros.
      intuition.
    - rewrite H0.
      apply sa_inter; trivial.
      now apply sa_le_ge.
  Qed.

  Require Import QArith.

  Definition Q_interval (l r : Q) (x:R) : Prop :=
    Qreals.Q2R l < x < Qreals.Q2R r.
  
  Axiom Q_dense :
    forall (l r : R),
    (l < r)%R -> (exists (m:Q), l < Qreals.Q2R m < r).

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
      (forall B: event R, open_set B -> sa_sigma (event_preimage f B)).
    Proof.
      unfold event_preimage; intros.
      generalize (Q_open_set B); intros.
      destruct H1.
      assert (event_equiv (fun omega : Ts => B (f omega))
                          (union_of_collection
                             (fun (n:nat) => 
                                let n12 := (@iso_b _ _ nat_pair_encoder) n in
                                let qint := Q_interval (iso_b (fst n12)) (iso_b (snd n12)) in
                                fun omega : Ts => (qint (f omega)) /\
                                                  (included qint B)))).
      - unfold event_equiv, union_of_collection; intros.
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
        
        
        Admitted.
      
    Lemma sa_open_set_le (f : Ts -> R) :
      (forall B: event R, open_set B -> sa_sigma (event_preimage f B)) ->
      (forall (r:R),  sa_sigma (fun omega : Ts => (f omega <= r)%R)).
    Proof.
      intros.
      assert (event_equiv (fun omega : Ts => (f omega <= r)%R)
                          (event_complement (fun omega : Ts => (f omega > r)%R))).
      - unfold event_equiv, event_complement.
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
      (forall B: event R, open_set B -> sa_sigma (event_preimage f B)) <->
      (forall (r:R),  sa_sigma (fun omega : Ts => (f omega <= r)%R)).
    Proof.
      split.
      apply sa_open_set_le.
      apply sa_le_open_set.
    Qed.

 End Borel.


(*
Definition included (D1 D2:R -> Prop) : Prop := forall x:R, D1 x -> D2 x.
Definition disc (x:R) (delta:posreal) (y:R) : Prop := Rabs (y - x) < delta.
Definition neighbourhood (V:R -> Prop) (x:R) : Prop :=
  exists delta : posreal, included (disc x delta) V.
Definition open_set (D:R -> Prop) : Prop :=
  forall x:R, D x -> neighbourhood D x.
*)
