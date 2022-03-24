Require Import QArith.
Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Export ConditionalExpectation.
Require Import RbarExpectation.

Require Import Event.
Require Import Almost DVector.
Require Import utils.Utils.
Require Import List.
Require Import PushNeg.
Require Import Reals.
Require Import Coquelicot.Rbar.

Require Import Martingale.

Set Bullet Behavior "Strict Subproofs". 

Section mct.
  Local Open Scope R.
  Local Existing Instance Rge_pre.
  Local Existing Instance Rbar_le_pre.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).
  
  Section doob_upcrossing_times.
    
    Context
      (M : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
      {rv:forall n, RandomVariable dom borel_sa (M n)}
      {isfe:forall n, IsFiniteExpectation prts (M n)}
      {adapt:IsAdapted borel_sa M sas}
      {filt:IsFiltration sas}
      {sub:IsSubAlgebras dom sas}
      {mart:IsMartingale prts Rle M sas}.
    
    Fixpoint upcrossing_times a b (n:nat) : Ts -> option nat
               := fun ts =>
                    match n with
                    | 0%nat => Some 0%nat
                    | 1%nat => hitting_time M (event_le _ id a) ts
                    | S m => match upcrossing_times a b m ts with
                            | None => None
                            | Some old => if Nat.even m
                                         then hitting_time_from M (S old) (event_le _ id a) ts
                                         else hitting_time_from M (S old) (event_ge _ id b) ts
                                                   
                            end
                    end.

    Lemma upcrossing_times_is_stop a b n : IsStoppingTime (upcrossing_times a b n) sas.
    Proof.
      destruct n; simpl.
      - apply is_stopping_time_constant.
      - induction n; simpl.
        + now apply hitting_time_is_stop.
        + apply is_stopping_time_compose_incr; trivial.
          * intros.
            match_destr; apply hitting_time_from_is_stop; trivial.
          * intros.
            match_destr_in H
            ; eapply hitting_time_from_ge in H; eauto; lia.
    Qed.

    (* sup {k | upcrossing_times a b (2*k) <= n} *)
    (* Since upcrossing_times is increasing, 
       and returns an integer, we only need to search the first n items 
       (actually less, but any upper bound works *)
 
    Definition upcrossing_var_expr a b n ts k
      := match upcrossing_times a b (2*k) ts with
         | None => 0%nat
         | Some upn => if le_dec upn n then k else 0%nat
         end.
    
    Definition upcrossing_var a b n (ts:Ts) : R
      := Rmax_list (map INR (map (upcrossing_var_expr a b n ts) (seq 0 (S n)))).
 
    Lemma upcrossing_times_gt a b k ts :
      match upcrossing_times a b (S k) ts with
      | Some n => (n >= k)%nat
      | _ => True
      end.
    Proof.
      induction k.
      - simpl.
        match_destr.
        lia.
      - replace (S k) with (k + 1)%nat in * by lia.
        simpl.
        match_case; intros.
        match_case_in H; intros; try lia.
        rewrite H0 in H.
        rewrite H0 in IHk.
        match_case_in IHk; intros; rewrite H1 in IHk; rewrite H1 in H; try congruence.
        unfold hitting_time_from in H.
        match_destr_in H; match_destr_in H; invcs H; lia.
    Qed.

    Lemma upcrossing_var_expr_gt a b n (ts:Ts):
      forall k,
        (k > n)%nat -> 
        upcrossing_var_expr a b n ts k = 0%nat.
    Proof.
      intros.
      unfold upcrossing_var_expr.
      match_case; intros.
      match_destr.
      destruct k; try lia.
      replace (2 * S k)%nat with (S (S (2 * k))) in H0 by lia.
      generalize (upcrossing_times_gt a b (S (2 * k)) ts); intros.
      rewrite H0 in H1.
      lia.
    Qed.
        

    Global Instance upcrossing_var_nneg a b n : NonnegativeFunction (upcrossing_var a b n).
    Proof.
      unfold upcrossing_var; intros ?.
      destruct n; simpl; try reflexivity.
      match_destr
      ; apply Rmax_l.
    Qed.

    Lemma upcrossing_var_is_nat a b n ts :
      { x | INR x = upcrossing_var a b n ts}.
    Proof.
      unfold upcrossing_var.
      generalize (map (upcrossing_var_expr a b n ts) (seq 0 (S n))); intros.
      induction l; simpl.
      - exists 0%nat; trivial.
      - destruct IHl as [? eqq].
        match_destr; [eauto|].
        rewrite <- eqq.
        unfold Rmax.
        match_destr; eauto.
    Qed.

    Definition upcrossing_var_nat a b n ts : nat
      := proj1_sig (upcrossing_var_is_nat a b n ts).

(*    Lemma upcrossing_var_times_le a b n :
      forall ts, upcrossing_times a b (2 * (upcrossing_var_nat a b n ts)) <= n.
*)

    Definition upcrossing_bound a b m : Ts -> R
      := EventIndicator 
           (classic_dec
              (pre_union_of_collection
                 (fun k x => (match upcrossing_times a b (2 * k - 1) x with
                                 | Some x => (x < m)%nat
                                 | None => False
                                  end /\
                                   match upcrossing_times a b (2 * k) x with
                                   | Some x => (m <= x)%nat
                                   | None => True
                                   end)))).
            
    Lemma upcrossing_bound_is_predictable a b :
      is_predictable (upcrossing_bound a b) sas.
    Proof.
      intros m.
      unfold upcrossing_bound.
      apply EventIndicator_pre_rv.
      apply sa_countable_union; intros n.
      apply sa_inter.
      +
        apply (sa_proper _
                         (fun x =>
                            exists y, (upcrossing_times a b (2 * n - 1) x) = Some y /\
                                   y <= m)%nat).
        * intros ?.
          { split.
            - intros [? [eqq ?]].
              rewrite eqq; simpl.
              lia.
            - destruct (upcrossing_times a b (2 * n - 1) x); simpl; intros HH.
              + eexists; split; [reflexivity | ]; lia.
              + tauto.
          } 
        * apply sa_countable_union; intros.
          {
            destruct (le_dec n0 m)%nat.
            - apply sa_inter.
              + generalize (upcrossing_times_is_stop a b (2 * n - 1) n0); unfold IsStoppingTime, stopping_time_pre_event.
                eapply is_filtration_le; trivial.
              + apply sa_sigma_const; eauto.
            - eapply sa_proper; try eapply sa_none.
              intros ?.
              split; intros; tauto.
          } 
      + apply (sa_proper _
                         (pre_event_complement
                            (fun x =>
                               exists y, (upcrossing_times a b (2 * n) x) = Some y /\
                                      y <= m)%nat)).
        * intros ?.
          { unfold pre_event_complement.
            split.
            - match_destr.
              intros HH.
              destruct (le_dec (S m) n0)%nat; trivial.
              elim HH.
              eexists; split; [reflexivity |].
              lia.
            - destruct (upcrossing_times a b (2 * n) x); simpl; intros HH.
              + intros [? [??]].
                invcs H.
                lia.
              + intros [? [??]]; congruence.
          } 
        *
          apply sa_complement.
          apply sa_countable_union; intros.
          {
            destruct (le_dec n0 m)%nat.
            - apply sa_inter.
              + generalize (upcrossing_times_is_stop a b (2 * n) n0); unfold IsStoppingTime, stopping_time_pre_event.
                eapply is_filtration_le; trivial.
              + apply sa_sigma_const; lia.
            - eapply sa_proper; try eapply sa_none.
              intros ?.
              split; intros; try tauto.
          } 
    Qed.


    Global Instance upcrossing_bound_rv a b n :
      RandomVariable dom borel_sa (upcrossing_bound a b n).
    Proof.
      destruct n.
      - unfold upcrossing_bound; simpl.
        apply EventIndicator_pre_rv.
        apply sa_countable_union; intros.
        apply sa_inter.
        + eapply sa_proper; try apply sa_none.
          intros ?; split; unfold pre_event_none; try tauto.
          match_destr; lia.
        + eapply sa_proper; try apply sa_all.
          intros ?; split; unfold pre_Ω; try tauto.
          match_destr; lia.
      - generalize (upcrossing_bound_is_predictable a b n).
        apply RandomVariable_proper_le; try reflexivity.
        apply sub.
    Qed.      

    Lemma plus_self_even x : Nat.even (x + x)%nat = true.
    Proof.
      induction x; simpl; trivial.
      destruct x; simpl; trivial.
      rewrite <- IHx.
      f_equal.
      lia.
    Qed.

    Lemma plus_self_and_one_odd x : Nat.even (x + S x)%nat = false.
    Proof.
      replace (x + S x)%nat with (S (x + x))%nat by lia.
      rewrite Nat.even_succ.
      rewrite <- NPeano.Nat.negb_even.
      now rewrite plus_self_even.
    Qed.

    Lemma upcrossing_times_even_ge_some a b k0 a0 :
      match upcrossing_times a b (2 * S k0) a0 with
      | Some x => M x a0 >= b
      | None => True
      end.
    Proof.
      intros.
      induction k0.
      - match_case; intros.
        + replace (2 * 1)%nat with (2)%nat in H by lia.
          simpl in H.
          match_case_in H; intros; rewrite H0 in H; try congruence.
          unfold hitting_time_from in H.
          match_case_in H; intros; rewrite H1 in H; try congruence.
          invcs H.
          unfold hitting_time in H1.
          apply classic_min_of_some in H1.
          simpl in H1.
          now unfold id in H1.
      - match_case; intros; simpl in H; match_case_in H; intros;rewrite H0 in H; try congruence.
        + match_case_in H; intros.
          * match_case_in H1; intros; try lia.
            rewrite H2 in H1.
            replace (k0 + S (S (k0 + 0)))%nat with (S (S (2 * k0)))%nat in H2 by lia.
            invcs H2.
            replace (k0 + (k0 + 0))%nat with (k0 + k0)%nat in H1 by lia.
            rewrite Nat.even_succ in H1.
            unfold Nat.odd in H1.
            generalize (plus_self_even k0); intros.
            now rewrite H2 in H1.
          * rewrite H1 in H.
            unfold hitting_time_from in H.
            match_case_in H; intros; rewrite H2 in H; try congruence.
            invcs H.
            unfold hitting_time in H2.
            apply classic_min_of_some in H2.
            simpl in H2.
            now unfold id in H2.
    Qed.

    Lemma upcrossing_times_odd_le_some a b k0 a0 :
      match upcrossing_times a b (2 * S k0 - 1) a0 with
      | Some x => M x a0 <= a
      | None => True
      end.
    Proof.
      intros.
      induction k0.
      - match_case; intros.
        + replace (2 * 1)%nat with (2)%nat in H by lia.
          simpl in H.
          unfold hitting_time in H.
          apply classic_min_of_some in H.
          simpl in H.
          now unfold id in H.
      - match_case; intros; simpl in H; match_case_in H; intros;rewrite H0 in H; try congruence.
        + unfold hitting_time in H.
          apply classic_min_of_some in H.
          simpl in H.
          now unfold id in H.
        + replace  (k0 + S (S (k0 + 0)))%nat with ((S k0) + (S k0))%nat in H0 by lia.
          match_case_in H; intros; rewrite H1 in H; try congruence.
          rewrite <- H0 in H.
          generalize (plus_self_even (S k0)); intros.
          rewrite H2 in H.
          unfold hitting_time_from in H.
          match_case_in H; intros; rewrite H3 in H; try congruence.
          invcs H.
          unfold hitting_time in H3.
          apply classic_min_of_some in H3.
          simpl in H3.
          now unfold id in H3.
    Qed.

    Lemma upcrossing_times_even_ge a b k0 a0 n :
      (upcrossing_var_expr a b (S n) a0 (S k0) > 0)%nat ->
      match upcrossing_times a b (2 * S k0) a0 with
      | Some x => M x a0 >= b
      | None => False
      end.
    Proof.
      intros.
      generalize (upcrossing_times_even_ge_some a b k0 a0); intros.
      match_case; intros.
      - now rewrite H1 in H0.
      - unfold upcrossing_var_expr in H.
        match_case_in H; intros; rewrite H1 in H; lia.
    Qed.
    
    Lemma upcrossing_times_none a b k a0 :
      upcrossing_times a b k a0 = None ->
      upcrossing_times a b (S k) a0 = None.
    Proof.
      intros.
      simpl.
      rewrite H.
      match_destr; try lia.
    Qed.

    Lemma upcrossing_times_none_plus a b k h a0 :
      upcrossing_times a b k a0 = None ->
      upcrossing_times a b (S k + h)%nat a0 = None.
    Proof.
      intros.
      induction h.
      - replace (S k + 0)%nat with (S k) by lia.
        now apply upcrossing_times_none.
      - replace (S k + S h)%nat with (S (S k + h)) by lia.
        apply upcrossing_times_none; try lia; easy.
    Qed.

    Lemma upcrossing_times_none_plus_alt a b k kk a0 :
      (k < kk)%nat ->
      upcrossing_times a b k a0 = None ->
      upcrossing_times a b kk a0 = None.
    Proof.
      intros.
      pose (h := (kk - k - 1)%nat).
      generalize (upcrossing_times_none_plus a b k h a0 H0); intros.
      subst h.
      now replace (S k + (kk - k - 1))%nat with kk in H1 by lia.
    Qed.

    Lemma upcrossing_times_some a b k a0 n0 n1:
      (k > 0)%nat ->
      upcrossing_times a b k a0 = Some n0 ->
      upcrossing_times a b (S k) a0 = Some n1 ->
      (n0 < n1)%nat.
    Proof.
      intros.
      simpl in *.
      destruct k; try lia.
      rewrite H0 in H1.
      match_destr_in H1; unfold hitting_time_from in H1;
        match_destr_in H1; invcs H1; lia.
    Qed.

    Lemma upcrossing_times_some_plus a b k a0 n0 h:
      (k > 0)%nat ->
      upcrossing_times a b k a0 = Some n0 ->
      match upcrossing_times a b (S k + h)%nat a0 with
      | Some n1 => (n0 < n1)%nat
      | _ => True
      end.
    Proof.
      intros.
      induction h.
      - replace (S k + 0)%nat with (S k) by lia.
        match_case; intros.
        apply (upcrossing_times_some a b k a0); trivial.
      - replace (S k + S h)%nat with (S (S k + h)) by lia.
        match_case; intros.
        match_case_in IHh; intros.
        + rewrite H2 in IHh.
          eapply lt_trans.
          apply IHh.
          apply upcrossing_times_some with (n0 := n1) in H1; trivial; try lia.
        + apply  upcrossing_times_none in H2; try lia.
          congruence.
    Qed.                                                  

    Lemma upcrossing_times_some_plus_alt a b k a0 n0 kk:
      (k > 0)%nat ->
      (k < kk)%nat ->
      upcrossing_times a b k a0 = Some n0 ->
      match upcrossing_times a b kk a0 with
      | Some n1 => (n0 < n1)%nat
      | _ => True
      end.
    Proof.
      intros.
      generalize (upcrossing_times_some_plus a b k a0 n0 (kk - k - 1)%nat H H1); intros.
      now replace (S k + (kk - k - 1))%nat with kk in H2 by lia.
    Qed.

    Lemma upcrossing_times_some_S a b k a0 n0:
      upcrossing_times a b (S k) a0 = Some n0 ->
      exists n1,
        upcrossing_times a b k a0 = Some n1.
    Proof.
      intros.
      simpl in H.
      match_destr_in H.
      - simpl; eauto.
      - match_destr_in H.
        now exists n.
    Qed.

    Lemma upcrossing_times_some2 a b k a0 n0 n1:
      upcrossing_times a b k a0 = Some n0 ->
      upcrossing_times a b (S (S k)) a0 = Some n1 ->
      (n0 < n1)%nat.
    Proof.
      intros.
      destruct (upcrossing_times_some_S a b (S k) a0 n1 H0); intros.
      destruct (lt_dec 0 k).
      - generalize (upcrossing_times_some a b k a0 n0 x l H H1); intros.
        generalize (upcrossing_times_some a b (S k) a0 x n1); intros.
        cut_to H3; try lia; trivial.
      - destruct k; try lia.
        simpl in *.
        rewrite H1 in H0.
        invcs H.
        generalize (hitting_time_from_ge _ _ _ _ _ _ H0).
        lia.
    Qed.

    Lemma upcrossing_times_odd_le a b k0 a0 n :
      (upcrossing_var_expr a b (S n) a0 (S k0) > 0)%nat ->
      match upcrossing_times a b (2 * S k0 - 1) a0 with
      | Some x => M x a0 <= a
      | None => False
      end.
    Proof.
      intros.
      generalize (upcrossing_times_odd_le_some a b k0 a0); intros.      
      match_case; intros.
      - now rewrite H1 in H0.
      - unfold upcrossing_var_expr in H.
        match_case_in H; intros; rewrite H2 in H; try lia.
        apply upcrossing_times_none in H1; try lia.
        replace (S (2 * S k0 - 1)) with (2 * S k0)%nat in H1 by lia.
        congruence.
    Qed.

    Lemma upcrossing_var_expr_0 a b n a0 k :
      (0 < k)%nat ->
      (upcrossing_var_expr a b (S n) a0 k = 0)%nat ->
      (upcrossing_var_expr a b (S n) a0 (S k) = 0)%nat.
    Proof.
      intros.
      unfold upcrossing_var_expr in *.
      match_case_in H0; intros; rewrite H1 in H0.
      - match_case_in H0; intros; rewrite H2 in H0; try lia.
        assert (n0 > S n)%nat by lia.
        match_case; intros.
        generalize (upcrossing_times_some2 a b (2 * k)%nat a0 n0 n2); intros.
        replace (S (S (2 * k))) with (2 * S k)%nat in H5 by lia.
        cut_to H5; try lia; trivial.
        match_destr; try lra; try lia.
      - generalize (upcrossing_times_none a b (2 * k)%nat a0); intros.
        cut_to H2; try lia; trivial.
        generalize (upcrossing_times_none a b (S (2 * k)) a0); intros.
        cut_to H3; try lia; trivial.
        replace (2 * S k)%nat with (S (S (2 * k))) by lia.
        now rewrite H3.
   Qed.

    Lemma upcrossing_var_expr_gt0 a b n a0 k :
      (upcrossing_var_expr a b (S n) a0 (S k) > 0)%nat ->
      forall h,
        (S h <= S k)%nat ->
        (upcrossing_var_expr a b (S n) a0 (S h) > 0)%nat.
    Proof.
      intros.
      case_eq (upcrossing_var_expr a b (S n) a0 (S h)); intros; try lia.
      assert (forall hh, (upcrossing_var_expr a b (S n) a0 ((S h)+hh)%nat = 0)%nat).
      {
        intros; induction hh.
        - now replace (S h + 0)%nat with (S h) by lia.
        - replace (S h + S hh)%nat with (S (S h + hh)) by lia.
          apply upcrossing_var_expr_0; try lia.
      }
      specialize (H2 (S k - S h)%nat).
      replace (S h + (S k - S h))%nat with (S k) in H2 by lia.
      lia.
    Qed.

    Lemma upcrossing_bound_range a b a0 k :
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        forall n, (N1 < n <= N2)%nat ->
                  upcrossing_bound a b n a0 = 1
      | _, _ => True
      end.
     Proof.
       match_case; intros.
       match_case; intros.       
       unfold upcrossing_bound.
       unfold EventIndicator.
       match_destr.
       unfold pre_union_of_collection in n2.
       elim n2.
       exists k.
       rewrite H.
       split; try lia.
       rewrite H0; try lia.
     Qed.

    Lemma upcrossing_bound_range_none a b a0 k :
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, None =>
        forall n, (N1 < n)%nat ->
                  upcrossing_bound a b n a0 = 1
      | _, _ => True
      end.
     Proof.
       match_case; intros.
       match_case; intros.       
       unfold upcrossing_bound.
       unfold EventIndicator.
       match_destr.
       unfold pre_union_of_collection in n1.
       elim n1.
       exists k.
       rewrite H.
       split; try lia.
       rewrite H0; try lia.
     Qed.

    Lemma upcrossing_bound_range_full a b a0 k :
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        forall n, (N1 < n <= N2)%nat ->
                  upcrossing_bound a b n a0 = 1
      | Some N1, None =>
        forall n, (N1 < n)%nat ->
                  upcrossing_bound a b n a0 = 1
      | _, _ => True
      end.
     Proof.
       generalize (upcrossing_bound_range a b a0 k); intros.
       generalize (upcrossing_bound_range_none a b a0 k); intros.       
       match_case; intros.
       match_case; intros.
       - rewrite H1, H2 in H.
         now apply H.
       - rewrite H1, H2 in H0.
         now apply H0.
    Qed.

     Lemma upcrossing_times_monotonic_l a b a0 n0 n1 m0 m1 :
       (m0 > 0)%nat ->
       upcrossing_times a b m0 a0 = Some n0 ->
       upcrossing_times a b m1 a0 = Some n1 ->
       (m0 < m1)%nat -> (n0 < n1)%nat.
     Proof.
       intros.
       generalize (upcrossing_times_some_plus a b m0 a0 n0 (m1-m0-1) H H0); intros.
       match_case_in H3; intros; rewrite H4 in H3.
       - replace (S m0 + (m1 - m0 - 1))%nat with (m1) in H4 by lia.
         rewrite H4 in H1.
         now invcs H1.
      - replace (S m0 + (m1 - m0 - 1))%nat with (m1) in H4 by lia.
        congruence.
     Qed.

     Lemma upcrossing_times_monotonic a b a0 n0 n1 m0 m1 :
       (m0 > 0)%nat -> (m1 > 0)%nat ->
       upcrossing_times a b m0 a0 = Some n0 ->
       upcrossing_times a b m1 a0 = Some n1 ->
       (m0 < m1)%nat <-> (n0 < n1)%nat.
     Proof.
       intros.
       split.
       - now apply (upcrossing_times_monotonic_l a b a0).
       - contrapose.
         intros.
         assert (m1 <= m0)%nat by lia.
         destruct (lt_dec m1 m0).
         + generalize (upcrossing_times_monotonic_l a b a0 n1 n0 m1 m0 ); intros.
           cut_to H5; trivial.
           lia.
         + assert (m1 = m0)%nat by lia.
           rewrite H5 in H2.
           rewrite H2 in H1.
           invcs H1.
           lia.
    Qed.

    Lemma upcrossing_bound_range0 a b a0 k :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k) a0, upcrossing_times a b (2 * k + 1) a0 with 
      | Some N2, Some N1 =>
        forall n, (n > N2)%nat /\ (n <= N1)%nat ->
                  upcrossing_bound a b n a0 = 0
      | Some N2, None =>
        forall n, (n > N2)%nat ->
                  upcrossing_bound a b n a0 = 0                                                
      | _, _ => True
      end.
    Proof.
      intros.
      unfold upcrossing_bound, EventIndicator.
      match_case; intros.
      match_case; intros.
      - match_destr.
        destruct p as [? [? ?]].
        destruct x.
        {
          replace (2 * 0 - 1)%nat with (0%nat) in H3 by lia.
          replace (2 * 0)%nat with (0%nat) in H4 by lia.
          simpl in H3.
          simpl in H4.
          lia.
        }
        destruct H2.
        match_case_in H3; intros; rewrite H6 in H3; try easy.
        assert (n2 < n0)%nat by lia.
        assert (2 * S x - 1 < 2 * k + 1)%nat.
        {
          generalize (upcrossing_times_monotonic a b a0 n2 n0); intros; trivial; try lia.
          specialize (H8 (2 * S x - 1)%nat (2 * k + 1)%nat).
          apply H8; trivial; try lia.
        }
        match_case_in H4; intros; rewrite H9 in H4.
        + assert (n < n3)%nat by lia.
          assert (2 * k < 2 * S x)%nat.
          {
            generalize (upcrossing_times_monotonic a b a0 n n3); intros; trivial; try lia.
            specialize (H11 (2 * k)%nat (2 * S x)%nat).
            apply H11; trivial; try lia.
          }
          lia.
        + assert (2 * S x < 2 * k + 1)%nat by lia.
          apply upcrossing_times_none_plus_alt with (kk := (2 * k + 1)%nat) in H9; try lia.
          congruence.
     - match_destr.
       destruct p as [? [? ?]].
       destruct x.
       {
         replace (2 * 0 - 1)%nat with (0%nat) in H3 by lia.
         replace (2 * 0)%nat with (0%nat) in H4 by lia.
         simpl in H3.
         simpl in H4.
         lia.
       }
       match_case_in H3; intros; rewrite H5 in H3; try easy.
       match_case_in H4; intros; rewrite H6 in H4.
       + assert (n < n2)%nat by lia.
         assert (2 * k < 2 * S x)%nat.
         {
           generalize (upcrossing_times_monotonic a b a0 n n2); intros.
           specialize (H8 (2 * k)%nat (2 * S x)%nat).
           apply H8; trivial; try lia.
         }
         assert (2 * k + 1 < 2*S x)%nat by lia.
         apply upcrossing_times_none_plus_alt with (kk := (2 * S x)%nat) in H1; try lia.
         congruence.         
       + destruct (lt_dec (2 * S x)%nat (2 *  k)%nat).
         * apply upcrossing_times_none_plus_alt with (kk := (2 * k)%nat) in H6; try lia.
           congruence.
         * destruct (lt_dec (2 * k)%nat (2 * S x)%nat).
           -- assert (2 * k + 1 <= 2 * S x - 1)%nat by lia.
              destruct (lt_dec (2 * k + 1)%nat (2 * S x - 1)%nat).
              ++ apply upcrossing_times_none_plus_alt with (kk := (2 * S x - 1)%nat) in H1; try lia.
                 congruence.                 
              ++ assert ( 2 * k + 1 = 2  * S x - 1)%nat by lia.
                 rewrite H8 in H1; congruence.
           -- assert (2 * S x = 2 * k)%nat by lia.
              rewrite H7 in H6; congruence.
     Qed.

    Lemma upcrossing_bound_range0_init a b a0 :
      match upcrossing_times a b (1%nat) a0 with
      | Some N1 =>
        forall n, (n <= N1)%nat ->
                  upcrossing_bound a b n a0 = 0
      | None =>
        forall n, upcrossing_bound a b n a0 = 0                                                
      end.
    Proof.
      match_case; intros.
      - unfold upcrossing_bound, EventIndicator.
        match_destr.
        destruct p as [? [? ?]].
        destruct x.
        {
          replace (2 * 0 - 1)%nat with (0%nat) in H1 by lia.
          replace (2 * 0)%nat with (0%nat) in H2 by lia.
          simpl in H1.
          simpl in H2.
          lia.
        }
        match_case_in H1; intros; rewrite H3 in H1; try easy.
        match_case_in H2; intros; rewrite H4 in H2.
        + assert (n1 < n)%nat by lia.
          assert (2 * S x - 1 < 1)%nat.
          {
            generalize (upcrossing_times_monotonic a b a0 n1 n); intros.
            specialize (H6 (2 * S x - 1)%nat 1%nat).
            apply H6; trivial; try lia.
          }
          lia.
        + assert (n1 < n)%nat by lia.
          assert (2 * S x - 1 < 1)%nat.
          {
             generalize (upcrossing_times_monotonic a b a0 n1 n); intros.
             specialize (H6 (2 * S x - 1)%nat 1%nat).
             apply H6; trivial; try lia.
          }
          lia.
     -  unfold upcrossing_bound, EventIndicator.
        match_destr.
        destruct p as [? [? ?]].
        match_case_in H0; intros; rewrite H2 in H0; try easy.
        match_case_in H1; intros; rewrite H3 in H1.
        + destruct x.
          * replace (2 * 0 - 1)%nat with (0%nat) in H2 by lia.
            replace (2 * 0)%nat with (0%nat) in H3 by lia.
            rewrite H3 in H2.
            assert (n0 < n1)%nat by lia.
            invcs H2.
            lia.
          * apply upcrossing_times_none_plus_alt with (kk := (2 * S x)%nat) in H; try lia.
            congruence.
        + destruct x.
          * replace (2 * 0)%nat with (0%nat) in H3 by lia.
            replace (2 * 0 - 1)%nat with (0%nat) in H2 by lia.
            congruence.
          * destruct x.
            -- replace (2 * 1 - 1)%nat with (1)%nat in H2 by lia.
               congruence.
            -- apply upcrossing_times_none_plus_alt with (kk := (2 * S (S x) - 1)%nat) in H; try lia.
               congruence.
    Qed.

    Lemma upcrossing_times_some_none a b k k2 a0 :
      upcrossing_times a b k a0 = None ->
      upcrossing_times a b k2 a0 <> None ->
      (k2 < k)%nat.
    Proof.
      intros.
      destruct (le_dec k k2); try lia.
      destruct (lt_dec k k2).
      - now apply (upcrossing_times_none_plus_alt a b k k2 a0) in H; try lia.
      - assert (k = k2) by lia.
        now rewrite H1 in H.
    Qed.

    Lemma upcrossing_bound_range10 a b a0 n k :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k) a0, upcrossing_times a b (2 * k + 1) a0 with 
      | Some N2, Some N1 =>
        (n > N2)%nat /\ (n <= N1)%nat
      | _, _ => False
      end -> upcrossing_bound a b n a0 = 0.
     Proof.
       intros kpos ?.
       unfold upcrossing_bound, EventIndicator.
       generalize (upcrossing_times_monotonic a b a0); intros.
       match_destr.
       unfold pre_union_of_collection in p.
       destruct p as [? [? ?]].
       destruct x.
       {
         replace (2 * 0 - 1)%nat with 0%nat in H1 by lia.
         replace (2 * 0)%nat with 0%nat in H2 by lia.
         match_case_in H1; intros.
         rewrite H3 in H1.
         rewrite H3 in H2.
         lia.
        }
       match_case_in H1; intros; rewrite H3 in H1; try easy.
       match_case_in H2; intros; rewrite H4 in H2.
       - match_case_in H; intros; rewrite H5 in H; try easy.
         match_case_in H; intros; rewrite H6 in H; try easy.
         destruct H.
         destruct (lt_dec (S x) k).
         + assert (n1 < n2)%nat.
           {
             specialize (H0 n1 n2 (2 * S x)%nat (2 * k)%nat).
             cut_to H0; try lia; trivial.
           }
           lia.
         + destruct (lt_dec k (S x)).
           * assert (2 * k + 1 <= 2 * S x - 1)%nat by lia.
             assert (n3 <= n0)%nat.
             {
               destruct (lt_dec (2 * k + 1)%nat (2 * S x - 1)%nat).
               - specialize (H0 n3 n0 (2 * k + 1)%nat (2 * S x - 1)%nat).
                 cut_to H0; try lia; trivial.
               - assert (2 * k + 1 = 2 * S x - 1)%nat by lia.
                 rewrite H9 in H6.
                 rewrite H6 in H3.
                 invcs H3.
                 lia.
             }
             lia.
           * assert (k = S x) by lia.
             assert (n1 = n2).
             {
               rewrite H8 in H5.
               rewrite H5 in H4.
               now invcs H4.
             }
             lia.
       - match_case_in H; intros; rewrite H5 in H; try easy.
         assert (2 * S x > 2 * k)%nat.
         {
           assert (upcrossing_times a b (2 * k)%nat a0 <> None) by congruence.
           generalize (upcrossing_times_some_none a b _ _ _ H4 H6); intros; try lia.               
         }
         assert (2 * S x - 1 >= 2 * k + 1)%nat by lia.
         match_case_in H; intros; rewrite H8 in H.
         + assert (n2 <= n0)%nat.
           {
             destruct (lt_dec (2 * k + 1)%nat (2 * S x - 1)%nat).
             - specialize (H0 n2 n0 (2 * k + 1)%nat (2 * S x - 1)%nat).
               cut_to H0; try lia; trivial.
             - assert (2 * k + 1 = 2 * S x - 1)%nat by lia.
               rewrite H9 in H8.
               rewrite H8 in H3.
               now invcs H3.
           }
           lia.
         + destruct (lt_dec (2 * k + 1)%nat (2 * S x - 1)).
           * now apply upcrossing_times_none_plus_alt with (kk := (2*S x - 1)%nat) in H8.
           * assert (2 * k + 1 = 2 * S x - 1)%nat by lia.
             rewrite H9 in H8.
             congruence.
      Qed.

     Lemma upcrossing_times_0 a b a0 n1 n2 :
       (n1 < n2)%nat ->
       upcrossing_times a b (2 * 0 - 1) a0 = Some n1 ->
       upcrossing_times a b (2 * 0) a0 = Some n2 ->
       False.
     Proof.
       intros.
       replace (2 * 0 - 1)%nat with 0%nat in H0 by lia.
       replace (2 * 0)%nat with 0%nat in H1 by lia.
       rewrite H1 in H0.
       invcs H1.
       lia.       
     Qed.
     
     Lemma upcrossing_bound_range10_none a b a0 n k :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k) a0, upcrossing_times a b (2 * k + 1) a0 with 
      | Some N2, None =>
        (n > N2)%nat
      | _, _ => False
      end -> upcrossing_bound a b n a0 = 0.
    Proof.
      intros.
      match_case_in H0; intros; rewrite H1 in H0; try easy.
      match_case_in H0; intros; rewrite H2 in H0; try easy.
      unfold upcrossing_bound.
      unfold EventIndicator, pre_union_of_collection.
      match_destr.
      destruct e as [? [? ?]].
      generalize (upcrossing_times_monotonic a b a0); intros.
      match_case_in H3; intros; rewrite H6 in H3; try easy.
      match_case_in H4; intros; rewrite H7 in H4.
      - destruct x.
        {
          generalize (upcrossing_times_0 a b a0 n1 n2); intros.
          cut_to H8; trivial; try lia.
        }
        destruct (lt_dec (S x) k).
        + assert (n2 < n0)%nat.
          {
            specialize (H5 n2 n0 (2 * S x)%nat (2 * k)%nat).
            cut_to H5; try lia; trivial.
          }
          lia.
        + destruct (lt_dec k (S x)).
          * assert (2 * k + 1 < 2 * S x)%nat by lia.
             apply (upcrossing_times_none_plus_alt a b (2 * k + 1)%nat (2 * S x)%nat a0) in H2; try lia.
             congruence.
          * assert (k = S x)%nat by lia.
             rewrite H8 in H1.
             rewrite H7 in H1.
             invcs H1.
             lia.
      - destruct x.
        {
          replace (2 * 0 - 1)%nat with 0%nat in H6 by lia.
          replace (2 * 0)%nat with 0%nat in H7 by lia.
          congruence.
        }
        destruct (lt_dec (S x) k).
        + apply (upcrossing_times_none_plus_alt a b (2 * S x)%nat (2 * k)%nat a0) in H7; try lia.
          congruence.
        + destruct (lt_dec k (S x)).
          * assert (2 * k +1 <= 2 * S x - 1)%nat by lia.
            assert (upcrossing_times a b (2 * S x - 1)%nat a0 = None).
            {
              destruct (lt_dec (2 * k + 1)%nat (2 * S x - 1)%nat).
              - now apply (upcrossing_times_none_plus_alt a b (2 * k + 1)%nat (2 * S x - 1)%nat a0) in H2; try lia.
              - now replace (2 * k + 1)%nat with (2 * S x - 1)%nat in H2 by lia.
            }
            congruence.
          * assert (k = S x)%nat by lia.
            rewrite H8 in H1.
            rewrite H7 in H1.
            invcs H1.
    Qed.

    Lemma upcrossing_bound_range10_full a b a0 n k :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k) a0, upcrossing_times a b (2 * k + 1) a0 with 
      | Some N2, Some N1 =>
        (n > N2)%nat /\ (n <= N1)%nat
      | Some N2, None =>
        (n > N2)%nat
      | _, _ => False
      end -> upcrossing_bound a b n a0 = 0.
    Proof.
      intros.
      generalize (upcrossing_bound_range10 a b a0 n k H); intros.
      generalize (upcrossing_bound_range10_none a b a0 n k H); intros.      
      match_case_in H0; intros; rewrite H3 in H0; rewrite H3 in H1; rewrite H3 in H2; try easy.
      match_case_in H1; intros;rewrite H4 in H0; rewrite H4 in H1; rewrite H4 in H2.
      - now apply H1.
      - now apply H2.
    Qed.

     Lemma telescope_sum (f : nat -> R) n h :
       @Hierarchy.sum_n_m 
         Hierarchy.R_AbelianGroup
         (fun n1 : nat => f (S n1) + -1 * f n1) n (n + h)%nat = f (n + (S h))%nat - f n.
     Proof.
       induction h.
       - replace (n + 0)%nat with (n) by lia.
         rewrite Hierarchy.sum_n_n.
         replace (n + 1)%nat with (S n) by lia.
         lra.
       - replace (n + S h)%nat with (S (n + h)) by lia.
         rewrite Hierarchy.sum_n_Sm; try lia.
         rewrite IHh.
         unfold Hierarchy.plus; simpl.
         replace (S (n + h)) with (n + S h)%nat by lia.
         replace (S (n + S h)) with (n + S (S h))%nat by lia.
         lra.
      Qed.
         
    Lemma transform_upcrossing a b a0 k :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N2-1)%nat = M N2 a0 - M N1 a0
      | _, _ => True
      end.
    Proof.
      intros.
       match_case; intros.
       match_case; intros.
       assert (up: (n < n0)%nat).
       {
         apply (upcrossing_times_some a b (2 * k - 1) a0); try lia; trivial.
         now replace (S (2 * k - 1)) with (2 * k)%nat by lia.
       }
       rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
           (b := fun n1 => M (S n1) a0 + -1 * M n1 a0).
       - pose (h := (n0 - 1 - n)%nat).
         replace (n0-1)%nat with (n + h)%nat by lia.
         rewrite (telescope_sum (fun n => M n a0)).
         now replace (n + S h)%nat with n0 by lia.
       - intros.
         generalize (upcrossing_bound_range a b a0 k); intros.
         rewrite H0, H1 in H3.
         specialize (H3 (S k0)).
         rewrite H3; try lra; try lia.
     Qed.
      
    Lemma transform_upcrossing2 a b a0 k N3 :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        (N1 < N3 <= N2)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N3-1)%nat = M N3 a0 - M N1 a0
      | _, _ => True
      end.
    Proof.
      intros.
       match_case; intros.
       match_case; intros.
       assert (up: (n < n0)%nat).
       {
         apply (upcrossing_times_some a b (2 * k - 1) a0); try lia; trivial.
         now replace (S (2 * k - 1)) with (2 * k)%nat by lia.
       }
       rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
           (b := fun n1 => M (S n1) a0 + -1 * M n1 a0).
       - pose (h := (N3 - 1 - n)%nat).
         replace (N3-1)%nat with (n + h)%nat by lia.
         rewrite (telescope_sum (fun n => M n a0)).
         now replace (n + S h)%nat with N3 by lia.
       - intros.
         generalize (upcrossing_bound_range a b a0 k); intros.
         rewrite H0, H1 in H4.
         specialize (H4 (S k0)).
         rewrite H4; try lra; try lia.
     Qed.

    Lemma transform_upcrossing2_none a b a0 k N3 :
      (k > 0)%nat ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, None =>
        (N1 < N3)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N3-1)%nat = M N3 a0 - M N1 a0
      | _, _ => True
      end.
    Proof.
      intros.
       match_case; intros.
       match_case; intros.
       rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
           (b := fun n1 => M (S n1) a0 + -1 * M n1 a0).
       - pose (h := (N3 - 1 - n)%nat).
         replace (N3-1)%nat with (n + h)%nat by lia.
         rewrite (telescope_sum (fun n => M n a0)).
         now replace (n + S h)%nat with N3 by lia.
       - intros.
         generalize (upcrossing_bound_range_none a b a0 k); intros.
         rewrite H0, H1 in H4.
         specialize (H4 (S k0)).
         rewrite H4; try lra; try lia.
     Qed.

     Lemma transform_upcrossing_zero_01 a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k) a0,
            upcrossing_times a b (2 * k + 1) a0 with
      | Some NN0, Some N1 =>
        (NN0 < N3 <= N1)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1) = 0
      | _, _ => True
      end.
    Proof.
      intros.
      match_case; intros.
      match_case; intros.
      rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
          (b := fun n1 => Hierarchy.zero).
      - rewrite Hierarchy.sum_n_m_const_zero.
        unfold Hierarchy.zero; now simpl.
      - intros.
        generalize (upcrossing_bound_range10 a b a0 (S k0) k H); intros.
        rewrite H1, H2 in H5.
        rewrite H5.
        * unfold Hierarchy.zero; simpl; lra.
        * split; try lia.
    Qed.

     Lemma transform_upcrossing_zero_01_none a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k) a0,
            upcrossing_times a b (2 * k + 1) a0 with
      | Some NN0, None =>
        (NN0 < N3 )%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1)%nat = 0
      | _, _ => True
      end.
    Proof.
      intros.
      match_case; intros.
      match_case; intros.
      rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
          (b := fun n1 => Hierarchy.zero).
      - rewrite Hierarchy.sum_n_m_const_zero.
        unfold Hierarchy.zero; now simpl.
      - intros.
        generalize (upcrossing_bound_range10_none a b a0 (S k0) k H); intros.
        rewrite H1, H2 in H5.
        rewrite H5.
        * unfold Hierarchy.zero; simpl; lra.
        * try lia.
    Qed.

    Lemma transform_upcrossing_zero_01_full a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k) a0,
            upcrossing_times a b (2 * k + 1) a0 with
      | Some NN0, Some N1 =>
        (NN0 < N3 <= N1)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1)%nat = 0
      | Some NN0, None =>
        (NN0 < N3 )%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1)%nat = 0
      | _, _ => True
      end.
    Proof.
      intros.
      generalize (transform_upcrossing_zero_01 a b a0 k N3); intros.
      generalize (transform_upcrossing_zero_01_none a b a0 k N3); intros.      
      match_case; intros.
      match_case; intros.
      - rewrite H3, H4 in H1.
        apply H1; trivial; try lia.
      - rewrite H3, H4 in H2.
        apply H2; trivial; try lia.
    Qed.
     
    Lemma transform_upcrossing_pos a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, Some N2 =>
        (N1 < N3 <= N2)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N3-1)%nat >= 0
      | _, _ => True
      end.
    Proof.
      intros.
      generalize (transform_upcrossing2 a b a0 k N3 H); intros.
      match_case; intros.
      match_case; intros.
      rewrite H2, H3 in H1.
      rewrite H1; trivial.
      assert (M n a0 = a).
      {
        generalize (upcrossing_times_odd_le_some a b (k-1)%nat a0); intros.
        replace (S (k - 1)) with k in H5 by lia.
        rewrite H2 in H5.
        specialize (H0 n a0).
        lra.
      }
      specialize (H0 N3 a0); lra.
    Qed.

     Lemma transform_upcrossing_pos_01 a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k) a0,
            upcrossing_times a b (2 * k + 1) a0, 
            upcrossing_times a b (2 * (S k)) a0 with 
      | Some NN0, Some N1, Some N2 =>
        (N1 < N3 <= N2)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1)%nat >= 0
      | _, _, _ => True
      end.
    Proof.
      intros.
      match_case; intros.
      match_case; intros.
      match_case; intros.
      assert (n0pos : (n0 > 0)%nat).
      {
        generalize (upcrossing_times_monotonic a b a0 n n0 (2 * k)%nat (2 * k + 1)%nat); intros.
        cut_to H5; try lia; trivial.
      }
      rewrite Hierarchy.sum_n_m_Chasles with (m := (n0-1)%nat).
      - rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
            (b := fun n1 => Hierarchy.zero).
        + rewrite Hierarchy.sum_n_m_const_zero.
          rewrite Hierarchy.plus_zero_l.
          replace (S (n0 - 1)) with n0 by lia.
          generalize (transform_upcrossing_pos a b a0 (S k) N3); intros.
          cut_to H5; try lia; trivial.
          replace (2 * S k - 1)%nat with (2 * k + 1)%nat in H5 by lia.
          rewrite H2, H3 in H5.
          now apply H5.
        + intros.
          generalize (upcrossing_bound_range10 a b a0 (S k0) k H); intros.
          rewrite H1, H2 in H6.
          rewrite H6.
          * unfold Hierarchy.zero; simpl; lra.
          * split; try lia.
    - replace (S (n0 - 1)) with n0 by lia.
      generalize (upcrossing_times_monotonic a b a0 n n0 (2 * k)%nat (2 * k + 1)%nat); intros.
      cut_to H5; try lia; trivial.
    - lia.
   Qed.

    Lemma transform_upcrossing_pos_none a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k - 1) a0, upcrossing_times a b (2 * k) a0 with 
      | Some N1, None =>
        (N1 < N3)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          N1 (N3-1)%nat >= 0
      | _, _ => True
      end.
    Proof.
      intros.
      generalize (transform_upcrossing2_none a b a0 k N3 H); intros.
      match_case; intros.
      match_case; intros.
      rewrite H2, H3 in H1.
      rewrite H1; trivial.
      assert (M n a0 = a).
      {
        generalize (upcrossing_times_odd_le_some a b (k-1)%nat a0); intros.
        replace (S (k - 1)) with k in H5 by lia.
        rewrite H2 in H5.
        specialize (H0 n a0).
        lra.
      }
      specialize (H0 N3 a0); lra.
    Qed.

     Lemma transform_upcrossing_pos_01_none a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k) a0,
            upcrossing_times a b (2 * k + 1) a0, 
            upcrossing_times a b (2 * (S k)) a0 with 
      | Some NN0, Some N1, None =>
        (N1 < N3)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1)%nat >= 0
      | _, _, _ => True
      end.
    Proof.
      intros.
      match_case; intros.
      match_case; intros.
      match_case; intros.
      assert (n0pos : (n0 > 0)%nat).
      {
        generalize (upcrossing_times_monotonic a b a0 n n0 (2 * k)%nat (2 * k + 1)%nat); intros.
        cut_to H5; try lia; trivial.
      }
      rewrite Hierarchy.sum_n_m_Chasles with (m := (n0-1)%nat).
      - rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
            (b := fun n1 => Hierarchy.zero).
        + rewrite Hierarchy.sum_n_m_const_zero.
          rewrite Hierarchy.plus_zero_l.
          replace (S (n0 - 1)) with n0 by lia.
          generalize (transform_upcrossing_pos_none a b a0 (S k) N3); intros.
          cut_to H5; try lia; trivial.
          replace (2 * S k - 1)%nat with (2 * k + 1)%nat in H5 by lia.
          rewrite H2, H3 in H5.
          now apply H5.
        + intros.
          generalize (upcrossing_bound_range10 a b a0 (S k0) k H); intros.
          rewrite H1, H2 in H6.
          rewrite H6.
          * unfold Hierarchy.zero; simpl; lra.
          * split; try lia.
    - replace (S (n0 - 1)) with n0 by lia.
      generalize (upcrossing_times_monotonic a b a0 n n0 (2 * k)%nat (2 * k + 1)%nat); intros.
      cut_to H5; try lia; trivial.
    - lia.
    Qed.

    Lemma transform_upcrossing_pos_01_full a b a0 k N3 :
      (k > 0)%nat ->
      (forall m x, M m x >= a) ->
      match upcrossing_times a b (2 * k) a0,
            upcrossing_times a b (2 * k + 1) a0, 
            upcrossing_times a b (2 * (S k)) a0 with
      | Some NN0, Some N1, Some N2 =>
        (N1 < N3 <= N2)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1)%nat >= 0
      | Some NN0, Some N1, None =>
        (N1 < N3)%nat ->
        @Hierarchy.sum_n_m  
          Hierarchy.R_AbelianGroup
          (fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
          NN0 (N3-1)%nat >= 0
      | _, _, _ => True
      end.
    Proof.
      intros.
      generalize (transform_upcrossing_pos_01 a b a0 k N3 H H0); intros.
      generalize (transform_upcrossing_pos_01_none a b a0 k N3 H H0); intros.      
      match_case; intros.
      match_case; intros.
      match_case; intros.
      - rewrite H3, H4, H5 in H1.
        apply H1.
        lia.
      - rewrite H3, H4, H5 in H2.
        apply H2.
        lia.
   Qed.

    Lemma one_upcrossing_bound a b a0 (f : nat -> Ts -> R) N1 N2 :
      (N1 < N2) %nat ->
      upcrossing_times a b (1%nat) a0 = Some N1 ->
      upcrossing_times a b (2%nat) a0 = Some N2 ->
      @Hierarchy.sum_n 
        Hierarchy.R_AbelianGroup
        (fun n0 : nat => 
           upcrossing_bound a b n0 a0 * f n0 a0) N2 =
      @Hierarchy.sum_n_m 
        Hierarchy.R_AbelianGroup
        (fun n0 => f n0 a0) (S N1) N2.
    Proof.
      intros.
      unfold Hierarchy.sum_n.
      rewrite Hierarchy.sum_n_m_Chasles with (m := N1); try lia.
      generalize (upcrossing_bound_range0_init a b a0); intros.
      rewrite H0 in H2.
      rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
          (b := fun n0 => 0); trivial.
      - rewrite Hierarchy.sum_n_m_const.
        rewrite Rmult_0_r.
        rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
            (b := fun n0 => f n0 a0); trivial.
        + unfold Hierarchy.plus; simpl.
          lra.
        + intros.
          generalize (upcrossing_bound_range a b a0 1); intros.
          replace (2 * 1 - 1)%nat with (1%nat) in H4 by lia.
          replace (2 * 1)%nat with (2%nat) in H4 by lia.
          rewrite H0 in H4.
          rewrite H1 in H4.
          specialize (H4 k).
          rewrite H4; try lra.
          lia.
     - intros.
       rewrite H2; try lra; lia.
    Qed.

    Lemma one_upcrossing_bound_S a b a0 (f : nat -> Ts -> R) N1 N2 :
      (N1 < N2) %nat ->
      upcrossing_times a b (1%nat) a0 = Some N1 ->
      upcrossing_times a b (2%nat) a0 = Some N2 ->
      @Hierarchy.sum_n 
        Hierarchy.R_AbelianGroup
        (fun n0 : nat => 
           upcrossing_bound a b (S n0) a0 * f (S n0) a0) (N2-1)%nat =
      @Hierarchy.sum_n_m 
        Hierarchy.R_AbelianGroup
        (fun n0 => f (S n0) a0) N1 (N2-1)%nat.
    Proof.
      intros.
      destruct N1.
      {
        unfold Hierarchy.sum_n.
        apply Hierarchy.sum_n_m_ext_loc.
        intros.
        generalize (upcrossing_bound_range a b a0 1); intros.
        replace (2 * 1 - 1)%nat with (1%nat) in H3 by lia.
        replace (2 * 1)%nat with (2%nat) in H3 by lia.
        rewrite H0 in H3.
        rewrite H1 in H3.
        specialize (H3 (S k)).
        rewrite H3; try lra.
        lia.
      }
      unfold Hierarchy.sum_n.
      rewrite Hierarchy.sum_n_m_Chasles with (m := N1); try lia.
      generalize (upcrossing_bound_range0_init a b a0); intros.
      rewrite H0 in H2.
      rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
          (b := fun n0 => 0); trivial.
      - rewrite Hierarchy.sum_n_m_const.
        rewrite Rmult_0_r.
        rewrite (@Hierarchy.sum_n_m_ext_loc Hierarchy.R_AbelianGroup) with
            (b := fun n0 => f (S n0) a0); trivial.
        + unfold Hierarchy.plus; simpl.
          lra.
        + intros.
          generalize (upcrossing_bound_range a b a0 1); intros.
          replace (2 * 1 - 1)%nat with (1%nat) in H4 by lia.
          replace (2 * 1)%nat with (2%nat) in H4 by lia.
          rewrite H0 in H4.
          rewrite H1 in H4.
          specialize (H4 (S k)).
          rewrite H4; try lra.
          lia.
     - intros.
       rewrite H2; try lra; lia.
    Qed.

    Lemma upcrossing_bound_transform_helper a b a0 k :
         upcrossing_times a b (2 * (S k))%nat a0 <> None ->
         @Hierarchy.sum_n 
            Hierarchy.R_AbelianGroup
            (fun n0 : nat => 
               upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0))
            (match upcrossing_times a b (2 * (S k))%nat a0 with
            | Some n => (n-1)%nat
            | _ => 0%nat
            end)
         = 
         @Hierarchy.sum_n_m 
           Hierarchy.R_AbelianGroup
           (fun k0 =>
              match upcrossing_times a b (2 * k0) a0, upcrossing_times a b (2 * k0 - 1) a0 with
              | Some N2, Some N1 => M N2 a0 - M N1 a0
              | _, _ => 0
              end) 
           1 (S k).
    Proof.
      intros.
      induction k.
      - rewrite Hierarchy.sum_n_n.
        replace (2 * 1)%nat with (2%nat) by lia.
        match_case; intros.
        + replace (2 - 1)%nat with 1%nat by lia.
          match_case; intros.
          * generalize (one_upcrossing_bound_S a b a0); intros.
            specialize (H2 (fun n1 x => M n1 x + -1 * M (n1-1)%nat x) n0 n).
            generalize (upcrossing_times_monotonic a b a0 n0 n 1%nat 2%nat); intros.
            cut_to H3; trivial; try lia.
            destruct H3.
            cut_to H3; try lia.
            cut_to H2; trivial; try lia.
            simpl in H2.
            rewrite (@Hierarchy.sum_n_ext  Hierarchy.R_AbelianGroup) with
                (b := fun n0 : nat => upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M (n0 - 0) a0)).
            rewrite H2.
            -- rewrite (@Hierarchy.sum_n_m_ext  Hierarchy.R_AbelianGroup) with
                   (b := fun n1 : nat => M (S n1) a0 + -1 * M n1 a0).
               ++ generalize (telescope_sum (fun n => M n a0) n0 (n-1-n0)%nat); intros.
                  replace (n0 + (n-1 - n0))%nat with (n-1)%nat in H5 by lia.
                  rewrite H5.
                  now replace (n0 + S(n-1 - n0))%nat with n by lia.
               ++ intros.
                  do 4 f_equal.
                  lia.
            -- intros.
               do 4 f_equal.
               lia.
        * apply upcrossing_times_none in H1.
          congruence.
      + now replace (2 * 1)%nat with (2%nat) in H by lia.
    - rewrite Hierarchy.sum_n_Sm; try lia.
      rewrite <- IHk.
      + symmetry; match_case; intros; symmetry.
        * unfold Hierarchy.sum_n.
          rewrite Hierarchy.sum_n_m_Chasles with (m := (n-1)%nat); try lia.
          -- f_equal.
             match_case; intros.
             match_case; intros.
             ++ assert (n < n1)%nat.
                {
                  assert (2 * S k < 2 * S (S k) - 1)%nat by lia.
                  generalize (upcrossing_times_monotonic a b a0 n n1 (2 * S k)%nat (2 * S (S k) - 1)%nat); intros.
                  cut_to H4; try lia; trivial.
                }
                rewrite Hierarchy.sum_n_m_Chasles with (m := (n1-1)%nat); try lia.
                ** rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
                       (b := fun n1 => Hierarchy.zero).
                   --- rewrite Hierarchy.sum_n_m_const_zero.
                       rewrite Hierarchy.plus_zero_l.
                       generalize (transform_upcrossing a b a0 (S (S k))); intros.
                       cut_to H4; try lia.
                       rewrite H1, H2 in H4.
                       replace (S (n1 - 1)) with n1 by lia.
                       apply H4; try lia.
                   --- intros.
                       unfold Hierarchy.zero; simpl.
                       rewrite (upcrossing_bound_range10 a b a0 (S k0) (S k)); try lia; try lra.
                       replace (2 * S k + 1)%nat with (2 * S (S k) - 1)%nat by lia.
                       rewrite H0, H2.
                       lia.
                ** assert (2 * S (S k) - 1 < 2 * S (S k))%nat by lia.
                  generalize (upcrossing_times_monotonic a b a0 n1 n0 (2 * S (S k)-1)%nat (2 * S (S k))%nat); intros.
                  cut_to H5; try lia; trivial.
             ++ apply upcrossing_times_none in H2.
                replace (S (2 * S (S k) - 1))%nat with (2 * S (S k))%nat in H2 by lia.
                congruence.
          -- match_case; intros; try easy.
             generalize (upcrossing_times_some2 a b (2 * S k)%nat a0 n n0); intros.
             replace (S (S (2 * S k))) with (2 * S (S k))%nat in H2 by lia.
             cut_to H2; trivial; try lia.
        * do 2 apply upcrossing_times_none in H0.
          now replace (S (S (2 * S k))) with (2 * S (S k))%nat in H0 by lia.
      + generalize (upcrossing_times_none a b (2 * S k)%nat a0); intros.
        generalize (upcrossing_times_none a b (S (2 * S k)) a0); intros.
        replace (S (S (2 * S k))) with (2 * S (S k))%nat in H1 by lia.
        tauto.
    Qed.

    Definition upcrossing_var_expr1 a b n ts k
      := match upcrossing_times a b k ts with
         | None => 0%nat
         | Some upn => if le_dec upn n then k else 0%nat
         end.

    Lemma upcrossing_bound_transform_ge_0 a b a0 k n0 n : 
      (k > 0)%nat ->
      a < b ->
      (n0 <= n)%nat ->
      (forall m x, M m x >= a) ->
      upcrossing_var_expr a b (S n) a0 (S k) = 0%nat ->      
      upcrossing_times a b (2 * k) a0 = Some n0 ->
      0 <=
      @Hierarchy.sum_n_m 
        Hierarchy.R_AbelianGroup        
        (fun n2 : nat => upcrossing_bound a b (S n2) a0 * (M (S n2) a0 + -1 * M n2 a0))
        n0 n.
    Proof.
      intros.
      unfold upcrossing_var_expr in H3.
      generalize (transform_upcrossing_zero_01_full a b a0 k (S n) H H2); intros.
      replace (S n - 1)%nat with (n) in H5 by lia.
      case_eq (upcrossing_var_expr1 a b (S n) a0 (2 * k + 1)%nat); intros.
      - right; symmetry.
        unfold upcrossing_var_expr1 in H6.
        rewrite H4 in H5.
        match_case_in H6; intros; rewrite H7 in H5; rewrite H7 in H6;
          apply H5; try lia; trivial.
        match_destr_in H6; try lia.
      - generalize (transform_upcrossing_pos_01_full a b a0 k (S n) H H2); intros.
        unfold upcrossing_var_expr1 in H6.
        apply Rge_le.
        rewrite H4 in H7.
        match_case_in H6; intros; rewrite H8 in H6; try easy.
        rewrite H8 in H7.
        replace (S n - 1)%nat with n in H7 by lia.
        destruct (lt_dec n2 (S n)).
        + match_case_in H3; intros; rewrite H9 in H3; rewrite H9 in H7; apply H7; try lia.
          match_destr_in H3; try lia.
        + assert (S n <= n2)%nat by lia.
          rewrite H4, H8 in H5.
          right; apply H5.
          lia.
     Qed.
    
    Lemma upcrossing_var_var_expr_le a b n a0 k :
      upcrossing_var a b (S n) a0 <= INR k ->
      forall j, (upcrossing_var_expr a b (S n) a0 j <= k)%nat.
    Proof.
      intros upk j.
      destruct (le_dec j (S n)).
      - unfold upcrossing_var, upcrossing_var_expr in *.
        match_option; [| lia].
        match_destr; [| lia].
        apply INR_le.
        eapply Rmax_list_le; try apply upk.
        apply in_map.
        apply in_map_iff.
        exists j.
        split.
        + rewrite eqq.
          match_destr; lia.
        + apply in_seq.
          lia.
      - rewrite (upcrossing_var_expr_gt a b (S n) a0 j); lia.
    Qed.

    Lemma upcrossing_var_var_expr_Sn a b n a0 k :
      upcrossing_var a b (S n) a0 = INR k ->
      upcrossing_var_expr a b (S n) a0 (S k) = 0%nat.
    Proof.
      intros.
      assert (leH:  upcrossing_var a b (S n) a0 <= INR k) by lra.
      generalize (upcrossing_var_var_expr_le a b n a0 k leH (S k)); intros.
      unfold upcrossing_var_expr in *.
      match_case; intros.
      rewrite H1 in H0.
      match_destr; try lia.
    Qed.

    Lemma upcrossing_bound_transform_ge_Sn a b n : 
      a < b ->
      (forall m x, M m x >= a) ->
      rv_le (rvscale (b-a) (upcrossing_var a b (S n))) (martingale_transform (upcrossing_bound a b) M (S n)).
    Proof.
      intros altb Mgea ?.
      unfold martingale_transform.
      rv_unfold.
      generalize (Rmax_list_In (map INR (map (upcrossing_var_expr a b (S n) a0) (seq 0 (S (S n))))))
      ; intros HH.
      cut_to HH; [| simpl; congruence].
      generalize (Rmax_spec_map (map (upcrossing_var_expr a b (S n) a0) (seq 0 (S (S n)))) INR)
      ; intros Hin'.
      apply in_map_iff in HH.
      destruct HH as [kk [??]].
      rewrite <- H in Hin'.
      unfold upcrossing_var.
      rewrite <- H.
      apply in_map_iff in H0.
      destruct H0 as [k [??]].
      apply in_seq in H1.
      destruct H1 as [_ ?].
      assert (k <= S n)%nat by lia; clear H1.
      assert (Hin : forall x1,
                 (upcrossing_var_expr a b (S n) a0 x1 <= kk)%nat).
      {
        intros.
        destruct (le_dec x1 (S n)).
        - apply INR_le.
          subst.
          apply Hin'.
          apply in_map.
          apply in_seq; lia.
        - rewrite upcrossing_var_expr_gt; lia.
      }
      clear Hin' H.
      subst.
      unfold rvsum.
      assert (forall k0 n,
               (upcrossing_var_expr a b (S n) a0 (S k0) > 0)%nat ->                 
               match upcrossing_times a b (2 * (S k0)) a0, upcrossing_times a b (2 * (S k0) - 1) a0 with
               | Some N2, Some N1 => M N2 a0 - M N1 a0 >= b-a
               | _, _ => False
               end) .
      {
        intros.
        generalize (upcrossing_times_even_ge a b k0 a0 n0 H)
        ; generalize (upcrossing_times_odd_le a b k0 a0 n0 H).
        repeat match_option.
        lra.
      }
      assert ( 
          @Hierarchy.sum_n 
            Hierarchy.R_AbelianGroup
            (fun n0 : nat => 
                             upcrossing_bound a b (S n0) a0 * (M (S n0) a0 + -1 * M n0 a0)) n
          >=
          @Hierarchy.sum_n_m 
            Hierarchy.R_AbelianGroup
            (fun k0 =>
               match upcrossing_times a b (2 * k0) a0, upcrossing_times a b (2 * k0 - 1) a0 with
              | Some N2, Some N1 => M N2 a0 - M N1 a0
              | _, _ => 0
              end) 
            1 
            (upcrossing_var_expr a b (S n) a0 k)).
      {
        case_eq (upcrossing_var_expr a b (S n) a0 k); intros.
        - rewrite Hierarchy.sum_n_m_zero; try lia.
          unfold Hierarchy.zero; simpl.
          apply Rle_ge.
          generalize (upcrossing_bound_range0_init a b a0); intros.
          unfold Hierarchy.sum_n.
          match_case_in H1; intros; rewrite H3 in H1.
          + destruct (lt_dec n n0).
            * rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
                  (b := fun n1 => Hierarchy.zero).
              -- rewrite Hierarchy.sum_n_m_const_zero.
                 unfold Hierarchy.zero; simpl; lra.
              -- intros.
                 rewrite H1; try lia.
                 unfold Hierarchy.zero; simpl; lra.
            * assert (ngtn0: (n >= n0)%nat) by lia.
              destruct n0.
              -- rewrite (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
                   (b := fun n2 =>  (M (S n2) a0 + -1 * M n2 a0)).
                 ++ generalize (telescope_sum (fun n => M n a0) 0 n); intros.
                    replace (0 + n)%nat with n in H4 by lia.
                    replace (0 + S n)%nat with (S n) in H4 by lia.
                    rewrite H4.
                    assert (M (0%nat) a0 = a).
                    {
                      unfold upcrossing_times, hitting_time in H3.
                      apply classic_min_of_some in H3.
                      simpl in H3.
                      unfold id in H3; simpl in H3.
                      specialize (Mgea (0%nat) a0).
                      lra.
                    }
                    rewrite H5.
                    specialize (Mgea (S n) a0); lra.
                 ++ intros.
                    assert (upcrossing_bound a b (S k0) a0 = 1).
                    {
                      unfold upcrossing_bound, EventIndicator.
                      match_destr.
                      unfold pre_union_of_collection in n0.
                      elim n0.
                      exists (1%nat).
                      replace (2 * 1 - 1)%nat with 1%nat by lia.
                      rewrite H3.
                      split; try lia.
                      match_case; intros.
                      assert (n < n2)%nat.
                      {
                        destruct n.
                        - case_eq (upcrossing_times a b 1%nat a0); intros.
                          + generalize (upcrossing_times_monotonic a b a0 n n2 1%nat (2 * 1)%nat); intros.
                            cut_to H7; try lia; trivial.
                          + apply upcrossing_times_none in H6.
                            replace (2 * 1)%nat with 2%nat in H5 by lia.
                            congruence.
                        - specialize (Hin 1%nat).
                          rewrite H0 in Hin.
                          assert (upcrossing_var_expr a b (S (S n)) a0 1 = 0)%nat by lia.
                          unfold upcrossing_var_expr in H6.
                          rewrite H5 in H6.
                          match_destr_in H6.
                          lia.
                     }
                      lia.
                    }
                    rewrite H5; lra.
              -- rewrite Hierarchy.sum_n_m_Chasles with (m := (S n0-1)%nat); try lia.
                 rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
                     (b := fun n1 => Hierarchy.zero).
                 ++ rewrite Hierarchy.sum_n_m_const_zero.
                    rewrite Hierarchy.plus_zero_l.
                    rewrite (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
                        (b := fun n2 =>  (M (S n2) a0 + -1 * M n2 a0)).
                    ** generalize (telescope_sum (fun n => M n a0) (S (S n0 - 1)) (n - (S (S n0 - 1)))); intros.
                       replace  (S (S n0 - 1) + (n - S (S n0 - 1)))%nat with n in H4 by lia.
                       rewrite H4.
                       replace (S (S n0 - 1)) with (S n0) by lia.
                       assert (M (S n0) a0 = a).
                       {
                         unfold upcrossing_times, hitting_time in H3.
                         apply classic_min_of_some in H3.
                         simpl in H3.
                         unfold id in H3; simpl in H3.
                         specialize (Mgea (S n0) a0).
                         lra.
                       }
                       rewrite H5.
                       specialize (Mgea (S n0 + S (n - S n0))%nat a0); lra.
                    ** intros.
                       assert (upcrossing_bound a b (S k0) a0 = 1).
                       {
                         unfold upcrossing_bound, EventIndicator.
                         match_destr.
                         unfold pre_union_of_collection in n2.
                         elim n2.
                         exists (1%nat).
                         replace (2 * 1 - 1)%nat with 1%nat by lia.
                         rewrite H3.
                         split; try lia.
                         match_case; intros.
                         assert (n < n3)%nat.
                         {
                           assert (n > 0)%nat by lia.
                           specialize (Hin 1%nat).
                           rewrite H0 in Hin.
                           assert (upcrossing_var_expr a b (S n) a0 1 = 0)%nat by lia.
                           unfold upcrossing_var_expr in H7.
                           rewrite H5 in H7.
                           match_destr_in H7.
                           lia.
                         }
                         lia.
                    }
                    rewrite H5; lra.
                 ++ intros.
                    rewrite H1; try lia.
                    unfold Hierarchy.zero; simpl; lra.
          + rewrite  (@Hierarchy.sum_n_m_ext_loc  Hierarchy.R_AbelianGroup) with
                (b := fun n1 => Hierarchy.zero).
            * rewrite Hierarchy.sum_n_m_const_zero.
              unfold Hierarchy.zero; simpl; lra.
            * intros.
              rewrite H1; try lia.
              unfold Hierarchy.zero; simpl; lra.
        - generalize (upcrossing_bound_transform_helper a b a0 n0); intros.
          match_case_in H1; intros; rewrite H3 in H1.
          + destruct (lt_dec (n1-1)%nat n).
            * unfold Hierarchy.sum_n.
              rewrite Hierarchy.sum_n_m_Chasles with (m := (n1-1)%nat); try lia.
              unfold Hierarchy.sum_n in H1.
              rewrite H1; try congruence.
              apply Rle_ge.
              apply Rplus_le_compat1_l.
              assert (n1 > 0)%nat.
              {
                case_eq (upcrossing_times a b (2 * S n0 - 1) a0); intros.
                - generalize (upcrossing_times_monotonic a b a0 n2 n1 (2 * S n0 - 1)%nat (2 * S n0)%nat); intros.                                 
                  cut_to H5; try lia; trivial.
                - apply upcrossing_times_none in H4.
                  replace (S (2 * S n0 - 1)) with (2 * S n0)%nat in H4 by lia.
                  congruence.
              }
              replace (S (n1 - 1)) with n1 by lia.
              apply upcrossing_bound_transform_ge_0 with (k := S n0); trivial; try lia.
              specialize (Hin (S (S n0))).
              rewrite H0 in Hin.
              unfold upcrossing_var_expr.
              match_case; intros.
              unfold upcrossing_var_expr in Hin.
              rewrite H5 in Hin.
              match_destr.
              lia.
            * assert (n <= n1 - 1)%nat by lia.
              unfold upcrossing_var_expr in H0.
              match_case_in H0; intros.
              -- rewrite H5 in H0.
                 match_destr_in H0.
                 rewrite H0 in H5.
                 rewrite H5 in H3.
                 invcs H3.
                 assert (n = n1 - 1)%nat by lia.
                 rewrite H0.
                 rewrite H1; try congruence.
                 now right.
              -- rewrite H5 in H0.
                 lia.
          + unfold upcrossing_var_expr in H0.
            match_case_in H0; intros; rewrite H4 in H0.
            * match_destr_in H0.
              rewrite H0 in H4; congruence.
            * lia.
      }
      apply Rge_le.
      eapply Rge_trans.
      apply H0.
      destruct k.
      - simpl.
        unfold upcrossing_var_expr.
        replace (2  * 0)%nat with (0)%nat by lia.
        simpl.
        rewrite Hierarchy.sum_n_m_zero; try lia.
        unfold Hierarchy.zero; simpl.
        lra.
      - destruct  (le_dec 1 (upcrossing_var_expr a b (S n) a0 (S k))).
        + transitivity
            (@Hierarchy.sum_n_m Hierarchy.R_AbelianGroup
                                (fun _ => b - a)
                                1 (upcrossing_var_expr a b (S n) a0 (S k))).
          * apply Rle_ge.
            apply sum_n_m_le_loc; trivial.
            intros.
            specialize (H (n0-1)%nat n).
            replace (S (n0 -1)) with (n0) in H by lia.
            assert (upcrossing_var_expr a b (S n) a0 n0 > 0)%nat.
            {
              unfold upcrossing_var_expr in H1.
              match_destr_in H1 ; try lia.
              match_destr_in H1; try lia.
              replace (n0) with (S (n0 - 1)) by lia.
              apply upcrossing_var_expr_gt0 with (k := k); try lia.
            }
            specialize (H H3).
            match_option.
            -- rewrite eqq in H.
               match_option.
               ++ rewrite eqq0 in H.
                  lra.
               ++ now rewrite eqq0 in H.
            -- now rewrite eqq in H.
          * rewrite Hierarchy.sum_n_m_const.
            replace (S (upcrossing_var_expr a b (S n) a0 (S k)) - 1)%nat with (upcrossing_var_expr a b (S n) a0 (S k)) by lia.
            lra.
        + assert ((upcrossing_var_expr a b (S n) a0 (S k))%nat = 0%nat) by lia.
          rewrite H1.
          simpl.
          rewrite Rmult_0_r.
          rewrite Hierarchy.sum_n_m_zero; try lia.
          unfold Hierarchy.zero; simpl; lra.
    Qed.

    Lemma upcrossing_bound_transform_ge a b n : a < b ->
      (forall m x, M m x >= a) -> 
      rv_le (rvscale (b-a) (upcrossing_var a b n)) (martingale_transform (upcrossing_bound a b) M n).
    Proof.
      intros Mgea ??.
      destruct n.
      - simpl.
        unfold upcrossing_var; simpl.
        rv_unfold; lra.
      - now apply upcrossing_bound_transform_ge_Sn.
    Qed.

    End doob_upcrossing_times.

    Section doob_upcrossing_ineq.

      Local Existing Instance Rbar_le_pre.

      Context
        (M : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
        {rv:forall n, RandomVariable dom borel_sa (M n)}
        {isfe:forall n, IsFiniteExpectation prts (M n)}
        {adapt:IsAdapted borel_sa M sas}
        {filt:IsFiltration sas}
        {sub:IsSubAlgebras dom sas}
        {mart:IsMartingale prts Rle M sas}.

      Theorem upcrossing_inequality a b n :
        a < b ->
        Rbar_le (Rbar_mult (b-a) (NonnegExpectation (upcrossing_var M a b (S n))))
                (Rbar_minus (NonnegExpectation (pos_fun_part (rvminus (M (S n)) (const a))))
                            (NonnegExpectation (pos_fun_part (rvminus (M 0%nat) (const a))))).
      Proof.
        intros altb.
      pose (ϕ x := Rmax (x - a) 0 + a).
      pose (Y n := fun x => ϕ (M n x)).

      assert (ϕconvex:(forall c x y : R, convex ϕ c x y)).
      {
        unfold ϕ.
        intros ????.
        unfold Rmax.
        repeat match_destr; try lra.
        - field_simplify.
          replace (y-a+a) with y by lra.
          assert (a < y) by lra.
          transitivity (c*a + (1-c)*a); try lra.
          apply Rplus_le_compat_l.
          apply Rmult_le_compat_l; try lra.
        - field_simplify.
          replace (x-a+a) with x by lra.
          assert (a < x) by lra.
          transitivity (c*a + (1-c)*a); try lra.
          apply Rplus_le_compat_r.
          apply Rmult_le_compat_l; try lra.
        - replace (x-a+a) with x by lra.
          replace (y-a+a) with y by lra.
          assert (a < x) by lra.
          assert (a < y) by lra.
          transitivity (c*a + (1-c)*a); try lra.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; try lra.
          + apply Rmult_le_compat_l; try lra.
        - rewrite Rplus_0_l.
          unfold Rminus.
          rewrite Rplus_assoc.
          rewrite Rplus_opp_l.
          rewrite Rplus_0_r.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; lra.
          + apply Rmult_le_compat_l; lra.
        - rewrite Rplus_0_l.
          unfold Rminus.
          repeat rewrite Rplus_assoc.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; lra.
          + rewrite Rplus_opp_l.
            lra.
        - rewrite Rplus_0_l.
          unfold Rminus.
          repeat rewrite Rplus_assoc.
          apply Rplus_le_compat.
          + apply Rmult_le_compat_l; lra.
          + rewrite Rplus_opp_l.
            rewrite Rplus_0_r.
            apply Rmult_le_compat_l; lra.
      } 

      assert (ϕincr : forall x y : R, x <= y -> ϕ x <= ϕ y).
      {
        unfold ϕ.
        intros ???.
        unfold Rmax.
        repeat match_destr; lra.
      }

      assert (adaptY:IsAdapted borel_sa Y sas).
      {
        apply is_adapted_convex; trivial.
      } 

      assert (rvY:forall n : nat, RandomVariable dom borel_sa (Y n)).
      {
        intros m.
        generalize (adaptY m).
        apply RandomVariable_proper_le; try reflexivity.
        apply sub.
      } 

      assert (isfeY:forall n : nat, IsFiniteExpectation prts (Y n)).
      {
        intros m.
        unfold Y, ϕ.
        assert (rv1:RandomVariable dom borel_sa (fun x : Ts => M m x - a)).
        {
          apply rvplus_rv.
          - generalize (adapt m).
            apply RandomVariable_proper_le; try reflexivity.
            apply sub.
          - apply rvconst.
        } 

        apply IsFiniteExpectation_plus.
        - apply positive_part_rv; trivial.
        - apply rvconst.
        - apply IsFiniteExpectation_max; trivial.
          + apply rvconst.
          + apply IsFiniteExpectation_plus; trivial.
            * apply rvconst.
            * apply IsFiniteExpectation_const.
          + apply IsFiniteExpectation_const.
        - apply IsFiniteExpectation_const.
      } 

      assert (martY:IsMartingale prts Rle Y sas).
      {
        eapply is_sub_martingale_incr_convex; eauto.
      } 

      assert (upcross_same:forall m, rv_eq (upcrossing_var Y a b m) (upcrossing_var M a b m)).
      {
        intros m ts.
        unfold Y, ϕ.
        unfold upcrossing_var.
        f_equal.
        repeat rewrite map_map.
        apply map_ext_in; intros c ?.
        apply in_seq in H.
        assert (c < S m)%nat by lia.
        f_equal.

        unfold upcrossing_var_expr.

        assert (eqq:forall c, upcrossing_times Y a b c ts = upcrossing_times M a b c ts).
        {

          assert (forall old, hitting_time_from Y old (event_ge borel_sa id b) ts =
                           hitting_time_from M old (event_ge borel_sa id b) ts).
          {
            unfold hitting_time_from; intros.
            unfold hitting_time.
            repeat match_option.
            - do 2 f_equal.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id; intros HHM1.
              generalize (classic_min_of_some_first _ _ eqq); simpl; unfold id; intros HHY2.
              generalize (classic_min_of_some_first _ _ eqq0); simpl; unfold id; intros HHM2.
              apply antisymmetry
              ; apply not_lt
              ; intros HH.
              + apply (HHY2 _ HH).
                unfold Y, ϕ.
                unfold Rmax.
                match_destr; lra.
              + apply (HHM2 _ HH).
                unfold Y, ϕ in HHY1.
                unfold Rmax in HHY1.
                match_destr_in HHY1; lra.
            - generalize (classic_min_of_none _ eqq0 n0); simpl; unfold id
              ; intros HHM.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              match_destr_in HHY1; try lra.
            - generalize (classic_min_of_none _ eqq n0); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id
              ; intros HHM1.
              match_destr_in HHY1; try lra.
          }
          
          assert (forall old, hitting_time_from Y old (event_le borel_sa id a) ts =
                           hitting_time_from M old (event_le borel_sa id a) ts).
          {
            unfold hitting_time_from; intros.
            unfold hitting_time.
            repeat match_option.
            - do 2 f_equal.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id; intros HHM1.
              generalize (classic_min_of_some_first _ _ eqq); simpl; unfold id; intros HHY2.
              generalize (classic_min_of_some_first _ _ eqq0); simpl; unfold id; intros HHM2.
              apply antisymmetry
              ; apply not_lt
              ; intros HH.
              + apply (HHY2 _ HH).
                unfold Y, ϕ.
                unfold Rmax.
                match_destr; lra.
              + apply (HHM2 _ HH).
                unfold Y, ϕ in HHY1.
                unfold Rmax in HHY1.
                match_destr_in HHY1; lra.
            - generalize (classic_min_of_none _ eqq0 n0); simpl; unfold id
              ; intros HHM.
              generalize (classic_min_of_some _ _ eqq); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              match_destr_in HHY1; try lra.
            - generalize (classic_min_of_none _ eqq n0); simpl; unfold id
              ; unfold Y, ϕ, Rmax; intros HHY1.
              generalize (classic_min_of_some _ _ eqq0); simpl; unfold id
              ; intros HHM1.
              match_destr_in HHY1; try lra.
          } 
          intros x; destruct x; simpl; trivial.
          induction x; simpl.
          - specialize (H2 0%nat).
            now repeat rewrite hitting_time_from0 in H2.
          - rewrite IHx.
            destruct (match x with
                      | 0%nat => hitting_time M (event_le borel_sa id a) ts
                      | S _ =>
                          match upcrossing_times M a b x ts with
                          | Some old =>
                              if Nat.even x
                              then hitting_time_from M (S old) (event_le borel_sa id a) ts
                              else hitting_time_from M (S old) (event_ge borel_sa id b) ts
                          | None => None
                          end
                      end); trivial.
            destruct (match x with
                      | 0%nat => false
                      | S n' => Nat.even n'
                      end); auto.
        }
        now rewrite eqq.
      }

      apply (Rbar_le_trans _ (Rbar_mult (b - a) (NonnegExpectation (upcrossing_var Y a b (S n))))).
      {
        apply Rbar_mult_le_compat_l; [simpl; lra |].
        apply refl_refl.
        now apply NonnegExpectation_ext.
      }

       assert (isfeb:forall n : nat,
                  IsFiniteExpectation prts
                                      (rvmult (upcrossing_bound Y a b (S n)) (rvminus (Y (S n)) (Y n)))).
      {
        intros.
        unfold upcrossing_bound.
        rewrite rvmult_comm.
        apply IsFiniteExpectation_indicator.
        - typeclasses eauto.
        - 
          generalize (upcrossing_bound_rv Y sas a b (S n0) (event_singleton _ (borel_singleton 1))).
          apply sa_proper.
          intros ?.
          unfold event_preimage, upcrossing_bound; simpl.
          unfold pre_event_singleton, EventIndicator.
          match_destr.
          + tauto.
          + split; try tauto.
            lra.
        - typeclasses eauto.
      } 

      assert (IsAdapted borel_sa (martingale_transform (upcrossing_bound Y a b) Y) sas).
      {
        apply martingale_transform_adapted; trivial.
        now apply upcrossing_bound_is_predictable.
      } 

      generalize (martingale_transform_predictable_sub_martingale
                    prts
                    (upcrossing_bound Y a b)
                    Y
                    sas); intros martT.
      { cut_to martT.
        shelve.
        - now apply upcrossing_bound_is_predictable.
        - intros.
          apply all_almost; intros.
          unfold const.
          unfold upcrossing_bound, EventIndicator; simpl.
          match_destr; lra.
        - trivial.
      }
      Unshelve.
      assert (Ygea: forall m x, Y m x >= a).
      {
        intros.
        unfold Y, ϕ.
        unfold Rmax.
        match_destr; lra.
      }
      generalize (upcrossing_bound_transform_ge Y sas a b (S n) altb Ygea); intros leup.
      assert (nneg1:NonnegativeFunction (rvscale (b - a) (upcrossing_var Y a b (S n)))).
      {
        apply scale_nneg_nnf.
        - typeclasses eauto.
        - lra.
      }

      generalize (NonnegativeFunction_le_proper _ _ leup nneg1); intros nneg2.
      generalize (NonnegExpectation_le _ _ leup)
      ; intros le2.
      rewrite (NonnegExpectation_scale' _ _) in le2; try lra.
      eapply Rbar_le_trans; try apply le2.

      assert (eqq1:rv_eq (rvminus (Y (S n)) (Y 0%nat))
                    (rvplus
                       ((martingale_transform (fun k => rvminus (const 1) (upcrossing_bound Y a b k)) Y) (S n))
                       ((martingale_transform (upcrossing_bound Y a b) Y) (S n)))).
      {
        rewrite martingale_transform_plus.
        transitivity (martingale_transform
                        (fun k' : nat =>
                           (const 1)) Y 
                        (S n)).
        - rewrite martingale_transform_1.
          reflexivity.
        - apply martingale_transform_proper; try reflexivity.
          intros ??.
          rv_unfold.
          lra.
      }

      assert (isfe2:IsFiniteExpectation _ (rvplus
              (martingale_transform
                 (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y 
                 (S n)) (martingale_transform (upcrossing_bound Y a b) Y (S n)))).
      {
        eapply IsFiniteExpectation_proper.
        - symmetry; apply eqq1.
        - typeclasses eauto.
      } 
      generalize (FiniteExpectation_ext _ _ _ eqq1); intros eqq2.
      rewrite FiniteExpectation_minus in eqq2.
      unfold Y in eqq2 at 1 2.
      unfold ϕ in eqq2 at 1 2.
      assert (isfe3:forall n, IsFiniteExpectation prts (pos_fun_part (rvminus (M n) (const a)))).
      {
        intros.
        - apply IsFiniteExpectation_max; trivial.
          + typeclasses eauto.
          + apply rvconst.
          + apply IsFiniteExpectation_minus; trivial.
            * apply rvconst.
            * apply IsFiniteExpectation_const.
          + apply IsFiniteExpectation_const.
      }
                                                
      assert (eqq3:FiniteExpectation prts (fun x : Ts => Rmax (M (S n) x - a) 0 + a) =
                FiniteExpectation prts (rvplus (pos_fun_part (rvminus (M (S n)) (const a)))
                                               (const a))).
      {
        apply FiniteExpectation_ext; intros ?.
        unfold rvminus, rvplus, rvopp, pos_fun_part, const, rvscale; simpl.
        f_equal.
        f_equal.
        lra.
      }
      rewrite eqq3 in eqq2.
      rewrite (FiniteExpectation_plus _ _) in eqq2. 
      assert (eqq4:FiniteExpectation prts (fun x : Ts => Rmax (M 0 x - a) 0 + a) =
                FiniteExpectation prts (rvplus (pos_fun_part (rvminus (M 0) (const a)))
                                               (const a))).
      {
        apply FiniteExpectation_ext; intros ?.
        unfold rvminus, rvplus, rvopp, pos_fun_part, const, rvscale; simpl.
        f_equal.
        f_equal.
        lra.
      }
      rewrite eqq4 in eqq2.
      rewrite (FiniteExpectation_plus _ _) in eqq2. 
      field_simplify in eqq2.
      rewrite (FiniteNonnegExpectation _ _) in eqq2.
      rewrite (FiniteNonnegExpectation _ _) in eqq2.

      match type of eqq2 with
        ?x = ?y =>
          match goal with
          | [|- Rbar_le ?a ?b] => assert (eqq5:b = x)
          end
      end.
      {
        assert (isfin:forall n, is_finite
                  (NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M n) (const a)) x))).
        {
          intros.
          apply IsFiniteNonnegExpectation.
          typeclasses eauto.
        }
        rewrite <- (isfin (S n)).
        rewrite <- (isfin 0)%nat.
        simpl.
        reflexivity.
      }
      rewrite eqq5, eqq2.

      assert (isfe4:IsFiniteExpectation prts (martingale_transform (upcrossing_bound Y a b) Y (S n))).
      {
        typeclasses eauto.
      } 

      assert (isfe5a: forall n0 : nat,
                 IsFiniteExpectation prts
                                     (rvmult (rvminus (const 1) (upcrossing_bound Y a b (S n0))) (rvminus (Y (S n0)) (Y n0)))).
      { 
        - intros.
          cut (IsFiniteExpectation prts
                                   (rvminus (rvminus (Y (S n0)) (Y n0))
                                            
                                            (rvmult (upcrossing_bound Y a b (S n0)) (rvminus (Y (S n0)) (Y n0))))).
          + apply IsFiniteExpectation_proper; intros ?.
            unfold rvmult, rvminus, rvplus, rvopp, rvscale, const.
            lra.
          + typeclasses eauto.
      } 
      
      assert (isfe5:IsFiniteExpectation
                      prts
                      (martingale_transform
                         (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y 
                         (S n))).
      {
        apply martingale_transform_isfe; trivial.
        - intros.
          typeclasses eauto.
      }
      
      rewrite (FiniteExpectation_plus' _ _ _).
      rewrite (FiniteNonnegExpectation _
                                       (martingale_transform (upcrossing_bound Y a b) Y (S n))).
      cut (Rbar_le
             (Rbar_plus 0
                        (NonnegExpectation (martingale_transform (upcrossing_bound Y a b) Y (S n))))
             (Rbar_plus
                (FiniteExpectation prts
                                   (martingale_transform
                                      (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y 
                                      (S n)))
                (real (NonnegExpectation (martingale_transform (upcrossing_bound Y a b) Y (S n)))))).
      {
        rewrite Rbar_plus_0_l.
        now simpl.
      } 
      apply Rbar_plus_le_compat
      ; [| now rewrite IsFiniteNonnegExpectation; try reflexivity].

      assert (ispredminus1:is_predictable (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) sas).
      {
        red.
        apply is_adapted_minus.
        - apply is_adapted_const.
        - now apply upcrossing_bound_is_predictable.
      } 

      assert (IsAdapted borel_sa
                        (martingale_transform (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y)
                        sas).
      {
        apply martingale_transform_adapted; trivial.
      } 
 

      generalize (martingale_transform_predictable_sub_martingale
                    prts
                    (fun k => (rvminus (const 1) (upcrossing_bound Y a b k)))
                    Y
                    sas); intros martT1.
      { cut_to martT1.
        shelve.
        - trivial.
        - intros.
          apply all_almost; intros.
          rv_unfold.
          unfold upcrossing_bound, EventIndicator; simpl.
          match_destr; lra.
        - trivial.
      }
      Unshelve.
      generalize (is_sub_martingale_expectation
                    prts
                    (martingale_transform
                       (fun k : nat => rvminus (const 1) (upcrossing_bound Y a b k)) Y)
                    sas
                    0
                    (S n)); intros HH.
      cut_to HH; [| lia].
      unfold Rbar_le.
      etransitivity; [etransitivity |]; [| apply HH |].
        - simpl.
          erewrite FiniteExpectation_pf_irrel; try rewrite FiniteExpectation_const.
          reflexivity.
        - right.
          apply FiniteExpectation_pf_irrel.
     Qed.
  End doob_upcrossing_ineq.


  Section mart_conv.

    Local Existing Instance Rbar_le_pre.
    
    Context
      (M : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
      {rv:forall n, RandomVariable dom borel_sa (M n)}
      {isfe:forall n, IsFiniteExpectation prts (M n)}
      {adapt:IsAdapted borel_sa M sas}
      {filt:IsFiltration sas}
      {sub:IsSubAlgebras dom sas}
      {mart:IsMartingale prts Rle M sas}.


    Lemma upcrossing_var_expr_incr a b n omega x :
      (upcrossing_var_expr M a b n omega x <=
         upcrossing_var_expr M a b (S n) omega x)%nat.
    Proof.
      unfold upcrossing_var_expr.
      match_destr.
      repeat match_destr; lia.
    Qed.        

    Lemma upcrossing_var_incr a b n omega : upcrossing_var M a b n omega <= upcrossing_var M a b (S n) omega.
    Proof.
      unfold upcrossing_var.
      transitivity (Rmax_list (map INR (map (upcrossing_var_expr M a b n omega) (seq 0 (S (S n)))))).
      - apply Rmax_list_incl.
        + simpl; congruence.
        + repeat apply incl_map.
          apply incl_seq; lia.
      - repeat rewrite map_map.
        apply Rmax_list_fun_le; intros.
        apply le_INR.
        apply upcrossing_var_expr_incr.
    Qed.

    Instance upcrossing_var_rv a b :
      forall n : nat, RandomVariable dom borel_sa (upcrossing_var M a b n).
    Proof.
      intros n.
      unfold upcrossing_var.
      cut (RandomVariable dom borel_sa
                          (fun ts : Ts => Rmax_list (map (fun a => a ts) (map (fun x ts => INR (upcrossing_var_expr M a b n ts x)) (seq 0 (S n)))))).
      - apply RandomVariable_proper; try reflexivity.
        intros ?.
        now repeat rewrite map_map.
      - apply Rmax_list_rv; intros.
        apply in_map_iff in H.
        destruct H as [?[??]]; subst.
        unfold upcrossing_var_expr.
        generalize (upcrossing_times_is_stop M sas a b (2 * x0)%nat).
        intros HH.
        apply is_stopping_time_as_alt in HH; trivial.
        apply is_stopping_time_alt_adapted in HH.
        red in HH.
        generalize (HH n); intros HH2.
        generalize (rvscale_rv _ (INR x0) _ HH2).
        apply RandomVariable_proper_le; try reflexivity
        ; try apply sub.
        intros ?.
        rv_unfold.
        match_destr; unfold stopping_time_pre_event_alt in *.
        + match_destr; try tauto.
          match_destr; try lia.
          lra.
        + match_destr.
          * match_destr.
            -- congruence.
            -- simpl; lra.
          * simpl; lra.
    Qed.

    Lemma upcrossing_var_lim_isfe (K:R) a b :
      is_ELimSup_seq (fun n => NonnegExpectation (pos_fun_part (M n))) K ->
      a < b ->
      Rbar_IsFiniteExpectation prts (Rbar_rvlim (upcrossing_var M a b)).
    Proof.
      intros.
      unfold IsFiniteExpectation.

      unfold Rbar_IsFiniteExpectation.
      rewrite (Rbar_Expectation_pos_pofrf _ (nnf:=(@Rbar_rvlim_nnf Ts (fun (n : nat) (ts : Ts) => Finite (upcrossing_var M a b n ts))
               (upcrossing_var_nneg M a b)))).
      rewrite <- (monotone_convergence_Rbar_rvlim (fun (n : nat) ts => upcrossing_var M a b n ts)).
      - cut (is_finite ( ELim_seq (fun n : nat => Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b n ts) (pofrf:=(upcrossing_var_nneg M a b n)))))
        ; [match_destr |].
        rewrite <- ELim_seq_incr_1.

        cut (is_finite
                (ELim_seq
                   (fun n : nat => (Rbar_mult (b-a)) (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts))))).
        {
          rewrite ELim_seq_scal_l.
          - destruct (ELim_seq
                        (fun n : nat => Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts))); simpl
            ; unfold is_finite; rbar_prover.
          - red; match_destr; trivial; lra.
        }

        cut (is_finite
               (ELim_seq
                  (fun n : nat => (Rbar_mult (b-a) (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts))))
)).
        {
          intros.
          unfold is_finite in *.
          unfold Rbar_minus, Rbar_plus in *.
          destruct (ELim_seq
    (fun n : nat =>
       Rbar_mult (b - a) (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts))))
          ; trivial; simpl in *.
        }

        cut (Rbar_lt
                (ELim_seq
                   (fun n : nat =>
                         (Rbar_mult (b - a)
                                    (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts)))
                      )) p_infty).

        {
          unfold Rbar_lt, is_finite.
          match_case; simpl; try tauto.
          assert (Rbar_le 0 (ELim_seq
                               (fun n : nat =>
                                  Rbar_mult (b - a) (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts))))).
          {
            apply ELim_seq_nneg; intros.
            apply Rbar_mult_nneg_compat.
            - simpl; lra.
            - apply Rbar_NonnegExpectation_pos.
          }
          intros eqq; rewrite eqq in H1.
          simpl in H1; tauto.
        } 
        
        cut (Rbar_lt
                (ELim_seq
                   (fun n : nat =>
                      (Rbar_minus 
                         (Rbar_mult (b - a)
                                    (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts)))
                         (Rmax (- a) 0))
                      )) p_infty).

        {
          intros.
          {
            rewrite ELim_seq_minus in H1.
            shelve.
            - apply ex_Elim_seq_scal_l.
              + red; match_destr; trivial; lra.
              + apply ex_Elim_seq_incr; intros.
                apply Rbar_NonnegExpectation_le; intros ?.
                apply upcrossing_var_incr.
              + exists 0%nat; intros.
                red; match_destr; lra.
            - apply ex_Elim_seq_const.
            - rewrite ELim_seq_const.
              do 2 red.
              destruct ((ELim_seq
                           (fun n : nat =>
                              Rbar_mult (b - a)
                                        (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts))))); simpl
              ; rbar_prover.
          }
          Unshelve.
          rewrite ELim_seq_const in H1.
          unfold Rbar_minus, Rbar_plus in H1.
          destruct ((ELim_seq
                (fun n : nat =>
                 Rbar_mult (b - a)
                           (Rbar_NonnegExpectation (fun ts : Ts => upcrossing_var M a b (S n) ts))))); simpl in *; trivial.
        } 
          
        
        cut (Rbar_lt (ELim_seq
                          (fun n =>
                             Rbar_minus
                               (Rbar_minus (NonnegExpectation (pos_fun_part (rvminus (M (S n)) (const a))))
                                         (NonnegExpectation (pos_fun_part (rvminus (M 0%nat) (const a))))) (Rmax (- a) 0))) p_infty).
        {
          intros.
          eapply Rbar_le_lt_trans; try apply H1.
          apply ELim_seq_le; intros.
          apply Rbar_plus_le_compat; try reflexivity.
          eapply upcrossing_inequality; eauto.
        }

        cut (Rbar_lt         
               (ELim_seq
                  (fun n : nat =>
                     Rbar_minus
                       (NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M (S n)) (const a)) x)) (Rmax (- a) 0))) p_infty).
        {
          intros.
          eapply Rbar_le_lt_trans; try apply H1.
          apply ELim_seq_le; intros.
          apply Rbar_plus_le_compat; try reflexivity.

          unfold Rbar_minus.
          apply (Rbar_le_trans _ (Rbar_plus (NonnegExpectation (fun x : Ts => pos_fun_part (rvminus (M (S n)) (const a)) x)) 0)).
          - apply Rbar_plus_le_compat; try reflexivity.
            rewrite <- Rbar_opp_le.
            rewrite Rbar_opp_involutive.
            replace (Rbar_opp (Finite 0)) with (Finite 0)
              by (simpl; f_equal; lra).
            apply NonnegExpectation_pos.
          - rewrite Rbar_plus_0_r.
            reflexivity.
        } 

        cut (Rbar_lt         
               (ELim_seq
                  (fun n : nat =>
                     Rbar_minus
                       (NonnegExpectation (rvplus (pos_fun_part (M (S n))) (neg_fun_part (const a)))) (Rmax (- a) 0))) p_infty).
        {
          intros.
          eapply Rbar_le_lt_trans; try apply H1.
          apply ELim_seq_le; intros.
          apply Rbar_plus_le_compat; try reflexivity.

          apply NonnegExpectation_le.
          apply pos_fun_part_nneg_tri.
        } 

        cut (Rbar_lt         
               (ELim_seq
                  (fun n : nat =>
                     Rbar_minus 
                       (Rbar_plus (NonnegExpectation (pos_fun_part (M (S n)))) (Rmax (- a) 0)) (Rmax (- a) 0))) p_infty).
        {
          intros.
          eapply Rbar_le_lt_trans; try apply H1.
          apply ELim_seq_le; intros.
          rewrite NonnegExpectation_sum; try typeclasses eauto.
          unfold neg_fun_part, const; simpl.
          apply Rbar_plus_le_compat; try reflexivity.
          apply refl_refl.
          
          assert (nnc :  0 <= Rmax (- a) 0) by apply Rmax_r.
          rewrite <- (NonnegExpectation_const (Rmax (- a) 0)) with (nnc0:=nnc).
          f_equal.
        }

        cut (Rbar_lt         
               (ELim_seq
                  (fun n : nat =>
                       (NonnegExpectation (pos_fun_part (M (S n)))))) p_infty).

        { 
          intros.
          eapply Rbar_le_lt_trans; try apply H1.
          apply ELim_seq_le; intros.
          rewrite Rbar_minus_plus_fin.
          reflexivity.
        }
        rewrite (ELim_seq_incr_1
                   (fun n : nat => NonnegExpectation (fun x : Ts => pos_fun_part (M n) x))).
        eapply Rbar_le_lt_trans.
        + apply ELimSup_ELim_seq_le.
        + apply is_ELimSup_seq_unique in H.
          rewrite H.
          now simpl.
      - intros.
        apply Real_Rbar_rv.
        apply upcrossing_var_rv.
      - intros ??; simpl.
        apply upcrossing_var_incr.
    Qed.        

    Corollary upcrossing_var_lim_isf (K:R) a b :
        is_ELimSup_seq (fun n => NonnegExpectation (pos_fun_part (M n))) K ->
        a < b ->
        almost prts (fun ts => is_finite (Rbar_rvlim (upcrossing_var M a b) ts)).
    Proof.
      intros.
      apply finexp_almost_finite.
      - apply Rbar_rvlim_rv; intros.
        apply Real_Rbar_rv.
        apply upcrossing_var_rv.
      - eapply upcrossing_var_lim_isfe; eauto.
    Qed.
      
    Corollary upcrossing_var_lim_isf_allQ (K:R) :
        is_ELimSup_seq (fun n => NonnegExpectation (pos_fun_part (M n))) K ->
        almost prts (fun ts => forall (a b:Q), (a < b)%Q -> is_finite (Rbar_rvlim (upcrossing_var M (Qreals.Q2R a) (Qreals.Q2R b)) ts)).
    Proof.
      intros.
      apply almost_forallQ; intros a.
      apply almost_forallQ; intros b.
      generalize (upcrossing_var_lim_isf K (Qreals.Q2R a) (Qreals.Q2R b) H)
      ; intros HH.
      destruct (Qlt_le_dec a b).
      - specialize (HH (Qreals.Qlt_Rlt _ _ q)).
        revert HH.
        now apply almost_impl; apply all_almost; intros ???.
      - apply all_almost; intros ??.
        apply Qle_not_lt in q.
        tauto.
    Qed.

    Lemma upcrossing_times_none_bounds a b (n:nat) ts :
      upcrossing_times M a b n ts = None ->
      (exists i, forall (j:nat), (i <= j)%nat -> a < M j ts)
      \/ (exists i, forall j, (i <= j)%nat -> M j ts < b).
    Proof.
      destruct n; simpl; [congruence |].
      induction n; simpl; intros eqq.
      - unfold hitting_time in eqq.
        generalize (classic_min_of_none _ eqq); intros nle.
        unfold event_le, id in nle; simpl in nle.
        left.
        exists 0%nat; intros.
        specialize (nle j).
        lra.
      - destruct (match n with
          | 0%nat => hitting_time M (event_le borel_sa id a) ts
          | S _ =>
              match upcrossing_times M a b n ts with
              | Some old =>
                  if Nat.even n
                  then hitting_time_from M (S old) (event_le borel_sa id a) ts
                  else hitting_time_from M (S old) (event_ge borel_sa id b) ts
              | None => None
              end
                  end); [| auto].
        match_destr_in eqq
        ; unfold hitting_time_from in eqq
        ; match_option_in eqq
        ;  unfold hitting_time in eqq0
        ; generalize (classic_min_of_none _ eqq0); intros nle
        ; unfold event_le, event_ge, id in nle; simpl in nle
        ; [left | right]
        ; exists (S n0)%nat; intros
        ; specialize (nle (j - S n0))%nat
        ; replace (j - S n0 + S n0)%nat with j in nle by lia
        ; lra.
    Qed.
          
    Corollary upcrossing_var_lim_ex (K:R) :
        is_ELimSup_seq (fun n => NonnegExpectation (pos_fun_part (M n))) K ->
        almost prts (fun ts => ex_Elim_seq (fun n => M n ts)).
    Proof.
      intros.
      generalize (upcrossing_var_lim_isf_allQ K H).
      apply almost_impl; apply all_almost; intros ??.
      apply ex_Elim_LimSup_LimInf_seq.
      generalize (ELimSup_ELimInf_seq_le (fun n : nat => M n x)); intros HH.
      apply Rbar_le_lt_or_eq_dec in HH.
      destruct HH; [| congruence].
      destruct (Qs_between_Rbars _ _ r) as [a [b [age [ab blt]]]].
      specialize (H0 a b ab).
      destruct (is_finite_witness _ H0) as [nmax eqq].
      elimtype False.
      unfold Rbar_rvlim in eqq.

      generalize (Elim_seq_incr_elem
                    (fun n : nat => upcrossing_var M (Qreals.Q2R a) (Qreals.Q2R b) n x))
      ; intros HHle.
      cut_to HHle; [| intros; apply upcrossing_var_incr].
      rewrite eqq in HHle.
      simpl in HHle.
      (* I think nmax must be an integer anyway, but it does not really matter *)
      (* assert (ELim_seq (fun n : nat => upcrossing_var M (Qreals.Q2R a) (Qreals.Q2R b) n x) <- nmax *)
      assert (nmax_nneg:0 <= nmax).
      {
        cut (Rbar_le 0 nmax); [trivial |].
        rewrite <- eqq.
        apply ELim_seq_nneg; intros.
        apply upcrossing_var_nneg.
      } 
      
      assert (HHle2:
               forall j n, (upcrossing_var_expr M (Qreals.Q2R a) (Qreals.Q2R b) (S n) x j <= (Z.to_nat (up nmax)))%nat).
      {
        intros.
        apply upcrossing_var_var_expr_le.
        rewrite HHle.
        rewrite INR_up_pos by lra.
        left.
        apply archimed.
      } 
      unfold upcrossing_var_expr in HHle2.

      specialize (HHle2 (S (Z.to_nat (up nmax))%nat)).
      assert (HHle3:
          (match
              upcrossing_times M (Qreals.Q2R a) (Qreals.Q2R b) (2 * S (Z.to_nat (up nmax))) x
            with
            | Some upn => S (Z.to_nat (up nmax))
            | None => 0
            end <= Z.to_nat (up nmax))%nat).
      {
        match_option; [| lia].
        rewrite eqq0 in HHle2.
        specialize (HHle2 n).
        match_destr_in HHle2.
        lia.
      }
      match_option_in HHle3; try lia.

      apply upcrossing_times_none_bounds in eqq0.
      destruct eqq0 as [[i alt]|[i bgt]].
      + apply Rbar_lt_not_le in age.
        apply age.
        rewrite <- (ELimInf_seq_const (Qreals.Q2R a)).
        apply ELimInf_le; simpl.
        exists i; intros.
        now left; apply alt.
      + apply Rbar_lt_not_le in blt.
        apply blt.
        rewrite <- (ELimSup_seq_const (Qreals.Q2R b)).
        apply ELimSup_le; simpl.
        exists i; intros.
        now left; apply bgt.
    Qed.

    Theorem martingale_convergence (K:R) :
      is_ELimSup_seq (fun n => NonnegExpectation (pos_fun_part (M n))) K ->
      RandomVariable dom Rbar_borel_sa (Rbar_rvlim M) /\
        Rbar_IsFiniteExpectation prts (Rbar_rvlim M) /\
          almost prts (fun omega => is_Elim_seq (fun n => M n omega) (Rbar_rvlim M omega)).
    Proof.
      intros sup.
      split; [| split].
      - apply Rbar_rvlim_rv; intros.
        apply Real_Rbar_rv.
        apply rv.
      - cut (Rbar_IsFiniteExpectation prts
                                 (fun omega : Ts => ELimInf_seq (fun n : nat => (M n) omega))).
        {
          intros HH2.
          eapply Rbar_IsFiniteExpectation_proper_almostR2; try eapply HH2.
          - apply Rbar_lim_inf_rv; intros.
            now apply Real_Rbar_rv.
          - apply Rbar_rvlim_rv; intros.
            now apply Real_Rbar_rv.
          - generalize (upcrossing_var_lim_ex K sup).
            apply almost_impl; apply all_almost; intros ??.
            unfold Rbar_rvlim.
            symmetry.
            apply is_Elim_seq_unique.
            now apply ex_Elim_seq_is_Elim_seq_inf.
        } 
        generalize (Rbar_NN_Fatou (fun n => Rbar_pos_fun_part (M n)) _); intros HH.
        {
          cut_to HH.
          shelve.
          - typeclasses eauto.
          - apply Rbar_lim_inf_rv; intros.
            apply Rbar_pos_fun_part_rv.
            now apply Real_Rbar_rv.
        } 
        Unshelve.
        
        assert (posle:Rbar_le
                  (Rbar_NonnegExpectation
                     (Rbar_pos_fun_part (fun omega => ELimInf_seq (fun n : nat => M n omega)))) K).
        {
          apply is_ELimSup_seq_unique in sup.
          rewrite <- sup.
          etransitivity; [| etransitivity]; [| apply HH |].
          - apply Rbar_NonnegExpectation_le.
            apply ELimInf_seq_pos_fun_part.
          - rewrite <- ELimSup_ELimInf_seq_le.
            apply refl_refl.
            apply ELimInf_seq_ext_loc.
            exists 0%nat; intros.
            rewrite NNExpectation_Rbar_NNExpectation.
            apply Rbar_NonnegExpectation_ext; intros ?.
            unfold Rbar_pos_fun_part, pos_fun_part; simpl.
            unfold Rbar_max, Rmax.
            match_destr; f_equal ; match_destr; simpl in *; lra.
        }
        apply Rbar_IsFiniteExpectation_from_fin_parts.
        {
          eapply Rbar_le_lt_trans; try apply posle.
          now simpl.
        } 

        generalize (Rbar_NN_Fatou (fun n => Rbar_neg_fun_part (M n)) _); intros HH2.
        {
          cut_to HH2.
          shelve.
          - typeclasses eauto.
          - apply Rbar_lim_inf_rv; intros.
            apply Rbar_neg_fun_part_rv.
            now apply Real_Rbar_rv.
        } 
        Unshelve.

        assert (le1:Rbar_le
                      (Rbar_NonnegExpectation
                         (Rbar_neg_fun_part (fun omega : Ts => ELimInf_seq (fun n : nat => M n omega))))
                      (Rbar_NonnegExpectation
                         (fun omega : Ts =>
                            ELimInf_seq (fun n : nat => Rbar_neg_fun_part (fun x : Ts => M n x) omega)))).
        {
          apply Rbar_NonnegExpectation_almostR2_le.
          - apply Rbar_neg_fun_part_rv.
            apply Rbar_lim_inf_rv; intros.
            now apply Real_Rbar_rv.
          - apply Rbar_lim_inf_rv; intros.
            apply Rbar_neg_fun_part_rv.
            now apply Real_Rbar_rv.
          - generalize (upcrossing_var_lim_ex K sup).
            apply almost_impl; apply all_almost; intros ??.
            now apply ELimInf_seq_neg_fun_part.
        }
        eapply Rbar_le_lt_trans; try apply le1.
        eapply Rbar_le_lt_trans; try apply HH2.

        assert (isfe' : forall n, Rbar_IsFiniteExpectation prts (fun x : Ts => M n x))
          by now (intros; apply IsFiniteExpectation_Rbar).

        assert (isfe1:forall n, Rbar_IsFiniteExpectation _ (Rbar_neg_fun_part (fun x : Ts => M n x)))
               by now (intros; apply Rbar_IsFiniteExpectation_parts).
        
        assert (eqq1:forall n,
                 rv_eq
                   (Rbar_neg_fun_part (fun x : Ts => M n x))
                   (Rbar_rvminus (Rbar_pos_fun_part (fun x : Ts => M n x)) (fun x : Ts => M n x))).
        {
          intros n ts.
          generalize (Rbar_rv_pos_neg_id (M n) ts)
          ; intros HH1.
          unfold Rbar_rvminus, Rbar_rvopp, Rbar_rvplus in *.
          unfold Rbar_pos_fun_part, Rbar_neg_fun_part in *.
          rewrite HH1 at 3.
          unfold Rbar_plus, Rbar_opp, Rbar_max.
          repeat destruct (Rbar_le_dec _ _); simpl; f_equal; lra.
        }

        assert (isfe2:forall n, Rbar_IsFiniteExpectation _
                       (Rbar_rvminus (Rbar_pos_fun_part (fun x : Ts => M n x)) (fun x : Ts => M n x))).
        {
          intros n.
          now rewrite <- eqq1.
        } 

        assert (nnf2:forall n, Rbar_NonnegativeFunction
                       (Rbar_rvminus (Rbar_pos_fun_part (fun x : Ts => M n x)) (fun x : Ts => M n x))).
        {
          intros n ?.
          rewrite <- eqq1.
          apply Rbar_neg_fun_pos.
        } 

        assert (eqq2':(ELimInf_seq
                        (fun n : nat => Rbar_NonnegExpectation (Rbar_neg_fun_part (fun x : Ts => M n x)))) =
                       (ELimInf_seq
                          (fun n : nat => Rbar_FiniteExpectation _
                                       (Rbar_rvminus
                                          (Rbar_pos_fun_part (fun x : Ts => M n x))
                                          (fun x : Ts => M n x)
               )))).
        {
          apply ELimInf_seq_ext_loc.
          exists 0%nat; intros ??.
          rewrite (Rbar_FiniteExpectation_Rbar_NonnegExpectation _ _).
          f_equal.
          apply Rbar_FiniteExpectation_ext.
          apply eqq1.
        }

        rewrite eqq2'; clear eqq2'.
        

          
        assert (eqq1':(ELimInf_seq
                        (fun n : nat => Rbar_NonnegExpectation (Rbar_neg_fun_part (fun x : Ts => M n x)))) =
                       (ELimInf_seq
                          (fun n : nat => Rbar_NonnegExpectation
                                       (Rbar_rvminus
                                          (Rbar_pos_fun_part (fun x : Ts => M n x))
                                          (fun x : Ts => M n x)
               )))).
        {
          apply ELimInf_seq_ext_loc.
          exists 0%nat; intros ??.
          apply Rbar_NonnegExpectation_ext.
          apply eqq1.
        }

        generalize (fun n => Rbar_is_finite_expectation_isfe_minus1 _
                      (Rbar_pos_fun_part (fun x : Ts => M n x))
                      (fun x : Ts => M n x)); intros isfepos.
        
        cut (Rbar_lt
               (ELimInf_seq
                  (fun n : nat =>
                     Rbar_minus (Rbar_FiniteExpectation prts
                                            (Rbar_pos_fun_part (fun x : Ts => M n x)))
                                (Rbar_FiniteExpectation prts (fun x : Ts => M n x))))
               p_infty).
        {
          intros HH3.
          eapply Rbar_le_lt_trans; try apply HH3.
          apply refl_refl.
          apply ELimInf_seq_ext_loc.
          exists 0%nat; intros ??.
          simpl.
          replace (Rbar_FiniteExpectation prts (Rbar_pos_fun_part (fun x : Ts => M n x)) +
                  - Rbar_FiniteExpectation prts (fun x : Ts => M n x)) with
(Rbar_FiniteExpectation prts (Rbar_pos_fun_part (fun x : Ts => M n x))
                  - Rbar_FiniteExpectation prts (fun x : Ts => M n x)) by lra.
          rewrite <- (Rbar_FiniteExpectation_minus _ _ _).
          f_equal.
          apply Rbar_FiniteExpectation_ext; reflexivity.
        }
        cut (Rbar_lt
               (ELimInf_seq
                  (fun n : nat =>
                     Rbar_minus (Rbar_FiniteExpectation prts (Rbar_pos_fun_part (fun x : Ts => M n x)))
                                (Rbar_FiniteExpectation prts (fun x : Ts => M 0%nat x)))) p_infty).
        {
          intros HH3.
          eapply Rbar_le_lt_trans; try apply HH3.
          apply ELimInf_le.
          exists 0%nat; intros.
          unfold Rbar_minus.
          apply Rbar_plus_le_compat; try reflexivity.
          apply Rbar_opp_le.
          apply Rbar_le_Rle.
          generalize (is_sub_martingale_expectation prts M _ 0%nat n ltac:(lia)).
          unfold Rbar_FiniteExpectation, FiniteExpectation, proj1_sig.
          repeat match_destr.
          rewrite <- Expectation_Rbar_Expectation in e1, e2.
          congruence.
        } 

        cut (Rbar_lt
               (ELimInf_seq
                  (fun n : nat =>
                     Rbar_plus (Finite (Ropp (Rbar_FiniteExpectation prts (fun x : Ts => M 0 x))))
                                (Rbar_FiniteExpectation prts (Rbar_pos_fun_part (fun x : Ts => M n x))))) p_infty).
        {
          intros HH3.
          eapply Rbar_le_lt_trans; try apply HH3.
          apply ELimInf_le.
          exists 0%nat; intros.
          apply refl_refl.
          unfold Rbar_minus.
          now rewrite Rbar_plus_comm.
        }
        rewrite ELimInf_seq_const_plus.
        cut (Rbar_lt
               (ELimInf_seq
                  (fun n : nat =>
                     Rbar_FiniteExpectation prts (Rbar_pos_fun_part (fun x : Ts => M n x)))) p_infty).
        {
          destruct ((ELimInf_seq
                       (fun n : nat => Rbar_FiniteExpectation prts (Rbar_pos_fun_part (fun x : Ts => M n x)))))
          ; simpl; trivial.
        } 
        eapply Rbar_le_lt_trans; try apply ELimSup_ELimInf_seq_le.
        apply is_ELimSup_seq_unique in sup.
        eapply (Rbar_le_lt_trans _ (Finite K)); simpl; trivial.
        apply refl_refl.
        rewrite <- sup.
        apply ELimSup_seq_ext_loc.
        exists 0%nat; intros.
        rewrite NNExpectation_Rbar_NNExpectation.
        rewrite <- (Rbar_FiniteExpectation_Rbar_NonnegExpectation _ _).
        apply Rbar_NonnegExpectation_ext.
        intros ?.
        unfold Rbar_pos_fun_part, pos_fun_part; simpl.
        unfold Rbar_max, Rmax.
        repeat match_destr; simpl in *; lra.
      - generalize (upcrossing_var_lim_ex K sup).
        apply almost_impl; apply all_almost; intros ??.
        unfold Rbar_rvlim.
        now apply ELim_seq_correct.
    Qed.
        
  End mart_conv.

  Section mart_conv_sup.

    Local Existing Instance Rbar_le_pre.
    
    Context
      (M : nat -> Ts -> R) (sas : nat -> SigmaAlgebra Ts)
      {rv:forall n, RandomVariable dom borel_sa (M n)}
      {isfe:forall n, IsFiniteExpectation prts (M n)}
      {adapt:IsAdapted borel_sa M sas}
      {filt:IsFiltration sas}
      {sub:IsSubAlgebras dom sas}
      {mart:IsMartingale prts Rge M sas}.

    Theorem sup_martingale_convergence (K:R) :
      is_ELimSup_seq (fun n => NonnegExpectation (neg_fun_part (M n))) K ->
      RandomVariable dom Rbar_borel_sa (Rbar_rvlim M) /\
        Rbar_IsFiniteExpectation prts (Rbar_rvlim M) /\
          almost prts (fun omega => is_Elim_seq (fun n => M n omega) (Rbar_rvlim M omega)).
    Proof.
      intros.
      apply is_sub_martingale_neg in mart.
      destruct (martingale_convergence (fun n : nat => rvopp (M n)) sas K) as [? [??]].
      - revert H.
        apply is_ELimSup_seq_ext; intros.
        apply NonnegExpectation_ext; intros ?.
        rv_unfold; simpl.
        f_equal; lra.
      - repeat split; unfold Rbar_rvlim in *.
        + typeclasses eauto.
        + cut (Rbar_IsFiniteExpectation prts (Rbar_rvopp (Rbar_rvopp (fun x : Ts => ELim_seq (fun n : nat => M n x))))).
          {
            apply Rbar_IsFiniteExpectation_proper; intros ?.
            unfold Rbar_rvopp.
            now rewrite Rbar_opp_involutive.
          }
          apply Rbar_IsFiniteExpectation_opp; [typeclasses eauto |].
          revert H1.
          apply Rbar_IsFiniteExpectation_proper; intros ?.
          unfold Rbar_rvopp.
          rewrite <- (ELim_seq_opp (fun n : nat => M n a)); simpl.
          rv_unfold.
          apply ELim_seq_ext; intros.
          f_equal; lra.
        + revert H2.
          apply almost_impl; apply all_almost; intros ??.
          apply is_Elim_seq_opp.
          rewrite <- ELim_seq_opp.
          replace (ELim_seq (fun n : nat => Rbar_opp (M n x))) with
            (ELim_seq (fun n : nat => rvopp (M n) x)).
          * revert H2.
            apply is_Elim_seq_ext; intros.
            unfold Rbar_opp; rv_unfold; f_equal; lra.
          * apply ELim_seq_ext; intros.
            unfold Rbar_opp; rv_unfold; f_equal; lra.
    Qed.

    Corollary pos_sup_martingale_convergence :
      (forall n, NonnegativeFunction (M n)) ->
      RandomVariable dom Rbar_borel_sa (Rbar_rvlim M) /\
        Rbar_IsFiniteExpectation prts (Rbar_rvlim M) /\
          almost prts (fun omega => is_Elim_seq (fun n => M n omega) (Rbar_rvlim M omega)).
    Proof.
      intros.
      apply (sup_martingale_convergence 0).
      eapply is_ELimSup_seq_ext
      ; try apply is_ELimSup_seq_const; intros n; simpl.
      symmetry.
      rewrite <- (NonnegExpectation_const 0 ltac:(lra)).
      apply NonnegExpectation_ext; intros ?.
      unfold Rmax, const; match_destr.
      specialize (H n a).
      lra.
    Qed.

  End mart_conv_sup.

End mct.
