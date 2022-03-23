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

Section stopped_process.

  Local Open Scope R.
  Local Existing Instance Rge_pre.
  Local Existing Instance Rbar_le_pre.
  
  Context {Ts:Type}.

    Definition process_under (Y : nat -> Ts -> R) (T:Ts -> option nat) (x : Ts) : R
    := match T x with
       | None => 0
       | Some n => Y n x
       end.

    Definition lift1_min (x:nat) (y : option nat)
      := match y with
         | None => x
         | Some b => min x b
         end.
    
  Lemma lift1_lift2_min (x:nat) (y : option nat) :
    lift2_min (Some x) y = Some (lift1_min x y).
  Proof.
    destruct y; reflexivity.
  Qed.
  
  Definition process_stopped_at (Y : nat -> Ts -> R) (T:Ts -> option nat) (n:nat) (x : Ts) : R
    := Y (lift1_min n (T x)) x.

  Definition process_stopped_at_alt (Y : nat -> Ts -> R) (T:Ts -> option nat) (n:nat) : Ts -> R
    := match n with
       | 0%nat => Y 0%nat
       | S n =>
           rvplus
             (rvsum (fun t => rvmult
                             (Y t)
                             (EventIndicator (stopping_time_pre_event_dec T t))) n%nat)
             (rvmult
                (Y (S n))
                (EventIndicator
                   (classic_dec (pre_event_complement (stopping_time_pre_event_alt T n%nat)))))
       end.
       
  Lemma process_stopped_at_as_alt (Y : nat -> Ts -> R) (T:Ts -> option nat) :
    forall n, rv_eq (process_stopped_at Y T n) (process_stopped_at_alt Y T n).
  Proof.
    intros n ts.
    unfold process_stopped_at_alt, process_stopped_at.
    unfold lift1_min.
    rv_unfold; unfold rvsum.
    destruct n; match_option.
    - destruct (Min.min_dec (S n) n0).
      + assert (nle: (S n <= n0)%nat) by lia.
        rewrite e.
        rewrite (@Hierarchy.sum_n_ext_loc Hierarchy.R_AbelianGroup _ (fun _ => 0)).
        * rewrite sum_n_zero.
          field_simplify.
          match_destr; try lra.
          elim n1.
          unfold stopping_time_pre_event_alt, pre_event_complement.
          match_option; auto 2.
          assert (n2 = n0) by congruence.
          lia.
        * intros; match_destr; try lra.
          unfold stopping_time_pre_event in *.
          assert (n0 = n1) by congruence.
          lia.
      + rewrite e.
        assert (nle: (n0 <= S n)%nat) by lia.
        match_destr.
        * red in p.
          unfold stopping_time_pre_event_alt in p.
          rewrite eqq in p.
          assert (n0 = S n) by lia.
          subst.
          rewrite (@Hierarchy.sum_n_ext_loc Hierarchy.R_AbelianGroup _ (fun _ => 0)).
          -- rewrite sum_n_zero.
             lra.
          -- intros.
             match_destr; try lra.
             unfold stopping_time_pre_event in *.
             congruence.
        * field_simplify.
          unfold stopping_time_pre_event_alt, pre_event_complement in *.
          match_option_in n1; [| tauto].
          assert (n0 = n2) by congruence.
          subst.
          assert (n2 <= n)%nat by tauto.
          clear nle n1 eqq0 e.
          {
            induction n; simpl.
            - rewrite Hierarchy.sum_O.
              assert (n2 = 0)%nat by lia.
              subst.
              match_destr; try lra.
              elim n.
              now red.
            - rewrite Hierarchy.sum_Sn.
              destruct (le_lt_dec n2 n).
              + specialize (IHn l).
                rewrite <- IHn.
                unfold Hierarchy.plus; simpl.
                match_destr; try lra.
                unfold stopping_time_pre_event in s.
                assert (n2 = S n) by congruence.
                lia.
              + assert (n2 = S n) by lia.
                subst.
                rewrite (@Hierarchy.sum_n_ext_loc Hierarchy.R_AbelianGroup _ (fun _ => 0)).
                -- rewrite sum_n_zero.
                   unfold Hierarchy.plus; simpl.
                   match_destr; try lra.
                   unfold stopping_time_pre_event in n0; congruence.
                -- intros.
                   match_destr; try lra.
                   unfold stopping_time_pre_event in *.
                   assert (S n = n0) by congruence.
                   lia.
          } 
    - rewrite (@Hierarchy.sum_n_ext Hierarchy.R_AbelianGroup _ (fun _ => 0)).
      + rewrite sum_n_zero.
        field_simplify.
        match_destr; try lra.
        elim n0.
        unfold stopping_time_pre_event_alt, pre_event_complement.
        match_option; auto 2.
        congruence.
      + intros; match_destr; try lra.
        unfold stopping_time_pre_event in *; congruence.
  Qed.

  
End stopped_process.
