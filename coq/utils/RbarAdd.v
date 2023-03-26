Require Import Coquelicot.Coquelicot.
Require Import Reals.
Require Import LibUtils List Permutation RealAdd ClassicUtils ELim_Seq ListAdd Sums CoquelicotAdd Isomorphism PairEncoding.
Require Import Reals Psatz Morphisms.

Require Import Classical_Prop Classical_Pred_Type.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.

Section sums.

  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Definition list_Rbar_sum (l : list Rbar) : Rbar
    := fold_right Rbar_plus (Finite 0) l.
               
  Lemma list_Rbar_sum_const_mulR {A : Type} f (l : list A) :
    forall (r:R), list_Rbar_sum (map (fun x => Rbar_mult r (f x)) l)  =
              Rbar_mult r (list_Rbar_sum (map (fun x => f x) l)).
  Proof.
    intro r.
    induction l; simpl.
    - f_equal; lra.
    - rewrite IHl.
      now rewrite Rbar_mult_r_plus_distr.
  Qed.

  Definition sum_Rbar_n (f:nat->Rbar) (n:nat) : Rbar
    := list_Rbar_sum (map f (seq 0 n)).

  Global Instance sum_Rbar_n_proper : Proper (pointwise_relation _ eq ==> eq ==> eq) sum_Rbar_n.
  Proof.
    intros ??????.
    unfold sum_Rbar_n.
    f_equal; subst.
    now apply map_ext; intros.
  Qed.
  
  Instance fold_right_plus_le_proper :
    Proper (Rbar_le ==> Forall2 Rbar_le ==> Rbar_le) (fold_right Rbar_plus).
  Proof.
    intros a b eqq1 x y eqq2.
    revert a b eqq1.
    induction eqq2; simpl; trivial; intros.
    apply Rbar_plus_le_compat; trivial.
    now apply IHeqq2.
  Qed.

  Lemma Rbar_plus_nneg_compat (a b : Rbar) :
    Rbar_le 0 a ->
    Rbar_le 0 b ->
    Rbar_le 0 (Rbar_plus a b).
  Proof.
    generalize (Rbar_plus_le_compat  0 a 0 b); intros HH.
    rewrite Rbar_plus_0_r in HH.
    auto.
  Qed.

  Lemma Rbar_mult_nneg_compat (a b : Rbar) :
    Rbar_le 0 a ->
    Rbar_le 0 b ->
    Rbar_le 0 (Rbar_mult a b).
  Proof.
    destruct a; destruct b; simpl; rbar_prover.
    intros.
    generalize (Rmult_le_compat  0 r 0 r0); intros HH.
    rewrite Rmult_0_r in HH.
    apply HH; lra.
  Qed.

  Lemma Rbar_mult_0_lt (a b : Rbar) :
      Rbar_lt 0 a ->
      Rbar_lt 0 b ->
      Rbar_lt 0 (Rbar_mult a b).
    Proof.
      intros.
      destruct a; destruct b; try now simpl in *.
      - simpl in *.
        now apply Rmult_lt_0_compat.
      - simpl in H.
        now rewrite Rbar_mult_comm, Rbar_mult_p_infty_pos.
      - simpl in H0.
        now rewrite Rbar_mult_p_infty_pos.
    Qed.

  Lemma Rbar_le_incr0 (f : nat -> Rbar) :
    (forall n, Rbar_le (f n) (f (S n))) ->
    forall n k, (Rbar_le (f n) (f (n + k)%nat)).
  Proof.
    intros.
    induction k.
    - replace (n + 0)%nat with n by lia.
      apply Rbar_le_refl.
    - eapply Rbar_le_trans.
      apply IHk.
      replace (n + S k)%nat with (S (n + k)%nat) by lia.
      apply H.
  Qed.

  Lemma Rbar_le_incr (f : nat -> Rbar) :
    (forall n, Rbar_le (f n) (f (S n))) ->
    forall n m, (n<=m)%nat -> Rbar_le (f n) (f m).
  Proof.
    intros.
    replace (m) with (n + (m-n))%nat by lia.
    now apply Rbar_le_incr0.
  Qed.

  Lemma sum_Rbar_n_pos_incr (f : nat -> Rbar) :
    (forall i : nat, Rbar_le 0 (f i)) ->
    forall n : nat, Rbar_le (sum_Rbar_n f n) (sum_Rbar_n f (S n)).
  Proof.
    unfold sum_Rbar_n, list_Rbar_sum; intros.
    rewrite seq_Sn, map_app, fold_right_app.
    apply fold_right_plus_le_proper; try reflexivity.
    simpl.
    apply Rbar_plus_nneg_compat; trivial.
    reflexivity.
  Qed.

  Lemma list_Rbar_sum_nneg_nneg (l:list Rbar) :
    (forall x, In x l -> Rbar_le 0 x) ->
    Rbar_le 0 (list_Rbar_sum l).
  Proof.
    intros.
    induction l; [reflexivity |].
    simpl list_Rbar_sum.
    apply Rbar_plus_nneg_compat.
    - apply H; simpl; tauto.
    - apply IHl; intros.
      apply H; simpl; tauto.
  Qed.

  Lemma sum_Rbar_n_nneg_nneg (f : nat -> Rbar) n :
    (forall i : nat, (i <= n)%nat -> Rbar_le 0 (f i)) ->
    Rbar_le 0 (sum_Rbar_n f n).
  Proof.
    intros.
    apply list_Rbar_sum_nneg_nneg; intros.
    apply in_map_iff in H0.
    destruct H0 as [? [??]]; subst.
    apply in_seq in H1.
    apply H; lia.
  Qed.

  Lemma nneg_fold_right_Rbar_plus_nneg l :
        Forall (Rbar_le 0) l ->
        Rbar_le 0 (fold_right Rbar_plus 0 l).
  Proof.
    induction l.
    - simpl; reflexivity.
    -  simpl map; simpl fold_right.
       intros HH; invcs HH.
       apply Rbar_plus_nneg_compat; auto.
  Qed.

  Lemma list_Rbar_sum_nneg_perm (l1 l2:list Rbar) :
    Forall (Rbar_le 0) l1 ->
    Forall (Rbar_le 0) l2 ->
    Permutation l1 l2 ->
    list_Rbar_sum l1 = list_Rbar_sum l2.
  Proof.
    intros.
    unfold list_Rbar_sum.
    induction H1; simpl; trivial.
    - invcs H; invcs H0; now rewrite IHPermutation.
    - invcs H; invcs H0; invcs H4; invcs H5.
      repeat rewrite <- Rbar_plus_assoc
      ; try apply ex_Rbar_plus_pos; trivial
      ; try apply nneg_fold_right_Rbar_plus_nneg
      ; trivial.
      f_equal.
      now rewrite Rbar_plus_comm.
    - assert (Forall (Rbar_le 0) l')
        by now rewrite <- H1_.
      now rewrite IHPermutation1, IHPermutation2.
  Qed.

  Lemma nneg_fold_right_Rbar_plus_acc l acc :
    Rbar_le 0 acc ->
    Forall (Rbar_le 0) l ->    
    fold_right Rbar_plus acc l = Rbar_plus acc (fold_right Rbar_plus (Finite 0) l).
  Proof.
    intros pos1 pos2; revert pos1.
    induction pos2; intros.
    - now rewrite Rbar_plus_0_r.
    - simpl.
      rewrite IHpos2; trivial.
      repeat rewrite <- Rbar_plus_assoc_nneg; trivial
      ; try now apply nneg_fold_right_Rbar_plus_nneg.
      f_equal.
      apply Rbar_plus_comm.
  Qed.

  Lemma list_Rbar_sum_nneg_plus (l1 l2 : list Rbar) :
    Forall (Rbar_le 0) l1 ->
    Forall (Rbar_le 0) l2 ->
    list_Rbar_sum (l1 ++ l2) =
      Rbar_plus (list_Rbar_sum l1) (list_Rbar_sum l2).
  Proof.
    intros.
    unfold list_Rbar_sum.
    rewrite fold_right_app.
    rewrite nneg_fold_right_Rbar_plus_acc; trivial
    ; try now apply nneg_fold_right_Rbar_plus_nneg.
    now rewrite Rbar_plus_comm.
  Qed.    

  Lemma sum_Rbar_n_nneg_plus (f g:nat->Rbar) (n:nat) :
    (forall x, (x < n)%nat -> Rbar_le 0 (f x)) ->
    (forall x, (x < n)%nat -> Rbar_le 0 (g x)) ->
      sum_Rbar_n (fun x => Rbar_plus (f x) (g x)) n =
        Rbar_plus (sum_Rbar_n f n) (sum_Rbar_n g n).
  Proof.
    unfold sum_Rbar_n; intros.
    induction n; [simpl; f_equal; lra | ].
    rewrite seq_Sn.
    rewrite plus_0_l.

    repeat rewrite map_app.
    repeat rewrite list_Rbar_sum_nneg_plus; simpl
    ; try solve [apply Forall_forall; intros ? HH
                 ; apply in_map_iff in HH
                 ; destruct HH as [? [? HH]]; subst
                 ; apply in_seq in HH
                 ; try apply Rbar_plus_nneg_compat
                 ; try (apply H || apply H0); lia
                |
                  repeat constructor
                  ; try apply Rbar_plus_nneg_compat
                  ; try (apply H || apply H0); lia].
    rewrite IHn
    ; intros; try solve [(apply H || apply H0); lia].
    repeat rewrite Rbar_plus_0_r.
    repeat rewrite <- Rbar_plus_assoc_nneg
    ; trivial
    ; try apply Rbar_plus_nneg_compat
    ; (try solve [
            try (apply list_Rbar_sum_nneg_nneg
                 ; intros ? HH
                 ; apply in_map_iff in HH
                 ; destruct HH as [? [? HH]]; subst
                 ; apply in_seq in HH)
            ; try (apply H || apply H0); lia]).
    f_equal.
    repeat rewrite Rbar_plus_assoc_nneg
    ; trivial
    ; (try solve [
            try (apply list_Rbar_sum_nneg_nneg
                 ; intros ? HH
                 ; apply in_map_iff in HH
                 ; destruct HH as [? [? HH]]; subst
                 ; apply in_seq in HH)
            ; try (apply H || apply H0); lia]).
    f_equal.
    apply Rbar_plus_comm.
  Qed.      

  Lemma fold_right_Rbar_plus_const {A} c (l:list A) :
    fold_right Rbar_plus 0 (map (fun _ => c) l) = (Rbar_mult (INR (length l)) c).
  Proof.
    induction l; intros.
    - simpl.
      now rewrite Rbar_mult_0_l.
    - simpl length.
      rewrite S_INR; simpl.
      rewrite IHl.
      generalize (pos_INR (length l)); intros HH.
      destruct c; simpl; rbar_prover.
  Qed.

  Lemma seq_sum_list_sum {T}
        (f:T -> Rbar) (B:list T) d :
    f d = 0 ->
    ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => f (nth n B d)) i) = list_Rbar_sum (map f B).
  Proof.
    intros.
    rewrite (ELim_seq_ext_loc _ (fun _ => sum_Rbar_n (fun n : nat => f (nth n B d)) (length B))).
    - rewrite ELim_seq_const.
      unfold sum_Rbar_n.
      f_equal.
      now rewrite <- map_map, <- list_as_nthseq.
    - exists (length B); intros.
      unfold sum_Rbar_n.
      replace n with (length B + (n - length B))%nat by lia.
      rewrite seq_plus.
      unfold list_Rbar_sum.
      rewrite map_app, fold_right_app.
      f_equal.
      rewrite (seq_shiftn_map (length B)).
      rewrite map_map.
      rewrite (map_ext
                 (fun x : nat => f (nth (length B + x) B d ))
                 (fun x : nat => 0)).
      + rewrite fold_right_Rbar_plus_const.
        now rewrite Rbar_mult_0_r.
      + intros ?.
        rewrite nth_overflow; trivial.
        lia.
  Qed.

    Global Instance list_Rbar_sum_monotone : Proper (Forall2 Rbar_le ==> Rbar_le) list_Rbar_sum.
  Proof.
    intros ???.
    induction H; simpl.
    - reflexivity.
    - now apply Rbar_plus_le_compat.
  Qed.
    
  Global Instance sum_Rbar_n_monotone : Proper (pointwise_relation _ Rbar_le ==> eq ==> Rbar_le) sum_Rbar_n.
  Proof.
    intros ??????; subst.
    apply list_Rbar_sum_monotone.
    apply Forall2_map_f.
    apply Forall2_refl_in.
    apply Forall_forall; intros.
    apply H.
  Qed.

  Lemma list_Rbar_sum_map_finite (l:list R) : list_Rbar_sum (map Finite l) = list_sum l.
  Proof.
    unfold list_Rbar_sum.
    induction l; simpl; trivial.
    now rewrite IHl; simpl.
  Qed.

End sums.

Section rbar_empty_props.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

    (** * Extended Emptiness is decidable *)

  Definition Rbar_Empty (E : Rbar -> Prop) :=
    Rbar_glb (fun x => x = 0 \/ E x) = Rbar_lub (fun x => x = 0 \/ E x)
    /\ Rbar_glb (fun x => x = 1 \/ E x) = Rbar_lub (fun x => x = 1 \/ E x).

  Lemma Rbar_Empty_correct_1 (E : Rbar -> Prop) :
    Rbar_Empty E -> forall x, ~ E x.
  Proof.
    intros.
    unfold Rbar_Empty, Rbar_glb, Rbar_lub, proj1_sig in *.
    repeat match_destr_in H.
    destruct H; subst.
    unfold Rbar_is_glb, Rbar_is_lub in *.
    intuition.
    assert (x1 = 0)
      by (apply Rbar_le_antisym; eauto).
    assert (x3 = 1)
      by (apply Rbar_le_antisym; eauto).
    subst.
    specialize (H2 x).
    cut_to H2; [| tauto].
    specialize (H4 x).
    cut_to H4; [| tauto].
    generalize (Rbar_le_trans _ _ _ H4 H2); simpl; lra.
  Qed.

  Lemma Rbar_Empty_correct_2 (E : Rbar -> Prop) :
    (forall x, ~ E x) -> Rbar_Empty E.
  Proof.
    intros H.
    unfold Rbar_Empty, Rbar_glb, Rbar_lub, proj1_sig in *.
    repeat match_destr.
    unfold Rbar_is_glb, Rbar_is_lub in *.
    destruct r; destruct r0; destruct r1; destruct r2.
    assert (x = Finite 0).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H1; intros ?[]; subst; [reflexivity | eelim H; eauto].
    }
    assert (x0 = Finite 0).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H3; intros ?[]; subst; [reflexivity | eelim H; eauto].
    } 
    assert (x1 = Finite 1).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H5; intros ?[]; subst; [reflexivity | eelim H; eauto].
    } 
    assert (x2 = Finite 1).
    {
      apply Rbar_le_antisym; eauto 3.
      apply H7; intros ?[]; subst; [reflexivity | eelim H; eauto].
    }
    split; congruence.
  Qed.

  Lemma Rbar_Empty_dec (E : Rbar -> Prop) :
    {~Rbar_Empty E}+{Rbar_Empty E}.
  Proof.
    unfold Rbar_Empty.
    destruct (Rbar_eq_dec (Rbar_glb (fun x => x = 0 \/ E x)) (Rbar_lub (fun x => x = 0 \/ E x))).
    - destruct (Rbar_eq_dec (Rbar_glb (fun x => x = 1 \/ E x)) (Rbar_lub (fun x => x = 1 \/ E x))).
      + right; tauto.
      + left; tauto.
    - left; tauto.
  Defined.

  Lemma not_Rbar_Empty_dec (E : Rbar -> Prop) : (Decidable.decidable (exists x, E x)) ->
                                        {(exists x, E x)} + {(forall x, ~ E x)}.
  Proof.
    intros.
    destruct (Rbar_Empty_dec E).
    - left.
      destruct H; trivial.
      contradict n.
      apply Rbar_Empty_correct_2; intros ??.
      apply H; eauto.
    - right; intros.
      now apply Rbar_Empty_correct_1.
  Qed.      

  Lemma Rbar_uniqueness_dec P : (exists ! x : Rbar, P x) -> {x : Rbar | P x}.
  Proof.
    intros HH.
    exists (Rbar_lub P).
    destruct HH as [? [??]].
    replace (Rbar_lub P) with x; trivial.
    apply sym_eq, Rbar_is_lub_unique.
    split.
    - intros ??.
      rewrite (H0 _ H1); apply Rbar_le_refl.
    - firstorder.
  Qed.

End rbar_empty_props.

Section rbar_props.
  
  Lemma is_finite_dec (a:Rbar) : {is_finite a} + {~ is_finite a}.
  Proof.
    unfold is_finite; destruct a; simpl; intuition congruence.
  Qed.

(*
  Lemma Rle_forall_le: forall a b : R, (forall eps : posreal, a <= b + eps) -> a <= b.
  Proof.
    intros.
    apply Rlt_forall_le; intros.
    specialize (H (pos_div_2 eps)).
    simpl in H.
    eapply Rle_lt_trans; try eapply H.
    destruct eps; simpl.
    lra.
  Qed.

  Lemma Rbar_le_forall_Rbar_le: forall a b : Rbar, (forall eps : posreal, Rbar_le a (Rbar_plus b eps)) -> Rbar_le a b.
  Proof.
    intros [] []; simpl; intros HH; trivial
    ; try (apply HH; exact posreal1).
    now apply Rle_forall_le.
  Qed.

 *)
  Lemma Rbar_glb_ge (E:Rbar->Prop) c :
    (forall x, E x -> Rbar_le c x) ->
    Rbar_le c (Rbar_glb E).
  Proof.
    unfold Rbar_glb, proj1_sig; match_destr; intros.
    apply r; intros ??.
    now apply H.
  Qed.

End rbar_props.

Section glb_props.

  Lemma Rbar_is_glb_fin_close_classic {E a} (eps:posreal):
    Rbar_is_glb E (Finite a) -> exists x, E x /\ Rbar_le x (a + eps).
  Proof.
    intros HH1.
    apply NNPP; intros HH2.
    generalize (not_ex_all_not _ _ HH2); intros HH3.
    assert (Rbar_is_glb E (Finite (a + eps))).
    {
      destruct HH1.
      split.
      - intros ??.
        specialize (H _ H1).
        specialize (HH3 x).
        intuition.
        apply Rbar_not_le_lt in H3.
        now apply Rbar_lt_le.
      - intros.
        eapply Rbar_le_trans; try now eapply H0.
        simpl.
        destruct eps; simpl; lra.
    }
    apply Rbar_is_glb_unique in HH1.
    apply Rbar_is_glb_unique in H.
    rewrite H in HH1.
    invcs HH1.
    destruct eps; simpl in *; lra.
  Qed.

End glb_props.
  
Section elim_seq_props.
  Local Existing Instance Rbar_le_pre.
  Local Existing Instance Rbar_le_part.

  Lemma ELim_seq_nneg (f : nat -> Rbar) :
    (forall n, Rbar_le 0 (f n)) ->
    Rbar_le 0 (ELim_seq f).
  Proof.
    intros.
    generalize (ELim_seq_le (fun _ => 0) f); intros.
    rewrite ELim_seq_const in H0.
    now apply H0.
  Qed.

    Lemma Elim_seq_sum_pos_fin_n_fin f r :
    (forall n, Rbar_le 0 (f n)) ->
    ELim_seq
        (fun i : nat => sum_Rbar_n f i) = Finite r ->
    forall n, is_finite (f n).
  Proof.
    intros.
    generalize (ELim_seq_nneg _ H); intros nneglim.
    case_eq (f n); intros; simpl; [reflexivity |..].
    - assert (HH:Rbar_le (ELim_seq (fun _ => sum_Rbar_n f (S n))) (ELim_seq (fun i : nat => sum_Rbar_n f i))).
      {
        apply ELim_seq_le_loc.
        exists (S n); intros.
        apply (le_ind (S n) (fun x => Rbar_le (sum_Rbar_n f (S n)) (sum_Rbar_n f x))); trivial.
        - reflexivity.
        - intros.
          eapply Rbar_le_trans; try eapply H4.
          apply sum_Rbar_n_pos_incr; trivial.
      }
      rewrite ELim_seq_const in HH.
      rewrite H0 in HH.
      
      unfold sum_Rbar_n in HH.
      rewrite seq_Sn, map_app in HH; simpl in HH.
      rewrite H1 in HH.
      erewrite list_Rbar_sum_nneg_perm in HH
      ; try eapply Permutation_app_comm.
      + simpl in HH.
        unfold Rbar_plus in HH; simpl in HH.
        assert (Rbar_le 0 (list_Rbar_sum (map f (seq 0 n)))).
        {
          apply list_Rbar_sum_nneg_nneg; intros.
          apply in_map_iff in H2.
          now destruct H2 as [?[??]]; subst.
        }
        destruct (list_Rbar_sum (map f (seq 0 n))); simpl in HH
        ; try contradiction.
      + apply List.Forall_app; split.
        * apply Forall_map; apply Forall_forall; intros; trivial.
        * repeat constructor.
      + apply List.Forall_app; split.
        * repeat constructor.
        * apply Forall_map; apply Forall_forall; intros; trivial.
    - specialize (H n).
      rewrite H1 in H.
      simpl in H.
      contradiction.
  Qed.

  Lemma Lim_seq_sum_2n2 : Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ x) (seq 0 n))) = 2.
  Proof.
    generalize (is_series_geom (1/2))
    ; intros HH.
    cut_to HH; [| rewrite Rabs_pos_eq; lra].
    apply is_series_Reals in HH.
    apply infinite_sum_is_lim_seq in HH.
    replace (/ (1 - 1 / 2)) with 2 in HH by lra.
    apply is_lim_seq_unique in HH.
    erewrite Lim_seq_ext in HH
    ; [| intros; rewrite <- sum_f_R0_sum_f_R0'; reflexivity].
    erewrite Lim_seq_ext in HH
    ; [| intros; rewrite <- sum_f_R0'_list_sum; reflexivity].
    rewrite <- Lim_seq_incr_1.
    rewrite <- HH.
    apply Lim_seq_ext; intros.
    f_equal.
    apply map_ext; intros.
    replace (1/2) with (/2) by lra.
    rewrite Rinv_pow; try lra.
  Qed.

  Lemma Lim_seq_sum_2n : Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ (S x)) (seq 0 n))) = 1.
  Proof.
    transitivity (Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ x) (seq 1 n)))).
    - apply Lim_seq_ext; intros.
      now rewrite <- seq_shift, map_map.
    - generalize (Lim_seq_sum_2n2); intros HH.
      rewrite <- Lim_seq_incr_1 in HH.
      erewrite Lim_seq_ext in HH
      ; [| intros; rewrite <- cons_seq; simpl; reflexivity].
      rewrite Lim_seq_plus in HH.
      + rewrite Lim_seq_const in HH.
        rewrite Rinv_1 in HH.
        destruct (Lim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ x) (seq 1 n)))); simpl in *
        ; invcs HH; try lra.
        f_equal; lra.
      + apply ex_lim_seq_const.
      + apply ex_lim_seq_incr; intros.
        rewrite seq_Sn, map_app, list_sum_cat.
        simpl.
        assert (0 < (/ (2 * 2 ^ n))).
        {
          intros.
          apply Rinv_pos.
          generalize (pow_lt 2 n); lra.
        }
        lra.
      + apply ex_Rbar_plus_pos.
        * rewrite Lim_seq_const; simpl; lra.
        * apply Lim_seq_pos; intros.
          apply list_sum_pos_pos'.
          apply Forall_map.
          apply Forall_forall; intros.
          left.
          apply Rinv_pos.
          apply pow_lt; lra.
  Qed.

  Lemma ELim_seq_sum_2n : ELim_seq (fun n : nat => list_sum (map (fun x : nat => / 2 ^ (S x)) (seq 0 n))) = 1.
  Proof.
    rewrite Elim_seq_fin.
    apply Lim_seq_sum_2n.
  Qed.


  Lemma ELim_seq_Rbar_sum_2n :
    ELim_seq (sum_Rbar_n (fun x : nat => Finite (/ 2 ^ (S x)))) = 1.
  Proof.
    unfold sum_Rbar_n.
    erewrite ELim_seq_ext
    ; [| intros ?; rewrite <- map_map; rewrite list_Rbar_sum_map_finite; reflexivity].
    apply ELim_seq_sum_2n.
  Qed.
    
  Lemma ELim_seq_sum_eps2n f eps :
    (0 <= eps) ->
    (forall x, Rbar_le 0 (f x)) ->
    ELim_seq (fun i => sum_Rbar_n (fun a => Rbar_plus (f a) (eps / 2 ^ (S a))) i) =
      Rbar_plus (ELim_seq (fun i => sum_Rbar_n f i)) eps.
  Proof.
    intros.
    assert (epsdivpos:forall i, 0 <= (eps / (2 * 2 ^ i))).
    {
      intros.
      apply Rdiv_le_0_compat; trivial.
      apply Rmult_lt_0_compat; try lra.
      apply pow_lt; lra.
    } 

    erewrite ELim_seq_ext
    ; [| intros; rewrite sum_Rbar_n_nneg_plus; [reflexivity |..]]
    ; trivial.
    - rewrite ELim_seq_plus.
      + f_equal.
        rewrite (ELim_seq_ext _ (sum_Rbar_n (fun x : nat => Rbar_mult eps (/ 2 ^ (S x))))) by reflexivity.
        unfold sum_Rbar_n.
        erewrite ELim_seq_ext
        ; [| intros; apply list_Rbar_sum_const_mulR].
        generalize ELim_seq_Rbar_sum_2n.
        unfold sum_Rbar_n; intros HH.
        rewrite ELim_seq_scal_l.
        * rewrite HH.
          now rewrite Rbar_mult_1_r.
        * now rewrite HH.
      + apply ex_Elim_seq_incr; intros.
        now apply sum_Rbar_n_pos_incr.
      + apply ex_Elim_seq_incr; intros.
        apply sum_Rbar_n_pos_incr; intros; simpl; trivial.
      + apply ex_Rbar_plus_pos
        ; apply ELim_seq_nneg
        ; intros
        ; apply sum_Rbar_n_nneg_nneg
        ; intros
        ; trivial
        ; simpl
        ; trivial.
    - intros; simpl; trivial.
  Qed.

  Lemma ELim_seq_sup_incr (f : nat -> Rbar) :
    (forall n, Rbar_le (f n) (f (S n))) ->
    ELim_seq f = ELimSup_seq f.
  Proof.
    intros.
    unfold ELim_seq.
    apply ex_Elim_seq_incr in H.
    unfold ex_Elim_seq in H.
    rewrite <- H.
    destruct (ELimSup_seq f); simpl; try congruence.
    apply Rbar_finite_eq.
    lra.
  Qed.

  Lemma Elim_seq_le_bound (f : nat -> Rbar) (B:Rbar) :
    (forall n, Rbar_le (f n) B) ->
    Rbar_le (ELim_seq f) B.
  Proof.
    intros.
    replace B with (ELim_seq (fun _ => B)).
    now apply ELim_seq_le.
    apply ELim_seq_const.
  Qed.

  Lemma sum_Rbar_n_Sn (f : nat -> Rbar) (n : nat) :
    (forall n, Rbar_le 0 (f n)) ->
    sum_Rbar_n f (S n) = Rbar_plus (sum_Rbar_n f n) (f n).
  Proof.
    intros.
    unfold sum_Rbar_n.
    rewrite seq_Sn; simpl.
    rewrite map_app.
    rewrite list_Rbar_sum_nneg_plus.
    - simpl.
      now rewrite Rbar_plus_0_r.
    - now apply Forall_map; apply Forall_forall; intros.
    - now apply Forall_map; apply Forall_forall; intros.
  Qed.
  
  Lemma sum_Rbar_n_pos_Sn (f : nat -> Rbar) (n : nat) :
    (forall n, Rbar_le 0 (f n)) ->
    Rbar_le (sum_Rbar_n f n) (sum_Rbar_n f (S n)).
  Proof.
    intros.
    replace (sum_Rbar_n f n) with (Rbar_plus (sum_Rbar_n f n) 0).
    - rewrite sum_Rbar_n_Sn; trivial.
      apply Rbar_plus_le_compat.
      + apply Rbar_le_refl.
      + apply H.
    - now rewrite Rbar_plus_0_r.
  Qed.

End elim_seq_props.

Section lim_sum.

    Lemma list_Rbar_sum_cat (l1 l2 : list Rbar) :
    (forall x1, In x1 l1 -> Rbar_le 0 x1) ->
    (forall x2, In x2 l2 -> Rbar_le 0 x2) ->    
    list_Rbar_sum (l1 ++ l2) = Rbar_plus (list_Rbar_sum l1) (list_Rbar_sum l2).
  Proof.
    induction l1.
    * simpl.
      now rewrite Rbar_plus_0_l.
    * intros.
      simpl.
      rewrite IHl1; trivial.
      -- rewrite Rbar_plus_assoc_nneg; trivial.
         ++ apply H.
            simpl.
            now left.
         ++ apply list_Rbar_sum_nneg_nneg.
            intros.
            apply H.
            now apply in_cons.
         ++ apply list_Rbar_sum_nneg_nneg.
            intros.
            now apply H0.
      -- intros; apply H.
         now apply in_cons.
   Qed.

  
 Lemma list_Rbar_sum_nneg_nested_prod {A B:Type} (X:list A) (Y:list B) (f:A->B->Rbar) :
    (forall x y, In x X -> In y Y -> Rbar_le 0 (f x y)) ->
    list_Rbar_sum (map (fun x => list_Rbar_sum (map (fun y => f x y) Y)) X) =
    list_Rbar_sum (map (fun xy => f (fst xy) (snd xy)) (list_prod X Y)).
   Proof.
     intros.
     induction X.
     - simpl.
       induction Y.
       + now simpl.
       + reflexivity.
     - simpl.
       rewrite IHX, map_app, list_Rbar_sum_cat.
       + f_equal.
         now rewrite map_map.
       + intros.
         rewrite in_map_iff in H0.
         destruct H0 as [[? ?] [? ?]].
         rewrite <- H0.
         apply in_map_iff in H1.
         destruct H1 as [? [? ?]].
         inversion H1.
         apply H.
         * simpl; now left.
         * now rewrite <- H5.
       + intros.
         rewrite in_map_iff in H0.
         destruct H0 as [[? ?] [? ?]].
         rewrite <- H0.
         rewrite in_prod_iff in H1.
         apply H.
         * now apply in_cons.
         * easy.
       + intros.
         apply H; trivial.
         now apply in_cons.
    Qed.

   Lemma list_Rbar_sum_nest_prod (f : nat -> nat -> Rbar ) (l1 l2 : list nat) :
    (forall a b, Rbar_le 0 (f a b)) ->
     list_Rbar_sum
       (map (fun i : nat => list_Rbar_sum (map (fun j : nat => f i j) l2)) l1) =
     list_Rbar_sum (map (fun '(a, b) => f a b) (list_prod l1 l2)).
   Proof.
     intros.
     induction l1.
     - simpl.
       induction l2.
       + now simpl.
       + reflexivity.
     - simpl.
       rewrite IHl1, map_app, list_Rbar_sum_cat.
       + f_equal.
         now rewrite map_map.
       + intros.
         rewrite in_map_iff in H0.
         destruct H0 as [[? ?] [? ?]].
         now rewrite <- H0.
       + intros.
         rewrite in_map_iff in H0.
         destruct H0 as [[? ?] [? ?]].
         now rewrite <- H0.
    Qed.

   Lemma sum_Rbar_n_pair_list_sum (f : nat -> nat -> Rbar ) (n m : nat) :
    (forall a b, Rbar_le 0 (f a b)) ->
     sum_Rbar_n (fun x0 => sum_Rbar_n (fun n1 => f x0 n1) m) n = 
     list_Rbar_sum (map (fun '(a, b) => f a b) (list_prod (seq 0 n) (seq 0 m))).
   Proof.
     intros.
     unfold sum_Rbar_n.
     apply list_Rbar_sum_nest_prod.
     apply H.
   Qed.

Lemma list_Rbar_sum_pos_sublist_le (l1 l2 : list Rbar) :
  (forall x, In x l2 -> Rbar_le 0 x) ->
  sublist l1 l2 ->
  Rbar_le (list_Rbar_sum l1) (list_Rbar_sum l2).
Proof.
  intros pos subl.
  induction subl.
  - simpl.
    lra.
  - simpl.
    apply Rbar_plus_le_compat.
    + apply Rbar_le_refl.
    + apply IHsubl.
      intros.
      apply pos.
      simpl; now right.
  - simpl.
    replace (list_Rbar_sum l1) with (Rbar_plus 0 (list_Rbar_sum l1)) by now rewrite Rbar_plus_0_l.
    apply Rbar_plus_le_compat.
    + apply pos.
      simpl.
      now left.
    + eapply IHsubl.
      intros.
      apply pos.
      simpl; now right.
Qed.

  Lemma bound_iso_f_pairs_sum_Rbar (f :nat -> nat -> Rbar) (n0 n : nat) :
    (forall a b, Rbar_le 0 (f a b)) ->
    exists (x : nat),
      Rbar_le (sum_Rbar_n (fun x0 : nat => sum_Rbar_n (fun n1 : nat => f x0 n1) n0) n)
              (sum_Rbar_n (fun n1 : nat => let '(a, b) := iso_b n1 in f a b) x).
  Proof.
    intros.
    destruct (pair_encode_contains_square (max n0 n)).    
    exists (S x).
    rewrite sum_Rbar_n_pair_list_sum; trivial.

    assert (subl:exists l, Permutation (list_prod (seq 0 n) (seq 0 n0)) l /\
                        sublist l (map iso_b (seq 0 (S x)))).
    {
      apply incl_NoDup_sublist_perm.
      - apply NoDup_prod
        ; apply seq_NoDup.
      - intros [??] ?.
        apply in_prod_iff in H1.
        apply in_map_iff.
        exists (iso_f (n1,n2)).
        split.
        + now rewrite iso_b_f.
        + apply in_seq.
          split; [lia |].
          rewrite plus_0_l.
          apply le_lt_n_Sm.
          destruct H1.
          apply in_seq in H1.
          apply in_seq in H2.
          apply H0; lia.
    } 

    destruct subl as [?[??]].
    apply (Permutation_map (fun '(a, b) => f a b)) in H1.
    apply (sublist_map (fun '(a, b) => f a b)) in H2.

    rewrite (list_Rbar_sum_nneg_perm
               (map (fun '(a, b) => f a b) (list_prod (seq 0 n) (seq 0 n0)))
               (map (fun '(a, b) => f a b) x0)); trivial.
    - apply list_Rbar_sum_pos_sublist_le.
      + intros.
        apply in_map_iff in H3.
        destruct H3 as [?[??]].
        subst.
        match_destr.
      + now rewrite map_map in H2.
    - apply Forall_map.
      now apply Forall_forall; intros [??] ?.
    - apply Forall_map.
      now apply Forall_forall; intros [??] ?.
  Qed.
        
  Lemma bound_pair_iso_b_sum_Rbar (f : nat -> nat -> Rbar) (x : nat) :

    (forall a b, Rbar_le 0 (f a b)) ->
    exists (n : nat),
      Rbar_le (sum_Rbar_n (fun n1 : nat => let '(a, b) := iso_b n1 in f a b) x)
              (sum_Rbar_n (fun x0 : nat => sum_Rbar_n (fun n1 : nat => f x0 n1) n) n).
  Proof.
    intros.
    destruct (square_contains_pair_encode x) as [n ?].
    exists (S n).
    rewrite sum_Rbar_n_pair_list_sum; trivial.
    unfold sum_Rbar_n.

    assert (subl:exists l, Permutation (map iso_b (seq 0 x)) l /\
                        sublist l (list_prod (seq 0 (S n)) (seq 0 (S n)))).
    {
      apply incl_NoDup_sublist_perm.
      - apply iso_b_nodup.
        apply seq_NoDup.
      - intros [??] ?.
        apply in_map_iff in H1.
        apply in_prod_iff.
        destruct H1 as [?[??]].
        apply in_seq in H2.
        specialize (H0 x0).
        cut_to H0; try lia.
        rewrite H1 in H0.
        split; apply in_seq; lia.
    } 

    destruct subl as [?[??]].
    apply (Permutation_map (fun '(a, b) => f a b)) in H1.
    apply (sublist_map (fun '(a, b) => f a b)) in H2.

    rewrite (list_Rbar_sum_nneg_perm
               (map (fun n1 : nat => let '(a, b) := iso_b n1 in f a b) (seq 0 x))
               (map (fun '(a, b) => f a b) x0)
             ); trivial.
    - apply list_Rbar_sum_pos_sublist_le; trivial.
      intros.
      apply in_map_iff in H3.
      destruct H3 as [?[??]].
      subst.
      match_destr.
    - apply Forall_map.
      apply Forall_forall; intros; match_destr.
    - apply Forall_map.
      apply Forall_forall; intros; match_destr.
    - rewrite <- H1.
      now rewrite map_map.
  Qed.

  Lemma Elim_seq_incr_elem (f : nat -> Rbar) :
    (forall n, Rbar_le (f n) (f (S n))) ->
    forall n, Rbar_le (f n) (ELim_seq f).
  Proof.
    intros.
    replace (f n) with (ELim_seq (fun _ => f n)) by now rewrite ELim_seq_const.
    apply ELim_seq_le_loc.
    exists n.
    intros.
    pose (h := (n0-n)%nat).
    replace (n0) with (h + n)%nat by lia.
    induction h.
    - replace (0 + n)%nat with n by lia.
      apply Rbar_le_refl.
    - eapply Rbar_le_trans.
      + apply IHh.
      + replace (S h + n)%nat with (S (h+n))%nat by lia.
        apply H.
  Qed.

  (* Fubini for nonnegative extended reals *)
  Lemma ELim_seq_Elim_seq_pair (f:nat->nat->Rbar) :
    (forall a b, Rbar_le 0 (f a b)) ->
    ELim_seq
      (fun i : nat =>
         sum_Rbar_n (fun x0 : nat => ELim_seq (fun i0 : nat => sum_Rbar_n (fun n : nat => (f x0 n)) i0)) i) =
      ELim_seq (fun i : nat => sum_Rbar_n (fun n : nat => let '(a, b) := iso_b (Isomorphism:=nat_pair_encoder) n in (f a b)) i).
  Proof.
    intros.
    apply Rbar_le_antisym.
    - apply Elim_seq_le_bound; intros.
      replace (sum_Rbar_n
                 (fun x0 : nat =>
                    ELim_seq 
                      (fun i0 : nat => sum_Rbar_n (fun n0 : nat => f x0 n0) i0)) n)
              with
                (ELim_seq (fun i0 =>
                             (sum_Rbar_n (fun x0 =>
                                            (sum_Rbar_n (fun n0 => f x0 n0) i0)) n))).
      + apply Elim_seq_le_bound; intros.
        destruct (bound_iso_f_pairs_sum_Rbar f n0 n).
        apply H.
        eapply Rbar_le_trans.
        * apply H0.
        * apply Elim_seq_incr_elem; intros.
          apply sum_Rbar_n_pos_Sn; intros.
          now destruct (iso_b n2).
      + symmetry.
        induction n.
        * unfold sum_Rbar_n.
          simpl.
          now rewrite ELim_seq_const.
        * rewrite sum_Rbar_n_Sn.
          rewrite IHn.
          rewrite <- ELim_seq_plus.
          -- apply ELim_seq_ext; intros.
             rewrite sum_Rbar_n_Sn; trivial; intros.
             now apply sum_Rbar_n_nneg_nneg.
          -- apply ex_Elim_seq_incr; intros.
             apply sum_Rbar_n_monotone; trivial; intros ?.
             now apply sum_Rbar_n_pos_Sn.
          -- apply ex_Elim_seq_incr; intros.
             now apply sum_Rbar_n_pos_Sn.
          -- apply ex_Rbar_plus_pos.
             ++ apply ELim_seq_nneg; intros.
                apply sum_Rbar_n_nneg_nneg; intros.
                now apply sum_Rbar_n_nneg_nneg.
             ++ apply ELim_seq_nneg; intros.
                now apply sum_Rbar_n_nneg_nneg.
          -- intros.
             apply ELim_seq_nneg; intros.
             now apply sum_Rbar_n_nneg_nneg; intros.
    - apply Elim_seq_le_bound; intros.
      destruct (bound_pair_iso_b_sum_Rbar f n).
      apply H.
      eapply Rbar_le_trans.
      + apply H0.
      + apply Rbar_le_trans with
            (y := sum_Rbar_n (fun x1 : nat => ELim_seq (fun i0 : nat => sum_Rbar_n (fun n0 : nat => f x1 n0) i0)) x).
        * apply sum_Rbar_n_monotone; trivial; intros ?.
          apply Elim_seq_incr_elem; intros.
          now apply sum_Rbar_n_pos_Sn.
        * apply Elim_seq_incr_elem; intros.
          apply sum_Rbar_n_pos_Sn; intros.
          apply ELim_seq_nneg; intros.
          now apply sum_Rbar_n_nneg_nneg.
  Qed.

(*
  (* Fubini for nonnegative reals *)
  Lemma Series_Series_seq_pair (f:nat->nat->R) :
    (forall a b, 0 <= (f a b)) ->
    Series (fun i : nat => Series (fun j : nat => f i j)) = 
    Series (fun i : nat => let '(a, b) := iso_b (Isomorphism:=nat_pair_encoder) i in (f a b)).
  Proof.
    intros.
    apply Rle_antisym.
*)
(*
    - apply Elim_seq_le_bound; intros.
      replace (sum_Rbar_n
                 (fun x0 : nat =>
                    ELim_seq 
                      (fun i0 : nat => sum_Rbar_n (fun n0 : nat => f x0 n0) i0)) n)
              with
                (ELim_seq (fun i0 =>
                             (sum_Rbar_n (fun x0 =>
                                            (sum_Rbar_n (fun n0 => f x0 n0) i0)) n))).
      + apply Elim_seq_le_bound; intros.
        destruct (bound_iso_f_pairs_sum_Rbar f n0 n).
        apply H.
        eapply Rbar_le_trans.
        * apply H0.
        * apply Elim_seq_incr_elem; intros.
          apply sum_Rbar_n_pos_Sn; intros.
          now destruct (iso_b n2).
      + symmetry.
        induction n.
        * unfold sum_Rbar_n.
          simpl.
          now rewrite ELim_seq_const.
        * rewrite sum_Rbar_n_Sn.
          rewrite IHn.
          rewrite <- ELim_seq_plus.
          -- apply ELim_seq_ext; intros.
             rewrite sum_Rbar_n_Sn; trivial; intros.
             now apply sum_Rbar_n_nneg_nneg.
          -- apply ex_Elim_seq_incr; intros.
             apply sum_Rbar_n_monotone; trivial; intros ?.
             now apply sum_Rbar_n_pos_Sn.
          -- apply ex_Elim_seq_incr; intros.
             now apply sum_Rbar_n_pos_Sn.
          -- apply ex_Rbar_plus_pos.
             ++ apply ELim_seq_nneg; intros.
                apply sum_Rbar_n_nneg_nneg; intros.
                now apply sum_Rbar_n_nneg_nneg.
             ++ apply ELim_seq_nneg; intros.
                now apply sum_Rbar_n_nneg_nneg.
          -- intros.
             apply ELim_seq_nneg; intros.
             now apply sum_Rbar_n_nneg_nneg; intros.
    - apply Elim_seq_le_bound; intros.
      destruct (bound_pair_iso_b_sum_Rbar f n).
      apply H.
      eapply Rbar_le_trans.
      + apply H0.
      + apply Rbar_le_trans with
            (y := sum_Rbar_n (fun x1 : nat => ELim_seq (fun i0 : nat => sum_Rbar_n (fun n0 : nat => f x1 n0) i0)) x).
        * apply sum_Rbar_n_monotone; trivial; intros ?.
          apply Elim_seq_incr_elem; intros.
          now apply sum_Rbar_n_pos_Sn.
        * apply Elim_seq_incr_elem; intros.
          apply sum_Rbar_n_pos_Sn; intros.
          apply ELim_seq_nneg; intros.
          now apply sum_Rbar_n_nneg_nneg.
  Qed.
*)

 Lemma list_Rbar_sum_nneg_nested_prod_swap {A B:Type} (X:list A) (Y:list B) (f:A->B->Rbar) :
   (forall x y, In x X -> In y Y -> Rbar_le 0 (f x y)) ->
   list_Rbar_sum (map (fun xy => f (fst xy) (snd xy)) (list_prod X Y)) =
   list_Rbar_sum (map (fun yx => f (snd yx) (fst yx)) (list_prod Y X)).
   Proof.
     intros.
     apply list_Rbar_sum_nneg_perm.
     - apply Forall_forall.
       intros.
       rewrite in_map_iff in H0.
       destruct H0 as [? [? ?]].
       rewrite <- H0.
       destruct x0.
       apply H; now apply in_prod_iff in H1.
     - apply Forall_forall.
       intros.
       rewrite in_map_iff in H0.       
       destruct H0 as [? [? ?]].
       rewrite <- H0.
       destruct x0.
       apply H; now apply in_prod_iff in H1.
     - generalize (list_prod_swap X Y); intros.
       replace (map (fun yx : B * A => f (snd yx) (fst yx)) (list_prod Y X)) with
           (map (fun xy : A * B => f (fst xy) (snd xy))
                (map swap (list_prod Y X))).
       + apply Permutation_map.
         apply H0.
       + unfold swap.
         rewrite map_map.
         apply map_ext.
         intros.
         now simpl.
   Qed.

 Lemma list_Rbar_sum_nneg_nested_swap {A B:Type} (X:list A) (Y:list B) (f:A->B->Rbar) :
    (forall x y, In x X -> In y Y -> Rbar_le 0 (f x y)) ->
    list_Rbar_sum (map (fun x => list_Rbar_sum (map (fun y => f x y) Y)) X) =
      list_Rbar_sum (map (fun y => list_Rbar_sum (map (fun x => f x y) X)) Y).
 Proof.
   intros.
   rewrite list_Rbar_sum_nneg_nested_prod.
   - rewrite list_Rbar_sum_nneg_nested_prod.
     + now apply list_Rbar_sum_nneg_nested_prod_swap.
     + intros.
       now apply H.
   - intros.
     now apply H.
 Qed.


 Lemma list_Rbar_sum_const c l : list_Rbar_sum (map (fun _ : nat => c) l) = Rbar_mult c (INR (length l)).
 Proof.
   induction l.
   - now rewrite Rbar_mult_0_r.
   - simpl length.
     rewrite S_INR.
     simpl.
     rewrite IHl.
     replace (Finite (INR (length l) + 1)) with (Rbar_plus (INR (length l)) 1) by reflexivity.
     rewrite Rbar_mult_plus_distr_l; simpl.
     + rewrite Rbar_mult_1_r.
       now rewrite Rbar_plus_comm.
     + apply pos_INR.
     + lra.
 Qed.

 Lemma sum_Rbar_n0 n : sum_Rbar_n (fun _ : nat => 0) n = 0.
 Proof.
   unfold sum_Rbar_n.
   rewrite list_Rbar_sum_const.
   now rewrite Rbar_mult_0_l.
 Qed.   
   
 Lemma Elim_seq_sum0 : ELim_seq (sum_Rbar_n (fun _ : nat => 0)) = 0.
 Proof.
   rewrite (ELim_seq_ext _ (fun _ => 0)).
   + apply ELim_seq_const.
   + intros.
     apply sum_Rbar_n0.
 Qed.

 Lemma list_Rbar_ELim_seq_nneg_nested_swap {A:Type} (X:list A) (f:A->nat->Rbar) :
   (forall a b, In a X -> Rbar_le 0 (f a b)) ->
   list_Rbar_sum (map (fun x => (ELim_seq (sum_Rbar_n (fun j : nat => (f x j))))) X) =
     ELim_seq
        (sum_Rbar_n (fun i : nat => list_Rbar_sum (map (fun x => f x i) X))).
 Proof.
   symmetry.
   induction X.
   - simpl.
     now rewrite Elim_seq_sum0.
   - simpl.
     rewrite <- IHX by firstorder.
     rewrite <- ELim_seq_plus.
     + apply ELim_seq_ext; intros.
       rewrite sum_Rbar_n_nneg_plus; trivial.
       * firstorder.
       * intros.
         apply list_Rbar_sum_nneg_nneg; intros.
         apply in_map_iff in H1.
         destruct H1 as [?[??]]; subst.
         firstorder.
     + apply ex_Elim_seq_incr; intros.
       apply sum_Rbar_n_pos_incr; firstorder.
     + apply ex_Elim_seq_incr; intros.
       apply sum_Rbar_n_pos_incr; intros.
       apply list_Rbar_sum_nneg_nneg; intros.
         apply in_map_iff in H0.
         destruct H0 as [?[??]]; subst.
         firstorder.
     + apply ex_Rbar_plus_pos.
       * apply ELim_seq_nneg; intros.
         apply sum_Rbar_n_nneg_nneg; intros.
         firstorder.
       * apply ELim_seq_nneg; intros.
         apply sum_Rbar_n_nneg_nneg; intros.
         apply list_Rbar_sum_nneg_nneg; intros.
         apply in_map_iff in H1.
         destruct H1 as [?[??]]; subst.
         firstorder.
 Qed.

  Definition swap_num_as_pair (n:nat) :=
    let '(a, b) := iso_b (Isomorphism:=nat_pair_encoder) n in
    iso_f (b,a).

  Lemma sum_Rbar_n_iso_swap (f:nat->nat->Rbar) (n : nat) :
    (forall a b, Rbar_le 0 (f a b)) ->
    exists (m : nat),
      Rbar_le
        (sum_Rbar_n (fun n0 : nat => let '(a, b) := iso_b n0 in f a b) n)
        (sum_Rbar_n (fun n0 : nat => let '(a, b) := iso_b n0 in f b a) m).
  Proof.
    intros.
    exists (S (list_max (map swap_num_as_pair (seq 0 n)))).
    unfold sum_Rbar_n.
    assert (subl:exists l,
               Permutation (map iso_b (seq 0 n)) l /\
               sublist l 
                       (map swap (map iso_b
                                      (seq 0 (S (list_max
                                                (map swap_num_as_pair (seq 0 n)))))))).
    {
      apply incl_NoDup_sublist_perm.
      - apply iso_b_nodup.
        apply seq_NoDup.
      - intros [??] ?.
        apply in_map_iff in H0.
        destruct H0 as [?[??]].
        rewrite in_map_iff.
        exists (n1,n0).
        split.
        + now unfold swap; simpl.
        + rewrite in_map_iff.
          exists (iso_f (n1, n0)).
          split.
          * now rewrite iso_b_f.
          * rewrite in_seq.
            split.
            -- lia.
            -- unfold swap_num_as_pair.
               assert (iso_f (n1, n0) <=
                       (list_max
                          (map (fun n2 : nat => let '(a, b) := iso_b n2 in iso_f (b, a)) (seq 0 n))))%nat.
               {
                 generalize (list_max_upper
                               (map (fun n2 : nat => let '(a, b) := iso_b n2 in iso_f (b, a)) (seq 0 n)))%nat; intros.
                 rewrite Forall_forall in H2.
                 apply H2.
                 rewrite in_map_iff.
                 exists x.
                 split; trivial.
                 destruct (iso_b x).
                 now inversion H0.
               }
               lia.
    }
    destruct subl as [? [? ?]].
    apply (Permutation_map (fun '(a, b) => f a b)) in H0.
    apply (sublist_map (fun '(a, b) => f a b)) in H1.
    rewrite (list_Rbar_sum_nneg_perm
               (map (fun n1 : nat => let '(a, b) := iso_b n1 in f a b) (seq 0 n))
               (map (fun '(a, b) => f a b) x)
             ); trivial.
    - apply list_Rbar_sum_pos_sublist_le; trivial.
      + intros.
        rewrite in_map_iff in H2.
        destruct H2 as [? [? ?]].
        rewrite <- H2.
        now destruct (iso_b x1).
      + unfold swap in H1.
        rewrite map_map, map_map in H1.
        rewrite map_ext with
            (g :=  (fun x : nat => f (snd (iso_b x)) (fst (iso_b x)))).
        * apply H1.
        * intros.
          destruct (iso_b a).
          now simpl.
    - rewrite Forall_map, Forall_forall.
      intros.
      now destruct (iso_b x0).
    - rewrite Forall_map, Forall_forall.
      intros.
      now destruct x0.
    - now rewrite map_map in H0.
    Qed.

  Lemma ELim_seq_sum_nneg_nested_swap (f:nat->nat->Rbar) :
    (forall a b, Rbar_le 0 (f a b)) ->
    ELim_seq
      (sum_Rbar_n (fun i : nat => ELim_seq (sum_Rbar_n (fun j : nat => (f i j))))) =
      ELim_seq
        (sum_Rbar_n (fun i : nat => ELim_seq (sum_Rbar_n (fun j : nat => (f j i))))).
  Proof.
    intros.
    rewrite ELim_seq_Elim_seq_pair.
    rewrite ELim_seq_Elim_seq_pair.
    - apply Rbar_le_antisym.
      + apply Elim_seq_le_bound; intros.
        destruct (sum_Rbar_n_iso_swap f n H).
        eapply Rbar_le_trans.
        * apply H0.
        * apply Elim_seq_incr_elem; intros.
          apply sum_Rbar_n_pos_Sn; intros.
          now destruct (iso_b n1).
      + apply Elim_seq_le_bound; intros.
        destruct (sum_Rbar_n_iso_swap (fun a b => f b a) n).
        * now intros.
        * eapply Rbar_le_trans.
          -- apply H0.
          -- apply Elim_seq_incr_elem; intros.
             apply sum_Rbar_n_pos_Sn; intros.
             now destruct (iso_b n1).
    - now intros.
    - now intros.
  Qed.
  
  Lemma is_finite_witness (x : Rbar) :
    is_finite x ->
    exists (r:R), x = Finite r.
  Proof.
    intros.
    unfold is_finite in H.
    now exists (real x).
  Qed.

  Lemma is_finite_Elim_seq_nneg_nested (f:nat->nat->Rbar) :
    (forall a b, Rbar_le 0(f a b)) ->
    is_finite (ELim_seq
      (sum_Rbar_n (fun i : nat => ELim_seq (sum_Rbar_n (fun j : nat => (f i j)))))) ->
    forall i, is_finite (ELim_seq (sum_Rbar_n (fun j : nat => (f i j)))).
  Proof.
    intros.
    apply is_finite_witness in H0.
    destruct H0.
    generalize (Elim_seq_sum_pos_fin_n_fin (fun i : nat => ELim_seq (sum_Rbar_n (fun j : nat => (f i j)))) x); intros.
    apply H1; trivial.
    intros.
    replace (Finite 0) with (ELim_seq (fun _ => 0)).
    + apply ELim_seq_le; intros.
      apply sum_Rbar_n_nneg_nneg; intros.
      apply H.
    + apply ELim_seq_const.
  Qed.
    
  Lemma ELim_seq_Lim_seq_Rbar (f : nat -> Rbar) :
    (forall n, is_finite (f n)) ->
    ELim_seq f = Lim_seq f.
  Proof.
    intros.
    generalize (Elim_seq_fin f); intros.
    rewrite ELim_seq_ext with (v := fun n => Finite (real (f n))); trivial.
    intros.
    now rewrite H.
  Qed.

  Lemma sum_Rbar_n_finite_sum_n f n:
    sum_Rbar_n (fun x => Finite (f x)) (S n) = Finite (sum_n f n).
  Proof.
    rewrite sum_n_fold_right_seq.
    unfold sum_Rbar_n, list_Rbar_sum.
    generalize (0).
    induction n; trivial; intros.
    rewrite seq_Sn.
    repeat rewrite map_app.
    repeat rewrite fold_right_app.
    now rewrite <- IHn.
  Qed.

  Lemma Lim_seq_sum_Elim f :
    Lim_seq (sum_n f) = ELim_seq (sum_Rbar_n (fun x => Finite (f x))).
  Proof.
    rewrite <- ELim_seq_incr_1.
    rewrite <- Elim_seq_fin.
    apply ELim_seq_ext; intros.
    now rewrite sum_Rbar_n_finite_sum_n.
  Qed.    

  Lemma Series_nneg_nested_swap (f:nat->nat->R) :
    (forall a b, 0 <= (f a b)) ->
    is_finite (ELim_seq 
      (sum_Rbar_n (fun i : nat => ELim_seq (sum_Rbar_n (fun j : nat => (f i j)))))) ->
    Series (fun i : nat => Series (fun j : nat => (f i j))) =
    Series (fun i : nat => Series (fun j : nat => (f j i))).
  Proof.
    intros.
    unfold Series.
    generalize (is_finite_Elim_seq_nneg_nested f); intros.
    cut_to H1; trivial.
    f_equal.
    generalize (ELim_seq_sum_nneg_nested_swap f); intros.
    cut_to H2; try now simpl.
    generalize (is_finite_Elim_seq_nneg_nested (fun i j => f j i)); intros.          
    cut_to H3; trivial; try (intros; now simpl).
    - do 2 rewrite Lim_seq_sum_Elim.
      rewrite ELim_seq_ext with
          (v :=  (sum_Rbar_n
                    (fun i : nat =>
                       ELim_seq (sum_Rbar_n (fun j : nat => Finite (f i j)))))).
      symmetry.
      rewrite ELim_seq_ext with
          (v := (sum_Rbar_n
                   (fun i : nat =>
                      ELim_seq (sum_Rbar_n (fun j : nat => Finite (f j i)))))).
      symmetry; trivial.
      + intros.
        apply sum_Rbar_n_proper; trivial.
        unfold pointwise_relation; simpl; intros.
        rewrite Lim_seq_sum_Elim.
        now rewrite H3.
      + intros.
        apply sum_Rbar_n_proper; trivial.
        unfold pointwise_relation; simpl; intros.
        rewrite Lim_seq_sum_Elim.
        now rewrite H1.        
   - now rewrite <- H2.
  Qed.

  Lemma lim_seq_sum_singleton_is_one f :
    (forall n1 n2, n1 <> n2 -> f n1 = 0 \/ f n2 = 0) ->
    exists n, Lim_seq (sum_n f) = f n.
  Proof.
    intros.
    destruct (classic (exists m, f m <> 0)%type) as [[n ?]|].
    - rewrite <- (Lim_seq_incr_n _ n).
      assert (eqq:forall x,
                 sum_n f (x + n) =
                   f n).
      {
        intros.
        induction x; simpl.
        - destruct n.
          + now rewrite sum_O.
          + rewrite sum_Sn.
            erewrite sum_n_ext_loc; try rewrite sum_n_zero.
            * unfold plus; simpl; lra.
            * intros ??; simpl.
              destruct (H (S n) n0); try lra.
              lia.
        - rewrite sum_Sn, IHx.
          unfold plus; simpl.
          destruct (H n (S (x + n))); try lra.
          lia.
      }
      rewrite (Lim_seq_ext _ _ eqq).
      rewrite Lim_seq_const.
      eauto.
    - assert (eqq:forall x,
                 sum_n f x = 0).
      {
        intros.
        erewrite sum_n_ext; try eapply sum_n_zero.
        intros ?; simpl.
        destruct (Req_EM_T (f n) 0); trivial.
        elim H0; eauto.
      }
      rewrite (Lim_seq_ext _ _ eqq).
      rewrite Lim_seq_const.
      exists (0%nat).
      f_equal; symmetry.
      destruct (Req_EM_T (f 0%nat) 0); trivial.
      elim H0; eauto.
  Qed.

  Lemma lim_seq_sum_singleton_finite f :
    (forall n1 n2, n1 <> n2 -> f n1 = 0 \/ f n2 = 0) ->
    is_finite (Lim_seq (sum_n f)).
  Proof.
    intros.
    destruct (lim_seq_sum_singleton_is_one f H).
    now rewrite H0.
  Qed.

End lim_sum.

Section Rmax_list.

  Lemma Rmax_list_lim_Sup_seq (a : nat -> R) (N : nat) :
    Lim_seq (fun M => Rmax_list (map a (seq N M))) = Sup_seq (fun n0 : nat => a (n0 + N)%nat).
  Proof.
    rewrite <- Elim_seq_fin.
    rewrite <- ELim_seq_incr_1.
    apply is_Elim_seq_unique.
    apply is_Elim_seq_fin.
    apply lim_seq_is_lub_incr.
    - intros.
      rewrite (seq_Sn _ (S n)).
      rewrite Rmax_list_app.
      + apply Rmax_l.
      + simpl; congruence.
    - split.
      + intros n [??]; subst.
        generalize (Rmax_list_In (map a (seq N (S x)))); intros HH.
        cut_to HH; [| simpl; congruence].
        apply in_map_iff in HH.
        destruct HH as [?[??]].
        rewrite <- H.
        apply in_seq in H0.
        apply (Sup_seq_minor_le _ _ (x0-N)).
        replace (x0 - N + N)%nat with x0 by lia.
        apply Rbar_le_refl.
      + intros ??.
        red in H.
        unfold Sup_seq, proj1_sig.
        match_destr.
        destruct x; simpl in i.
        * apply Rbar_le_forall_Rbar_le; intros eps.
          destruct (i eps) as [?[??]].
          specialize (H (Rmax_list (map a (seq N (S x))))).
          cut_to H; [| eauto].
          generalize (@Rmax_spec (map a (seq N (S x))) (a (x+N)%nat)); intros HH.
          cut_to HH.
          -- destruct b; simpl in *; lra.
          -- apply in_map.
             apply in_seq.
             lia.
        * destruct b; simpl; trivial.
          -- destruct (i r).
             specialize (H (Rmax_list (map a (seq N (S x))))).
             cut_to H; [| eauto].
             generalize (@Rmax_spec (map a (seq N (S x))) (a (x+N)%nat)); intros HH.
             cut_to HH.
             ++ simpl in *; lra.
             ++ apply in_map.
                apply in_seq.
                lia.
          -- apply (H (a N)).
             exists 0%nat.
             reflexivity.
        * now simpl.
  Qed.

  Lemma Rmax_list_Sup_seq (a : nat -> R) (N M : nat) :
    Rbar_le (Rmax_list (map a (seq N (S M)))) (Sup_seq (fun n0 : nat => a (n0 + N)%nat)).
  Proof.
    rewrite <- Rmax_list_lim_Sup_seq.
    rewrite <- Elim_seq_fin.
    rewrite <- ELim_seq_incr_1.
    apply (Elim_seq_incr_elem (fun x : nat => Rmax_list (map a (seq N (S x))))); intros.
    rewrite (seq_Sn _ (S n)).
    rewrite Rmax_list_app.
    - simpl.
      apply Rmax_l.
    - simpl; congruence.
  Qed.

End Rmax_list.

Section zeroprop.

  Definition zerotails_prop a ϵ n : Prop :=
  forall N, (n <= N)%nat -> Rabs (Series (fun k => a (S (N+k)%nat))) < ϵ.

Lemma zerotails_witness_pack (a : nat -> R) :
  ex_series a -> forall (ϵ:posreal), { n : nat | zerotails_prop a ϵ n  /\ forall n', zerotails_prop a ϵ n' -> (n <= n')%nat }.
Proof.
  intros.
  case_eq (classic_min_of (zerotails_prop a ϵ)).
  - intros.
    exists n.
    split.
    + now apply classic_min_of_some in H0.
    + intros.
      apply NPeano.Nat.nlt_ge; intros nlt.
      eapply classic_min_of_some_first in H0; try apply nlt.
      tauto.
  - intros.
    generalize (classic_min_of_none _ H0); intros.
    apply zerotails in H.
    apply is_lim_seq_spec in H.
    simpl in H.
    elimtype False.
    destruct (H ϵ) as [N ?].
    elim (H1 N).
    red; intros.
    specialize (H2 _ H3).
    now rewrite Rminus_0_r in H2.
Qed.

Definition zerotails_witness (a : nat -> R)
           (pf:ex_series a) (ϵ:posreal) : nat
  := proj1_sig (zerotails_witness_pack a pf ϵ).

Lemma zerotails_witness_prop (a : nat -> R) (pf:ex_series a) (ϵ:posreal) :
  forall N, ((zerotails_witness a pf ϵ) <= N)%nat -> Rabs (Series (fun k => a (S N + k)%nat)) < ϵ.
Proof.
  unfold zerotails_witness, proj1_sig.
  match_destr.
  tauto.
Qed.

Lemma zerotails_prop_nondecr a ϵ1 ϵ2 n :
    ϵ1 <= ϵ2 ->
    zerotails_prop a ϵ1 n -> zerotails_prop a ϵ2 n.
Proof.
  unfold zerotails_prop; intros.
  eapply Rlt_le_trans; try apply H.
  now apply H0.
Qed.  

Lemma zerotails_witness_min (a : nat -> R) (pf:ex_series a) (ϵ:posreal) :
  forall n', (forall N, (n' <= N)%nat -> Rabs (Series (fun k => a (S N + k)%nat)) < ϵ) ->
        ((zerotails_witness a pf ϵ) <= n')%nat.
Proof.
  unfold zerotails_witness, proj1_sig.
  match_destr.
  tauto.
Qed.

Lemma zerotails_witness_nondecr (a : nat -> R) (pf:ex_series a) (ϵ1 ϵ2:posreal) :
  ϵ2 <= ϵ1 ->
  (zerotails_witness a pf ϵ1 <= zerotails_witness a pf ϵ2)%nat.
Proof.
  intros.
  unfold zerotails_witness, proj1_sig; repeat match_destr.
  apply a0.
  eapply zerotails_prop_nondecr; try apply H.
  tauto.
Qed.

Definition zerotails_eps2k_fun' (a : nat -> R) (pf:ex_series a) (k:nat) : nat
  := zerotails_witness a pf (inv_2_pow_posreal k).

Definition zerotails_eps2k_fun (a : nat -> R) (pf:ex_series a) (k:nat) : nat
  := zerotails_eps2k_fun' a pf k + k.

Lemma zerotails_eps2k_fun_shifted_bound (a : nat -> R) (pf:ex_series a) (k:nat)
  : Rabs (Series (fun x => a (S (x+ (zerotails_eps2k_fun a pf k)%nat)))) < (/ (2 ^ k)).
Proof.
  unfold zerotails_eps2k_fun.
  unfold zerotails_eps2k_fun'.
  unfold zerotails_witness, proj1_sig.
  match_destr.
  destruct a0 as [r _].
  simpl in r.
  specialize (r (x+k)%nat).
  eapply Rle_lt_trans; try apply r; try lia.
  right; f_equal.
  apply Series_ext; intros.
  f_equal; lia.
Qed.

Lemma zerotails_eps2k_double_sum_ex (a : nat -> R) (pf:ex_series a) :
  ex_series (fun k => Series (fun x => a (S (x+ (zerotails_eps2k_fun a pf k)%nat)))).
Proof.
  eapply (@ex_series_le R_AbsRing R_CompleteNormedModule _ (fun k =>  (/ (2 ^ k)))).
  - intros.
    left.
    apply zerotails_eps2k_fun_shifted_bound.
  - generalize (ex_series_geom (1/2)); intros HH.
    cut_to HH.
    + revert HH.
      apply ex_series_ext; intros.
      rewrite Rinv_pow; try lra.
      f_equal.
      lra.
    + rewrite Rabs_right; lra.
Qed.

Lemma zerotails_eps2k_fun'_nondecr a pf n :
  ((zerotails_eps2k_fun' a pf n) <= (zerotails_eps2k_fun'  a pf (S n)))%nat.
Proof.
  unfold zerotails_eps2k_fun'.
  apply zerotails_witness_nondecr.
  simpl.
  assert (0 < 2) by lra.
  assert (0 < 2 ^ n).
  {
    apply pow_lt; lra.
  }
  rewrite <- (Rmult_1_l (/ 2 ^ n)).
  rewrite Rinv_mult_distr.
  - apply Rmult_le_compat_r; try lra.
    left.
    apply Rinv_0_lt_compat.
    apply pow_lt; lra.
  - lra.
  - apply pow_nzero; lra.
Qed.

Lemma zerotails_incr_mult_strict_incr a pf n :
  ((zerotails_eps2k_fun a pf n) < (zerotails_eps2k_fun a pf (S n)))%nat.
Proof.
  unfold zerotails_eps2k_fun.
  generalize (zerotails_eps2k_fun'_nondecr a pf n); lia.
Qed.

Lemma zerotails_incr_mult_strict_incr_lt a pf m n :
  (m < n)%nat ->
  ((zerotails_eps2k_fun a pf m) < (zerotails_eps2k_fun a pf n))%nat.
Proof.
  intros.
  induction H.
  - apply zerotails_incr_mult_strict_incr.
  - rewrite IHle.
    apply  zerotails_incr_mult_strict_incr.
Qed.

Definition zerotails_incr_mult (a : nat -> R) (pf:ex_series a) n : R
  := Series (fun n0 : nat => if le_dec (S (zerotails_eps2k_fun a pf n0)) n then 1 else 0).

Lemma zerotails_incr_mult_ex (a : nat -> R) (pf:ex_series a) n :
  ex_series (fun n0 : nat => if le_dec (S (zerotails_eps2k_fun a pf n0)) n then 1 else 0).
Proof.
  apply (ex_series_incr_n _ n).
  apply (ex_series_ext (fun _ => 0)).
  - intros.
    match_destr.
    unfold zerotails_eps2k_fun in *; lia.
  - exists 0.
    apply is_series_Reals.
    apply infinite_sum_infinite_sum'.
    apply infinite_sum'0.
Qed.

Lemma zerotails_incr_mult_trunc  (a : nat -> R) (pf:ex_series a) n :
  zerotails_incr_mult a pf n = sum_n (fun n0 : nat => if le_dec (S (zerotails_eps2k_fun a pf n0)) n then 1 else 0) n.
Proof.
  unfold zerotails_incr_mult.
  apply is_series_unique.
  apply -> series_is_lim_seq.
  apply is_lim_seq_spec.
  simpl; intros.
  exists n; intros.
  generalize (sum_n_m_sum_n (fun n1 : nat => if le_dec (S (zerotails_eps2k_fun a pf n1)) n then 1 else 0) n n0).
  match goal with
    [|- context [minus ?x ?y]] => replace (minus x y) with (x - y) by reflexivity
  end; simpl.
  intros HH;  rewrite <- HH; trivial.
  erewrite (sum_n_m_ext_loc _ (fun _ => zero)).
  - rewrite sum_n_m_const_zero.
    unfold zero; simpl.
    rewrite Rabs_R0.
    now destruct eps.
  - intros.
    match_destr.
    unfold zerotails_eps2k_fun in l; lia.
Qed.
  
Lemma zerotails_eps2k_fun_unbounded a pf :
  forall m, exists k, (m < (zerotails_eps2k_fun a pf k))%nat.
Proof.
  unfold zerotails_eps2k_fun; intros.
  exists (S m).
  lia.
Qed.

Lemma zerotails_incr_mult_incr a pf n :
  exists m, (n < m)%nat /\
         zerotails_incr_mult a pf n + 1 <= zerotails_incr_mult a pf m.
Proof.
  destruct (zerotails_eps2k_fun_unbounded a pf (zerotails_eps2k_fun a pf (S n))) as [m HH].
  exists ((n + S (zerotails_eps2k_fun a pf m))%nat).
  assert (nlt:(n < n + zerotails_eps2k_fun a pf m)%nat).
  {
    lia.
  } 
  split; try lia.
  repeat rewrite zerotails_incr_mult_trunc.
  repeat rewrite sum_n_Reals.
  rewrite (sum_f_R0_split _ (n + S (zerotails_eps2k_fun a pf m)) n).
  - apply Rplus_le_compat.
    + apply sum_growing; intros.
      repeat match_destr; try lra; try lia.
    + replace ((n + S (zerotails_eps2k_fun a pf m) - S n))%nat with (zerotails_eps2k_fun a pf m) by lia.
      rewrite sum_f_R0_sum_f_R0'.
      replace (S (zerotails_eps2k_fun a pf m)) with (1+ (zerotails_eps2k_fun a pf m))%nat by lia.
      rewrite sum_f_R0'_plus_n.
      simpl.
      rewrite Rplus_0_l.
      assert (0 <=  sum_f_R0'
    (fun x : nat =>
     if
      le_dec (S (zerotails_eps2k_fun a pf (S (x + S n))))
        (n + S (zerotails_eps2k_fun a pf m))
     then 1
     else 0) (zerotails_eps2k_fun a pf m)
             ).
      {
        apply sum_f_R0'_le; intros.
        match_destr; lra.
      }
      match_destr; try lra.
      lia.
  - lia.
Qed.


Lemma zerotails_incr_mult_unbounded_nat a pf M :
  exists m, (INR M <= zerotails_incr_mult a pf m).
Proof.
  induction M.
  - exists 0%nat.
    simpl.
    unfold zerotails_incr_mult.
    apply Series_nonneg.
    + intros.
      match_destr; lra.
  - destruct IHM.
    destruct (zerotails_incr_mult_incr a pf x) as [? [??]].
    exists x0.
    rewrite S_INR.
    lra.
Qed.

Lemma zerotails_incr_mult_incr_incr a pf x n :
  (x <= n)%nat ->
  ((zerotails_incr_mult a pf x) <= (zerotails_incr_mult a pf n)).
Proof.
  intros.
  unfold zerotails_incr_mult.
  apply Series_le.
  - intros.
    repeat match_destr; try lra.
    lia.
  - apply zerotails_incr_mult_ex.
Qed.

Lemma zerotails_incr_mult_unbounded (a : nat -> R) (pf:ex_series a) :
  is_lim_seq (zerotails_incr_mult a pf) p_infty.
Proof.
  apply is_lim_seq_spec; simpl.
  intros.
  red.
  destruct (zerotails_incr_mult_unbounded_nat a pf (Z.to_nat (up (Rmax M 0)))).
  exists x; intros.

  assert (le1:((zerotails_incr_mult a pf x) <= (zerotails_incr_mult a pf n))).
  {
    now apply zerotails_incr_mult_incr_incr.
  } 

  eapply Rlt_le_trans; try eapply le1.
  eapply Rlt_le_trans; try eapply H.
  destruct (archimed (Rmax M 0)).
  rewrite INR_up_pos.
  - apply Rgt_lt in H1.
    eapply Rle_lt_trans; try eapply H1.
    apply Rmax_l.
  - apply Rle_ge.
    apply Rmax_r.
Qed.

Lemma zerotails_eps2k_double_sum_finite  (a : nat -> R) (pf:ex_series a) {anneg: forall x, 0 <= a x}:
  is_finite
    (ELim_seq
       (sum_Rbar_n
          (fun i : nat =>
             ELim_seq
               (sum_Rbar_n
                  (fun x : nat => a (S (x+ (zerotails_eps2k_fun a pf i)%nat))))))).
  Proof.
    generalize (zerotails_eps2k_fun_shifted_bound a pf); intros.
    generalize (zerotails_eps2k_double_sum_ex a pf); intros.
    rewrite <- ex_finite_lim_series in H0.
    rewrite ex_finite_lim_seq_correct in H0.
    destruct H0.
    rewrite <- ELim_seq_incr_1.
    rewrite ELim_seq_ext with
        (v := fun n => Finite (sum_n  (fun k : nat => Series (fun x : nat => a (S (x + zerotails_eps2k_fun a pf k)))) n)).
    now rewrite Elim_seq_fin.
    intros.
    rewrite <- sum_Rbar_n_finite_sum_n.
    apply sum_Rbar_n_proper; trivial.
    unfold pointwise_relation; intros.
    rewrite <- ex_series_Lim_seq.
    - rewrite <- ELim_seq_incr_1.
      rewrite ELim_seq_ext with
          (v := fun n => Finite (sum_n (fun x : nat => a (S (x + zerotails_eps2k_fun a pf a0))) n)).
      + now rewrite Elim_seq_fin.
      + intros.
        now rewrite sum_Rbar_n_finite_sum_n.
    - generalize (ex_series_incr_n a); intros.
      apply (ex_series_ext 
          (fun x : nat => a (S (zerotails_eps2k_fun a pf a0) + x)%nat)).
      + intros.
        f_equal.
        lia.
      + now apply ex_series_incr_n.
  Qed.

Lemma zerotails_eps2k_double_sum_eq (a : nat -> R) (pf:ex_series a) {anneg: forall x, 0 <= a x}:
  Series (fun k => Series (fun x => a (S (x+ (zerotails_eps2k_fun a pf k)%nat)))) =
    Series (fun n => zerotails_incr_mult a pf n * (a n)).
Proof.
  transitivity (
      Series (fun k : nat => Series (fun n : nat =>
                                  a n *
                                    if le_dec (S (zerotails_eps2k_fun a pf k)) n 
                                    then 1 else 0))).
  {
    apply Series_ext; intros.
    rewrite (Series_incr_n_aux
               (fun n0 : nat =>
                  a n0 * (if le_dec (S (zerotails_eps2k_fun a pf n))%nat n0 then 1 else 0))
               (S (zerotails_eps2k_fun a pf n))).
    - apply Series_ext; intros.
      match_destr.
      + field_simplify.
        f_equal.
        lia.
      + elim n1.
        lia.
    - intros.
      match_destr; try lra.
      unfold zerotails_eps2k_fun in *.
      lia.
  } 
  transitivity (Series
    (fun n : nat =>
     Series
       (fun k : nat =>
        a n * (if le_dec (S (zerotails_eps2k_fun a pf k)) n then 1 else 0)))).
  {
    apply Series_nneg_nested_swap.
    - intros.
      apply Rmult_le_pos; trivial.
      match_destr; lra.
    - rewrite ELim_seq_ext with
          (v :=  (sum_Rbar_n
                    (fun i : nat =>
                       ELim_seq
                         (sum_Rbar_n
                            (fun x : nat => a (S (x+ (zerotails_eps2k_fun a pf i)%nat))))))).
      + apply zerotails_eps2k_double_sum_finite; trivial.
      + intros.
        apply sum_Rbar_n_proper; trivial.
        unfold pointwise_relation; simpl; intros.
        rewrite <- ELim_seq_incr_1.
        rewrite ELim_seq_ext with
            (v := (fun n => Finite (sum_n (fun j : nat => a j * (if le_dec (S (zerotails_eps2k_fun a pf a0)) j then 1 else 0)) n))).
        rewrite Elim_seq_fin.
        rewrite <- ELim_seq_incr_1.        
        rewrite ELim_seq_ext with
            (v := (fun n => Finite (sum_n (fun x : nat => a (S (x + zerotails_eps2k_fun a pf a0))) n))).
        rewrite Elim_seq_fin.
        * rewrite ex_series_Lim_seq.
          rewrite ex_series_Lim_seq.
          -- rewrite (Series_incr_n_aux
                        (fun n0 : nat =>
                           a n0 * (if le_dec (S (zerotails_eps2k_fun a pf a0))%nat n0 then 1 else 0))
                        (S (zerotails_eps2k_fun a pf a0))).
             ++ apply Rbar_finite_eq.
                apply Series_ext; intros.
                match_destr.
                ** field_simplify.
                   f_equal.
                   lia.
                ** elim n1.
                   lia.
             ++ intros.
                match_destr; try lra.
                unfold zerotails_eps2k_fun in *.
                lia.
          -- apply (ex_series_ext 
                      (fun x => a ((S (zerotails_eps2k_fun a pf a0)) + x)%nat)).
             ++ intros; f_equal; lia.
             ++ now apply ex_series_incr_n.
          -- apply (ex_series_le (fun j : nat => a j * (if le_dec (S (zerotails_eps2k_fun a pf a0)) j then 1 else 0)) a); trivial.
             intros.
             unfold norm; simpl.
             unfold abs; simpl.
             rewrite Rabs_right.
             ++ replace (a n0) with ((a n0) * 1) at 2 by lra.
                apply Rmult_le_compat_l; trivial.
                match_destr; lra.
             ++ apply Rle_ge, Rmult_le_pos; trivial.
                match_destr; lra.
        * intros; now rewrite sum_Rbar_n_finite_sum_n.
        * intros; now rewrite sum_Rbar_n_finite_sum_n.          
  }
  apply Series_ext; intros.
  rewrite Series_scal_l.
  now rewrite Rmult_comm.
 Qed.

End zeroprop.

Lemma ELimSup_ELim_seq_le f : Rbar_le (ELim_seq f) (ELimSup_seq f).
Proof.
  unfold ELim_seq.
  generalize (ELimSup_ELimInf_seq_le f).
  destruct (ELimInf_seq f)
  ; destruct (ELimSup_seq f)
  ; simpl; try lra.
Qed.

Lemma ELimInf_ELim_seq_le f : Rbar_le (ELimInf_seq f) (ELim_seq f).
Proof.
  unfold ELim_seq.
  generalize (ELimSup_ELimInf_seq_le f).
  destruct (ELimInf_seq f)
  ; destruct (ELimSup_seq f)
  ; simpl; try lra.
Qed.

  Lemma is_ELim_seq_sup_seq_incr_R (f : nat -> Rbar) (l : R) :
    (forall n, Rbar_le (f n) (f (S n))) ->
    (is_ELimSup_seq f l) <-> is_sup_seq f l.
  Proof.
    intros.
    unfold is_ELimSup_seq, is_sup_seq.
    split; intros; destruct (H0 eps); split; generalize (cond_pos eps); intros eps_pos.
    - intros.
      simpl.
      destruct H2.
      destruct (le_dec x n).
      + now apply H2.
      + specialize (H2 x).
        cut_to H2; try lia; simpl in H2.
        assert (n <= x)%nat by lia.
        assert (Rbar_le (f n) (f x)) by now apply Rbar_le_incr.
        eapply Rbar_le_lt_trans.
        * apply H4.
        * apply H2.
    - destruct (H1 0%nat) as [? [? ?]].
      now exists x.
    - intros.
      destruct H2.
      exists (max x N).
      split; try lia.
      assert (Rbar_le (f x) (f (Init.Nat.max x N))).
      {
        destruct (le_dec N x).
        - rewrite Nat.max_l; try lia.
          apply Rbar_le_refl.
        - rewrite Nat.max_r; try lia.
          assert (x <= N)%nat by lia.
          now apply Rbar_le_incr.
      }
      eapply Rbar_lt_le_trans.
      * apply H2.
      * apply H3.
    - exists (0%nat).
      intros.
      apply H1.
   Qed.

  Lemma is_ELim_seq_sup_seq_incr (f : nat -> Rbar) (l : Rbar) :
    (forall n, Rbar_le (f n) (f (S n))) ->
    (is_ELimSup_seq f l) <-> is_sup_seq f l.
  Proof.
    intros.
    destruct l.
    - now apply is_ELim_seq_sup_seq_incr_R.
    - unfold is_ELimSup_seq, is_sup_seq.
      split; intros.
      + destruct (H0 M 0%nat) as [? [? ?]].
        now exists x.
      + destruct (H0 M).
        exists (max x N).
        split; try lia.
        assert (Rbar_le (f x) (f (Init.Nat.max x N))).
        {
          destruct (le_dec N x).
          - rewrite Nat.max_l; try lia.
            apply Rbar_le_refl.
          - rewrite Nat.max_r; try lia.
            assert (x <= N)%nat by lia.
            now apply Rbar_le_incr.
        }
      eapply Rbar_lt_le_trans.
      * apply H1.
      * apply H2.
    - unfold is_ELimSup_seq, is_sup_seq.
      split; intros.
      + destruct (H0 M).
        destruct (le_dec x n).
        * now apply H1.
        * assert (n <= x)%nat by lia.
          apply Rbar_le_lt_trans with (y := f x).
          -- now apply Rbar_le_incr.
          -- apply H1; try lia.
      + exists (0%nat).
        intros.
        apply H0.
   Qed.        

