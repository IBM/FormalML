Require Import Coquelicot.Coquelicot.
Require Import Reals.
Require Import LibUtils List Permutation RealAdd ELim_Seq ListAdd Sums.
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
  
