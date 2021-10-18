Require Import LibUtils List RealAdd.
Require Import Reals Psatz Morphisms.
Require Import mathcomp.ssreflect.ssreflect.

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Coquelicot.Rcomplements.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Markov Coquelicot.Hierarchy.
Require Import Coquelicot.Rcomplements Coquelicot.Rbar Coquelicot.Markov Coquelicot.Iter Coquelicot.Lub.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.

Require Coquelicot.Lim_seq.

Require Import Classical_Pred_Type.

Definition is_ELimSup_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal,
        (forall N : nat, exists n : nat, (N <= n)%nat /\ Rbar_lt (l - eps) (u n))
        /\ (exists N : nat, forall n : nat, (N <= n)%nat -> Rbar_lt (u n) (l + eps))
    | p_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ Rbar_lt M (u n))
    | m_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> Rbar_lt (u n) M)
  end.

Lemma is_ELimSup_seq_fin (u : nat -> R) (l : Rbar) :
  is_ELimSup_seq u l <-> Lim_seq.is_LimSup_seq u l.
Proof.
  unfold is_ELimSup_seq, Lim_seq.is_LimSup_seq.
  destruct l; simpl; tauto.
Qed.

Definition is_ELimInf_seq (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal,
        (forall N : nat, exists n : nat, (N <= n)%nat /\ Rbar_lt (u n) (l + eps))
        /\ (exists N : nat, forall n : nat, (N <= n)%nat -> Rbar_lt (l - eps) (u n))
    | p_infty => forall M : R, (exists N : nat, forall n : nat, (N <= n)%nat -> Rbar_lt M (u n))
    | m_infty => forall M : R, (forall N : nat, exists n : nat, (N <= n)%nat /\ Rbar_lt (u n) M)
  end.

Lemma is_ELimInf_seq_fin (u : nat -> R) (l : Rbar) :
  is_ELimInf_seq u l <-> Lim_seq.is_LimInf_seq u l.
Proof.
  unfold is_ELimInf_seq, Lim_seq.is_LimInf_seq.
  destruct l; simpl; tauto.
Qed.

Lemma is_ELimInf_opp_ELimSup_seq (u : nat -> Rbar) (l : Rbar) :
  is_ELimInf_seq (fun n => Rbar_opp (u n)) (Rbar_opp l)
                <-> is_ELimSup_seq u l.
Proof.
  destruct l; simpl.
  - intuition
    ; specialize (H eps); destruct H as [HH1 [N2 HH2]]
    ; try solve [destruct (HH1 N) as [x [??]]
                 ; exists x; split; trivial
                 ; destruct (u x); simpl in *; lra
                |
                exists N2; intros N ltN
                ; specialize (HH2 _ ltN)
                ; destruct (u N); simpl in *; lra
                ] .
  - intuition
    ; specialize (H (- M) N)
    ; destruct H as [?[??]]
    ; exists x; split; trivial
    ; destruct (u x); simpl in *; trivial; lra.
  - intuition
    ; specialize (H (- M))
    ; destruct H as [x ?]
    ; exists x; intros n nlt
    ; specialize (H n nlt)
    ; destruct (u n); simpl in *; trivial; lra.
Qed.

Lemma is_ELimInf_seq_ext_loc (u v : nat -> Rbar) (l : Rbar) :
  eventually (fun n => u n = v n) ->
  is_ELimInf_seq u l -> is_ELimInf_seq v l.
Proof.
  intros [Neqq eqq] lim1.
  destruct l; simpl in *.
  - intros eps.
    specialize (lim1 eps).
    destruct lim1 as [HH1 [N2 HH2]].
    split.
    + intros N.
      destruct (HH1 (Nat.max N Neqq)) as [x [xlt lt2]].
      exists x.
      split.
      * etransitivity; try apply xlt.
        apply Nat.le_max_l.
      * rewrite <- eqq; trivial.
        etransitivity; try apply xlt.
        apply Nat.le_max_r.
    + exists (Nat.max N2 Neqq).
      intros x xlt.
      rewrite <- eqq.
      * apply HH2.
        etransitivity; try apply xlt.
        apply Nat.le_max_l.
      * etransitivity; try apply xlt.
        apply Nat.le_max_r.
  - intros M.
    specialize (lim1 M).
    destruct lim1 as [N lim1].
    exists (Nat.max N Neqq); intros x xlt.
      rewrite <- eqq.
      * apply lim1.
        etransitivity; try apply xlt.
        apply Nat.le_max_l.
      * etransitivity; try apply xlt.
        apply Nat.le_max_r.
  - intros M N.
    specialize (lim1 M (Nat.max N Neqq)).
    destruct lim1 as [x [xlt lt2]].
    exists x.
    split.
      * etransitivity; try apply xlt.
        apply Nat.le_max_l.
      * rewrite <- eqq; trivial.
        etransitivity; try apply xlt.
        apply Nat.le_max_r.
Qed.

Lemma all_eventually (P : nat -> Prop) :
  (forall x, P x) -> eventually P.
Proof.
  intros.
  exists 0%nat; auto.
Qed.

Lemma eventually_impl (P Q : nat -> Prop) :
  eventually (fun n => P n  -> Q n) ->
  eventually P ->
  eventually Q.
Proof.
  intros [N1 ?] [N2 ?].
  exists (Nat.max N1 N2).
  intros N ltN.
  apply H.
  - rewrite <- ltN.
    apply Nat.le_max_l.
  - apply H0.
    rewrite <- ltN.
    apply Nat.le_max_r.
Qed.

Lemma eventually_and (P Q : nat -> Prop) :
  eventually P ->
  eventually Q ->
  eventually (fun n => P n /\ Q n).
Proof.
  intros [N1 ?] [N2 ?].
  exists (Nat.max N1 N2).
  intros N ltN.
  split.
  - apply H.
    rewrite <- ltN.
    apply Nat.le_max_l.
  - apply H0.
    rewrite <- ltN.
    apply Nat.le_max_r.
Qed.

Lemma is_ELimInf_seq_ext (u v : nat -> Rbar) (l : Rbar) :
  (forall n, u n = v n)
  -> is_ELimInf_seq u l -> is_ELimInf_seq v l.
Proof.
  intros eqq.
  apply is_ELimInf_seq_ext_loc.
  now apply all_eventually.
Qed.

Global Instance is_ELimInf_seq_proper :
  Proper (pointwise_relation _ eq ==> eq ==> iff)  is_ELimInf_seq.
Proof.
  unfold pointwise_relation.
  intros ??????; subst.
  split; apply is_ELimInf_seq_ext; eauto.
Qed.

Lemma is_ELimSup_opp_ELimInf_seq (u : nat -> Rbar) (l : Rbar) :
  is_ELimSup_seq (fun n => Rbar_opp (u n)) (Rbar_opp l)
  <-> is_ELimInf_seq u l.
Proof.
  rewrite <- is_ELimInf_opp_ELimSup_seq.
  apply is_ELimInf_seq_proper.
  - intros ?.
    now rewrite Rbar_opp_involutive.
  - now rewrite Rbar_opp_involutive.
Qed.

Lemma is_ELimSup_seq_ext_loc (u v : nat -> Rbar) (l : Rbar) :
  eventually (fun n => u n = v n) ->
  is_ELimSup_seq u l -> is_ELimSup_seq v l.
Proof.
  intros.
  apply is_ELimInf_opp_ELimSup_seq.
  apply (is_ELimInf_seq_ext_loc (fun n => Rbar_opp (u n))).
  - revert H.
    apply filter_imp.
    intros; congruence.
  - now apply is_ELimInf_opp_ELimSup_seq.
Qed.
  
Lemma is_ELimSup_seq_ext (u v : nat -> Rbar) (l : Rbar) :
  (forall n, u n = v n)
  -> is_ELimSup_seq u l -> is_ELimSup_seq v l.
Proof.
  intros eqq.
  apply is_ELimSup_seq_ext_loc.
  now apply filter_forall.
Qed.

Global Instance is_ELimSup_seq_proper :
  Proper (pointwise_relation _ eq ==> eq ==> iff) is_ELimSup_seq.
Proof.
  unfold pointwise_relation.
  intros ??????; subst.
  split; apply is_ELimSup_seq_ext; eauto.
Qed.

Example posreal1 : posreal := mkposreal 1 Rlt_0_1.

Lemma is_ELimSup_infSup_seq (u : nat -> Rbar) (l : Rbar) :
  is_ELimSup_seq u l <-> Lim_seq.is_inf_seq (fun m => Lim_seq.Sup_seq (fun n => u (n + m)%nat)) l.
Proof.
  unfold is_ELimSup_seq, Lim_seq.is_inf_seq.
  destruct l; simpl.
  - split.
    + intros.
      split; intros.
      * specialize (H eps).
        destruct H as [? _].
        apply Lim_seq.Sup_seq_minor_lt.
        destruct (H n) as [x [??]].
        exists (x-n)%nat.
        rewrite Nat.sub_add; trivial.
      * specialize (H (pos_div_2 eps)).
        destruct H as [_ [??]].
        exists x.
        unfold Lim_seq.Sup_seq, proj1_sig.
        match_destr.
        red in i.
        destruct x0; simpl in *; try tauto.
        -- destruct (i (pos_div_2 eps)) as [?[??]].
           specialize (H (x0 + x)%nat).
           cut_to H; try lia.
           match_destr_in H1; try tauto.
           simpl in *.
           lra.
        -- destruct (i (r + eps / 2)).
           specialize (H (x0 + x)%nat).
           cut_to H; try lia.
           match_destr_in H0.
           simpl in *.
           lra.
    + intros.
      split; intros.
      * specialize (H eps).
        destruct H as [? _].
        specialize (H N).
        apply Lim_seq.Sup_seq_minor_lt in H.
        destruct H as [??].
        exists (x + N)%nat.
        split; try lia.
        match_destr.
      * specialize (H eps).
        destruct H as [_ ?].
        destruct H as [??].
        exists x; intros.
        apply (Rbar_not_le_lt).
        intros ?.
        apply Rbar_lt_not_le in H.
        apply H.
        apply (Lim_seq.Sup_seq_minor_le _ _ (n - x)%nat).
        rewrite Nat.sub_add; trivial.
  - split; intros.
    destruct (H M n) as [? [??]].
    + apply Lim_seq.Sup_seq_minor_lt.
      exists (x - n)%nat.
      rewrite Nat.sub_add; trivial.
    + specialize (H M N).
      apply  Lim_seq.Sup_seq_minor_lt in H.
      destruct H as [x ?].
      exists (x + N)%nat.
      split; trivial; try lia.
  - split; intros HH M.
    + specialize (HH (M-1)).
      destruct HH as [N HH].
      exists N.
      unfold Lim_seq.Sup_seq, proj1_sig.
      match_destr.
      red in i.
      destruct x; simpl; try tauto.
      * destruct (i posreal1) as [? [n ?]]; simpl in *.
        specialize (HH (n+N)%nat).
        cut_to HH; try lia.
        match_destr_in H0; try tauto.
        simpl in *.
        lra.
      * destruct (i M) as [x ?].
        specialize (HH (x+N)%nat).
        cut_to HH; try lia.
        destruct (u (x+N)%nat); simpl in *; try lra.
    + destruct (HH M) as [N ?].
      exists N; intros.
      apply (Rbar_not_le_lt M (u n)).
      intros ?.
      apply Rbar_le_not_lt in H; trivial.
      apply (Lim_seq.Sup_seq_minor_le _ _ (n - N)%nat).
      now rewrite MyNat.sub_add.
Qed.
  
Lemma is_ELimInf_supInf_seq (u : nat -> Rbar) (l : Rbar) :
  is_ELimInf_seq u l <-> Lim_seq.is_sup_seq (fun m => Lim_seq.Inf_seq (fun n => u (n + m)%nat)) l.
Proof.
  rewrite <- is_ELimSup_opp_ELimInf_seq.
  rewrite is_ELimSup_infSup_seq.
  rewrite <- Lim_seq.is_sup_opp_inf_seq.
  rewrite Rbar_opp_involutive.
  split ; apply Lim_seq.is_sup_seq_ext; intros
  ; now rewrite Lim_seq.Inf_opp_sup.
Qed.

Lemma ex_ELimSup_seq (u : nat -> Rbar) :
  {l : Rbar | is_ELimSup_seq u l}.
Proof.
  destruct (Lim_seq.ex_inf_seq (fun m : nat => Lim_seq.Sup_seq (fun n : nat => u (n + m)%nat))).
  exists x.
  now apply is_ELimSup_infSup_seq.
Qed.
  
Lemma ex_ELimInf_seq (u : nat -> Rbar) :
  {l : Rbar | is_ELimInf_seq u l}.
Proof.
  destruct (Lim_seq.ex_sup_seq (fun m : nat => Lim_seq.Inf_seq (fun n : nat => u (n + m)%nat))).
  exists x.
  now apply is_ELimInf_supInf_seq.
Qed.

Definition ELimSup_seq (u : nat -> Rbar) :=
  proj1_sig (ex_ELimSup_seq u).

Definition ELimInf_seq (u : nat -> Rbar) :=
  proj1_sig (ex_ELimInf_seq u).

Lemma is_ELimSup_seq_correct (u: nat -> Rbar) :
  is_ELimSup_seq u (ELimSup_seq u).
Proof.
  unfold ELimSup_seq, proj1_sig.
  match_destr.
Qed.

Lemma is_ELimInf_seq_correct (u: nat -> Rbar) :
  is_ELimInf_seq u (ELimInf_seq u).
Proof.
  unfold ELimInf_seq, proj1_sig.
  match_destr.
Qed.

Lemma is_ELimSup_seq_unique (u : nat -> Rbar) (l : Rbar) :
  is_ELimSup_seq u l -> ELimSup_seq u = l.
Proof.
  intros.
  unfold ELimSup_seq, proj1_sig.
  match_destr.
  apply is_ELimSup_infSup_seq in H.
  apply is_ELimSup_infSup_seq in i.

  rewrite <- (Lim_seq.is_inf_seq_unique _ _ H).
  now rewrite <- (Lim_seq.is_inf_seq_unique _ _ i).
Qed.
  
Lemma is_ELimInf_seq_unique (u : nat -> Rbar) (l : Rbar) :
  is_ELimInf_seq u l -> ELimInf_seq u = l.
Proof.
  intros.
  unfold ELimInf_seq, proj1_sig.
  match_destr.
  apply is_ELimInf_supInf_seq in H.
  apply is_ELimInf_supInf_seq in i.
  rewrite <- (Lim_seq.is_sup_seq_unique _ _ H).
  now rewrite <- (Lim_seq.is_sup_seq_unique _ _ i).
Qed.

Lemma ELimInf_seq_fin (u : nat -> R) :
  ELimInf_seq u = Lim_seq.LimInf_seq u.
Proof.
  apply is_ELimInf_seq_unique.
  apply is_ELimInf_seq_fin.
  unfold Lim_seq.LimInf_seq, proj1_sig.
  match_destr.
Qed.

Lemma ELimSup_seq_fin (u : nat -> R) :
  ELimSup_seq u = Lim_seq.LimSup_seq u.
Proof.
  apply is_ELimSup_seq_unique.
  apply is_ELimSup_seq_fin.
  unfold Lim_seq.LimSup_seq, proj1_sig.
  match_destr.
Qed.

Lemma ELimSup_InfSup_seq (u : nat -> Rbar) :
  ELimSup_seq u = Lim_seq.Inf_seq (fun m => Lim_seq.Sup_seq (fun n => u (n + m)%nat)).
Proof.
  apply is_ELimSup_seq_unique.
  apply is_ELimSup_infSup_seq.
  apply Lim_seq.Inf_seq_correct.
Qed.

Lemma ELimInf_SupInf_seq (u : nat -> Rbar) :
  ELimInf_seq u = Lim_seq.Sup_seq (fun m => Lim_seq.Inf_seq (fun n => u (n + m)%nat)).
Proof.
  apply is_ELimInf_seq_unique.
  apply is_ELimInf_supInf_seq.
  apply Lim_seq.Sup_seq_correct.
Qed.


Lemma is_ELimSup_ELimInf_seq_le (u : nat -> Rbar) (ls li : Rbar) :
  is_ELimSup_seq u ls -> is_ELimInf_seq u li -> Rbar_le li ls.
Proof.
  intros sup inf.
  destruct ls; destruct li; simpl; try tauto
  ; simpl in *.
  - apply le_epsilon; intros eps pos.
    specialize (sup (pos_div_2 (mkposreal _ pos))).
    specialize (inf (pos_div_2 (mkposreal _ pos))).
    destruct sup as [sup1 [xs sup2]].
    destruct inf as [inf1 [xi inf2]].
    specialize (sup2 (xi + xs)%nat).
    cut_to sup2; try lia.
    specialize (inf2 (xi + xs)%nat).
    cut_to inf2; try lia.
    simpl in *.
    destruct (u (xi + xs)%nat); simpl in *; lra.
  - destruct (sup posreal1) as [?[??]].
    destruct (inf (r+1)).
    specialize (H0 (x + x0)%nat).
    cut_to H0; try lia.
    specialize (H1 (x + x0)%nat).
    cut_to H1; try lia.
    destruct (u (x + x0)%nat); simpl in *; lra.
  - destruct (inf posreal1) as [?[??]].
    destruct (sup (r-1)).
    specialize (H0 (x + x0)%nat).
    cut_to H0; try lia.
    specialize (H1 (x + x0)%nat).
    cut_to H1; try lia.
    destruct (u (x + x0)%nat); simpl in *; lra.
  - destruct (sup 0).
    destruct (inf 0).
    specialize (H (x + x0)%nat).
    cut_to H; try lia.
    specialize (H0 (x + x0)%nat).
    cut_to H0; try lia.
    destruct (u (x + x0)%nat); simpl in *; lra.
Qed.    

Lemma ELimSup_ELimInf_seq_le (u : nat -> Rbar) :
  Rbar_le (ELimInf_seq u) (ELimSup_seq u).
Proof.
  unfold ELimInf_seq, ELimSup_seq, proj1_sig.
  repeat match_destr.
  eapply is_ELimSup_ELimInf_seq_le; eauto.
Qed.

Lemma is_ELimSup_seq_const (a : Rbar) :
  is_ELimSup_seq (fun _ => a) a.
Proof.
  destruct a; simpl; intros.
  - split.
    + intros.
      exists N.
      split; trivial.
      destruct eps; simpl; lra.
    + exists 0%nat; intros.
      destruct eps; simpl; lra.
  - exists N.
    split; trivial.
  - exists 0%nat.
    trivial.
Qed.
  
Lemma ELimSup_seq_const (a : Rbar) :
  ELimSup_seq (fun _ => a) = a.
Proof.
  apply is_ELimSup_seq_unique.
  apply is_ELimSup_seq_const.
Qed.

Lemma is_ELimInf_seq_const (a : Rbar) :
  is_ELimInf_seq (fun _ => a) a.
Proof.
  apply is_ELimSup_opp_ELimInf_seq.
  apply is_ELimSup_seq_const.
Qed.

Lemma ELimInf_seq_const (a : Rbar) :
  ELimInf_seq (fun _ => a) = a.
Proof.
  apply is_ELimInf_seq_unique.
  apply is_ELimInf_seq_const.
Qed.

Lemma ELimSup_seq_opp (u : nat -> Rbar) :
  ELimSup_seq (fun n => Rbar_opp (u n)) = Rbar_opp (ELimInf_seq u).
Proof.
  apply is_ELimSup_seq_unique.
  apply is_ELimSup_opp_ELimInf_seq.
  apply is_ELimInf_seq_correct.
Qed.
  
Lemma ELimInf_seq_opp (u : nat -> Rbar) :
  ELimInf_seq (fun n => Rbar_opp (u n)) = Rbar_opp (ELimSup_seq u).
Proof.
  apply is_ELimInf_seq_unique.
  apply is_ELimInf_opp_ELimSup_seq.
  apply is_ELimSup_seq_correct.
Qed.  

Lemma is_ELimSup_le (u v : nat -> Rbar) (lu lv:Rbar) :
  eventually (fun n : nat => Rbar_le (u n) (v n)) ->
  is_ELimSup_seq u lu ->
  is_ELimSup_seq v lv ->
  Rbar_le lu lv.
Proof.
  intros [N le] sup1 sup2.
  destruct lu; destruct lv; simpl in *; trivial.
  - destruct (Rle_dec r r0); trivial.
    assert (pos:0 < r - r0) by lra.
    specialize (sup1 (pos_div_2 (mkposreal _ pos))).
    specialize (sup2 (pos_div_2 (mkposreal _ pos))).
    destruct sup1 as [sup1 _].
    destruct sup2 as [_ [x2 sup2]].
    specialize (sup1 (N+x2)%nat).
    destruct sup1 as [? [??]].
    specialize (le x).
    cut_to le; try lia.
    specialize (sup2 x).
    cut_to sup2; try lia.
    simpl in *.
    destruct (u x); destruct (v x); simpl in *; try lra.
  - destruct (sup2 (r-1)).
    destruct (sup1 posreal1) as [HH _].
    destruct (HH (N+x)%nat) as [?[??]].
    specialize (le x0).
    cut_to le; try lia.
    specialize (H x0).
    cut_to H; try lia.
    destruct (u x0); destruct (v x0); simpl in *; lra.
  - destruct (sup2 posreal1) as [_ [??]].
    destruct (sup1 (r+1) (N+x)%nat) as [?[??]].
    specialize (le x0).
    cut_to le; try lia.
    specialize (H x0).
    cut_to H; try lia.
    destruct (u x0); destruct (v x0); simpl in *; lra.
  - destruct (sup2 0) as [??].
    destruct (sup1 0 (N+x)%nat).
    specialize (le x0).
    cut_to le; try lia.
    specialize (H x0).
    cut_to H; try lia.
    destruct (u x0); destruct (v x0); simpl in *; lra.
Qed.

Lemma Rbar_opp_le_contravar (r1 r2 : Rbar) :
  Rbar_le (Rbar_opp r1) (Rbar_opp r2) <->
  Rbar_le r2 r1.
Proof.
  intros.
  destruct r1; destruct r2; simpl in *; rbar_prover.
Qed.

Lemma is_ELimInf_le (u v : nat -> Rbar) (lu lv:Rbar) :
  eventually (fun n : nat => Rbar_le (u n) (v n)) ->
  is_ELimInf_seq u lu ->
  is_ELimInf_seq v lv ->
  Rbar_le lu lv.
Proof.
  intros.
  apply Rbar_opp_le_contravar.
  apply is_ELimSup_opp_ELimInf_seq in H0.
  apply is_ELimSup_opp_ELimInf_seq in H1.
  eapply is_ELimSup_le; try eapply H1; try eapply H0.
  revert H.
  apply filter_imp; intros.
  now apply Rbar_opp_le_contravar.
Qed.

Lemma ELimSup_le (u v : nat -> Rbar) :
  eventually (fun n => Rbar_le (u n) (v n))
  -> Rbar_le (ELimSup_seq u) (ELimSup_seq v).
Proof.
  intros.
  unfold ELimSup_seq, proj1_sig.
  repeat match_destr.
  eapply is_ELimSup_le; eauto.
Qed.
  
Lemma ELimInf_le (u v : nat -> Rbar) :
  eventually (fun n => Rbar_le (u n) (v n))
  -> Rbar_le (ELimInf_seq u) (ELimInf_seq v).
Proof.
  intros.
  unfold ELimInf_seq, proj1_sig.
  repeat match_destr.
  eapply is_ELimInf_le; eauto.
Qed.

Lemma ELimSup_seq_ext_loc (u v : nat -> Rbar) :
  eventually (fun n => u n = v n) ->
  ELimSup_seq u = ELimSup_seq v.
Proof.
  intros eqq.
  apply is_ELimSup_seq_unique.
  apply (is_ELimSup_seq_ext_loc v u).
  - revert eqq.
    apply filter_imp.
    eauto.
  - apply is_ELimSup_seq_correct.
Qed.

Lemma ELimInf_seq_ext_loc (u v : nat -> Rbar) :
  eventually (fun n => u n = v n) ->
  ELimInf_seq u = ELimInf_seq v.
Proof.
  intros eqq.
  apply is_ELimInf_seq_unique.
  apply (is_ELimInf_seq_ext_loc v u).
  - revert eqq.
    apply filter_imp.
    eauto.
  - apply is_ELimInf_seq_correct.
Qed.

Global Instance ELimSup_proper :
  Proper (pointwise_relation _ eq ==> eq) ELimSup_seq.
Proof.
  intros ???.
  apply ELimSup_seq_ext_loc.
  now apply filter_forall.
Qed.

Global Instance ELimInf_proper :
  Proper (pointwise_relation _ eq ==> eq) ELimInf_seq.
Proof.
  intros ???.
  apply ELimInf_seq_ext_loc.
  now apply filter_forall.
Qed.

Global Instance ELimSup_le_proper :
  Proper (pointwise_relation _ Rbar_le ==> Rbar_le) ELimSup_seq.
Proof.
  intros ???.
  apply ELimSup_le.
  now apply filter_forall.
Qed.

Global Instance ELimInf_le_proper :
  Proper (pointwise_relation _ Rbar_le ==> Rbar_le) ELimInf_seq.
Proof.
  intros ???.
  apply ELimInf_le.
  now apply filter_forall.
Qed.

Lemma is_ELimSup_seq_scal_pos_aux (a : R) (u : nat -> Rbar) (l : Rbar) :
  0 < a ->
  is_ELimSup_seq u l ->
  is_ELimSup_seq (fun n => Rbar_mult a (u n)) (Rbar_mult a l).
Proof.
  intros apos sup.
  destruct l; simpl in *.
  - intros eps.
    assert (pos:0 < eps / a).
    {
      apply RIneq.Rdiv_lt_0_compat; trivial.
      apply cond_pos.
    } 
    specialize (sup (mkposreal _ pos)).
    destruct sup as [sup1 sup2].
    split.
    + intros N1.
      destruct (sup1 N1) as [x [xle sup1N]].
      exists x.
      split; trivial.
      destruct eps; simpl in *.
      destruct (u x); simpl in *; rbar_prover.
      rewrite (Rmult_comm _ r0).
      apply Rlt_div_l; try lra.
      rewrite RIneq.Rdiv_minus_distr.
      unfold Rdiv.
      rewrite Rinv_r_simpl_m; lra.
    + destruct sup2 as [x sup2].
      exists x; intros n len.
      specialize (sup2 n len).
      simpl in sup2.
      destruct eps; simpl in *.
      destruct (u n); simpl in *; rbar_prover.
      apply (Rmult_lt_compat_l a) in sup2; try lra.
      rewrite Rmult_plus_distr_l in sup2.
      unfold Rdiv in sup2.
      rewrite <- Rmult_assoc in sup2.
      rewrite Rinv_r_simpl_m in sup2; lra.
  - rbar_prover; simpl.
    intros M N.
    destruct (sup (M / a) N) as [?[??]].
    exists x.
    split; trivial.
    destruct (u x); simpl; rbar_prover.
    rewrite Rmult_comm.
    apply Rlt_div_l; try lra.
  - rbar_prover; simpl.
    intros M.
    destruct (sup (M / a)).
    exists x; intros.
    specialize (H _ H0).
    destruct (u n); simpl in *; rbar_prover.
    rewrite Rmult_comm.
    apply Rlt_div_r; try lra.
Qed.

Lemma is_ELimSup_seq_scal_pos (a : R) (u : nat -> Rbar) (l : Rbar) :
  0 <= a ->
  is_ELimSup_seq u l ->
  is_ELimSup_seq (fun n => Rbar_mult a (u n)) (Rbar_mult a l).
Proof.
  intros [?|?].
  - now apply is_ELimSup_seq_scal_pos_aux.
  - subst; intros.
    generalize (is_ELimSup_seq_const 0).
    apply is_ELimSup_seq_proper.
    + intros ?.
      now rewrite Rbar_mult_0_l.
    + now rewrite Rbar_mult_0_l.
Qed.

Lemma ELimSup_seq_scal_pos (a : R) (u : nat -> Rbar) :
  0 <= a ->
  ELimSup_seq (fun n => Rbar_mult a (u n))  = Rbar_mult a (ELimSup_seq u).
Proof.
  intros.
  apply is_ELimSup_seq_unique.
  apply is_ELimSup_seq_scal_pos; trivial.
  apply is_ELimSup_seq_correct.
Qed.

Lemma is_ELimInf_seq_scal_pos (a : R) (u : nat -> Rbar) (l : Rbar) :
  0 <= a ->
  is_ELimInf_seq u l ->
  is_ELimInf_seq (fun n => Rbar_mult a (u n)) (Rbar_mult a l).
Proof.
  intros.
  apply is_ELimSup_opp_ELimInf_seq.
  assert (eqq1:pointwise_relation _ eq
                                  (fun n : nat => Rbar_opp (Rbar_mult a (u n)))
                                  (fun n : nat => Rbar_mult a (Rbar_opp (u n)))).
  {
    intros ?.
    now rewrite Rbar_mult_opp_r.
  }
  rewrite eqq1.
  rewrite <- Rbar_mult_opp_r.
  apply is_ELimSup_seq_scal_pos; trivial.
  now apply is_ELimSup_opp_ELimInf_seq in H0.
Qed.

Lemma ELimInf_seq_scal_pos (a : R) (u : nat -> Rbar) :
  0 <= a ->
  ELimInf_seq (fun n => Rbar_mult a (u n))  = Rbar_mult a (ELimInf_seq u).
Proof.
  intros.
  apply is_ELimInf_seq_unique.
  apply is_ELimInf_seq_scal_pos; trivial.
  apply is_ELimInf_seq_correct.
Qed.

Lemma is_ELimSup_seq_ind_1 (u : nat -> Rbar) (l : Rbar) :
  is_ELimSup_seq u l <->
  is_ELimSup_seq (fun n => u (S n)) l.
Proof.
  destruct l; simpl.
  - split; intros HH eps
    ; specialize (HH eps);
      (split; [destruct HH as [HH _] | destruct HH as [_ [n HH]]]).
    + intros N.
      destruct (HH (S N)) as [?[??]].
      destruct x; try lia.
      exists x.
      split; trivial; lia.
    + exists n; intros.
      apply HH; lia.
    + intros N.
      destruct (HH N) as [?[??]].
      exists (S x).
      split; trivial; lia.
    + exists (S n); intros.
      destruct n0; try lia.
      apply HH; lia.
  - split; intros HH M N
    ; specialize (HH M).
    + destruct (HH (S N)) as [?[??]].
      destruct x; try lia.
      exists x.
      split; trivial; lia.
    + destruct (HH N) as [?[??]].
      exists (S x).
      split; trivial; lia.
  - split; intros HH M
    ; specialize (HH M); destruct HH as [N ?].
    + exists N; intros.
      apply H; lia.
    + exists (S N); intros.
      destruct n; try lia.
      apply H; lia.
Qed.

Lemma ELimSup_seq_ind_1 (u : nat -> Rbar)  :
  ELimSup_seq (fun n => u (S n)) = ELimSup_seq u.
Proof.
  apply is_ELimSup_seq_unique.
  apply -> is_ELimSup_seq_ind_1.
  apply is_ELimSup_seq_correct.
Qed.

Lemma is_ELimInf_seq_ind_1 (u : nat -> Rbar) (l : Rbar) :
  is_ELimInf_seq u l <->
  is_ELimInf_seq (fun n => u (S n)) l.
Proof.
  split; intros HH
  ; apply is_ELimSup_opp_ELimInf_seq in HH
  ; apply is_ELimSup_opp_ELimInf_seq.
  - now apply is_ELimSup_seq_ind_1 in HH.
  - now apply is_ELimSup_seq_ind_1.
Qed.

Lemma ELimInf_seq_ind_1 (u : nat -> Rbar)  :
  ELimInf_seq (fun n => u (S n)) = ELimInf_seq u.
Proof.
  apply is_ELimInf_seq_unique.
  apply -> is_ELimInf_seq_ind_1.
  apply is_ELimInf_seq_correct.
Qed.

Lemma is_ELimSup_seq_ind_k (u : nat -> Rbar) (k : nat) (l : Rbar) :
  is_ELimSup_seq u l <->
  is_ELimSup_seq (fun n => u (n + k)%nat) l.
Proof.
  induction k; simpl.
  - apply is_ELimSup_seq_proper; trivial.
    intros ?; f_equal; lia.
  - rewrite IHk.
    rewrite is_ELimSup_seq_ind_1.
    apply is_ELimSup_seq_proper; trivial.
    intros ?; f_equal; lia.
Qed.
  
Lemma is_ELimInf_seq_ind_k (u : nat -> Rbar) (k : nat) (l : Rbar) :
  is_ELimInf_seq u l <->
    is_ELimInf_seq (fun n => u (n + k)%nat) l.
Proof.
  induction k; simpl.
  - apply is_ELimInf_seq_proper; trivial.
    intros ?; f_equal; lia.
  - rewrite IHk.
    rewrite is_ELimInf_seq_ind_1.
    apply is_ELimInf_seq_proper; trivial.
    intros ?; f_equal; lia.
Qed.

Lemma ELimSup_seq_ind_k (u : nat -> Rbar) (k:nat)  :
  ELimSup_seq (fun n => u (n + k)%nat) = ELimSup_seq u.
Proof.
  apply is_ELimSup_seq_unique.
  apply -> is_ELimSup_seq_ind_k.
  apply is_ELimSup_seq_correct.
Qed.

Lemma ELimInf_seq_ind_k (u : nat -> Rbar) (k : nat) :
  ELimInf_seq (fun n => u (n + k)%nat) = ELimInf_seq u.
Proof.
  apply is_ELimInf_seq_unique.
  apply -> is_ELimInf_seq_ind_k.
  apply is_ELimInf_seq_correct.
Qed.

Definition ELim_seq (u : nat -> Rbar) : Rbar :=
  Rbar_div_pos (Rbar_plus (ELimSup_seq u) (ELimInf_seq u))
    {| pos := 2; cond_pos := Rlt_R0_R2 |}.

Definition ex_Elim_seq (u : nat -> Rbar) := ELimSup_seq u = ELimInf_seq u.

Definition is_Elim_seq (u : nat -> Rbar) (l : Rbar) := is_ELimInf_seq u l /\ is_ELimSup_seq u l.

Definition is_Elim_seq' (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, eventually (fun n => Rbar_lt (Rbar_abs (Rbar_minus (u n) l)) eps)
    | p_infty => forall M : R, eventually (fun n => Rbar_lt M (u n))
    | m_infty => forall M : R, eventually (fun n => Rbar_lt (u n) M)
  end.

Lemma is_Elim_seq_spec :
  forall u l,
    is_Elim_seq' u l <-> is_Elim_seq u l.
Proof.
  unfold is_Elim_seq.
  destruct l; simpl in *; split; intros HH.
  - split; intros eps; destruct (HH eps); clear HH
    ; repeat split; intros.
    + exists (max N x).
      split; try lia.
      specialize (H (max N x)).
      cut_to H; try lia.
      destruct (u (Init.Nat.max N x)); simpl in *; rbar_prover.
      generalize (Rle_abs (r0 + - r)); intros; lra.
    + exists x; intros.
      specialize (H _ H0).
      match_destr; simpl in *.
      rewrite Rabs_minus_sym in H.
      generalize (Rle_abs (r - r0)); intros; lra.
    + exists (max N x).
      split; try lia.
      specialize (H (max N x)).
      cut_to H; try lia.
      destruct (u (Init.Nat.max N x)); simpl in *; rbar_prover.
      rewrite Rabs_minus_sym in H.
      generalize (Rle_abs (r - r0)); intros; lra.
    + exists x; intros.
      specialize (H _ H0).
      destruct (u n); simpl in *; rbar_prover.
      generalize (Rle_abs (r0 + - r)); intros; lra.
  - intros eps; red.
    destruct HH as [HH1 HH2].
    specialize (HH1 eps); specialize (HH2 eps).
    destruct HH1 as [?[??]].
    destruct HH2 as [?[??]].

    exists (max x x0); intros.
    specialize (H0 n).
    specialize (H2 n).
    cut_to H0; try lia.
    cut_to H2; try lia.
    destruct (u n); simpl in *; try lra.
    unfold Rabs.
    match_destr; lra.
  - split; intros M; specialize (HH M); destruct HH.
    + exists x; intros.
      now apply H.
    + intros.
      exists (max N x).
      split; try lia.
      apply H; lia.
  - intros M.
    destruct HH as [HH1 HH2].
    specialize (HH1 M); specialize (HH2 M).
    destruct HH1 as [??].
    exists x; trivial.
  - split; intros M; specialize (HH M); destruct HH; intros.
    + exists (max x N).
      split; try lia.
      apply H; lia.
    + eauto.
  - intros M.
    destruct HH as [HH1 HH2].
    specialize (HH1 M); specialize (HH2 M).
    destruct HH2 as [??].
    exists x; trivial.
Qed.      

Lemma is_Elim_seq_fin (u : nat -> R) (l : Rbar) :
  is_Elim_seq u l <-> Lim_seq.is_lim_seq u l.
Proof.
  split; intros HH.
  - destruct HH as [HHi HHs].
    apply Lim_seq.is_LimSup_LimInf_lim_seq.
    + now apply is_ELimSup_seq_fin.
    + now apply is_ELimInf_seq_fin.
  - split.    
    + apply is_ELimInf_seq_fin.
      now apply Lim_seq.is_lim_LimInf_seq.
    + apply is_ELimSup_seq_fin.
      now apply Lim_seq.is_lim_LimSup_seq.
Qed.

Lemma is_Elim_seq_Reals (u : nat -> R) (l : R) :
  is_Elim_seq u l <-> Un_cv u l.
Proof.
  etransitivity; [apply is_Elim_seq_fin | ].
  apply Lim_seq.is_lim_seq_Reals.
Qed.
  
Lemma is_Elim_seq_p_infty_Reals (u : nat -> R) :
  is_Elim_seq u p_infty <-> cv_infty u.
Proof.
  etransitivity; [apply is_Elim_seq_fin | ].
  apply Lim_seq.is_lim_seq_p_infty_Reals.
Qed.

Lemma is_Elim_LimSup_seq (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l -> is_ELimSup_seq u l.
Proof.
  now intros [??].
Qed.
  
Lemma is_Elim_LimInf_seq (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l -> is_ELimInf_seq u l.
Proof.
  now intros [??].
Qed.

Lemma is_ELimSup_LimInf_lim_seq (u : nat -> Rbar) (l : Rbar) :
  is_ELimSup_seq u l -> is_ELimInf_seq u l -> is_Elim_seq u l.
Proof.
    split; trivial.
Qed.

Lemma ex_Elim_LimSup_LimInf_seq (u : nat -> Rbar) :
  ex_Elim_seq u <-> ELimSup_seq u = ELimInf_seq u.
Proof.
  reflexivity.
Qed.

Lemma is_Elim_seq_ex_Elim_seq (u : nat -> Rbar) (l: Rbar) :
  is_Elim_seq u l -> ex_Elim_seq u.
Proof.
  intros [??].
  red.
  now rewrite (is_ELimInf_seq_unique _ _ H) (is_ELimSup_seq_unique _ _ H0).
Qed.

Lemma ex_Elim_seq_is_Elim_seq_sup (u : nat -> Rbar) :
  ex_Elim_seq u -> is_Elim_seq u (ELimSup_seq u).
Proof.
  unfold is_Elim_seq; intros.
  split.
  - red in H; rewrite H.
    apply is_ELimInf_seq_correct.
  - apply is_ELimSup_seq_correct.
Qed.

Lemma ex_Elim_seq_is_Elim_seq_inf (u : nat -> Rbar) :
  ex_Elim_seq u -> is_Elim_seq u (ELimInf_seq u).
Proof.
  unfold is_Elim_seq; intros.
  split.
  - apply is_ELimInf_seq_correct.
  - red in H; rewrite <- H.
    apply is_ELimSup_seq_correct.
Qed.

Lemma is_Elim_seq_ext_loc (u v : nat -> Rbar) (l : Rbar) :
  eventually (fun n => u n = v n) ->
  is_Elim_seq u l -> is_Elim_seq v l.
Proof.
  intros ? [??].
  split.
  - eapply is_ELimInf_seq_ext_loc; eauto.
  - eapply is_ELimSup_seq_ext_loc; eauto.
Qed.
  
Lemma ex_Elim_seq_ext_loc (u v : nat -> Rbar) :
  eventually (fun n => u n = v n) ->
  ex_Elim_seq u -> ex_Elim_seq v.
Proof.
  unfold ex_Elim_seq; intros.
  erewrite <- ELimSup_seq_ext_loc; eauto.
  erewrite <- ELimInf_seq_ext_loc; eauto.
Qed.
  
Lemma ELim_seq_ext_loc (u v : nat -> Rbar) :
  eventually (fun n => u n = v n) ->
  ELim_seq u = ELim_seq v.
Proof.
  unfold ELim_seq; intros.
  erewrite ELimSup_seq_ext_loc; eauto.
  erewrite ELimInf_seq_ext_loc; eauto.
Qed.

Lemma is_Elim_seq_ext (u v : nat -> Rbar) (l : Rbar) :
  (forall n, u n = v n) -> is_Elim_seq u l -> is_Elim_seq v l.
Proof.
  intros.
  eapply is_Elim_seq_ext_loc; eauto.
  now apply all_eventually.
Qed.
  
Lemma ex_Elim_seq_ext (u v : nat -> Rbar) :
  (forall n, u n = v n) -> ex_Elim_seq u -> ex_Elim_seq v.
Proof.
  intros.
  eapply ex_Elim_seq_ext_loc; eauto.
  now apply all_eventually.
Qed.

Lemma ELim_seq_ext (u v : nat -> Rbar) :
  (forall n, u n = v n) ->
  ELim_seq u = ELim_seq v.
Proof.
  intros.
  eapply ELim_seq_ext_loc; eauto.
  now apply all_eventually.
Qed.

Global Instance is_Elim_seq_proper :
  Proper (pointwise_relation _ eq ==> eq ==> iff)  is_Elim_seq.
Proof.
  intros ??????; subst.
  now split; apply is_Elim_seq_ext.
Qed.

Global Instance ex_Elim_seq_proper :
  Proper (pointwise_relation _ eq ==> iff) ex_Elim_seq.
Proof.
  intros ???; subst.
  now split; apply ex_Elim_seq_ext.
Qed.

Global Instance ELim_seq_proper :
  Proper (pointwise_relation _ eq ==> eq) ELim_seq.
Proof.
  intros ???; subst.
  now apply ELim_seq_ext.
Qed.


Lemma is_Elim_seq_unique (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l -> ELim_seq u = l.
Proof.
  intros [??].
  unfold ELim_seq.
  erewrite is_ELimSup_seq_unique; try eassumption.
  erewrite is_ELimInf_seq_unique; try eassumption.
  destruct l; simpl; rbar_prover.
Qed.

Lemma ELim_seq_correct (u : nat -> Rbar) :
  ex_Elim_seq u -> is_Elim_seq u (ELim_seq u).
Proof.
  intros HH.
  red in HH.
  unfold ELim_seq.
  rewrite HH.
  cut (is_Elim_seq u (ELimInf_seq u)).
  - apply is_Elim_seq_proper; try reflexivity.
    destruct (ELimInf_seq u); simpl; rbar_prover.
  - split.
    + apply is_ELimInf_seq_correct.
    + rewrite <- HH.
      apply is_ELimSup_seq_correct.
Qed.

Lemma ex_Elim_seq_fin (u : nat -> R) :
  ex_Elim_seq u <-> Lim_seq.ex_lim_seq u.
Proof.
  split; intros HH.
  - apply ELim_seq_correct in HH.
    apply is_Elim_seq_fin in HH.
    eexists; eauto.
  - destruct HH.
    eapply is_Elim_seq_ex_Elim_seq.
    apply is_Elim_seq_fin.
    eauto.
Qed.

Lemma Elim_seq_fin (u : nat -> R) :
  ELim_seq u = Lim_seq.Lim_seq u.
Proof.
  unfold ELim_seq, Lim_seq.Lim_seq.
  do 2 f_equal.
  - apply ELimSup_seq_fin.
  - apply ELimInf_seq_fin.
Qed.

Definition ex_finite_Elim_seq (u : nat -> Rbar) :=
  ex_Elim_seq u /\ is_finite (ELim_seq u).

Lemma ELim_seq_correct' (u : nat -> Rbar) :
  ex_finite_Elim_seq u -> is_Elim_seq u (real (ELim_seq u)).
Proof.
  intros [??].
  generalize (ELim_seq_correct _ H).
  apply is_Elim_seq_proper; try reflexivity.
  now rewrite <- H0.
Qed.

Lemma ex_finite_Elim_seq_correct (u : nat -> Rbar) :
  ex_finite_Elim_seq u <-> ex_Elim_seq u /\ is_finite (ELim_seq u).
Proof.
  reflexivity.
Qed.

Lemma ex_Elim_seq_sup (u : nat -> Rbar) :
  ex_Elim_seq u -> ELim_seq u = ELimSup_seq u.
Proof.
  intros.
  unfold ELim_seq.
  rewrite H.
  destruct (ELimInf_seq u); simpl; rbar_prover.
Qed.

Lemma ex_Elim_seq_dec (u : nat -> Rbar) :
  {ex_Elim_seq u} + {~ ex_Elim_seq u}.
Proof.
  apply Rbar_eq_dec.
Defined.

Lemma ex_finite_Elim_seq_dec (u : nat -> Rbar) :
  {ex_finite_Elim_seq u} + {~ ex_finite_Elim_seq u}.
Proof.
  unfold ex_finite_Elim_seq.
  destruct (ex_Elim_seq_dec u).
  - destruct (ELim_seq u); simpl; unfold is_finite.
    + left; intuition.
    + right; intuition congruence.
    + right; intuition congruence.
  - right; intros [??]; tauto.
Defined.

Definition ex_Elim_seq_cauchy (u : nat -> Rbar) :=
  forall eps : posreal, exists N : nat, forall n m,
        (N <= n)%nat -> (N <= m)%nat -> Rbar_lt (Rbar_abs (Rbar_minus (u n) (u m))) eps.

Local Existing Instance Rbar_le_pre.

(*
Lemma ex_lim_seq_cauchy_corr (u : nat -> Rbar) :
  (ex_finite_Elim_seq u) <-> ex_Elim_seq_cauchy u.
Proof.
  split; intros HH.
  - intros eps.
    apply ELim_seq_correct' in HH.
    apply is_Elim_seq_spec in HH.
    specialize (HH (pos_div_2 eps)).
    destruct HH as [N HH].
    exists N; intros.
    generalize (HH _ H); intros HH1.
    generalize (HH _ H0); intros HH2.
    generalize (Rbar_plus_lt_compat _ _ _ _ HH1 HH2)
    ; simpl
    ; intros HH3.
    rewrite <- double_var in HH3.
    eapply Rbar_le_lt_trans; try eapply HH3.
    rewrite (Rbar_abs_minus_sym (u m)).
    eapply Rbar_le_trans; [| apply Rbar_abs_triang].
    apply BasicUtils.refl_refl; f_equal.
    destruct (u n); destruct (u m); simpl; rbar_prover.
  - red in HH.
    
    assert (ex_Elim_seq u).
    {
      apply (is_Elim_seq_ex_Elim_seq u (ELimSup_seq u)).
      red.
      generalize (is_ELimSup_seq_correct u); intros HH1.
      split; trivial.
      red; match_case; intros.
      - rewrite H in HH1.
        specialize (HH1 eps).
        specialize (HH eps).
        destruct HH as [??].
        destruct HH1 as [? [??]].
        admit.
      - rewrite H in HH1.
        red in HH1.
        destruct (HH1 M 0%nat) as [?[??]].
        case_eq (u x)
        ; [intros ? eqq1 | intros eqq1..]
        ; rewrite eqq1 in H1
        ; simpl in *
        ; try tauto.
        + admit.
        + 
        
        
        case_eq (u n)
        ; [intros ? eqq1 | intros eqq1..]
        ; rewrite eqq1 in H1
        ; simpl in *
        ; try tauto.
        
        
        exists x; intros.
        eapply Rbar_lt_le_trans; try eapply H1.
        apply Rbar_not_lt_le
        ; intros nlt.
        case_eq (u x)
        ; [intros ? eqq1 | intros eqq1..]
        ; rewrite eqq1 in H1, nlt
        ; simpl in *
        ; try tauto.
        + 
        + specialize (HH posreal1).
          destruct HH as [??].
          specialize (H3 x n).
          cut_to H3.
          * rewrite Rbar_abs_minus_sym in H3.
            rewrite eqq1 in H3.
            destruct (u n); simpl in *; try tauto.
  
Qed.
 *)


Lemma is_Elim_seq_INR :
  is_Elim_seq INR p_infty.
Proof.
  apply is_Elim_seq_fin.
  apply Lim_seq.is_lim_seq_INR.
Qed.
  
Lemma ex_Elim_seq_INR :
  ex_Elim_seq INR.
Proof.
  eapply is_Elim_seq_ex_Elim_seq.
  apply is_Elim_seq_INR.
Qed.
  
Lemma ELim_seq_INR :
  ELim_seq INR = p_infty.
Proof.
  rewrite Elim_seq_fin.
  apply Lim_seq.Lim_seq_INR.
Qed.

Lemma is_Elim_seq_const (a : Rbar) :
  is_Elim_seq (fun n => a) a.
Proof.
  red.
  split.
  - apply is_ELimInf_seq_const.
  - apply is_ELimSup_seq_const.
Qed.
  
Lemma ex_Elim_seq_const (a : Rbar) :
  ex_Elim_seq (fun n => a).
Proof.
  eapply is_Elim_seq_ex_Elim_seq.
  apply is_Elim_seq_const.
Qed.
  
Lemma ELim_seq_const (a : Rbar) :
  ELim_seq (fun n => a) = a.
Proof.
  apply is_Elim_seq_unique.
  apply is_Elim_seq_const.
Qed.

Lemma is_Elim_seq_subseq (u : nat -> Rbar) (l : Rbar) (phi : nat -> nat) :
  filterlim phi eventually eventually ->
  is_Elim_seq u l ->
  is_Elim_seq (fun n => u (phi n)) l.
Proof.
  intros.
  destruct H0.
  split.
  {
    destruct l.
    - intros eps.
      specialize (H0 eps).
      specialize (H1 eps).
      destruct H0 as [H11 H12].
      destruct H1 as [H21 H22].
      split; intros.
      + destruct (H (fun n => Rbar_lt (u n) (r + eps))).
        {
          eapply filter_imp; try eapply H22; intros.
          simpl in H0.
          destruct eps; simpl in *.
          destruct (u x); simpl in *; rbar_prover.
        } 
        * exists (max N x); intros.
          split; try lia.
          specialize (H0 (max N x)).
          cut_to H0; try lia.
          destruct eps; simpl in *.
          destruct (u (phi (Init.Nat.max N x))); simpl in *; rbar_prover.
      + destruct (H (fun n => Rbar_lt (r - eps) (u n))).
        { 
          eapply filter_imp; try eapply H12; auto.
        }
        eauto.
    - intros M.
      specialize (H0 M).
      destruct H0 as [??].
      destruct (H (fun n => Rbar_lt M (u n))).
      {
        exists x; apply H0.
      }
      eauto.
    - intros M N.
      specialize (H1 M).
      destruct H1 as [??].
      repeat red in H.
      destruct (H (fun n => Rbar_lt (u n) M)).
      {
        exists x; intros.
        now apply H1.
      }
      exists (max N x0).
      split; try lia.
      apply H2; lia.
  } 

  {
    destruct l.
    - intros eps.
      specialize (H0 eps).
      specialize (H1 eps).
      destruct H0 as [H11 H12].
      destruct H1 as [H21 H22].
      split; intros.
      + destruct (H (fun n => Rbar_lt (r - eps) (u n))).
        {
          eapply filter_imp; try eapply H12; intros.
          simpl in H0.
          destruct eps; simpl in *.
          destruct (u x); simpl in *; rbar_prover.
        } 
        * exists (max N x); intros.
          split; try lia.
          specialize (H0 (max N x)).
          cut_to H0; try lia.
          destruct eps; simpl in *.
          destruct (u (phi (Init.Nat.max N x))); simpl in *; rbar_prover.
      + destruct (H (fun n => Rbar_lt (u n) (r + eps))).
        { 
          eapply filter_imp; try eapply H22; auto.
        }
        eauto.
    - intros M N.
      specialize (H0 M).
      destruct H0 as [??].
      repeat red in H.
      destruct (H (fun n => Rbar_lt M (u n))).
      {
        exists x; intros.
        now apply H0.
      }
      exists (max N x0).
      split; try lia.
      apply H2; lia.
    - intros M.
      specialize (H1 M).
      destruct H1 as [??].
      destruct (H (fun n => Rbar_lt (u n) M)).
      {
        exists x; apply H1.
      }
      eauto.
  } 
Qed.
  
Lemma ex_Elim_seq_subseq (u : nat -> Rbar) (phi : nat -> nat) :
  filterlim phi eventually eventually ->
  ex_Elim_seq u ->
  ex_Elim_seq (fun n => u (phi n)).
Proof.
  intros.
  apply ex_Elim_seq_is_Elim_seq_sup in H0.
  eapply is_Elim_seq_ex_Elim_seq.
  eapply is_Elim_seq_subseq; eauto.
Qed.
  
Lemma ELim_seq_subseq (u : nat -> Rbar) (phi : nat -> nat) :
  filterlim phi eventually eventually ->
  ex_Elim_seq u ->
  ELim_seq (fun n => u (phi n)) = ELim_seq u.
Proof.
  intros.
  apply is_Elim_seq_unique.
  apply is_Elim_seq_subseq; trivial.
  now apply ELim_seq_correct.
Qed.

Lemma is_Elim_seq_incr_1 (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l <-> is_Elim_seq (fun n => u (S n)) l.
Proof.
  unfold is_Elim_seq; split
  ; intros [??]
  ; split.
  - now apply -> is_ELimInf_seq_ind_1.
  - now apply -> is_ELimSup_seq_ind_1.
  - now apply <- is_ELimInf_seq_ind_1.
  - now apply <- is_ELimSup_seq_ind_1.
Qed.
  
Lemma ex_Elim_seq_incr_1 (u : nat -> Rbar) :
  ex_Elim_seq u <-> ex_Elim_seq (fun n => u (S n)).
Proof.
  unfold ex_Elim_seq.
  now rewrite ELimSup_seq_ind_1 ELimInf_seq_ind_1.
Qed.

Lemma ELim_seq_incr_1 (u : nat -> Rbar) :
  ELim_seq (fun n => u (S n)) = ELim_seq u.
Proof.
  unfold ELim_seq.
  now rewrite ELimSup_seq_ind_1 ELimInf_seq_ind_1.
Qed.

Lemma is_Elim_seq_incr_n (u : nat -> Rbar) (N : nat) (l : Rbar) :
  is_Elim_seq u l <-> is_Elim_seq (fun n => u (n + N)%nat) l.
Proof.
  intros.
  induction N; simpl.
  - apply is_Elim_seq_proper; trivial.
    intros ?; f_equal; lia.
  - rewrite IHN.
    rewrite is_Elim_seq_incr_1.
    apply is_Elim_seq_proper; trivial.
    intros ?; f_equal; lia.
Qed.
  
Lemma ex_Elim_seq_incr_n (u : nat -> Rbar) (N : nat) :
  ex_Elim_seq u <-> ex_Elim_seq (fun n => u (n + N)%nat).
Proof.
  unfold ex_Elim_seq.
  now rewrite ELimSup_seq_ind_k ELimInf_seq_ind_k.
Qed.
  
Lemma ELim_seq_incr_n (u : nat -> Rbar) (N : nat) :
  ELim_seq (fun n => u (n + N)%nat) = ELim_seq u.
Proof.
  unfold ELim_seq.
  now rewrite ELimSup_seq_ind_k ELimInf_seq_ind_k.
Qed.

Lemma ELim_seq_le_loc (u v : nat -> Rbar) :
  eventually (fun n => Rbar_le (u n) (v n)) ->
  Rbar_le (ELim_seq u) (ELim_seq v).
Proof.
  intros.
  unfold ELim_seq.
  apply Rbar_div_pos_le.
  apply Rbar_plus_le_compat.
  - now apply ELimSup_le.
  - now apply ELimInf_le.
Qed.

Lemma ELim_seq_le (u v : nat -> Rbar) :
  (forall n, Rbar_le (u n) (v n)) ->
  Rbar_le (ELim_seq u) (ELim_seq v).
Proof.
  intros.
  apply ELim_seq_le_loc.
  now apply filter_forall.
Qed.

Global Instance ELim_le_proper :
  Proper (pointwise_relation _ Rbar_le ==> Rbar_le) ELim_seq.
Proof.
  intros ???.
  now apply ELim_seq_le.
Qed.

Lemma is_Elim_seq_le_loc (u v : nat -> Rbar) (l1 l2 : Rbar) :
  eventually (fun n => Rbar_le (u n) (v n)) ->
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  Rbar_le l1 l2.
Proof.
  intros.
  apply is_Elim_seq_unique in H0.
  apply is_Elim_seq_unique in H1.
  subst.
  now apply ELim_seq_le_loc.
Qed.  

Lemma is_Elim_seq_le (u v : nat -> Rbar) (l1 l2 : Rbar) :
  (forall n, Rbar_le (u n) (v n)) ->
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  Rbar_le l1 l2.
Proof.
  intros.
  eapply is_Elim_seq_le_loc; eauto.
  now apply filter_forall.
Qed.  

Lemma is_ELimSup_seq_le_le_loc (u v w : nat -> Rbar) (l : Rbar) :
  eventually (fun n => Rbar_le (u n) (v n) /\ Rbar_le (v n) (w n)) ->
  is_ELimSup_seq u l -> is_ELimSup_seq w l -> is_ELimSup_seq v l.
Proof.
  intros.
  apply is_ELimSup_seq_unique in H0.
  apply is_ELimSup_seq_unique in H1.
  assert (le1:Rbar_le (ELimSup_seq u) (ELimSup_seq v)).
  {
    apply ELimSup_le.
    revert H.
    eapply filter_imp; tauto.
  } 
  assert (le2:Rbar_le (ELimSup_seq v) (ELimSup_seq w)).
  {
    apply ELimSup_le.
    revert H.
    eapply filter_imp; tauto.
  } 
  rewrite H0 in le1.
  rewrite H1 in le2.
  assert (eqq:l = (ELimSup_seq v)).
  {
    apply Rbar_le_antisym; trivial.
  }
  rewrite eqq.
  apply is_ELimSup_seq_correct.
Qed.

Lemma is_ELimInf_seq_le_le_loc (u v w : nat -> Rbar) (l : Rbar) :
  eventually (fun n => Rbar_le (u n) (v n) /\ Rbar_le (v n) (w n)) ->
  is_ELimInf_seq u l -> is_ELimInf_seq w l -> is_ELimInf_seq v l.
Proof.
  intros.
  apply is_ELimInf_seq_unique in H0.
  apply is_ELimInf_seq_unique in H1.
  assert (le1:Rbar_le (ELimInf_seq u) (ELimInf_seq v)).
  {
    apply ELimInf_le.
    revert H.
    eapply filter_imp; tauto.
  } 
  assert (le2:Rbar_le (ELimInf_seq v) (ELimInf_seq w)).
  {
    apply ELimInf_le.
    revert H.
    eapply filter_imp; tauto.
  } 
  rewrite H0 in le1.
  rewrite H1 in le2.
  assert (eqq:l = (ELimInf_seq v)).
  {
    apply Rbar_le_antisym; trivial.
  }
  rewrite eqq.
  apply is_ELimInf_seq_correct.
Qed.

Lemma is_Elim_seq_le_le_loc (u v w : nat -> Rbar) (l : Rbar) :
  eventually (fun n => Rbar_le (u n) (v n) /\ Rbar_le (v n) (w n)) ->
  is_Elim_seq u l -> is_Elim_seq w l -> is_Elim_seq v l.
Proof.
  intros ? [??] [??].
  split.
  - eapply is_ELimInf_seq_le_le_loc; eauto.
  - eapply is_ELimSup_seq_le_le_loc; eauto.
Qed.

Lemma is_Elim_seq_le_le (u v w : nat -> Rbar) (l : Rbar) :
  (forall n, Rbar_le (u n) (v n) /\ Rbar_le (v n) (w n)) ->
  is_Elim_seq u l -> is_Elim_seq w l -> is_Elim_seq v l.
Proof.
  intros H.
  apply is_Elim_seq_le_le_loc.
  now apply filter_forall.
Qed.
  
Lemma is_Elim_seq_le_p_loc (u v : nat -> Rbar) :
  eventually (fun n => Rbar_le (u n) (v n)) ->
  is_Elim_seq u p_infty ->
  is_Elim_seq v p_infty.
Proof.
  intros.
  apply (is_Elim_seq_le_le_loc u _ (fun _ => p_infty)); trivial.
  - revert H.
    apply filter_imp; intros.
    split; trivial.
    unfold Rbar_le; match_destr.
  - apply is_Elim_seq_const.
Qed.

Lemma is_Elim_seq_le_m_loc (u v : nat -> Rbar) :
  eventually (fun n => Rbar_le (v n) (u n)) ->
  is_Elim_seq u m_infty ->
  is_Elim_seq v m_infty.
Proof.
  intros.
  apply (is_Elim_seq_le_le_loc (fun _ => m_infty) _ u ); trivial.
  - revert H.
    apply filter_imp; intros.
    split; simpl; trivial.
  - apply is_Elim_seq_const.
Qed.

Lemma preorder_S_le_incr {A} (RR:A->A->Prop) {RR_pre:PreOrder RR} (f:nat->A) :
  (forall n, RR (f n) (f (S n))) ->
  forall n m, (n <= m)%nat -> RR (f n) (f m).
Proof.
  intros.
  induction H0.
  - reflexivity.
  - etransitivity; eauto.
Qed.

Lemma preorder_S_le_decr {A} (RR:A->A->Prop) {RR_pre:PreOrder RR} (f:nat->A) :
  (forall n, RR (f (S n)) (f n)) ->
  forall n m, (n <= m)%nat -> RR (f m) (f n).
Proof.
  intros.
  induction H0.
  - reflexivity.
  - etransitivity; eauto.
Qed.
                           
Lemma is_Elim_seq_decr_compare (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l
  -> (forall n, Rbar_le (u (S n)) (u n))
  -> forall n, Rbar_le l (u n).
Proof.
  intros.
  apply (is_Elim_seq_le_loc u (fun _ => u n)); trivial.
  - exists n; intros.
    apply preorder_S_le_decr; trivial.
    apply Rbar_le_pre.
  - apply is_Elim_seq_const.
Qed.

Lemma is_Elim_seq_incr_compare (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l
  -> (forall n, Rbar_le (u n) (u (S n)))
  -> forall n, Rbar_le (u n) l.
Proof.
  intros.
  apply (is_Elim_seq_le_loc (fun _ => u n) u); trivial.
  - exists n; intros.
    apply preorder_S_le_incr; trivial.
    apply Rbar_le_pre.
  - apply is_Elim_seq_const.
Qed.

Lemma ex_Elim_seq_decr (u : nat -> Rbar) :
  (forall n, (Rbar_le (u (S n)) (u n)))
  -> ex_Elim_seq u.
Proof.
  intros.
  apply (is_Elim_seq_ex_Elim_seq _ (ELimInf_seq u)).
  split; [apply is_ELimInf_seq_correct |].
  unfold ELimInf_seq, proj1_sig.
  match_destr.
  destruct x.
  - intros eps.
    specialize (i eps).
    split.
    + intros.
      destruct i as [_ [??]].
      exists (max N x).
      split; try lia.
      apply H0.
      lia.
    + destruct i as [??].
      destruct (H0 0%nat) as [?[??]].
      exists x; intros.
      eapply Rbar_le_lt_trans; try eapply H3.
      apply preorder_S_le_decr; trivial.
      apply Rbar_le_pre.
  - intros M N.
    specialize (i M).
    destruct i as [??].
    exists (max N x).
    split; try lia.
    apply H0.
    lia.
  - intros M.
    specialize (i M 0%nat) as [? [??]].
    exists x; intros.
      eapply Rbar_le_lt_trans; try eapply H1.
      apply preorder_S_le_decr; trivial.
      apply Rbar_le_pre.
Qed.
  
Lemma ex_Elim_seq_incr (u : nat -> Rbar) :
  (forall n, Rbar_le (u n) (u (S n)))
  -> ex_Elim_seq u.
Proof.
  intros.
  apply (is_Elim_seq_ex_Elim_seq _ (ELimSup_seq u)).
  split; [| apply is_ELimSup_seq_correct].
  unfold ELimSup_seq, proj1_sig.
  match_destr.
  destruct x.
  - intros eps.
    specialize (i eps).
    split.
    + intros.
      destruct i as [_ [??]].
      exists (max N x).
      split; try lia.
      apply H0.
      lia.
    + destruct i as [??].
      destruct (H0 0%nat) as [?[??]].
      exists x; intros.
      eapply Rbar_lt_le_trans; try eapply H3.
      apply preorder_S_le_incr; trivial.
      apply Rbar_le_pre.
  - intros M.
    specialize (i M 0%nat) as [? [??]].
    exists x; intros.
      eapply Rbar_lt_le_trans; try eapply H1.
      apply preorder_S_le_incr; trivial.
      apply Rbar_le_pre.
  - intros M N.
    specialize (i M).
    destruct i as [??].
    exists (max N x).
    split; try lia.
    apply H0.
    lia.
Qed.

Lemma ex_finite_Elim_seq_decr (u : nat -> Rbar) (M : R) (m:nat):
  (forall n, Rbar_le (u (S n)) (u n)) -> (forall n, Rbar_le M (u n)) ->
  (u m <> p_infty) ->
  ex_finite_Elim_seq u.
Proof.
  intros.
  split.
  - now apply ex_Elim_seq_decr.
  - generalize (ELim_seq_correct u)
    ; intros HH.
    cut_to HH; try now apply ex_Elim_seq_decr.
    generalize (is_Elim_seq_decr_compare u _ HH H m)
    ; intros HH2.
    generalize (is_Elim_seq_const M)
    ; intros HH3.
    generalize (is_Elim_seq_le (fun _ : nat => M)  u _ _ H0 HH3 HH)
    ; intros HH4.
    destruct (ELim_seq u); destruct (u m);
      simpl in *; rbar_prover
      ; try congruence
      ; try reflexivity.
Qed.
  
Lemma ex_finite_Elim_seq_incr (u : nat -> Rbar) (M : R) (m:nat):
  (forall n, Rbar_le (u n) (u (S n))) -> (forall n, Rbar_le (u n) M) ->
  (u m <> m_infty) ->
  ex_finite_Elim_seq u.
Proof.
  intros.
  split.
  - now apply ex_Elim_seq_incr.
  - generalize (ELim_seq_correct u)
    ; intros HH.
    cut_to HH; try now apply ex_Elim_seq_incr.
    generalize (is_Elim_seq_incr_compare u _ HH H m)
    ; intros HH2.
    generalize (is_Elim_seq_const M)
    ; intros HH3.
    generalize (is_Elim_seq_le u  (fun _ : nat => M) _ _ H0 HH HH3)
    ; intros HH4.
    destruct (ELim_seq u); destruct (u m);  simpl in *;
      rbar_prover
      ; try congruence
      ; try reflexivity.
Qed.

Lemma is_Elim_seq_opp (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l <-> is_Elim_seq (fun n => Rbar_opp (u n)) (Rbar_opp l).
Proof.
  split; intros [??]; split.
  - now apply is_ELimInf_opp_ELimSup_seq.
  - now apply is_ELimSup_opp_ELimInf_seq.
  - now apply is_ELimSup_opp_ELimInf_seq.
  - now apply is_ELimInf_opp_ELimSup_seq.
Qed.

Lemma ex_Elim_seq_opp (u : nat -> Rbar) :
  ex_Elim_seq u <-> ex_Elim_seq (fun n => Rbar_opp (u n)).
Proof.
  intros.
  split; intros HH.
  - apply ELim_seq_correct in HH.
    apply is_Elim_seq_opp in HH.
    eapply is_Elim_seq_ex_Elim_seq; eauto.
  - apply ELim_seq_correct in HH.
    apply is_Elim_seq_opp in HH.
    eapply is_Elim_seq_ex_Elim_seq in HH.
    revert HH.
    apply ex_Elim_seq_proper.
    intros ?.
    now rewrite Rbar_opp_involutive.
Qed.

Lemma ELim_seq_opp (u : nat -> Rbar) :
  ELim_seq (fun n => Rbar_opp (u n)) = Rbar_opp (ELim_seq u).
Proof.
  unfold ELim_seq.
  rewrite ELimSup_seq_opp ELimInf_seq_opp.
  rewrite Rbar_plus_comm.
  destruct (ELimSup_seq u); destruct (ELimInf_seq u); simpl; rbar_prover.
Qed.

Lemma is_Elim_seq_plus_aux (u v : nat -> Rbar) (l1 l2 l : Rbar) :
  Rbar_le 0 l ->
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  is_Rbar_plus l1 l2 l ->
  is_Elim_seq (fun n => Rbar_plus (u n) (v n)) l.
Proof.
  intros zpos limu limv isp.

  apply is_Elim_seq_spec in limu.
  apply is_Elim_seq_spec in limv.
  apply is_Elim_seq_spec.
  unfold is_Elim_seq', is_Rbar_plus in *.
  destruct l.
  - intros eps.
    destruct l1; destruct l2; simpl in isp; invcs isp.
    eapply filter_imp; [| eapply filter_and; [apply (limu (pos_div_2 eps)) | apply (limv (pos_div_2 eps))]]
    ; simpl; intros ? [??].
    
    generalize (Rbar_plus_lt_compat _ _ _ _ H H0)
    ; intros.
    destruct (u x); destruct (v x); simpl in *; rbar_prover.
    rewrite <- double_var in H1.
    eapply Rle_lt_trans; try eapply H1.
    eapply Rle_trans; [| eapply Rabs_triang].
    apply BasicUtils.refl_refl.
    f_equal; lra.
  - intros M.
    destruct l1; destruct l2; invcs isp.
    + specialize (limu posreal1).
      specialize (limv (M - r + 1)).
      eapply filter_imp; [| eapply filter_and; [apply limu | apply limv]]
      ; simpl; intros ? [??].
      destruct (u x); destruct (v x); simpl in *; rbar_prover.
      assert (M < r + r1 - 1) by lra.
      eapply Rlt_le_trans; try eapply H1.
      cut (r - 1 <= r0); [lra | ].
      cut ((r - r0) <= 1); [lra | ].
      unfold Rabs in *.
      match_destr_in H; lra.
    + specialize (limu (M - r + 1)).
      specialize (limv posreal1).
      eapply filter_imp; [| eapply filter_and; [apply limu | apply limv]]
      ; simpl; intros ? [??].
      destruct (u x); destruct (v x); simpl in *; rbar_prover.
      assert (M < r + r0 - 1) by lra.
      eapply Rlt_le_trans; try eapply H1.
      cut (r - 1 <= r1); [lra | ].
      cut ((r - r1) <= 1); [lra | ].
      unfold Rabs in *.
      match_destr_in H0; lra.
    + specialize (limu (M / 2)).
      specialize (limv (M / 2)).
      eapply filter_imp; [| eapply filter_and; [apply limu | apply limv]]
      ; simpl; intros ? [??].
      destruct (u x); destruct (v x); simpl in *; rbar_prover.
  - simpl in zpos; tauto.
Qed.    

Lemma is_Elim_seq_plus (u v : nat -> Rbar) (l1 l2 l : Rbar) :
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  is_Rbar_plus l1 l2 l ->
  is_Elim_seq (fun n => Rbar_plus (u n) (v n)) l.
Proof.
  intros.
  destruct (Rbar_le_dec 0 l).
  - eapply is_Elim_seq_plus_aux; eauto.
  - assert (Rbar_le 0 (Rbar_opp l)).
    {
      destruct l; simpl in *; rbar_prover.
    }
    apply is_Elim_seq_opp.
    apply (is_Elim_seq_proper _ _ (fun n => Rbar_plus_opp (u n) (v n))  _ _ (reflexivity _)).
    apply is_Elim_seq_opp in H.
    apply is_Elim_seq_opp in H0.
    apply (is_Elim_seq_plus_aux (fun n => (Rbar_opp (u n))) (fun n => (Rbar_opp (v n))) _ _ _ H2 H H0).
    unfold is_Rbar_plus in *.
    destruct l1; destruct l2; destruct l; simpl in *; try invcs H1; rbar_prover.
Qed.

Lemma is_Elim_seq_plus' (u v : nat -> Rbar) (l1 l2 : R) :
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  is_Elim_seq (fun n => (Rbar_plus (u n) (v n))) (l1 + l2).
Proof.
  intros.
  replace (Finite (l1 + l2)) with (Rbar_plus l1 l2) by reflexivity.
  eapply is_Elim_seq_plus; eauto.
  reflexivity.
Qed.

Lemma ex_Elim_seq_plus (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v ->
  ex_Rbar_plus (ELim_seq u) (ELim_seq v) ->
  ex_Elim_seq (fun n => Rbar_plus (u n) (v n)).
Proof.
  intros.
  apply ELim_seq_correct in H.
  apply ELim_seq_correct in H0.
  apply Rbar_plus_correct in H1.
  eapply is_Elim_seq_ex_Elim_seq.
  eapply is_Elim_seq_plus; eauto.
Qed.

Lemma ELim_seq_plus (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v ->
  ex_Rbar_plus (ELim_seq u) (ELim_seq v) ->
  ELim_seq (fun n => Rbar_plus (u n) (v n)) = Rbar_plus (ELim_seq u) (ELim_seq v).
Proof.
  intros.
  apply ELim_seq_correct in H.
  apply ELim_seq_correct in H0.
  apply Rbar_plus_correct in H1.

  eapply is_Elim_seq_unique.
  eapply is_Elim_seq_plus; eauto.
Qed.

Lemma is_Elim_seq_minus (u v : nat -> Rbar) (l1 l2 l : Rbar) :
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  is_Rbar_minus l1 l2 l ->
  is_Elim_seq (fun n => Rbar_minus (u n) (v n)) l.
Proof.
  intros.
  unfold Rbar_minus.
  eapply is_Elim_seq_plus; try eapply H1; trivial.
  now apply -> is_Elim_seq_opp.
Qed.

Lemma is_Elim_seq_minus' (u v : nat -> Rbar) (l1 l2 : R) :
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  is_Elim_seq (fun n => Rbar_minus (u n) (v n)) (l1 - l2).
Proof.
  intros.
  unfold Rbar_minus.
  eapply is_Elim_seq_plus'; try eapply H1; trivial.
  now apply is_Elim_seq_opp in H0.
Qed.

Lemma ex_Elim_seq_minus (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v ->
  ex_Rbar_minus (ELim_seq u) (ELim_seq v) ->
  ex_Elim_seq (fun n => Rbar_minus (u n) (v n)).
Proof.
  intros.
  unfold Rbar_minus.
  apply ex_Elim_seq_plus; trivial.
  - now apply ex_Elim_seq_opp in H0.
  - rewrite ELim_seq_opp.
    apply H1.
Qed.

Lemma ELim_seq_minus (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v ->
  ex_Rbar_minus (ELim_seq u) (ELim_seq v) ->
  ELim_seq (fun n => Rbar_minus (u n) (v n)) = Rbar_minus (ELim_seq u) (ELim_seq v).
Proof.
  intros.
  unfold Rbar_minus.
  rewrite ELim_seq_plus; trivial.
  - now rewrite ELim_seq_opp.
  - now apply ex_Elim_seq_opp in H0.
  - now rewrite ELim_seq_opp.
Qed.

Lemma is_Elim_seq_inv_pos (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l ->
  Rbar_lt 0 l ->
  is_Elim_seq (fun n => Rbar_inv (u n)) (Rbar_inv l).
Proof.
  intros limu lpos.
  apply is_Elim_seq_spec in limu.
  apply is_Elim_seq_spec.

  destruct l; try tauto.
  - simpl in lpos.
    intros eps.
    red in limu; simpl.

    assert (pos:0 < Rmin (eps * ((r / 2) * r)) (r / 2)).
    { destruct eps; simpl.
      apply Rmin_pos; try lra.
      repeat (apply Rmult_lt_0_compat; try lra).
    }
    specialize (limu (mkposreal _ pos)).
    revert limu; apply filter_imp; simpl; intros.
    destruct (u x); simpl in *; rbar_prover; clear x.
    assert (r / 2 < r0).
    {
      apply Rle_lt_trans with (r - r / 2).
      apply Req_le ; field.
      apply Rabs_lt_between'.
      apply Rlt_le_trans with (1 := H).
      apply Rmin_r.
    }
    assert (H3: 0 < r0) by lra.
    assert (eqq1:/ r0 + - / r = ((r - r0) / r / r0)).
    {
      unfold Rdiv.
      rewrite Rmult_plus_distr_r.
      rewrite Rinv_r; try lra.
      rewrite Rmult_plus_distr_r.
      repeat rewrite <- Ropp_mult_distr_l.
      rewrite -> Rinv_r_simpl_m; try lra.
    }
    rewrite eqq1.
    repeat rewrite Rabs_div; try lra.
    rewrite (Rabs_right r); try lra.
    rewrite (Rabs_right r0); try lra.
    rewrite Rabs_minus_sym.
    eapply Rlt_le_trans.
    {
      eapply Rmult_lt_compat_r.
      - now apply Rinv_pos.
      - eapply Rmult_lt_compat_r.
        + now apply Rinv_pos.
        + apply H.
    }
    etransitivity.
    {
      eapply Rmult_le_compat_r.
      - left; now apply Rinv_pos.
      - eapply Rmult_le_compat_r.
        + left; now apply Rinv_pos.
        + apply Rmin_l.
    }

    cut (eps * (r / 2 * (r * / r) * / r0) <= eps); try lra.
    rewrite Rinv_r; try lra.
    rewrite Rmult_1_r.
    etransitivity.
    {
      apply Rmult_le_compat_l.
      - destruct eps; simpl; lra.
      - apply Rmult_le_compat_r.
        + left; now apply Rinv_pos.
        + left. apply H0.
    }
    rewrite Rinv_r; try lra.
  - intros eps.
    specialize (limu (/ eps)).
    revert limu.
    apply filter_imp; intros.
    unfold Rbar_minus.
    simpl.
    rewrite Ropp_0 Rbar_plus_0_r.
    destruct (u x); simpl in *; rbar_prover.
    + apply (Rmult_lt_compat_r eps _ _ (cond_pos eps)) in H.
      rewrite Rinv_l in H; [| destruct eps; simpl; lra].
      assert (r <> 0).
      {
        intros ?; subst.
        rewrite Rmult_0_l in H.
        lra.
      } 
      apply (Rmult_lt_compat_l (Rabs (/ r)) _ _) in H.
      * rewrite Rmult_1_r in H.
        eapply Rlt_le_trans; try eapply H.
        unfold Rabs.
        match_destr.
        -- repeat rewrite <- Ropp_mult_distr_l.
           rewrite <- Rmult_assoc.
           rewrite Rinv_l; trivial.
           rewrite Rmult_1_l.
           destruct eps; simpl; lra.
        -- rewrite <- Rmult_assoc.
           rewrite Rinv_l; trivial.
           rewrite Rmult_1_l.
           lra.
      * apply Rabs_pos_lt.
        apply Rinv_neq_0_compat.
        intros ?; subst.
        lra.
    + rewrite Rabs_R0.
      now destruct eps.
Qed.    

Lemma is_Elim_seq_inv_neg (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l ->
  Rbar_lt 0 (Rbar_opp l) ->
  is_Elim_seq (fun n => Rbar_inv (u n)) (Rbar_inv l).
Proof.
  intros limu lpos.
  apply is_Elim_seq_spec in limu.
  apply is_Elim_seq_spec.

  destruct l; try tauto.
  - simpl in lpos.
    intros eps.
    red in limu; simpl.

    assert (pos:0 < Rmin (eps * ((r / 2) * r)) (- r / 2)).
    { destruct eps; simpl.
      apply Rmin_pos; try lra.
      apply Rmult_lt_0_compat; try lra.
      unfold Rdiv.
      rewrite Rmult_comm.
      rewrite <- Rmult_assoc.
      apply Rmult_lt_0_compat; try lra.
      rewrite <- Rmult_opp_opp.
      apply Rmult_lt_0_compat; try lra.
    }
    specialize (limu (mkposreal _ pos)).
    revert limu; apply filter_imp; simpl; intros.
    destruct (u x); simpl in *; rbar_prover; clear x.
    assert (- r / 2 < - r0).
    {
      apply Rle_lt_trans with (- r - - r / 2).
      apply Req_le ; field.
      apply Rabs_lt_between'.
      unfold Rminus.
      rewrite <- Ropp_plus_distr.
      rewrite Rabs_Ropp.
      apply Rlt_le_trans with (1 := H).
      apply Rmin_r.
    }
    assert (H3: 0 < - r0) by lra.
    assert (eqq1:/ (- r0) + - / (- r) = (((- r) - (- r0)) / (- r) / (- r0))).
    {
      unfold Rdiv.
      rewrite Rmult_plus_distr_r.
      rewrite Rinv_r; try lra.
      rewrite Rmult_plus_distr_r.
      repeat rewrite <- Ropp_mult_distr_l.
      rewrite Rmult_1_l.
      f_equal.
      repeat rewrite <- Ropp_inv_permute; try lra.
      rewrite <- Ropp_mult_distr_r.
      rewrite -> Rinv_r_simpl_m; try lra.
    }
    rewrite Rabs_minus_sym.
    
    assert (eqq1': / r - / r0 = / - r0 + - / - r).
    {
      repeat rewrite <- Ropp_inv_permute; try lra.
    } 
    rewrite eqq1'.
    rewrite eqq1.
    repeat rewrite Rabs_div; try lra.
    rewrite (Rabs_right (- r)); try lra.
    rewrite (Rabs_right (- r0)); try lra.
    rewrite Rabs_minus_sym.
    rewrite <- Rabs_Ropp.
    rewrite Ropp_plus_distr.
    repeat rewrite Ropp_involutive.
    eapply Rlt_le_trans.
    {
      eapply Rmult_lt_compat_r.
      - now apply Rinv_pos.
      - eapply Rmult_lt_compat_r.
        + now apply Rinv_pos.
        + apply H.
    }
    etransitivity.
    {
      eapply Rmult_le_compat_r.
      - left; now apply Rinv_pos.
      - eapply Rmult_le_compat_r.
        + left; now apply Rinv_pos.
        + apply Rmin_l.
    }

    cut (eps * (r / 2 * (r * / - r) * / - r0) <= eps); try lra.
    repeat rewrite <- Ropp_inv_permute; try lra.
    repeat rewrite <- Ropp_mult_distr_r.
    rewrite Rinv_r; try lra.
    rewrite Rmult_1_r.
    repeat rewrite Ropp_mult_distr_r.
    etransitivity.
    {
      apply Rmult_le_compat_l.
      - destruct eps; simpl; lra.
      - apply Rmult_le_compat_r.
        + left.
          rewrite Ropp_inv_permute; try lra.
          apply Rinv_pos; lra.
        + left.
          rewrite <- Ropp_mult_distr_r.
          rewrite Ropp_mult_distr_l.
          apply H0.
    }
    rewrite Rmult_opp_opp.
    rewrite Rinv_r; try lra.
  - red.
    intros eps.
    specialize (limu (- / eps)).
    revert limu.
    apply filter_imp; intros.
    unfold Rbar_minus.
    simpl.
    rewrite Ropp_0 Rbar_plus_0_r.
    destruct (u x); simpl in *; rbar_prover.
    + apply (Rmult_lt_compat_r eps _ _ (cond_pos eps)) in H.
      rewrite <- Ropp_mult_distr_l in H.
      rewrite Rinv_l in H; [| destruct eps; simpl; lra].
      assert (r <> 0).
      {
        intros ?; subst.
        rewrite Rmult_0_l in H.
        lra.
      } 
      apply (Rmult_lt_compat_l (Rabs (/ r)) _ _) in H.
      * rewrite <- Ropp_mult_distr_r in H.
        rewrite Rmult_1_r in H.
        apply Ropp_lt_cancel.
        eapply Rle_lt_trans; try eapply H.
        unfold Rabs.
        match_destr.
        -- repeat rewrite <- Ropp_mult_distr_l.
           rewrite <- Rmult_assoc.
           rewrite Rinv_l; trivial.
           rewrite Rmult_1_l.
           destruct eps; simpl; lra.
        -- rewrite <- Rmult_assoc.
           rewrite Rinv_l; trivial.
           rewrite Rmult_1_l.
           destruct eps; simpl.
           lra.
      * apply Rabs_pos_lt.
        apply Rinv_neq_0_compat.
        intros ?; subst.
        lra.
    + rewrite Rabs_R0.
      now destruct eps.
Qed.    

Lemma is_Elim_seq_inv (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l ->
  l <> 0 ->
  is_Elim_seq (fun n => Rbar_inv (u n)) (Rbar_inv l).
Proof.
  intros.
  destruct (Rbar_total_order 0 l) as [[?|?]|?].
  - eapply is_Elim_seq_inv_pos; eauto.
  - congruence.
  - eapply is_Elim_seq_inv_neg; eauto.
    apply Rbar_opp_lt.
    rewrite Rbar_opp_involutive; simpl.
    now rewrite Ropp_0.
Qed.    

Lemma ex_Elim_seq_inv (u : nat -> Rbar) :
  ex_Elim_seq u
  -> ELim_seq u <> 0
  -> ex_Elim_seq (fun n => Rbar_inv (u n)).
Proof.
  intros.
  apply ELim_seq_correct in H.
  eapply is_Elim_seq_ex_Elim_seq.
  eapply is_Elim_seq_inv; eauto.
Qed.

Lemma ELim_seq_inv (u : nat -> Rbar) :
  ex_Elim_seq u -> (ELim_seq u <> 0)
  -> ELim_seq (fun n => Rbar_inv (u n)) = Rbar_inv (ELim_seq u).
Proof.
  intros.
  apply ELim_seq_correct in H.
  eapply is_Elim_seq_unique.
  eapply is_Elim_seq_inv; eauto.
Qed.

Lemma is_Elim_seq_mult_aux_pos123 (u v : nat -> Rbar) (l1 l2 l : Rbar) :
  Rbar_le 0 l1 ->
  Rbar_le 0 l2 ->
  Rbar_le l1 l2 ->
  is_Elim_seq u l1 ->
  is_Elim_seq v l2 ->
  is_Rbar_mult l1 l2 l ->
  (eventually (fun n => ex_Rbar_mult (u n) ( v n))) ->
  is_Elim_seq (fun n => Rbar_mult (u n) (v n)) l.
Proof.
  intros l1_nneg l2_nneg l1_le_l2 limu limv is_valid is_valid_n.
  apply is_Elim_seq_spec in limu.
  apply is_Elim_seq_spec in limv.
  apply is_Elim_seq_spec.
  unfold is_Rbar_mult in is_valid.
  destruct l1 as [l1 | | ]; destruct l2 as [l2 | | ]; invcs is_valid; try tauto.
  - simpl in *.
    intros eps.
    destruct eps as [eps eps_pos].
    assert (pos: 0 < Rmin (eps / (l1 + l2 + 1)) 1).
    {
      apply Rmin_pos.
      - apply Rmult_lt_0_compat; try lra.
        apply Rinv_pos; lra.
      - lra.
    }
    specialize (limu (mkposreal _ pos)).
    specialize (limv (mkposreal _ pos)).
    eapply filter_imp; [| eapply filter_and; [apply limu | eapply filter_and; [apply limv | apply is_valid_n]]]
    ; simpl; intros ? [?[? is_valid_n']].
    red in is_valid_n'.
    unfold Rbar_minus, Rbar_plus, Rbar_mult.
    destruct (u x) as [ux | |]; destruct (v x) as [vx | |]; simpl in *; rbar_prover; simpl; rbar_prover; try lra.
    assert (eqq1:
              (ux * vx + - (l1 * l2)) =
              (l1 * (vx - l2) + l2 * (ux - l1) + (ux - l1) * (vx - l2))) by lra.
    rewrite eqq1.

    eapply Rle_lt_trans; try eapply Rabs_triang.
    assert (eqq2: eps = (l1 * (eps / (l1 + l2 + 1)) + l2 * (eps / (l1 + l2 + 1)) + 1 * (eps / (l1 + l2 + 1)))).
    {
      field; lra.
    } 
    rewrite eqq2.
    
    apply Rplus_le_lt_compat.
    + apply Rle_trans with (1 := Rabs_triang _ _).
      apply Rplus_le_compat.
      * rewrite Rabs_mult.
        rewrite Rabs_pos_eq; try lra.
        apply Rmult_le_compat_l; trivial.
        apply Rlt_le in H0.
        etransitivity; try eapply H0.
        apply Rmin_l.
      * rewrite Rabs_mult.
        rewrite Rabs_pos_eq; trivial.
        apply Rmult_le_compat_l; trivial.
        apply Rlt_le in H.
        etransitivity; try eapply H.
        apply Rmin_l.
    + rewrite Rabs_mult.
      apply Rmult_le_0_lt_compat.
      * apply Rabs_pos.
      * apply Rabs_pos.
      * eapply Rlt_le_trans; try eapply H.
        apply Rmin_r.
      * eapply Rlt_le_trans; try eapply H0.
        apply Rmin_l.
  - repeat match_destr_in H0; try (simpl in *; lra).
    invcs H0.
    intros M.
    red in limu, limv.
    specialize (limu (pos_div_2 (mkposreal l1 r0))).
    specialize (limv (Rmax (M / (l1 / 2)) 0)).
    eapply filter_imp; [| eapply filter_and; [apply limu | eapply filter_and; [apply limv | apply is_valid_n]]]
    ; simpl; intros ? [?[? is_valid_n']].
    destruct (u x); destruct (v x); simpl in *; rbar_prover.
    + apply Rle_lt_trans with ((l1 - l1 / 2) * Rmax (M / (l1 / 2)) 0).
      * field_simplify.
        unfold Rmax in *; match_destr.
        -- cut (M <= 0); try lra.
           apply (Rmult_le_compat_r (l1 / 2)) in r3; try lra.
           rewrite Rmult_assoc in r3.
           rewrite Rinv_l in r3; try lra.
        -- apply Rnot_le_lt in n.
           assert (0 < M).
           { 
             apply (Rmult_lt_compat_r (l1 / 2)) in n; try lra.
             rewrite Rmult_assoc in n.
             rewrite Rinv_l in n; try lra.
           }
           unfold Rdiv.
           rewrite Rinv_Rdiv; try lra.
           unfold Rdiv.
           replace (l1 * (M * (2 * / l1)) * / 2) with
               (l1 * (M * (2 * / l1 * / 2))) by now repeat rewrite <- Rmult_assoc.
           rewrite Rinv_r_simpl_m; try lra.
           rewrite <- Rmult_assoc.
           rewrite Rinv_r_simpl_m; try lra.
      * apply Rmult_le_0_lt_compat; try lra.
        -- apply Rmax_r.
        -- apply Rabs_lt_between' in H.
           tauto.
    + apply Rabs_lt_between in H.
      destruct H; lra.
  - intros M.
    specialize (limu posreal1).
    specialize (limv (Rabs M)).
    eapply filter_imp; [| eapply filter_and; [apply limu | eapply filter_and; [apply limv | apply is_valid_n]]]
    ; simpl; intros ? [?[? is_valid_n']].
    destruct (u x); destruct (v x); simpl in *; rbar_prover.
    + eapply Rle_lt_trans; try apply Rle_abs.
      replace (Rabs M) with (1 * Rabs M) by lra.
      apply Rmult_le_0_lt_compat; try lra.
      apply Rabs_pos.
    + apply n.
      apply Rlt_le in H0.
      etransitivity; try apply H0.
      apply Rabs_pos.
Qed.


Lemma is_Elim_seq_mult_aux_pos12 (u v : nat -> Rbar) (l1 l2 l : Rbar) :
  Rbar_le 0 l1 ->
  Rbar_le 0 l2 ->
  is_Elim_seq u l1 ->
  is_Elim_seq v l2 ->
  is_Rbar_mult l1 l2 l ->
  (eventually (fun n => ex_Rbar_mult (u n) ( v n))) ->
  is_Elim_seq (fun n => Rbar_mult (u n) (v n)) l.
Proof.
  intros.
  destruct (Rbar_le_dec l1 l2).
  - eapply is_Elim_seq_mult_aux_pos123; try eapply H1; try eapply H2; eauto.
  - generalize (is_Elim_seq_mult_aux_pos123 v u l2 l1 l)
    ; intros.
    cut_to H5; trivial.
    + revert H5.
      apply is_Elim_seq_ext; intros.
      now rewrite Rbar_mult_comm.
    + apply Rbar_not_le_lt in n.
      now apply Rbar_lt_le.
    + now apply is_Rbar_mult_sym.
    + revert H4.
      apply filter_imp; intros.
      now apply ex_Rbar_mult_sym.
Qed.

Lemma is_Elim_seq_mult (u v : nat -> Rbar) (l1 l2 l : Rbar) :
  is_Elim_seq u l1 ->
  is_Elim_seq v l2 ->
  is_Rbar_mult l1 l2 l ->
  (eventually (fun n => ex_Rbar_mult (u n) ( v n))) ->
  is_Elim_seq (fun n => Rbar_mult (u n) (v n)) l.
Proof.
  intros.
  destruct (Rbar_le_dec 0 l1)
  ;  destruct (Rbar_le_dec 0 l2).
  - eapply is_Elim_seq_mult_aux_pos12; try eapply H0; try eapply H1
    ; trivial.
  - apply Rbar_not_le_lt in n.
    apply is_Elim_seq_opp in H0.
    generalize (is_Elim_seq_mult_aux_pos12 u (fun n : nat => Rbar_opp (v n)) l1 (Rbar_opp l2) (Rbar_opp l))                 
      ; intros HH.
    cut_to HH; trivial.
    + apply is_Elim_seq_opp.
      revert HH.
      apply is_Elim_seq_ext; intros.
      now rewrite Rbar_mult_opp_r.
    + destruct l2; simpl in *; rbar_prover.
    + now apply is_Rbar_mult_opp_r.
    + revert H2; apply filter_imp; intros.
      now apply ex_Rbar_mult_opp_r.
  - apply Rbar_not_le_lt in n.
    apply is_Elim_seq_opp in H.
    generalize (is_Elim_seq_mult_aux_pos12 (fun n : nat => Rbar_opp (u n)) v (Rbar_opp l1) l2 (Rbar_opp l))                 
      ; intros HH.
    cut_to HH; trivial.
    + apply is_Elim_seq_opp.
      revert HH.
      apply is_Elim_seq_ext; intros.
      now rewrite Rbar_mult_opp_l.
    + destruct l1; simpl in *; rbar_prover.
    + now apply is_Rbar_mult_opp_l.
    + revert H2; apply filter_imp; intros.
      now apply ex_Rbar_mult_opp_l.
  - apply Rbar_not_le_lt in n.
    apply Rbar_not_le_lt in n0.
    apply is_Elim_seq_opp in H.
    apply is_Elim_seq_opp in H0.
    generalize (is_Elim_seq_mult_aux_pos12 (fun n : nat => Rbar_opp (u n)) (fun n : nat => Rbar_opp (v n)) (Rbar_opp l1) (Rbar_opp l2) l)                 
      ; intros HH.
    cut_to HH; trivial.
    + revert HH.
      apply is_Elim_seq_ext; intros.
      now rewrite Rbar_mult_opp.
    + destruct l1; simpl in *; rbar_prover.
    + destruct l2; simpl in *; rbar_prover.
    + apply is_Rbar_mult_opp_l in H1.
      apply is_Rbar_mult_opp_r in H1.
      now rewrite Rbar_opp_involutive in H1.
    + revert H2; apply filter_imp; intros.
      apply ex_Rbar_mult_opp_l.
      now apply ex_Rbar_mult_opp_r.
Qed.
  
Lemma is_Elim_seq_mult' (u v : nat -> Rbar) (l1 l2 : R) :
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  (eventually (fun n => ex_Rbar_mult (u n) ( v n))) ->
  is_Elim_seq (fun n => Rbar_mult (u n) (v n)) (l1 * l2).
Proof.
  intros.
  apply  (is_Elim_seq_mult u v l1 l2 (Rbar_mult l1 l2)); trivial.
  reflexivity.
Qed.

Lemma ex_Elim_seq_mult (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v ->
  ex_Rbar_mult (ELim_seq u) (ELim_seq v) ->
  (eventually (fun n => ex_Rbar_mult (u n) ( v n))) ->
  ex_Elim_seq (fun n => Rbar_mult (u n) (v n)).
Proof.
    intros.
    apply ELim_seq_correct in H.
    apply ELim_seq_correct in H0.
    eapply is_Elim_seq_ex_Elim_seq.
    eapply is_Elim_seq_mult; eauto.
    now apply Rbar_mult_correct.
Qed.

Lemma ELim_seq_mult (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v ->
  ex_Rbar_mult (ELim_seq u) (ELim_seq v) ->
  (eventually (fun n => ex_Rbar_mult (u n) ( v n))) ->
  ELim_seq (fun n => Rbar_mult (u n) (v n)) = Rbar_mult (ELim_seq u) (ELim_seq v).
Proof.
  intros.
  apply ELim_seq_correct in H.
  apply ELim_seq_correct in H0.
  apply Rbar_mult_correct in H1.
  eapply is_Elim_seq_unique.
  eapply is_Elim_seq_mult; eauto.
Qed.

Lemma is_Elim_seq_scal_l (u : nat -> Rbar) (a : Rbar) (lu : Rbar) :
  is_Elim_seq u lu ->
  ex_Rbar_mult a lu ->
  eventually (fun n : nat => ex_Rbar_mult a (u n)) ->
  is_Elim_seq (fun n => Rbar_mult a (u n)) (Rbar_mult a lu).
Proof.
  intros.
  apply (is_Elim_seq_mult (fun _ => a) u a lu); trivial.
  - apply is_Elim_seq_const.
  - now apply Rbar_mult_correct in H0.
Qed.

Lemma is_Elim_seq_scal_l' (u : nat -> Rbar) (a : R) (lu : Rbar) :
  is_Elim_seq u lu ->
  is_Elim_seq (fun n => Rbar_mult a (u n)) (Rbar_mult a lu).
Proof.
  intros.
  destruct (Req_EM_T a 0).
  - subst.
    rewrite Rbar_mult_0_l.
    generalize (is_Elim_seq_const 0).
    apply is_Elim_seq_ext; intros.
    now rewrite Rbar_mult_0_l.
  - apply is_Elim_seq_scal_l; trivial.
    destruct lu; simpl; trivial.
    apply filter_forall; intros.
    now destruct (u x); simpl.
Qed.

Lemma ex_Elim_seq_scal_l (u : nat -> Rbar) (a : Rbar) :
  ex_Rbar_mult a (ELim_seq u) ->
  ex_Elim_seq u ->
  eventually (fun n : nat => ex_Rbar_mult a (u n)) ->
  ex_Elim_seq (fun n => Rbar_mult a (u n)).
Proof.
  intros.
  apply ELim_seq_correct in H0.
  eapply is_Elim_seq_ex_Elim_seq.
  eapply is_Elim_seq_scal_l; eauto.
Qed.

Lemma ex_Elim_seq_scal_l' (u : nat -> Rbar) (a : R) :
  ex_Elim_seq u -> ex_Elim_seq (fun n => Rbar_mult a (u n)).
Proof.
  intros.
  apply ELim_seq_correct in H.
  eapply is_Elim_seq_ex_Elim_seq.
  eapply is_Elim_seq_scal_l'; eauto.
Qed.

Lemma ELim_seq_scal_l_pos (u : nat -> Rbar) (a : R) :
  0 <= a ->
  ex_Rbar_mult a (ELim_seq u) ->
  ELim_seq (fun n => Rbar_mult a (u n)) = Rbar_mult a (ELim_seq u).
Proof.
  intros.
  unfold ELim_seq.
  rewrite (ELimSup_seq_scal_pos a u); trivial.
  rewrite (ELimInf_seq_scal_pos a u); trivial.
  unfold Rbar_plus, Rbar_div_pos.
  destruct (ELimSup_seq u)
    ; destruct (ELimInf_seq u)
    ; simpl in *
    ; rbar_prover
    ; simpl; try lra; try (f_equal; lra).
  Qed.
    
Lemma ELim_seq_scal_l (u : nat -> Rbar) (a : R) :
  ex_Rbar_mult a (ELim_seq u) ->
  ELim_seq (fun n => Rbar_mult a (u n)) = Rbar_mult a (ELim_seq u).
Proof.
  intros.
  destruct (Rle_dec 0 a).
  - now apply ELim_seq_scal_l_pos.
  - apply Rbar_opp_eq.
    rewrite <- Rbar_mult_opp_l.
    repeat rewrite <- ELim_seq_opp.
    simpl.
    rewrite <- ELim_seq_scal_l_pos.
    + apply ELim_seq_proper; intros ?.
      now rewrite <- Rbar_mult_opp_l; simpl.
    + lra.
    + destruct (ELim_seq u); simpl in *; lra.
Qed.

Lemma is_Elim_seq_scal_r (u : nat -> Rbar) (a : Rbar) (lu : Rbar) :
  is_Elim_seq u lu ->
  ex_Rbar_mult lu a ->
  eventually (fun n : nat => ex_Rbar_mult (u n) a) ->
  is_Elim_seq (fun n => Rbar_mult (u n) a) (Rbar_mult lu a).
Proof.
  intros.
  generalize (is_Elim_seq_scal_l u a lu)
  ; intros HH.
  cut_to HH; trivial.
  revert HH
  ; apply is_Elim_seq_proper
  ; try red; intros; now rewrite Rbar_mult_comm.
  - now apply ex_Rbar_mult_sym.
  - revert H1; apply filter_imp; intros; now apply ex_Rbar_mult_sym.
Qed.

Lemma is_Elim_seq_scal_r' (u : nat -> Rbar) (a : R) (lu : Rbar) :
  is_Elim_seq u lu ->
  is_Elim_seq (fun n => Rbar_mult (u n) a) (Rbar_mult lu a).
Proof.
  intros.
  generalize (is_Elim_seq_scal_l' u a lu)
  ; intros HH.
  cut_to HH; trivial.
  revert HH
  ; apply is_Elim_seq_proper
  ; try red; intros; now rewrite Rbar_mult_comm.
Qed.

Lemma ex_Elim_seq_scal_r (u : nat -> Rbar) (a : Rbar) :
  ex_Rbar_mult a (ELim_seq u) ->
  ex_Elim_seq u ->
  eventually (fun n : nat => ex_Rbar_mult (u n) a) ->
  ex_Elim_seq (fun n => Rbar_mult (u n) a).
Proof.
  intros.
  generalize (ex_Elim_seq_scal_l u a)
  ; intros HH.
  cut_to HH; trivial.
  revert HH
  ; apply ex_Elim_seq_proper
  ; try red; intros; now rewrite Rbar_mult_comm.
  revert H1; apply filter_imp; intros; now apply ex_Rbar_mult_sym.
Qed.

Lemma ex_Elim_seq_scal_r' (u : nat -> Rbar) (a : R) :
  ex_Elim_seq u -> ex_Elim_seq (fun n => Rbar_mult (u n) a).
Proof.
  intros.
  generalize (ex_Elim_seq_scal_l' u a)
  ; intros HH.
  cut_to HH; trivial.
  revert HH
  ; apply ex_Elim_seq_proper
  ; try red; intros; now rewrite Rbar_mult_comm.
Qed.

Lemma ELim_seq_scal_r (u : nat -> Rbar) (a : R) :
  ex_Rbar_mult (ELim_seq u) a ->
  ELim_seq (fun n => Rbar_mult (u n) a) = Rbar_mult (ELim_seq u) a.
Proof.
  intros.
  rewrite Rbar_mult_comm.
  rewrite <- ELim_seq_scal_l.
  - apply ELim_seq_ext; intros.
    apply Rbar_mult_comm.
  - now apply ex_Rbar_mult_sym.
Qed.

Lemma is_Elim_seq_div (u v : nat -> Rbar) (l1 l2 l : Rbar) :
  is_Elim_seq u l1 -> is_Elim_seq v l2 ->
  l2 <> 0 ->
  is_Rbar_div l1 l2 l ->
  (eventually (fun n => ex_Rbar_div (u n) ( v n))) ->
  is_Elim_seq (fun n => Rbar_div (u n) (v n)) l.
Proof.
  intros.
  unfold Rbar_div.
  eapply is_Elim_seq_mult.
  - apply H.
  - apply is_Elim_seq_inv; eauto.
  - apply H2.
  - apply H3.
Qed.
  
Lemma is_elim_seq_div' (u v : nat -> Rbar) (l1 l2 : R) :
  is_Elim_seq u l1 -> is_Elim_seq v l2 -> l2 <> 0 ->
  (eventually (fun n => ex_Rbar_div (u n) (v n))) ->
  is_Elim_seq (fun n => Rbar_div (u n) (v n)) (l1 / l2).
Proof.
  intros.
  replace (Finite (l1 / l2)) with (Rbar_div l1 l2) by reflexivity.
  eapply is_Elim_seq_div; eauto.
  - congruence.
  - reflexivity.
Qed.
  
Lemma ex_Elim_seq_div (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v -> ELim_seq v <> 0 ->
  ex_Rbar_div (ELim_seq u) (ELim_seq v) ->
  (eventually (fun n => ex_Rbar_div (u n) (v n))) ->
  ex_Elim_seq (fun n => Rbar_div (u n) (v n)).
Proof.
  intros.
  unfold Rbar_div.
  eapply ex_Elim_seq_mult.
  - apply H.
  - apply ex_Elim_seq_inv; eauto.
  - rewrite ELim_seq_inv; trivial.
  - apply H3.
Qed.
  
Lemma ELim_seq_div (u v : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq v -> (ELim_seq v <> 0) ->
  ex_Rbar_div (ELim_seq u) (ELim_seq v) ->
  (eventually (fun n => ex_Rbar_div (u n) ( v n))) ->
  ELim_seq (fun n => Rbar_div (u n) (v n)) = Rbar_div (ELim_seq u) (ELim_seq v).
Proof.
  intros.
  unfold Rbar_div.
  rewrite <- ELim_seq_inv; trivial.
  rewrite <- ELim_seq_mult; trivial.
  - apply ex_Elim_seq_inv; trivial.
  - rewrite ELim_seq_inv; trivial.
Qed.

(*

Lemma ex_lim_seq_adj (u v : nat -> R) :
  (forall n, u n <= u (S n)) -> (forall n, v (S n) <= v n)
  -> is_lim_seq (fun n => v n - u n) 0
  -> ex_finite_lim_seq u /\ ex_finite_lim_seq v /\ Lim_seq u = Lim_seq v.

 *)

Lemma is_Elim_seq_continuous (f : R -> R) (u : nat -> Rbar) (l : R) :
  continuity_pt f l -> is_Elim_seq u l
  -> is_Elim_seq (fun n => match u n with
                       | Finite y => Finite (f y)
                       | p_infty => p_infty
                       | m_infty => m_infty
                       end)
                (f l).
Proof.
  intros cont lim.
  apply is_Elim_seq_spec in lim.
  apply is_Elim_seq_spec.
  intros [eps eps_pos].
  destruct (continuity_pt_locally f l) as [HH _].
  specialize (HH cont).
  destruct (HH (mkposreal eps eps_pos)).
  generalize (lim x).
  apply filter_imp; intros.
  destruct (u x0); simpl in *; try lra.
  apply H.
  apply H0.
Qed.

Lemma is_Elim_seq_abs (u : nat -> Rbar) (l : Rbar) :
  is_Elim_seq u l -> is_Elim_seq (fun n => Rbar_abs (u n)) (Rbar_abs l).
Proof.
  intros.
  apply is_Elim_seq_spec in H.
  apply is_Elim_seq_spec.
  destruct l.
  - intros eps.
    generalize (H eps).
    apply filter_imp; intros.
    destruct (u x); simpl in *; try lra.
    unfold Rabs in *.
    destruct (Rcase_abs r0)
    ; destruct (Rcase_abs r)
    ; match_destr_in H0; try lra
    ; match_destr; lra.
  - intros ?.
    generalize (H M).
    apply filter_imp; intros.
    eapply Rbar_lt_le_trans; try eapply H0.
    destruct (u x); simpl in *; try lra.
    apply Rle_abs.
  - intros M.
    generalize (H (- M)).
    apply filter_imp; intros.
    destruct (u x); simpl in *; try lra.
    unfold Rabs.
    match_destr; lra.
Qed.
  
Lemma ex_Elim_seq_abs (u : nat -> Rbar) :
  ex_Elim_seq u -> ex_Elim_seq (fun n => Rbar_abs (u n)).
Proof.
  intros.
  apply ELim_seq_correct in H.
  eapply is_Elim_seq_ex_Elim_seq.
  eapply is_Elim_seq_abs; eauto.
Qed.

Lemma ELim_seq_abs (u : nat -> Rbar) :
  ex_Elim_seq u ->
  ELim_seq (fun n => Rbar_abs (u n)) = Rbar_abs (ELim_seq u).
Proof.
  intros.
  apply ELim_seq_correct in H.
  eapply is_Elim_seq_unique.
  eapply is_Elim_seq_abs; eauto.
Qed.

Lemma is_Elim_seq_abs_0 (u : nat -> Rbar) :
  is_Elim_seq u 0 <-> is_Elim_seq (fun n => Rbar_abs (u n)) 0.
Proof.
  intros.
  split; intros HH.
  - apply is_Elim_seq_abs in HH.
    now simpl in HH; rewrite Rabs_R0 in HH.
  - apply is_Elim_seq_spec in HH.
    apply is_Elim_seq_spec.
    intros eps.
    specialize (HH eps).
    revert HH; apply filter_imp; intros.
    destruct (u x); simpl in *; try lra.
    rewrite Ropp_0 in H.
    rewrite Ropp_0.
    rewrite Rplus_0_r in H.
    rewrite Rplus_0_r.
    now rewrite Rabs_Rabsolu in H.
Qed.

Lemma is_Elim_seq_geom (q : R) :
  Rabs q < 1 -> is_Elim_seq (fun n => q ^ n) 0.
Proof.
  intros.
  apply is_Elim_seq_fin.
  now apply Lim_seq.is_lim_seq_geom.
Qed.
  
Lemma ex_Elim_seq_geom (q : R) :
  Rabs q < 1 -> ex_Elim_seq (fun n => q ^ n).
Proof.
  intros.
  apply ex_Elim_seq_fin.
  now apply Lim_seq.ex_lim_seq_geom.
Qed.
  
Lemma ELim_seq_geom (q : R) :
  Rabs q < 1 -> ELim_seq (fun n => q ^ n) = 0.
Proof.
  intros.
  rewrite Elim_seq_fin.
  now apply Lim_seq.Lim_seq_geom.
Qed.

Lemma is_Elim_seq_geom_p (q : R) :
  1 < q -> is_Elim_seq (fun n => q ^ n) p_infty.
Proof.
  intros.
  rewrite is_Elim_seq_fin.
  now apply Lim_seq.is_lim_seq_geom_p.
Qed.
  
Lemma ex_Elim_seq_geom_p (q : R) :
  1 < q -> ex_Elim_seq (fun n => q ^ n).
Proof.
  intros.
  rewrite ex_Elim_seq_fin.
  now apply Lim_seq.ex_lim_seq_geom_p.
Qed.

Lemma ELim_seq_geom_p (q : R) :
  1 < q -> ELim_seq (fun n => q ^ n) = p_infty.
Proof.
  intros.
  rewrite Elim_seq_fin.
  now apply Lim_seq.Lim_seq_geom_p.
Qed.

Lemma ex_Elim_seq_geom_m (q : R) :
  q <= -1 -> ~ ex_Elim_seq (fun n => q ^ n).
Proof.
  intros.
  rewrite ex_Elim_seq_fin.
  now apply Lim_seq.ex_lim_seq_geom_m.
Qed.

