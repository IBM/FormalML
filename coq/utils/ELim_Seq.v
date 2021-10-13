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

(* we should also make a derived eventuallyR2
   and show that it preserves equiv... and then we can make a proper instance for it.
   Like we do for almost
 *)

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

Lemma is_ELimSup_seq_scal_pos (a : R) (u : nat -> Rbar) (l : Rbar) :
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

Lemma ELimSup_seq_scal_pos (a : R) (u : nat -> Rbar) (l : Rbar) :
  0 < a ->
  ELimSup_seq (fun n => Rbar_mult a (u n))  = Rbar_mult a (ELimSup_seq u).
Proof.
  intros.
  apply is_ELimSup_seq_unique.
  apply is_ELimSup_seq_scal_pos; trivial.
  apply is_ELimSup_seq_correct.
Qed.

Lemma is_ELimInf_seq_scal_pos (a : R) (u : nat -> Rbar) (l : Rbar) :
  Rbar_lt 0 a ->
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

Lemma ELimInf_seq_scal_pos (a : R) (u : nat -> Rbar) (l : Rbar) :
  0 < a ->
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

(*
Definition ERbar_locally (a : Rbar) (P : Rbar -> Prop)
  := Rbar_locally a (fun x => P (Finite x)).

Local Existing Instance Rbar_lt_strict.

Global Instance ERbar_locally_filter :
  forall x, ProperFilter (ERbar_locally x).
Proof.
  unfold ERbar_locally.
  intros.
  destruct (Rbar_locally_filter x) as [? [???]].
  split.
  - intros ? HH.
    destruct (filter_ex _ HH); eauto.
  - split; eauto 2; intros.
    eapply filter_imp; eauto; simpl; eauto.
Qed.

Lemma ERbar_locally_fin (l : Rbar):
  forall (x:R->Prop), ERbar_locally l (fun a => x (Finite a)) <-> Rbar_locally l x.
Proof.
  intros.
  reflexivity.
Qed.
 *)

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

Lemma Rbar_abs_triang (a b : Rbar) :
  Rbar_le (Rbar_abs (Rbar_plus a b)) (Rbar_plus (Rbar_abs a) (Rbar_abs b)).
Proof.
  destruct a; destruct b; simpl; rbar_prover.
  apply Rabs_triang.
Qed.

Lemma Rbar_abs_minus_sym (x y : Rbar) :
  Rbar_abs (Rbar_minus x y) = Rbar_abs (Rbar_minus y x).
Proof.
  destruct x; destruct y; simpl; try solve [rbar_prover; trivial].
  now rewrite Rabs_minus_sym.
Qed.

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

(*
Lemma eventually_subseq_loc :
  forall phi,
  eventually (fun n => (phi n < phi (S n))%nat) ->
  filterlim phi eventually eventually.
Lemma eventually_subseq :
  forall phi,
  (forall n, (phi n < phi (S n))%nat) ->
  filterlim phi eventually eventually.
 *)

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

