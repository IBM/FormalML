Require Import List.
Require Import mdp qvalues pmf_monad Finite EquivDec.
Require Import Reals RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import RandomVariableL2 infprod Dvoretzky Expectation.
Require Import RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace DiscreteProbSpace.

Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Section MDP.
  Context (M : MDP) (γ : R).

  Arguments reward {_}.
  Arguments outcomes {_}.
  Arguments t {_}.

  Class MDPonline : Type := mkMDP
  { on_state : Type;
    on_act : on_state -> Type;
    on_st_eqdec : EquivDec.EqDec on_state eq;
    on_fs : Finite on_state;
    on_fa : forall s : on_state, Finite (on_act s);
    on_ne : mdp.NonEmpty on_state;
    on_na : forall s : on_state, mdp.NonEmpty (on_act s);
    on_t : forall s : on_state, on_act s -> ProbSpace (discrete_sa on_state);
    on_reward : forall s : on_state, on_act s -> on_state -> R;
  }.

  Class MDPoffline : Type := mkMDPoffline
  { off_state : Type;
    off_act : off_state -> Type;
    off_st_eqdec : EquivDec.EqDec off_state eq;
    off_fs : Finite off_state;
    off_fa : forall s : off_state, Finite (off_act s);
    off_ne : mdp.NonEmpty off_state;
    off_na : forall s : off_state, mdp.NonEmpty (off_act s);
    off_t : (forall s : off_state, off_act s -> off_state) -> ProbSpace (discrete_sa (forall s, off_act s));
    off_reward : forall s : off_state, off_act s -> off_state -> R;
  }.


  (*
    How do we port this over to the new version?
    We will need a new definition of MDPs accounting for the RandomVariable
    and ProbSpace structure.
  *)

  Definition reward_sa (sa : sigT M.(act)) (s' : M.(state)) : R :=
    let (s, a) := sa in reward s a s'.

  Definition bellmanQ' : Rfct(sigT M.(act)) -> (sigT M.(act) -> M.(state)) -> Rfct(sigT M.(act))
  := fun W => fun pi sa => let s' := pi sa in
                  reward_sa sa s' + γ*Max_{act_list s'}(fun a => W (existT _ s' a)).

  Context (alpha : nat -> sigT M.(act) -> R)
          (pi : nat -> sigT M.(act) -> M.(state))
          (max_reward min_reward : R)
          (Q0 : Rfct(sigT M.(act))).

  Fixpoint Q (n : nat) : Rfct(sigT M.(act)) 
    := match n with
       | 0 => Q0
       | (S n') => fun sa =>
                     (1 - alpha n' sa) * (Q n' sa) + 
                     (alpha n' sa) *
                     (bellmanQ' (Q n') (pi n') sa)
       end.

  Definition s_act_list : list (sigT M.(act)) :=
    let (la, Hla) := act_finite M in la.

  Lemma s_act_list_not_nil :
    nil <> s_act_list.
  Proof.
    apply not_nil_exists.
    unfold s_act_list.
    generalize (ne M); intros.
    generalize (na M X); intros.
    exists (existT _ X X0).
    apply finite.
  Qed.

  (* lemma 5 *)
  Lemma upper_bound_step :
    0 < γ < 1 ->
    (forall sa s', reward_sa sa s' <= max_reward) ->
    (forall t sa, 0 <= alpha t sa < 1) ->
    forall t,
      Max_{s_act_list}(Q (S t)) <= Rmax (max_reward/(1-γ)) 
                                        (Max_{s_act_list}(Q t)).
  Proof.
    intros gc rw ac ?.
    assert (step1: forall t sa,
               (1 - alpha t sa)*(Q t sa) <= (1 - alpha t sa)*
                                            (Max_{s_act_list}(Q t))).
    {
      intros.
      apply Rmult_le_compat_l.
      - specialize (ac t0 sa); lra.
      - apply Rmax_spec_map.
        unfold s_act_list.
        match_destr.
    }
    assert (step2: forall (t:nat) (sa:sigT M.(act)),
               (alpha t sa)*(reward_sa sa (pi t sa) +
                             γ*Max_{act_list (pi t sa)}
                                   (fun a => Q t (existT _ (pi t sa) a))) <=
               (alpha t sa)*(max_reward + γ*Max_{s_act_list}(Q t))).
    {
      intros.
      apply Rmult_le_compat_l.
      - specialize (ac t0 sa); lra.
      - apply Rplus_le_compat; trivial.
        apply Rmult_le_compat_l; try lra.
        apply Rmax_list_incl.
        + unfold not; intros.
          symmetry in H.
          apply map_eq_nil in H.
          generalize (act_list_not_nil (pi t0 sa)); intros.
          now rewrite H in H0.
        + rewrite incl_Forall_in_iff.
          rewrite Forall_forall.
          intros.
          rewrite in_map_iff in H.
          destruct H as [? [? ?]].
          rewrite <- H.
          apply in_map.
          apply finite.
    }
    assert (step12: forall (t:nat) (sa:sigT M.(act)),
               Q (S t) sa <= (1 - alpha t sa)*
                             (Max_{s_act_list}(Q t)) +
                             (alpha t sa)*(max_reward + γ*Max_{s_act_list}(Q t))).
    {
      intros.
      specialize (step1 t0 sa).
      specialize (step2 t0 sa).
      simpl.
      unfold bellmanQ'.
      lra.
    }
    assert (cases: forall (t:nat) (sa:sigT M.(act)),
               Q (S t) sa <= Rmax (max_reward / (1 - γ)) (Max_{ s_act_list}(Q t))).
    {
      intros.
      rewrite Rmax_comm.
      eapply Rle_trans.
      apply step12.
      unfold Rmax.
      match_destr.
      - apply Rle_trans with 
            (r2 :=
               ((1 - alpha t0 sa) * (max_reward / (1 - γ)) +
                (alpha t0 sa) * (max_reward + γ * (max_reward / (1 - γ))))).
        + apply Rplus_le_compat.
          * apply Rmult_le_compat_l; trivial.
            specialize (ac t0 sa); lra.
          * apply Rmult_le_compat_l.
            -- specialize (ac t0 sa); lra.
            -- apply Rplus_le_compat_l.
               apply Rmult_le_compat_l; trivial.
               lra.
        + right.
          field.
          lra.
      - apply Rle_trans with 
            (r2 :=
               ((1 - alpha t0 sa) * (Max_{ s_act_list}(Q t0)) + 
                (alpha t0 sa) * ((1-γ)*(Max_{ s_act_list}(Q t0)) + 
                                 γ * (Max_{ s_act_list}(Q t0))))). 
        + apply Rplus_le_compat.
          * apply Rmult_le_compat_l; try lra.
            specialize (ac t0 sa); lra.
          * apply Rmult_le_compat_l.
            -- specialize (ac t0 sa); lra.
            -- apply Rplus_le_compat; try lra.
               apply Rmult_le_reg_l with (r := /  (1 - γ)).
               ++ apply Rinv_0_lt_compat; lra.
               ++ rewrite <- Rmult_assoc.
                  rewrite <- Rinv_l_sym; lra.
        + right.
          field.
    }
    rewrite Rmax_list_le_iff.
    - intros.
      rewrite in_map_iff in H.
      destruct H as [? [? ?]].
      rewrite <- H.
      apply cases.
    - unfold not; intros.
      symmetry in H.
      apply map_eq_nil in H.
      generalize (s_act_list_not_nil); intros.
      now rewrite H in H0.
  Qed.

  Notation "Min_{ l } ( f )" := (Rmin_list (List.map f l)) (at level 50).

  Lemma Rmax_list_map_ge_Rmin {A} (l : list A) (f : A -> R) :
    Rmax_list (map f l) >= Rmin_list (map f l).
  Proof.
    destruct l.
    - simpl; lra.
    - apply Rge_trans with (r2 := f a).
      + apply Rle_ge, Rmax_spec_map, in_eq.
      + apply Rmin_spec_map, in_eq.
   Qed.

  (* lemma 6 *)
  Lemma lower_bound_step :
    0 < γ < 1 ->
    (forall sa s', reward_sa sa s' >= min_reward) ->
    (forall t sa, 0 <= alpha t sa < 1) ->
    forall t,
      Min_{s_act_list}(Q (S t)) >= Rmin (min_reward/(1-γ)) 
                                        (Min_{s_act_list}(Q t)).
  Proof.
    intros gc rw ac ?.
    assert (step1: forall t sa,
               (1 - alpha t sa)*(Q t sa) >= (1 - alpha t sa)*
                                            (Min_{s_act_list}(Q t))).
    {
      intros.
      apply Rmult_ge_compat_l.
      - specialize (ac t0 sa); lra.
      - apply Rmin_spec_map.
        unfold s_act_list.
        match_destr.
    }
    assert (step2: forall (t:nat) (sa:sigT M.(act)),
               (alpha t sa)*(reward_sa sa (pi t sa) +
                             γ*Max_{act_list (pi t sa)}
                                   (fun a => Q t (existT _ (pi t sa) a))) >=
               (alpha t sa)*(min_reward + γ*Min_{s_act_list}(Q t))).
    {
      intros.
      apply Rmult_ge_compat_l.
      - specialize (ac t0 sa); lra.
      - apply Rplus_ge_compat; trivial.
        apply Rmult_ge_compat_l; try lra.
        apply Rge_trans with
            (r2 :=  Min_{ act_list (pi t0 sa)}
                        (fun a : act M (pi t0 sa) => Q t0 (existT (act M) (pi t0 sa) a))).
        + apply Rmax_list_map_ge_Rmin.
        + apply Rmin_list_incl.
          * unfold not; intros.
            symmetry in H.
            apply map_eq_nil in H.
            generalize (act_list_not_nil (pi t0 sa)); intros.
            now rewrite H in H0.
          * rewrite incl_Forall_in_iff.
            rewrite Forall_forall.
            intros.
            rewrite in_map_iff in H.
            destruct H as [? [? ?]].
            rewrite <- H.
            apply in_map.
            apply finite.
    }
    assert (step12: forall (t:nat) (sa:sigT M.(act)),
               Q (S t) sa >= (1 - alpha t sa)*
                             (Min_{s_act_list}(Q t)) +
                             (alpha t sa)*(min_reward + γ*Min_{s_act_list}(Q t))).
    {
      intros.
      specialize (step1 t0 sa).
      specialize (step2 t0 sa).
      simpl.
      unfold bellmanQ'.
      lra.
    }
    assert (cases: forall (t:nat) (sa:sigT M.(act)),
               Q (S t) sa >= Rmin (min_reward / (1 - γ)) (Min_{ s_act_list}(Q t))).
    {
      intros.
      eapply Rge_trans.
      apply step12.
      unfold Rmin.
      match_destr.
      - apply Rge_trans with 
            (r2 :=
               ((1 - alpha t0 sa) * (min_reward / (1 - γ)) +
                (alpha t0 sa) * (min_reward + γ * (min_reward / (1 - γ))))).
        + apply Rplus_ge_compat.
          * apply Rmult_ge_compat_l; try lra.
            specialize (ac t0 sa); lra.
          * apply Rmult_ge_compat_l.
            -- specialize (ac t0 sa); lra.
            -- apply Rplus_ge_compat_l.
               apply Rmult_ge_compat_l; lra.
        + right.
          field.
          lra.
      - apply Rge_trans with 
            (r2 :=
               ((1 - alpha t0 sa) * (Min_{ s_act_list}(Q t0)) + 
                (alpha t0 sa) * ((1-γ)*(Min_{ s_act_list}(Q t0)) + 
                                 γ * (Min_{ s_act_list}(Q t0))))). 
        + apply Rplus_ge_compat.
          * apply Rmult_ge_compat_l; try lra.
            specialize (ac t0 sa); lra.
          * apply Rmult_ge_compat_l.
            -- specialize (ac t0 sa); lra.
            -- apply Rplus_ge_compat; try lra.
               apply Rle_ge.
               apply Rmult_le_reg_l with (r := /  (1 - γ)).
               ++ apply Rinv_0_lt_compat; lra.
               ++ rewrite <- Rmult_assoc.
                  rewrite <- Rinv_l_sym; lra.
        + right.
          field.
    }
    rewrite Rmin_list_ge_iff.
    - intros.
      rewrite in_map_iff in H.
      destruct H as [? [? ?]].
      rewrite <- H.
      apply cases.
    - unfold not; intros.
      symmetry in H.
      apply map_eq_nil in H.
      generalize (s_act_list_not_nil); intros.
      now rewrite H in H0.
  Qed.

  (* Theorem 7 *)
  Lemma upper_bound :
    0 < γ < 1 ->
    (forall sa s', reward_sa sa s' <= max_reward) ->
    (forall t sa, 0 <= alpha t sa < 1) ->
    exists (Cmax : R),
      forall t sa, Q t sa <= Cmax.
  Proof.
    intros gc rw ac.
    exists (Rmax (Max_{ s_act_list}(Q 0))  (max_reward / (1 - γ))).
    intros.
    revert sa.
    induction t.
    - intros.
      rewrite Rmax_Rle.
      left.
      apply Rmax_spec_map.
      apply finite.
    - intros.
      assert (Max_{ s_act_list}(Q t) <=  Rmax (Max_{ s_act_list}(Q 0)) (max_reward / (1 - γ))).
      {
        rewrite Rmax_list_le_iff.
        - intros.
          rewrite in_map_iff in H.
          destruct H as [? [? ?]].
          rewrite <- H.
          apply IHt.
        - unfold not; intros.
          symmetry in H.
          apply map_eq_nil in H.
          generalize (s_act_list_not_nil); intros.
          now rewrite H in H0.
      }
      assert (Q (S t) sa <= (Max_{ s_act_list}(Q (S t)))).
      {
        apply Rmax_spec_map.
        apply finite.
      }
      eapply Rle_trans.
      apply H0.
      eapply Rle_trans.
      apply upper_bound_step; try lra; trivial.
      apply Rle_Rmax.
      split; trivial.
      apply Rmax_r.
  Qed.
        
  (* Theorem 7 *)
  Lemma lower_bound :
    0 < γ < 1 ->
    (forall sa s', reward_sa sa s' >= min_reward) ->
    (forall t sa, 0 <= alpha t sa < 1) ->
    exists (Cmin : R),
      forall t sa, Q t sa >= Cmin.
  Proof.
    intros gc rw ac.
    exists (Rmin (Min_{ s_act_list}(Q 0))  (min_reward / (1 - γ))).
    intros.
    revert sa.
    induction t.
    - intros.
      apply Rge_trans with (r2 := Min_{ s_act_list}(Q 0)).
      + apply Rmin_spec_map.
        unfold s_act_list.
        apply finite.
      + apply Rle_ge, Rmin_l.
    - intros.
      assert (Min_{ s_act_list}(Q t) >=  Rmin (Min_{ s_act_list}(Q 0)) (min_reward / (1 - γ))).
      {
        rewrite Rmin_list_ge_iff.
        - intros.
          rewrite in_map_iff in H.
          destruct H as [? [? ?]].
          rewrite <- H.
          apply IHt.
        - unfold not; intros.
          symmetry in H.
          apply map_eq_nil in H.
          generalize (s_act_list_not_nil); intros.
          now rewrite H in H0.
      }
      assert (Q (S t) sa >= (Min_{ s_act_list}(Q (S t)))).
      {
        apply Rmin_spec_map.
        unfold s_act_list.
        apply finite.
      }
      eapply Rge_trans.
      apply H0.
      eapply Rge_trans.
      apply lower_bound_step; try lra; trivial.
      apply Rle_ge.
      apply Rmin_glb.
      + apply Rmin_r.
      + now apply Rge_le.
  Qed.

  Lemma abs_bound a b c :
    a <= b <= c ->
    Rabs b <= Rabs a + Rabs c.
  Proof.
    intros.
    unfold Rabs.
    match_destr; match_destr; match_destr; try lra.
  Qed.
  
  Lemma noise_bound :
       0 < γ < 1 ->
       (forall sa s', reward_sa sa s' <= max_reward) ->
       (forall sa s', reward_sa sa s' >= min_reward) ->
       (forall t sa, 0 <= alpha t sa < 1) ->
        exists (sigma : R),
        forall n sa,
          Rsqr ((bellmanQ' (Q n) (pi n) sa) -
                bellmanQbar γ (Q n) sa) <= Rsqr sigma.
   Proof.
     intros glim maxr minr alim.
     destruct (upper_bound glim maxr alim) as [Cmax ?].
     destruct (lower_bound glim minr alim) as [Cmin ?].
     assert (forall sa s', Rabs (reward_sa sa s') <= Rabs min_reward + Rabs max_reward).
     {
       intros.
       apply abs_bound.
       specialize (maxr sa  s').
       specialize (minr sa  s').
       lra.
     }
     assert (exists (s1:R),
                (0 <= s1) /\
                forall (n : nat) (sa : {x : state M & act M x}),
                  Rabs (bellmanQ' (Q n) (pi n) sa) <= Rabs s1).
     {
       exists ((Rabs min_reward + Rabs max_reward) + (Rabs Cmin + Rabs Cmax)).
       split.
       - apply Rplus_le_le_0_compat; apply Rplus_le_le_0_compat; apply Rabs_pos.
       - intros.
         unfold bellmanQ'.
         generalize (Rabs_triang  (reward_sa sa (pi n sa))
                                (γ *
                                 (Max_{ act_list (pi n sa)}
                                      (fun a : act M (pi n sa) => 
                                         Q n (existT (act M) (pi n sa) a))))); intros.
         eapply Rle_trans.
         apply H2.
         apply Rge_le; rewrite Rabs_right; apply Rle_ge.
         + apply Rplus_le_compat; trivial.
           rewrite Rabs_mult.
           apply Rle_trans with
               (r2 :=  Rabs
                         (Max_{ act_list (pi n sa)}
                              (fun a : act M (pi n sa) => Q n (existT (act M) (pi n sa) a)))).
           * rewrite Rabs_right; try lra.
             rewrite <- Rmult_1_l.
             apply Rmult_le_compat; try lra.
             apply Rabs_pos.
           * apply abs_bound.
             assert ( nil <>
                      map (fun a : act M (pi n sa) => Q n (existT (act M) (pi n sa) a))
                          (act_list (pi n sa))).
             {
               unfold not; intros.
               symmetry in H3.
               apply map_eq_nil in H3.
               generalize (act_list_not_nil (pi n sa)); intros.
               congruence.
             }
             split.
             -- apply Rmax_list_glb; trivial.
                intros.
                apply in_map_iff in H4.
                destruct H4 as [? [? ?]].
                rewrite <- H4.
                apply Rge_le.
                apply H0.
             -- apply Rmax_list_lub; trivial.
                intros.
                apply in_map_iff in H4.
                destruct H4 as [? [? ?]].
                rewrite <- H4.
                apply H.
         + apply Rplus_le_le_0_compat; apply Rplus_le_le_0_compat; apply Rabs_pos.
     }
      assert (exists (s2:R),
                (0 <= s2) /\
                forall (n : nat) (sa : {x : state M & act M x}),
                  Rabs (bellmanQbar γ (Q n) sa) <= Rabs s2).
     {
       exists ((Rabs min_reward + Rabs max_reward) + (Rabs Cmin + Rabs Cmax)).
       split.
       - apply Rplus_le_le_0_compat; apply Rplus_le_le_0_compat; apply Rabs_pos.
       - intros.
         unfold bellmanQbar.
         destruct sa.
         generalize (Rabs_triang (act_expt_reward x a)
                                 ( γ *
                                   expt_value (t x a)
                                              (fun s' : state M =>
                                                 Max_{ act_list s'}(fun a0 : act M s' => Q n (existT (act M) s' a0))))); intros.
         eapply Rle_trans.
         apply H3.
         apply Rge_le; rewrite Rabs_right; apply Rle_ge.
         + apply Rplus_le_compat.
           * apply abs_bound.
             unfold act_expt_reward.
             split.
             -- apply expt_value_lbdd.
                unfold reward_sa in minr.
                intros.
                apply Rge_le.
                specialize (minr (existT _ x a) a0).
                apply minr.
             -- apply expt_value_bdd.
                unfold reward_sa in maxr.
                intros.
                specialize (maxr (existT _ x a) a0).
                apply maxr.
           * rewrite Rabs_mult.
             apply Rle_trans with
                 (r2 :=  Rabs
                           (expt_value (t x a)
                                       (fun s' : state M =>
                                          Max_{ act_list s'}(fun a0 : act M s' => Q n (existT (act M) s' a0))))).
             -- rewrite Rabs_right; try lra.
                rewrite <- Rmult_1_l.
                apply Rmult_le_compat; try lra.
                apply Rabs_pos.
             -- apply abs_bound.
                split.
                ++ apply expt_value_lbdd.
                   intros.
                   apply Rmax_list_glb.
                   ** unfold not; intros.
                      symmetry in H4.
                      apply map_eq_nil in H4.
                      generalize (act_list_not_nil a0); intros.
                      congruence.
                   ** intros.
                      apply in_map_iff in H4.
                      destruct H4 as [? [? ?]].
                      rewrite <- H4.
                      apply Rge_le.
                      apply H0.
                ++ apply expt_value_bdd.
                   intros.
                   apply Rmax_list_lub.
                   ** unfold not; intros.
                      symmetry in H4.
                      apply map_eq_nil in H4.
                      generalize (act_list_not_nil a0); intros.
                      congruence.
                   ** intros.
                      apply in_map_iff in H4.
                      destruct H4 as [? [? ?]].
                      rewrite <- H4.
                      apply H.
         + apply Rplus_le_le_0_compat; apply Rplus_le_le_0_compat; apply Rabs_pos.
     }
     destruct H2 as [s1 [? ?]].
     destruct H3 as [s2 [? ?]].
     exists (s1 + s2).
     intros. 
     specialize (H n sa).
     specialize (H0 n sa).
     apply Rsqr_le_abs_1.
     unfold Rminus.
     apply Rle_trans with
         (r2 := Rabs (bellmanQ' (Q n) (pi n) sa) +
                Rabs (- bellmanQbar γ (Q n) sa)).
     apply Rabs_triang.
     replace (Rabs (s1 + s2)) with (Rabs s1 + Rabs s2).
     - rewrite Rabs_Ropp.
       apply Rplus_le_compat; trivial.
     - rewrite Rabs_right; try lra.
       rewrite Rabs_right; try lra.
       rewrite Rabs_right; try lra.
  Qed.

   Fixpoint Y (tk:nat) (C: R) (n:nat) sa : R :=
    match n with
    | 0%nat => C
    | S n' => (1-alpha (n'+tk)%nat sa)*(Y tk C n' sa) +
              (alpha (n'+tk)%nat sa) * γ * C 
    end.

   Fixpoint Z (tk:nat) (QQ : nat -> Rfct(sigT M.(act))) (n:nat) sa : R :=
    match n with
    | 0%nat => 0
    | S n' => (1-alpha (n' + tk)%nat sa)*(Z tk QQ n' sa) +
              (alpha (n'+tk)%nat sa) * (QQ n' sa)
    end.

   Lemma le_minus (a b : R) :
     a - b <= 0 ->
     a <= b.
   Proof.
     lra.
   Qed.

   Lemma le_minus2 (a b : R) :
     a <= b ->
     a - b <= 0.
   Proof.
     lra.
   Qed.

   Lemma Rmax_norm_spec {A : Type} (finA : Finite A) (X : Rfct A):
     forall a, Rabs (X a) <= Rmax_norm _ X.
     Proof.
       intros a.
       unfold Rmax_norm. destruct finA.
       apply Rmax_spec. rewrite in_map_iff.
       exists a. split; trivial.
     Qed.

     Lemma bellmanQbar_0 (X Y : Rfct(sigT M.(act))) :
       bellmanQbar 0 X = bellmanQbar 0 Y.
     Proof.
       unfold bellmanQbar.
       apply Rfct_eq_ext.
       intros.
       destruct x.
       do 2 rewrite Rmult_0_l.
       lra.
     Qed.

     Lemma bellmanQbar_contraction :
       0 <= γ < 1 ->
       forall (X1 X2 : Rfct(sigT M.(act))),
         Hierarchy.norm (Hierarchy.minus (bellmanQbar γ X1) (bellmanQbar γ X2)) <=
         γ * Hierarchy.norm (Hierarchy.minus X1 X2).
     Proof.
       intros glim ? ?.
       destruct (Req_EM_T γ 0).
       - rewrite e; right.
         rewrite Rmult_0_l.
         rewrite bellmanQbar_0 with (Y := X2).
         rewrite Hierarchy.minus_eq_zero.
         unfold Hierarchy.norm, Hierarchy.zero; simpl.
         unfold Rmax_norm.
         destruct (act_finite M).
         unfold Rfct_zero; simpl.
         setoid_rewrite Rabs_R0.
         now rewrite Rmax_list_zero.
       - generalize (@isContraction_bellmanQbar_gamma M γ glim); intros.
         cut_to H; try lra.
         unfold fixed_point.is_Lipschitz in H.
         destruct H.
         assert (HH1: 0 <= γ <= 1) by lra.
         generalize (@is_Lipschitz_cond Hierarchy.R_AbsRing _ _ (@bellmanQbar M γ) _ HH1); intros.
         apply H1.
         intros.
         apply H0.
         + generalize (Hierarchy.norm_ge_0 (Hierarchy.minus y x)); intros.
           apply Rle_lt_trans with
               (r2 := Hierarchy.norm (Hierarchy.minus y x)); trivial.
         + apply H2.
     Qed.

   Lemma core_bounding_upper (Qstar : Rfct(sigT M.(act))) (tk:nat) (Ck : R) :
     0 <= γ < 1 ->
     (forall t sa, 0 <= alpha t sa < 1) ->
     bellmanQbar γ Qstar = Qstar ->
     (forall t, Rmax_norm _ (Rfct_plus _ (Q (t+tk)%nat) (Rfct_opp _ Qstar)) <= Ck) ->
     forall t sa,
       Q (t+tk)%nat sa - Qstar sa <= Y tk Ck t sa + 
                                     Z tk (fun n sa => 
                                          (bellmanQ' (Q (n+tk)%nat) (pi (n+tk)%nat) sa -
                                           bellmanQbar γ (Q (n+tk)%nat) sa))
                                       t sa.
   Proof.
     intros glim alim fixedQstar Qbound t sa.
     induction t.
     - simpl.
       rewrite Rplus_0_r.
       specialize (Qbound (0%nat)).
       generalize (Rmax_norm_spec _ (Hierarchy.minus (Q tk) Qstar)); intros.
       apply Rle_trans with
           (r2 := Rabs (Q tk sa - Qstar sa)); [apply Rle_abs|].
       apply Rle_trans with
           (r2 := Rmax_norm _  (Hierarchy.minus (Q tk) Qstar)); trivial.
       apply H.
     - assert (forall t,
                  Q (S t) sa - Qstar sa = 
                  (1 - alpha t sa) * (Q t sa - Qstar sa) +
                  (alpha t sa) * ((bellmanQbar γ  (Q t) sa) -
                                  (bellmanQbar γ Qstar sa)) +
                  (alpha t sa) * ((bellmanQ' (Q t) (pi t) sa) - 
                                  (bellmanQbar γ (Q t) sa))).
       {
         intros.
         simpl.
         rewrite fixedQstar.
         ring.
       }
       specialize (H (t + tk)%nat).
       replace (S (t + tk)) with (S t + tk)%nat in H by lia.
       rewrite H.
       apply Rle_trans with
           (r2 := ((1 - alpha (t + tk) sa) * (Y tk Ck t sa +
                   Z tk
                     (fun (n : nat) (sa : {x : state M & act M x}) =>
                        bellmanQ' (Q (n + tk)) (pi (n + tk)) sa -
                        bellmanQbar γ (Q (n + tk)) sa) t sa)) +
                  alpha (t + tk) sa * 
                  (bellmanQbar γ (Q (t + tk)) sa - bellmanQbar γ Qstar sa) +
                  alpha (t + tk) sa *
                  (bellmanQ' (Q (t + tk)) (pi (t + tk)) sa - 
                   bellmanQbar γ (Q (t + tk)) sa)).
       + apply Rplus_le_compat; try lra.
         apply Rplus_le_compat; try lra.
         apply Rmult_le_compat_l with (r := 1 - alpha (t + tk) sa) in IHt; trivial.
         specialize (alim (t + tk)%nat sa).
         lra.
       + apply Rle_trans with
             (r2 := (1 - alpha (t + tk) sa) *
                    (Y tk Ck t sa +
                     Z tk
                       (fun (n : nat) (sa0 : {x : state M & act M x}) =>
                          bellmanQ' (Q (n + tk)) (pi (n + tk)) sa0 - 
                          bellmanQbar γ (Q (n + tk)) sa0)
                       t sa) +
                    alpha (t + tk) sa * (γ * Ck) +
                    alpha (t + tk) sa *
                    (bellmanQ' (Q (t + tk)) (pi (t + tk)) sa - 
                     bellmanQbar γ (Q (t + tk)) sa)).
         * apply Rplus_le_compat; try lra.
           apply Rplus_le_compat; try lra.
           assert ((bellmanQbar γ (Q (t + tk)) sa - bellmanQbar γ Qstar sa) <=
                   (γ * Ck)).
           {
             generalize (bellmanQbar_contraction glim (Q (t + tk)) Qstar); intros.
             apply Rle_trans with
                 (r2 := Rabs (bellmanQbar γ (Q (t + tk)) sa - bellmanQbar γ Qstar sa)); [apply Rle_abs|].
             unfold Hierarchy.norm in H0; simpl in H0.
             apply Rle_trans with
                 (r2 :=  Rmax_norm {x : state M & act M x}
                                   (Hierarchy.minus  (bellmanQbar γ (Q (t + tk))) (bellmanQbar γ Qstar)) ).
             - replace  (bellmanQbar γ (Q (t + tk)) sa - bellmanQbar γ Qstar sa) with
                   (Hierarchy.minus  (bellmanQbar γ (Q (t + tk))) (bellmanQbar γ Qstar) sa); [apply Rmax_norm_spec | ].
               unfold Hierarchy.minus, Hierarchy.plus, Hierarchy.opp; simpl.
               unfold Rfct_opp, Hierarchy.opp; simpl.
               unfold Rfct_plus.
               lra.
             - eapply Rle_trans.
               apply H0.
               apply Rmult_le_compat_l; try lra.
               apply Qbound.
           }
           apply Rmult_le_compat_l with (r := alpha (t + tk) sa) in H0; trivial.
           specialize (alim (t + tk)%nat sa).
           lra.
         * simpl.
           ring_simplify.
           apply Rplus_le_compat; [|right; reflexivity].
           apply Rplus_le_compat; [|right; reflexivity].
           apply le_minus.
           ring_simplify.
           rewrite Rplus_comm.
           ring_simplify.
           apply le_minus2.
           right.
           reflexivity.
   Qed.

   Lemma ge_minus (a b : R) :
     a - b >= 0 ->
     a >= b.
   Proof.
     lra.
   Qed.

   Lemma ge_minus2 (a b : R) :
     a >= b ->
     a - b >= 0.
   Proof.
     lra.
   Qed.

   Lemma core_bounding_lower (Qstar : Rfct(sigT M.(act))) (tk:nat) (Ck : R) :
     0 <= γ < 1 ->
     (forall t sa, 0 <= alpha t sa < 1) ->
     bellmanQbar γ Qstar = Qstar ->
     (forall t, Rmax_norm _ (Rfct_plus _ (Q (t+tk)%nat) (Rfct_opp _ Qstar)) <= Ck) ->
     forall t sa,
       Q (t+tk)%nat sa - Qstar sa >= - Y tk Ck t sa + 
                                     Z tk (fun n sa => 
                                          (bellmanQ' (Q (n+tk)%nat) (pi (n+tk)%nat) sa -
                                           bellmanQbar γ (Q (n+tk)%nat) sa))
                                       t sa.
   Proof.
     intros glim alim fixedQstar Qbound t sa.
     induction t.
     - simpl.
       rewrite Rplus_0_r.
       specialize (Qbound (0%nat)).
       generalize (Rmax_norm_spec _ (Hierarchy.minus (Q tk) Qstar)); intros.
       assert (Rabs (Q tk sa - Qstar sa) <= Ck).
       {
         apply Rle_trans with
             (r2 := Rmax_norm _  (Hierarchy.minus (Q tk) Qstar)); trivial.
         apply H.
       }
       apply Rcomplements.Rabs_le_between in H0.
       lra.
     - assert (forall t,
                  Q (S t) sa - Qstar sa = 
                  (1 - alpha t sa) * (Q t sa - Qstar sa) +
                  (alpha t sa) * ((bellmanQbar γ  (Q t) sa) -
                                  (bellmanQbar γ Qstar sa)) +
                  (alpha t sa) * ((bellmanQ' (Q t) (pi t) sa) - 
                                  (bellmanQbar γ (Q t) sa))).
       {
         intros.
         simpl.
         rewrite fixedQstar.
         ring.
       }
       specialize (H (t + tk)%nat).
       replace (S (t + tk)) with (S t + tk)%nat in H by lia.
       rewrite H.
       apply Rge_trans with
           (r2 := ((1 - alpha (t + tk) sa) * (- Y tk Ck t sa +
                   Z tk
                     (fun (n : nat) (sa : {x : state M & act M x}) =>
                        bellmanQ' (Q (n + tk)) (pi (n + tk)) sa -
                        bellmanQbar γ (Q (n + tk)) sa) t sa)) +
                  alpha (t + tk) sa * 
                  (bellmanQbar γ (Q (t + tk)) sa - bellmanQbar γ Qstar sa) +
                  alpha (t + tk) sa *
                  (bellmanQ' (Q (t + tk)) (pi (t + tk)) sa - 
                   bellmanQbar γ (Q (t + tk)) sa)).
       + apply Rplus_ge_compat; try lra.
         apply Rplus_ge_compat; try lra.
         apply Rmult_ge_compat_l with (r := 1 - alpha (t + tk) sa) in IHt; trivial.
         specialize (alim (t + tk)%nat sa).
         lra.
       + apply Rge_trans with
             (r2 := (1 - alpha (t + tk) sa) *
                    (-Y tk Ck t sa +
                     Z tk
                       (fun (n : nat) (sa0 : {x : state M & act M x}) =>
                          bellmanQ' (Q (n + tk)) (pi (n + tk)) sa0 - 
                          bellmanQbar γ (Q (n + tk)) sa0)
                       t sa) +
                    alpha (t + tk) sa * (- (γ * Ck)) +
                    alpha (t + tk) sa *
                    (bellmanQ' (Q (t + tk)) (pi (t + tk)) sa - 
                     bellmanQbar γ (Q (t + tk)) sa)).
         * apply Rplus_ge_compat; try lra.
           apply Rplus_ge_compat; try lra.           
           assert ((bellmanQbar γ (Q (t + tk)) sa - bellmanQbar γ Qstar sa) >=
                   -(γ * Ck)).
           {
             generalize (bellmanQbar_contraction glim (Q (t + tk)) Qstar); intros.
             assert (Rabs (bellmanQbar γ (Q (t + tk)) sa - bellmanQbar γ Qstar sa) <= γ * Ck).
             {
               generalize (Rmax_norm_spec _ (Hierarchy.minus (bellmanQbar γ (Q (t + tk))) (bellmanQbar γ Qstar)) sa); intros.
               apply Rle_trans with
                   (r2 :=   Rmax_norm {x : state M & act M x}
                                      (Hierarchy.minus (bellmanQbar γ (Q (t + tk)))
                                                       (bellmanQbar γ Qstar))); trivial.
               eapply Rle_trans.
               - apply H0.
               - apply Rmult_le_compat_l; try lra.
                 apply Qbound.
             }
             apply Rcomplements.Rabs_le_between in H1; lra.
           }
           apply Rmult_ge_compat_l with (r := alpha (t + tk) sa) in H0; trivial.
           specialize (alim (t + tk)%nat sa).
           lra.
         * simpl.
           ring_simplify.
           apply Rplus_ge_compat; [|right; reflexivity].
           apply Rplus_ge_compat; [|right; reflexivity].
           apply ge_minus.
           ring_simplify.
           rewrite Rplus_comm.
           ring_simplify.
           apply ge_minus2.
           right.
           reflexivity.
   Qed.
           
   Lemma gamma_eps :
     0 <= γ < 1 ->
     γ + (1-γ)/2 < 1.
   Proof.
     lra.
   Qed.

End MDP.

           
Section stuff.

  Lemma list_sum_nzero (l : list R) :
    list_sum l = list_sum (remove Req_EM_T 0 l).
  Proof.
    induction l.
    - now simpl.
    - destruct (Req_EM_T a 0).
      + rewrite e.
        rewrite remove_cons.
        simpl.
        rewrite Rplus_0_l.
        apply IHl.
      + simpl.
        match_destr; try lra.
        simpl.
        f_equal.
        apply IHl.
   Qed.

   Lemma list_sum_perm_eq_nzero (l1 l2 : list R) :
    Permutation.Permutation (remove Req_EM_T 0 l1) (remove Req_EM_T 0 l2) ->
    list_sum l1 = list_sum l2.
   Proof.
     intros.
     rewrite list_sum_nzero.
     rewrite (list_sum_nzero l2).
     now apply list_sum_perm_eq.
   Qed.

  Context (M : MDP).
  Context (act_eqdec:forall s, EqDec (act M s) eq).
  
  Definition fun_space := forall s:M.(state), M.(act) s -> M.(state).

  Instance fun_space_finite : Finite fun_space.
  Proof.
    unfold fun_space.
    apply (@Finite_fun_dep M.(state) M.(st_eqdec)).
    - apply M.(fs).
    - intros.
      apply Finite_fun.
      + apply M.(fa).
      + apply M.(fs).
  Qed.

  (* uses functional extensionality *)
  Local Instance eqdec_finite_fun_ext {A B} {fin:Finite A} {decA:EqDec A eq} {decB:EqDec B eq}:
    EqDec (A -> B) eq.
  Proof.
    intros ??.
    destruct fin.
    cut ({forall a, In a elms -> x a = y a} + {~ (forall a, In a elms -> x a = y a)}).
    {
      intros [?|?].
      - left; apply functional_extensionality; intros a.
        auto.
      - right; intros eqq.
        red in eqq.
        subst.
        now apply n; intros.
    }         
    clear finite.
    induction elms.
    - left; simpl; tauto.
    - destruct (decB (x a) (y a)).
      + destruct IHelms.
        * left; simpl; intros a' [?|inn]; subst; auto.
        * right; intros HH; simpl in *; eauto.
      + right; intros HH; simpl in *.
        elim c; apply HH; eauto.
  Qed.

    (* uses functional extensionality *)
  Local Instance eqdec_finite_fun_dep_ext {A} {B:A->Type} {fin:Finite A} {decA:EqDec A eq} {decB:forall a, EqDec (B a) eq}:
    EqDec (forall a, B a) eq.
  Proof.
    intros ??.
    destruct fin.
    cut ({forall a, In a elms -> x a = y a} + {~ (forall a, In a elms -> x a = y a)}).
    {
      intros [?|?].
      - left; apply functional_extensionality_dep; intros a.
        auto.
      - right; intros eqq.
        red in eqq.
        subst.
        now apply n; intros.
    }         
    clear finite.
    induction elms.
    - left; simpl; tauto.
    - destruct (decB _ (x a) (y a)).
      + destruct IHelms.
        * left; simpl; intros a' [?|inn]; subst; auto.
        * right; intros HH; simpl in *; eauto.
      + right; intros HH; simpl in *.
        elim c; apply HH; eauto.
  Qed.

  Instance fun_space_eqdec : EqDec fun_space eq.
  Proof.
    unfold fun_space.
    apply @eqdec_finite_fun_dep_ext.
    - apply M.(fs).
    - apply M.(st_eqdec).
    - intros.
      apply @eqdec_finite_fun_ext.
      + apply M.(fa).
      + apply act_eqdec.
      + apply M.(st_eqdec).
  Qed.
  
  Context (f: forall (s:M.(state)), M.(act) s -> M.(state) -> nonnegreal)
          (fsum_one : forall (s:M.(state)) (a : M.(act) s),
              list_sum (map (fun s' => nonneg (f s a s')) 
                            (nodup M.(st_eqdec) (@elms _ M.(fs)))) = 1).

  Definition fun_space_pmf_pmf
             (sp:fun_space) : R
    :=
    fold_right Rmult 1
               (map
                  (fun s =>
                     fold_right Rmult 1
                                (map
                                   (fun a => nonneg (f s a (sp s a)))
                                   (nodup (act_eqdec s) (@elms _ (M.(fa) s))))
                  )
                  (nodup M.(st_eqdec) (@elms _ M.(fs)))).

  Lemma fold_right_Rmult_nneg acc l :
    0 <= acc ->
    Forall (fun x => 0 <= x) l ->
    0 <= fold_right Rmult acc l.
  Proof.
    revert acc.
    induction l; simpl; trivial; intros.
    invcs H0.
    apply Rmult_le_pos; auto.
  Qed.
  
  Lemma fun_space_pmf_nneg sp : 0 <= fun_space_pmf_pmf sp.
  Proof.
    apply fold_right_Rmult_nneg; [lra |].
    apply Forall_forall; intros.
    apply in_map_iff in H.
    destruct H as [? [??]]; subst.
    apply fold_right_Rmult_nneg; [lra |].
    apply Forall_forall; intros.
    apply in_map_iff in H.
    destruct H as [? [??]]; subst.
    apply cond_nonneg.
  Qed.

  Lemma fun_space_pmf_finite_sum_one :
    list_sum (map fun_space_pmf_pmf (nodup fun_space_eqdec (@elms _ fun_space_finite))) = 1.
    Admitted.

  Lemma fun_space_pmf_one : countable_sum fun_space_pmf_pmf 1.
  Proof.
  Admitted.
  
  Definition fun_space_pmf : prob_mass_fun fun_space
    := {|
      pmf_pmf := fun_space_pmf_pmf
    ; pmf_pmf_pos := fun_space_pmf_nneg
    ; pmf_pmf_one := fun_space_pmf_one
    |}.
      
  Instance fun_space_ps : ProbSpace (discrete_sa fun_space) := discrete_ps fun_space_pmf.

  Definition sa_space_pmf_pmf (sa : sigT M.(act)) : M.(state) -> R
    := let (s,a) := sa in f s a.

  Lemma sa_space_pmf_nneg sa s : 0 <= sa_space_pmf_pmf sa s.
  Proof.
    unfold sa_space_pmf_pmf.
    destruct sa.
    apply cond_nonneg.
  Qed.

(*
  Instance countable_state_m : Countable M.(state).
  Proof.
    apply finite_countable.
    - apply st_eqdec.
    - apply M.(fs).
  Qed.
*)

  Instance countable_finite_eqdec {A : Type} (fsA : Finite A) (eqdec: EqDec A eq) :
    Countable A.
  Proof.
    intros.
    now apply finite_countable.
  Qed.

  Lemma finite_countable_inv { A : Type} 
        (fsA : Finite A) (eqdec: EqDec A eq) :
    exists (n:nat), 
      forall m, (m>n)%nat ->
                (@countable_inv A _ m) = None.
  Proof.
    intros.
    exists (list_max (map countable_index (@elms _ fsA))).
    intros.
    unfold countable_inv.
    match_destr.
    destruct e.
    generalize (list_max_upper (map countable_index (@elms _ fsA))); intros.
    destruct (Forall_forall
                  (fun k : nat => (k <= list_max (map countable_index (@elms _ fsA)))%nat) (map countable_index (@elms _ fsA))).
    specialize (H1 H0 m).
    cut_to H1; try lia.
    apply in_map_iff.
    exists x.
    split; trivial.
    apply fsA.
  Qed.
                              
  Lemma finite_countable_inv_sum { A : Type} (g : A -> R)
    (fsA : Finite A) (eqdec: EqDec A eq) :
    exists (n : nat),
      countable_sum g (sum_f_R0' (fun k => 
                                    match countable_inv k with
                                    | Some a => g a
                                    | None => 0
                                    end) n) /\
      forall m, (m>=n)%nat ->
                (@countable_inv A _ m) = None.
      
  Proof.
    destruct (finite_countable_inv fsA eqdec).
    exists (S x).
    unfold countable_sum.
    generalize (infinite_sum'_split (S x) (fun k : nat => match countable_inv k with
                       | Some a => g a
                       | None => 0
                       end)
                (sum_f_R0'
       (fun k : nat => match countable_inv k with
                       | Some a => g a
                       | None => 0
                       end) (S x))); intros.
    split.
    - apply H0; clear H0.
      rewrite Rminus_eq_0.
      apply infinite_sum'_ext with (s1 := fun _ => 0).
      + intros.
        match_case.
        intros.
        specialize (H (x0 + S x)%nat).
        cut_to H; try lia.
        congruence.
      + apply infinite_sum'0.
    - intros.
      apply H.
      lia.
  Qed.

  Lemma sa_space_pmf_one (sa : sigT M.(act)) : 
    @countable_sum _ (countable_finite_eqdec _ M.(st_eqdec)) (sa_space_pmf_pmf sa) 1.
  Proof.
    destruct (finite_countable_inv_sum (sa_space_pmf_pmf sa) _ M.(st_eqdec)) as [? [? ?]].
    assert ((sum_f_R0'
               (fun k : nat =>
                  match (@countable_inv M.(state) (countable_finite_eqdec _ M.(st_eqdec)) k) with
                  | Some s' => sa_space_pmf_pmf sa s'
                  | None => 0
                  end) x) = 1).
    {
      unfold sa_space_pmf_pmf.
      destruct sa.
      specialize (fsum_one x0 a).
      rewrite sum_f_R0'_list_sum.
      rewrite <- fsum_one.
      generalize list_sum_perm_eq_nzero; intros.
      rewrite list_sum_perm_eq_nzero 
        with (l2 := (map (fun s' : state M => nonneg (f x0 a s')) (nodup M.(st_eqdec) elms))); trivial.
      admit.
    }
    now rewrite H1 in H.
  Admitted.

  Definition sa_space_pmf (sa : sigT M.(act)) : prob_mass_fun M.(state)
    := {|
      pmf_pmf := sa_space_pmf_pmf sa
    ; pmf_pmf_pos := sa_space_pmf_nneg sa
    ; pmf_pmf_one := sa_space_pmf_one sa
      |}.

  Instance sa_space_ps (sa : sigT M.(act)) : ProbSpace (discrete_sa M.(state)) := discrete_ps (sa_space_pmf sa).

End stuff.
