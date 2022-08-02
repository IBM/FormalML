Require Import List.
Require Import mdp qvalues pmf_monad Finite EquivDec Permutation Morphisms.
Require Import Reals RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import RandomVariableL2 infprod Dvoretzky Expectation.
Require Import RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace DiscreteProbSpace ProductSpace.
Require Import DVector.
Require Import pmf_monad.
Require pmf_prob.
Require SetoidList.

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

  Context (M : MDP).
  Context (act_eqdec:forall s, EqDec (act M s) eq).
  
  Definition fun_space := forall s:M.(state), M.(act) s -> M.(state).
  Definition fun_space_sa := sigT M.(act) -> M.(state).

  Instance fun_space_finite : Finite fun_space.
  Proof.
    apply (@Finite_fun_dep M.(state) M.(st_eqdec)).
    - apply M.(fs).
    - intros.
      apply Finite_fun.
      + apply M.(fa).
      + apply M.(fs).
  Qed.

  Instance fun_space_sa_finite : Finite fun_space_sa.
  Proof.
    apply (@Finite_fun _ (sigT_eqdec  M.(st_eqdec) act_eqdec) _  _ _); intros.
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
  
  Instance fun_space_sa_eqdec : EqDec fun_space_sa eq.
  Proof.
    unfold fun_space.
    apply @eqdec_finite_fun_ext.
    - typeclasses eauto.
    - apply (sigT_eqdec  M.(st_eqdec) act_eqdec).
    - apply M.(st_eqdec).
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

  Definition f_sa (sa : sigT M.(act)) (s' : M.(state)) : nonnegreal := 
    let (s,a) := sa in f s a s'.
    
  Definition fun_space_sa_pmf_pmf (sp:fun_space_sa) : R :=
    fold_right Rmult 1 (map (fun sa => nonneg (f_sa sa (sp sa)))
                            (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms)).

  Lemma fun_space_sa_pmf_equal (sp : fun_space) :
    fun_space_pmf_pmf sp = fun_space_sa_pmf_pmf  (fun (sa : sigT M.(act)) => sp (projT1 sa) (projT2 sa)).
  Proof.
    unfold fun_space_pmf_pmf, fun_space_sa_pmf_pmf.
    unfold f_sa.
    Admitted.

  Lemma f_sa_sum_one (sa : sigT M.(act)) :
    list_sum (map (fun s' => nonneg (f_sa sa s')) 
                  (nodup M.(st_eqdec) (@elms _ M.(fs)))) = 1.
   Proof.
     unfold f_sa.
     destruct sa.
     apply fsum_one.
   Qed.


   Lemma nodup_singleton {A} dec (x:A) :
     nodup dec (x::nil) = x::nil.
   Proof.
     reflexivity.
   Qed.

   Definition holds_on {A B : Type} (R:B->B->Prop) (elmsA:list A) : (A -> B) -> (A -> B) -> Prop
     := fun f g => forall a, In a elmsA -> R (f a) (g a).

   Global Instance holds_on_refl {A B : Type} (R:B->B->Prop) (elmsA:list A) {refl:Reflexive R}:
     Reflexive (holds_on R elmsA).
   Proof.
     now intros ???.
   Qed.

   Global Instance holds_on_sym {A B : Type} (R:B->B->Prop) (elmsA:list A) {sym:Symmetric R}:
     Symmetric (holds_on R elmsA).
   Proof.
     intros ?????; eauto.
   Qed.

   Global Instance holds_on_trans {A B : Type} (R:B->B->Prop) (elmsA:list A) {sym:Transitive R}:
     Transitive (holds_on R elmsA).
   Proof.
     intros ???????; eauto.
   Qed.

   Global Instance holds_on_equiv {A B : Type} (R:B->B->Prop) (elmsA:list A) {eqR:Equivalence R}:
     Equivalence (holds_on R elmsA).
   Proof.
     constructor; typeclasses eauto.
   Qed.

   Global Instance holds_on_dec {A B : Type} {R:B->B->Prop} {eqR:Equivalence R} (dec:EqDec B R) (elmsA:list A) :
     EqDec (A->B) (holds_on R elmsA).
   Proof.
     intros ??; unfold equiv, complement, holds_on.
     induction elmsA; simpl.
     - left; tauto.
     - destruct (dec (x a) (y a)).
       + destruct IHelmsA.
         * left; firstorder congruence.
         * right; eauto.
       + right; intros HH.
         apply c.
         apply (HH a); eauto.
   Defined.

   Lemma InA_eq {A} a (l:list A) : SetoidList.InA eq a l <-> In a l.
   Proof.
     rewrite SetoidList.InA_alt.
     firstorder congruence.
   Qed.

   Section ndA.

     Context {A} {R:A->A->Prop} (decR : forall x y : A, {R x y} + {~ R x y}).

     Fixpoint nodupA (l:list A)
       := match l with
          | nil => nil
          | x :: xs => if existsb (fun y => if decR x y then true else false) xs then nodupA xs else x :: nodupA xs
          end.

     Lemma nodupA_In {x l} :
       In x (nodupA l) -> In x l.
     Proof.
       induction l; simpl; trivial.
       match_destr; simpl; firstorder.
     Qed.
     
     Lemma InA_nodupA {x l} {trans:Transitive R} :
       SetoidList.InA R x l -> SetoidList.InA R x (nodupA l).
     Proof.
       induction l; simpl; trivial; intros HH.
       invcs HH.
       - match_case.
         + intros HH.
           apply existsb_exists in HH.
           destruct HH as [? [??]].
           match_destr_in H1.
           apply IHl.
           apply SetoidList.InA_alt.
           eauto.
         + intros.
           now constructor.
       - match_destr; auto.
     Qed.

     Lemma NoDupA_nodupA l : SetoidList.NoDupA R (nodupA l).
     Proof.
       induction l; simpl; trivial.
       match_case.
       intros HH.
       constructor; trivial.
       rewrite existsb_not_forallb in HH.
       apply Bool.negb_false_iff in HH.
       destruct (forallb_forall (fun x : A => negb (if decR a x then true else false)) l) as [HH2 _].
       specialize (HH2 HH).
       intros inn.
       apply SetoidList.InA_altdef in inn.
       apply Exists_exists in inn.
       destruct inn as [?[??]].
       specialize (HH2 _ (nodupA_In H)).
       match_destr_in HH2; tauto.
     Qed.

   End ndA.

   Lemma NoDupA_holds_on_singleton {A B} {R:B->B->Prop} a fs:
     SetoidList.NoDupA (holds_on R (a::nil)) fs <->
     SetoidList.NoDupA R (map (fun sp : A -> B => sp a) fs).
   Proof.
     split; intros nd.
     - induction fs; simpl; trivial.
       invcs nd.
       constructor; trivial; auto 2.
       intros ?.
       apply SetoidList.InA_alt in H.
       destruct H as [? [??]].
       apply in_map_iff in H0.
       destruct H0 as [? [??]]; subst.
       apply H1.
       apply SetoidList.InA_alt.
       exists x0; split; trivial.
       intros ? [|]; [subst| tauto]; eauto.
     - induction fs; simpl; trivial.
       invcs nd.
       constructor; trivial; auto 2.
       intros ?.
       apply SetoidList.InA_alt in H.
       destruct H as [? [??]].
       apply H1.
       apply SetoidList.InA_alt.
       exists (x a).
       split.
       + apply H; simpl; eauto.
       + apply in_map_iff.
         eauto.
   Qed.

   
   Lemma NoDupA_eq {A} (l:list A) : SetoidList.NoDupA eq l <-> NoDup l.
   Proof.
     split; induction l; intros HH; try invcs HH; constructor; auto 2
     ; intros HH; apply InA_eq in HH; eauto.
   Qed.

   Global Instance InA_subr {A} : Proper (subrelation ==> eq ==> @incl A ==> impl) (@SetoidList.InA A).
   Proof.
     intros ??????????; subst.
     apply SetoidList.InA_alt in H2.
     apply SetoidList.InA_alt.
     destruct H2 as [? [??]].
     exists x0.
     eauto.
   Qed.

   Lemma NoDupA_perm' {A:Type} R {a b:list A} {sym:Symmetric R} : SetoidList.NoDupA R a -> Permutation a b -> SetoidList.NoDupA R b.
    Proof.
      intros nd p.
      revert nd.
      revert a b p.
      apply (Permutation_ind_bis (fun l l' => SetoidList.NoDupA R l -> SetoidList.NoDupA R l')); intuition.
      - invcs H1.
        constructor; auto.
        intros HH; apply H4.
        eapply InA_subr; try apply HH; try reflexivity.
        intros ?.
        apply Permutation_in.
        now symmetry.
      - invcs H1.
        invcs H5.
        specialize (H0 H6).
        constructor; [|constructor]; simpl in *; trivial.
        + intros HH.
          invcs HH.
          * apply H4.
            constructor.
            now symmetry.
          * apply H3; revert H2.
            eapply InA_subr; try apply HH; try reflexivity.
            intros ?.
            apply Permutation_in.
            now symmetry.
        + intros HH.
          apply H4.
          apply SetoidList.InA_cons_tl.
            eapply InA_subr; try apply HH; try reflexivity.
            intros ?.
            apply Permutation_in.
            now symmetry.
    Qed.
    
    Global Instance NoDupA_perm {A:Type} R {sym:Symmetric R}:
      Proper (@Permutation A ==> iff) (@SetoidList.NoDupA A R).
    Proof.
      Hint Resolve NoDupA_perm' Permutation_sym : fml.
      unfold Proper, respectful; intros; subst; intuition; eauto with fml.
    Qed.

   Global Instance NoDupA_subr {A} : Proper (subrelation --> eq ==> impl) (@SetoidList.NoDupA A).
   Proof.
     intros ???????; subst.
     induction y0; trivial.
     invcs H1.
     constructor; auto 2.
     intros HH; apply H3.
     revert HH.
     apply InA_subr; try reflexivity.
     apply H.
   Qed.

   Lemma NoDupA_NoDup {A} {R} {refl:Reflexive R} {l:list A} : SetoidList.NoDupA R l -> NoDup l.
   Proof.
     intros.
     apply NoDupA_eq.
     revert H.
     apply NoDupA_subr; trivial.
     intros ???; subst; reflexivity.
   Qed.

   Lemma InA_map {A B} (R:B->B->Prop) (g:A->B) a l :
     SetoidList.InA R (g a) (map g l) <->
       SetoidList.InA (fun x y : A => R (g x) (g y)) a l.
   Proof.
     split; intros HH
     ; apply SetoidList.InA_alt in HH
     ; apply SetoidList.InA_alt
     ; destruct HH as [? [??]].
     - apply in_map_iff in H0.
       destruct H0 as [?[??]]; subst.
       eauto.
     - exists (g x).
       split; trivial.
       now apply in_map.
   Qed.

   Lemma NoDupA_map {A B} (R:B->B->Prop) (g:A->B) l :
     SetoidList.NoDupA R (map g l) <-> SetoidList.NoDupA (fun x y => R (g x) (g y)) l.
   Proof.
     split; induction l; intros HH; invcs HH; constructor; auto 2.
     - now rewrite <- InA_map.
     - now rewrite <- InA_map in H1.
   Qed.

   Lemma NoDup_nodupA {A} {R} {refl:Reflexive R} (dec:forall x y : A, {R x y} + {~ R x y}) l :
     NoDup (nodupA dec l).
   Proof.
     generalize (NoDupA_nodupA dec l).
     apply NoDupA_NoDup.
   Qed.

   Lemma In_nodupA {A} {R}  (decR : forall x y : A, {R x y} + {~ R x y}) {x l} {preR:PreOrder R} :
     In x l -> SetoidList.InA R x (nodupA decR l).
   Proof.
     intros.
     apply InA_nodupA; [typeclasses eauto |].
     apply InA_eq in H.
     revert H.
     apply InA_subr; try reflexivity.
     apply eq_subrelation.
     typeclasses eauto.
   Qed.

   Lemma nodupA_sub {A : Type} {R1 R2 : A -> A -> Prop} (decR1 : forall x y : A, {R1 x y} + {~ R1 x y}) (decR2 : forall x y : A, {R2 x y} + {~ R2 x y})
         (subr: forall x y, R2 x y -> R1 x y)
         {l : list A} :
     sublist (nodupA decR1 l) (nodupA decR2 l).
   Proof.
     induction l; simpl; [reflexivity |].
     repeat match_case; intros ex1 ex2; try now constructor.
     apply existsb_ex in ex1.
     destruct ex1 as [?[??]].
     match_destr_in H0.
     rewrite existsb_not_forallb in ex2.
     apply Bool.negb_false_iff in ex2.
     destruct (forallb_forall (fun x : A => negb (if decR1 a x then true else false)) l) as [HH2 _].
     specialize (HH2 ex2 _ H).
     match_destr_in HH2.
     specialize (subr _ _ r).
     tauto.
   Qed.

   Lemma NoDupA_concat {A} (eqA:A->A->Prop) {equivA:Equivalence eqA} (l: list (list A)) :
     Forall (SetoidList.NoDupA (A:=A) eqA) l ->
     SetoidList.NoDupA (fun l1 l2 => Exists (fun x => Exists (eqA x) l2) l1) l ->
     SetoidList.NoDupA eqA (concat l).
   Proof.
     induction l; simpl; trivial.
     intros FF nd.
     invcs FF.
     invcs nd.
     cut_to IHl; trivial.
     apply SetoidList.NoDupA_app; trivial.
     intros.
     apply H3.
     apply SetoidList.InA_alt.
     apply SetoidList.InA_alt in H.
     apply SetoidList.InA_alt in H0.
     destruct H as [?[??]].
     destruct H0 as [?[??]].
     apply in_concat in H6.
     destruct H6 as [?[??]].
     exists x2.
     split; trivial.
     apply Exists_exists.
     exists x0; split; trivial.
     apply Exists_exists.
     exists x1; split; trivial.
     now rewrite <- H.
   Qed.

   Global Instance holds_on_proper {A B} :
     Proper (subrelation ==> @incl A --> subrelation) (@holds_on A B).
   Proof.
     intros ???????????.
     apply H.
     apply H1.
     now apply H0.
   Qed.

   Lemma nodupA_sup {A : Type} {R1 R2 : A -> A -> Prop} (decR1 : forall x y : A, {R1 x y} + {~ R1 x y}) (decR2 : forall x y : A, {R2 x y} + {~ R2 x y}) {pre1:PreOrder R1}
         (subr: forall x y, R2 x y -> R1 x y) x l :
     In x (nodupA decR2 l) ->
     Exists (fun y => R1 x y /\ (x = y \/ ~ R2 x y)) (nodupA decR1 l).
   Proof.
     induction l; simpl; [tauto |].
     repeat match_case; intros ex1 ex2 inn.
     - apply Exists_cons_tl; auto.
     - destruct inn; [subst | auto].
       apply existsb_exists in ex1.
       destruct ex1 as [?[??]].
       match_destr_in H0.
       apply Exists_exists.
       assert (SetoidList.InA R1 x0 (nodupA decR1 l)).
       {
         apply InA_nodupA; try typeclasses eauto.
         apply SetoidList.InA_alt.
         eauto.
         exists x0; split; trivial.
         reflexivity.
       }
       apply SetoidList.InA_alt in H1.
       destruct H1 as [?[??]].
       exists x1.
       split; trivial.
       split.
       + now rewrite r.
       + rewrite existsb_not_forallb in ex2.
         apply Bool.negb_false_iff in ex2.
         destruct (forallb_forall (fun xx : A => negb (if decR2 x xx then true else false)) l) as [HH2 _].
         apply nodupA_In in H2.
         specialize (HH2 ex2 _ H2).
         match_destr_in HH2.
         eauto.
     - destruct inn; [subst | auto].
       apply Exists_exists.
       exists x; simpl.
       split; [eauto |].
       split; [| eauto].
       reflexivity.
   Qed.
   
   Lemma nodupA_sup' {A : Type} {R1 R2 : A -> A -> Prop} (decR1 : forall x y : A, {R1 x y} + {~ R1 x y}) (decR2 : forall x y : A, {R2 x y} + {~ R2 x y}) {pre1:PreOrder R1}
         (subr: forall x y, R2 x y -> R1 x y) x l :
     In x (nodupA decR2 l) ->
     In x (nodupA decR1 l) \/
       Exists (fun y => R1 x y /\ ~ R2 x y) (nodupA decR1 l).
   Proof.
     intros inn.
     generalize (nodupA_sup decR1 decR2 subr _ _ inn); intros ina.
     apply Exists_exists in ina.
     destruct ina as [? [?[?[?|?]]]].
     - subst; eauto.
     - right.
       apply Exists_exists.
       eauto.
   Qed.        

   Lemma holds_on_dec_eq_sup {A B : Type} (dec : EqDec B eq) (l1 l2: list A) l :
     incl l2 l1 ->
     forall x, In x (nodupA (holds_on_dec dec l1) l) ->
          Exists (fun y => forall a, (In a l2 \/ ~ In a l1) -> x a = y a) (nodupA (holds_on_dec dec l2) l).
   Proof.
   Admitted.

   
   Lemma nodupA_holds_on_dec_eq_sup {A B : Type} (dec : EqDec B eq) (l1 l2: list A) l :
     incl l2 l1 ->
     forall x, In x (nodupA (holds_on_dec dec l1) l) ->
          Exists (fun y => forall a, (In a l2 \/ ~ In a l1) -> x a = y a) (nodupA (holds_on_dec dec l2) l).
   Proof.
     intros lincl x.
     induction l; simpl; [tauto |].
     repeat match_case; intros ex1 ex2 inn.
     - apply Exists_cons_tl; auto.
     - destruct inn; [subst | auto].
       apply existsb_exists in ex1.
       destruct ex1 as [?[??]].
       match_destr_in H0.
       apply Exists_exists.
       red in e.
       rewrite existsb_not_forallb in ex2.
       apply Bool.negb_false_iff in ex2.
       destruct (forallb_forall (fun x0 : A -> B => negb (if holds_on_dec dec l1 x x0 then true else false)) l) as [HH2 _].
       specialize (HH2 ex2).
       assert (SetoidList.InA (holds_on eq l2) x0 (nodupA (holds_on_dec dec l2) l)).
       {
         apply InA_nodupA; try typeclasses eauto.
         apply SetoidList.InA_alt.
         exists x0; split; trivial.
         reflexivity.
       }
       apply SetoidList.InA_alt in H1.
       destruct H1 as [?[??]].
       rewrite H1 in e.
       clear x0 H H1.
       exists x1.
       split; trivial.
       intros ? [?|?].
       + now apply e.
       + apply nodupA_In in H2.
         admit.
(*         specialize (HH2 ex2 _ H2).
         match_destr_in HH2.
         eauto. *)
     - destruct inn; [subst | auto].
       apply Exists_exists.
       exists x; simpl.
       split; [eauto |].
(*       split; [| eauto].
       reflexivity. *)
   Admitted.
   
   Lemma fun_finite_sum_one_aux {A B : Type}
         (decA : EqDec A eq)
         (decB : EqDec B eq)        
         (decAB : EqDec (A -> B) eq) 
         
         (elmsA:list A)
         (NoDup_elmsA : NoDup elmsA)
         (nnilA : elmsA <> nil)
         (finB:Finite B)
         (elmsAB: Finite (A -> B))
         (fab : A -> B -> R)
         (sumone:(forall (a : A),
                     list_sum (map (fab a) (nodup decB elms)) = 1)) :
        list_sum (map (fun sp =>
                         (fold_right Rmult 1 (map (fun a => fab a (sp a))
                                                  elmsA)))
                      ((nodupA (holds_on_dec decB elmsA) elms))) = 1.
  Proof.
    induction elmsA; [simpl; congruence | clear nnilA].
    destruct elmsA; [clear IHelmsA | cut_to IHelmsA; trivial]; intros.
    - simpl.
      rewrite <- (sumone a) at 1.
      apply list_sum_perm_eq.
      transitivity (map (fab a) (map (fun sp : A -> B => (sp a)) (nodupA (holds_on_dec decB (a :: nil)) elms))).
      {
        rewrite map_map. 
        apply refl_refl.
        apply map_ext; intros ?.
        lra.
      }
      apply Permutation_map.
      destruct finB; simpl.
      apply NoDup_Permutation'.
      + apply NoDupA_eq.
        apply NoDupA_map.
        eapply NoDupA_subr; [| reflexivity | apply NoDupA_nodupA].
        unfold equiv, flip; intros ???? inn.
        simpl in inn.
        destruct inn; [| tauto].
        congruence.
      + apply NoDup_nodup.
      + intros b; split; intros inn.
        * apply nodup_In.
          apply finite.
        * apply in_map_iff.
          destruct elmsAB; simpl.
          generalize (finite0 (fun _ => b)); intros inn2.
          apply (In_nodupA (holds_on_dec decB (a :: nil))) in inn2.
          apply SetoidList.InA_alt in inn2.
          destruct inn2 as [?[??]].
          red in H.
          exists x.
          split; trivial.
          symmetry; apply H; simpl; tauto.
    - revert IHelmsA.
      assert (HH:a0 :: elmsA <> nil) by congruence.
      revert HH.
      invcs NoDup_elmsA.
      invcs H2.
      revert H1.
      generalize (a0 :: elmsA); clear a0 elmsA H3 H4; intros elmsA anin elmsAnnil.
      intros IHelmsA.
      simpl.
      specialize (sumone a).
      
      assert (perm1:Permutation
                (nodupA (holds_on_dec decB (a :: elmsA)) elms)
                (concat (map
                           (fun b =>
                              map 
                                (fun f => fun x => if decA x a then b else f x)
                                (nodupA (holds_on_dec decB elmsA) elms)) (nodup decB elms)))).
      {
        apply NoDup_Permutation'.
        - apply NoDup_nodupA.
        - apply NoDupA_eq.
          apply NoDupA_concat; [typeclasses eauto |..].
          + apply Forall_map.
            apply Forall_forall; intros.
            apply NoDupA_eq.
            revert anin.
            clear; intros anin.
            induction elms; simpl; [constructor |].
            match_case.
            intros exf.
            rewrite existsb_not_forallb in exf.
            apply Bool.negb_false_iff in exf.
            rewrite forallb_forall in exf.
            simpl.
            constructor; trivial.
            intros inn.
            apply in_map_iff in inn.
            destruct inn as [? [??]]; subst.
            assert (inn2:In x0 l).
            {
              eapply nodupA_In; eauto.
            }
            specialize (exf _ inn2).
            match_destr_in exf.
            apply c.
            intros ??.
            cut ((fun x1 : A => if decA x1 a then x else x0 x1) a1 =
                   (fun x0 : A => if decA x0 a then x else a0 x0) a1)
            ; [| now rewrite H].
            simpl.
            intros HH.
            match_destr_in HH; [| eauto].
            red in e; subst.
            congruence.
          + apply NoDupA_map.
            eapply NoDupA_subr; [| reflexivity | apply NoDupA_eq; apply NoDup_nodup].
            intros ???.
            apply Exists_exists in H.
            destruct H as [?[??]].
            apply Exists_exists in H0.
            destruct H0 as [?[??]]; subst.
            apply in_map_iff in H.
            destruct H as [? [??]]; subst.
            apply in_map_iff in H0.
            destruct H0 as [? [??]]; subst.
            cut ( (fun x : A => if decA x a then y else x1 x) a =
                    (fun x1 : A => if decA x1 a then x else x0 x1) a)
            ; [| now rewrite H].
            simpl.
            match_destr; intuition.
        - intros x; split; intros inn.
          + apply in_concat.
            exists (map (fun (f0 : A -> B) (x1 : A) => if decA x1 a then (x a) else f0 x1)
                   (nodupA (holds_on_dec decB elmsA) elms)).
            split.
            * admit.
            * apply in_map_iff.
              generalize (nodupA_sup
                            (holds_on_dec decB elmsA)
                            (holds_on_dec decB (a :: elmsA)))
              ; intros HH.
              cut_to HH
              ; [| apply holds_on_proper; try reflexivity; intros ?; simpl; eauto].
              specialize (HH _ _ inn).
              apply Exists_exists in HH.
              destruct HH as [? [?[??]]].
              unfold equiv in *.
              
              exists x0.
              split; trivial.
              unfold equiv in *.
              apply functional_extensionality; intros.
              match_destr; [congruence |].
              destruct H1; [congruence |].
              unfold holds_on in *.
              assert (x a <> x0 a) by admit.
  Admitted.
(*              admit.
              
              
              intros ?[?|?].

              eexists; split.
              - apply in_map_iff.
                eexists; split.
                + reflexivity.
                + apply nodup_In.
                  shelve.
              - apply in_map_iff.
                destruct elmsAB; simpl.
                Set Printing All.
                
                
                eexists x.
                split.
                + apply functional_extensionality; intros.
                  match_destr; congruence.
                + revert inn.
                  apply sublist_incl_sub.
                  apply nodupA_sub.
                  apply holds_on_proper; try reflexivity.
                  intros ?; simpl.
                  unfold equiv; intros.
                  holds_on R l




            
            assert (inn2:SetoidList.InA (holds_on eq elmsA)
                                        x
                                        (nodupA (holds_on_dec decB (a :: elmsA)) elms)).
            {
              apply nodupA_In in inn.
              eapply InA_subr; try apply In_nodupA; try apply inn
              ; try typeclasses eauto; trivial.
              apply sublist_incl_sub.
              apply nodupA_sub.
              
              intros ??; unfold equiv, holds_on; simpl; eauto.
            } 
            apply SetoidList.InA_alt in inn2.
            destruct inn2 as [xx [??]].
            { eexists; split.
              - apply in_map_iff.
                eexists; split.
                + reflexivity.
                + apply nodup_In.
                  apply (finite (x a)).
              - apply in_map_iff.
                eexists x.
                split.
                + apply functional_extensionality; intros.
                  match_destr; congruence.
                + revert inn.
                  apply sublist_incl_sub.
                  apply nodupA_sub.
                  apply holds_on_proper; try reflexivity.
                  intros ?; simpl.
                  unfold equiv; intros.
                  holds_on R l
                  
            } 
            
            
      } 

      erewrite list_sum_perm_eq; [| apply Permutation_map; apply perm1].
      rewrite concat_map.
      repeat rewrite map_map.
      erewrite map_ext; [| intros; rewrite map_map; match_destr; [| congruence]; reflexivity].
      rewrite list_sum_map_concat.
      rewrite <- sumone.
      f_equal.
      rewrite map_map.
      apply map_ext.
      intros.
      rewrite <- map_map.
      rewrite list_sum_mult_const.
      replace (fab a a0) with ((fab a a0) * 1) at 2 by lra.
      f_equal.
      rewrite map_map.
      rewrite <- IHelmsA.
      f_equal.
      apply map_ext.
      intros.
      rewrite sumone.
      f_equal.
      apply map_ext_in.
      intros.
      assert (NoDup (a :: elmsA)) by admit.
      apply NoDup_cons_iff in H0.
      match_destr.
      now rewrite e in H.
    - congruence.
  Admitted.
  *)
   (*
   Lemma fun_finite_sum_one_aux {A B : Type}
         (decA : EqDec A eq)
         (decB : EqDec B eq)        
         (decAB : EqDec (A -> B) eq) 

         (elmsA:list A)
         (nnilA : elmsA <> nil)
         (finB:Finite B)
         (elmsAB: list (A -> B))

         (elmsABfin : forall (f:A->B), exists (g:A->B), In g elmsAB /\ holds_on eq elmsA f g)
         (elmsABnd : SetoidList.NoDupA (holds_on eq elmsA) elmsAB)
        (fab : A -> B -> R)
        (sumone:(forall (a : A),
                    list_sum (map (fab a) (nodup decB elms)) = 1)) :
    list_sum (map (fun sp =>
                     (fold_right Rmult 1 (map (fun a => fab a (sp a))
                                              elmsA)))
                  elmsAB) = 1.
  Proof.
    revert elmsAB elmsABfin elmsABnd.
    induction elmsA; [simpl; congruence | clear nnilA].
    destruct elmsA; [clear IHelmsA | cut_to IHelmsA; trivial]; intros.
    - simpl.
      rewrite <- (sumone a) at 1.
      apply list_sum_perm_eq.
      transitivity (map (fab a) (map (fun sp : A -> B => (sp a)) elmsAB)).
      {
        rewrite map_map. 
        apply refl_refl.
        apply map_ext; intros ?.
        lra.
      }
      apply Permutation_map.
      destruct finB; simpl.
      apply NoDup_Permutation'.
      + apply NoDupA_holds_on_singleton in elmsABnd.
        now apply NoDupA_eq in elmsABnd.
      + apply NoDup_nodup.
      + intros b; split; intros inn.
        * apply nodup_In.
          apply finite.
        * apply in_map_iff.
          destruct (elmsABfin (fun _ => b)) as [g [??]].
          exists g.
          split; trivial.
          symmetry; apply H0; simpl; eauto.
    - simpl in *.
*)      

  Lemma holds_on_finite {A B : Type} (R:B->B->Prop) {fin:Finite A} :
    forall x y, holds_on R elms x y <-> forall a, R (x a) (y a).
  Proof.
    destruct fin; unfold holds_on; simpl.
    firstorder.
   Qed.

  Lemma nodupA_holds_on_fin {A B : Type} {fin:Finite A}
        (decB : EqDec B eq)
        (decAB : EqDec (A -> B) eq) l:
    nodupA (holds_on_dec decB elms) l = nodup decAB l.
  Proof.
    induction l; simpl; trivial.
    repeat match_case; intros.
    - apply existsb_exists in H0.
      destruct H0 as [?[??]].
      match_destr_in H1.
      repeat red in e.
      cut (a = x); [congruence |].
      apply functional_extensionality; intros.
      apply e.
      apply finite.
    - rewrite existsb_not_forallb in H0.
      apply Bool.negb_false_iff in H0.
      rewrite forallb_forall in H0.
      specialize (H0 _ i).
      match_destr_in H0.
      elim c.
      reflexivity.
    - f_equal.
      auto.
  Qed.
      

  (* nodup dec l = nodupA eq l *)
  (* nodupA_ext *)

         
  Lemma fun_finite_sum_one {A B : Type} 
        (finA : Finite A)
        (finB : Finite B)         
        (decA : EqDec A eq)
        (decB : EqDec B eq)        
        (finAB : Finite (A -> B))
        (decAB : EqDec (A -> B) eq) 
        (fab : A -> B -> R)
    :
    inhabited A ->
    (forall (a : A),
        list_sum (map (fab a) (nodup decB elms)) = 1) ->
    list_sum (map (fun sp =>
                     (fold_right Rmult 1 (map (fun a => fab a (sp a))
                                              (nodup decA elms))))
                  (nodup decAB elms)) = 1.
  Proof.
    intros inhA sum1.
    generalize (fun_finite_sum_one_aux decA decB decAB (nodup decA elms)) ; intros.
    assert (nodup decA elms <> nil).
    {
      rewrite <- nodup_not_nil.
      destruct inhA.
      generalize (finite X); intros.
      destruct finA.
      unfold not; intros.
      rewrite H1 in H0.
      tauto.
    }
    cut_to H; trivial.
    - specialize (H finB finAB fab sum1).
      replace (nodup decAB elms) with
        (nodupA (holds_on_dec decB (nodup decA elms)) elms).
      apply H.
      apply (@nodupA_holds_on_fin A B (finite_nodup finA) decB decAB).
    - apply NoDup_nodup.
  Qed.
  
   Lemma fun_finite_sum_prob_aux {A B : Type}
         (decA : EqDec A eq)
         (decB : EqDec B eq)        
         (decAB : EqDec (A -> B) eq) 
         
         (elmsA:list A)
(*         (NoDup_elmsA : NoDup elmsA) *)
         (nnilA : elmsA <> nil)
         (finB:Finite B)
         (elmsAB: Finite (A -> B))
         (fab : A -> B -> R)
         (sumone:(forall (a : A),
                     list_sum (map (fab a) (nodup decB elms)) = 1)) :
     forall (aa : A) (bb : B),
       list_sum (map (fun sp =>
                        (fold_right Rmult 1 (map (fun a => fab a (sp a))
                                                 elmsA)))
                     (filter 
                        (fun ff => if (decB (ff aa) bb) then true else false)
                        (nodupA (holds_on_dec decB elmsA) elms))) = fab aa bb.
  Proof.
    induction elmsA; [simpl; congruence | clear nnilA].
    destruct elmsA; [clear IHelmsA | cut_to IHelmsA; trivial]; intros.
    - simpl.
      unfold nodupA, holds_on_dec; simpl.
(*      
      rewrite <- (sumone a) at 1.
      apply list_sum_perm_eq.
      transitivity (map (fab a) (map (fun sp : A -> B => (sp a)) (nodupA (holds_on_dec decB (a :: nil)) elms))).
      {
        rewrite map_map. 
        apply refl_refl.
        apply map_ext; intros ?.
        lra.
      }
      apply Permutation_map.
      destruct finB; simpl.
      apply NoDup_Permutation'.
      + apply NoDupA_eq.
        apply NoDupA_map.
        eapply NoDupA_subr; [| reflexivity | apply NoDupA_nodupA].
        unfold equiv, flip; intros ???? inn.
        simpl in inn.
        destruct inn; [| tauto].
        congruence.
      + apply NoDup_nodup.
      + intros b; split; intros inn.
        * apply nodup_In.
          apply finite.
        * apply in_map_iff.
          destruct elmsAB; simpl.
          generalize (finite0 (fun _ => b)); intros inn2.
          apply (In_nodupA (holds_on_dec decB (a :: nil))) in inn2.
          apply SetoidList.InA_alt in inn2.
          destruct inn2 as [?[??]].
          red in H.
          exists x.
          split; trivial.
          symmetry; apply H; simpl; tauto.
    - revert IHelmsA.
      assert (HH:a0 :: elmsA <> nil) by congruence.
      revert HH.
      generalize (a0 :: elmsA); clear a0 elmsA; intros elmsA elmsAnnil.
      intros IHelmsA.
      simpl.
      specialize (sumone a).
      
      assert (perm1:Permutation
                (nodupA (holds_on_dec decB (a :: elmsA)) elms)
                (concat (map
                           (fun b =>
                              map 
                                (fun f => fun x => if decA x a then b else f x)
                                (nodupA (holds_on_dec decB elmsA) elms)) (nodup decB elms)))).
      {
        admit.
      } 

      erewrite list_sum_perm_eq; [| apply Permutation_map; apply perm1].
      rewrite concat_map.
      repeat rewrite map_map.
      erewrite map_ext; [| intros; rewrite map_map; match_destr; [| congruence]; reflexivity].
      rewrite list_sum_map_concat.
      rewrite <- sumone.
      f_equal.
      rewrite map_map.
      apply map_ext.
      intros.
      rewrite <- map_map.
      rewrite list_sum_mult_const.
      replace (fab a a0) with ((fab a a0) * 1) at 2 by lra.
      f_equal.
      rewrite map_map.
      rewrite <- IHelmsA.
      f_equal.
      apply map_ext.
      intros.
      rewrite sumone.
      f_equal.
      apply map_ext_in.
      intros.
      assert (NoDup (a :: elmsA)) by admit.
      apply NoDup_cons_iff in H0.
      match_destr.
      now rewrite e in H.
    - congruence.
 *)
  Admitted.

  
  Lemma fun_finite_sum_prob {A B : Type} 
        (finA : Finite A)
        (finB : Finite B)         
        (decA : EqDec A eq)
        (decB : EqDec B eq)        
        (finAB : Finite (A -> B))
        (decAB : EqDec (A -> B) eq) 
        (fab : A -> B -> R) :
    inhabited A ->
    (forall (a : A),
        list_sum (map (fab a) (nodup decB elms)) = 1) ->
    forall (aa : A) (bb : B),
      list_sum (map (fun sp =>
                       (fold_right Rmult 1 (map (fun a => fab a (sp a))
                                                (nodup decA elms))))
                    (filter 
                       (fun ff => if (decB (ff aa) bb) then true else false)
                       (nodup decAB elms))) = fab aa bb.
   Proof.
     intros.
     
     Admitted.
  

  Lemma fun_space_sa_pmf_finite_sum_one :
    inhabited (sigT M.(act)) ->
    list_sum (map fun_space_sa_pmf_pmf 
                  (nodup fun_space_sa_eqdec elms)) = 1.
   Proof.
     generalize (f_sa_sum_one); intros fsa_sum_one.
     unfold fun_space_sa_pmf_pmf.
     generalize (fun_finite_sum_one _ _ (sigT_eqdec  M.(st_eqdec) act_eqdec) (M.(st_eqdec)) _ _ f_sa); intros.
     now apply H.
   Qed.
      
  Lemma fun_space_pmf_finite_sum_one :
    list_sum (map fun_space_pmf_pmf (nodup fun_space_eqdec elms)) = 1.
  Proof.
    unfold fun_space_pmf_pmf.
    Admitted.

  
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

    Lemma fun_space_sa_pmf_pmf_nonneg (sp:fun_space_sa) :
      0 <= fun_space_sa_pmf_pmf sp.
    Proof.
      apply fold_right_Rmult_nneg; [lra |].
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [? [??]]; subst.
      apply cond_nonneg.
    Qed.
      
    Lemma fun_space_sa_pmf_list_fst_sum_one (inh : inhabited (sigT M.(act))):
      list_fst_sum
        (map (fun fsa => (mknonnegreal _ (fun_space_sa_pmf_pmf_nonneg fsa), fsa))
             (nodup fun_space_sa_eqdec elms)) = 1.
    Proof.
      rewrite list_fst_sum_compat.
      unfold list_fst_sum'.
      generalize (fun_space_sa_pmf_finite_sum_one inh); intros.
      rewrite <- H.
      f_equal.
      rewrite pmf_prob.seqmap_map.
      rewrite map_map.
      apply map_ext.
      intros.
      now simpl.
   Qed.
    
  Definition fun_space_sa_Pmf (inh : inhabited (sigT M.(act))) : Pmf fun_space_sa :=
    mkPmf (map (fun fsa => (mknonnegreal _ (fun_space_sa_pmf_pmf_nonneg fsa), fsa))
                 (nodup fun_space_sa_eqdec elms))
          (fun_space_sa_pmf_list_fst_sum_one inh).

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


  Lemma perm_countable_inv_elms (x:nat) {A : Type} 
        (fsA : Finite A) (eqdec: EqDec A eq) :
    (forall m : nat, (m >= x)%nat -> (@countable_inv _ (countable_finite_eqdec _ eqdec) m) = None) ->
    Permutation 
      (filter (fun x => match x with | Some _ => true | None => false end)
              (map (@countable_inv _ (countable_finite_eqdec _ eqdec)) (seq 0 x)))
      (map Some (nodup eqdec elms)).
    Proof.
        intros.
        apply NoDup_Permutation'.
        - clear H.
          generalize 0%nat.
          induction x; simpl; [constructor |]; intros n.
          match_case; match_case; intros.
          constructor; trivial.
          intros inn.
          apply filter_In in inn.
          destruct inn as [inn _].
          apply in_map_iff in inn.
          destruct inn as [? [? inn]].
          apply in_seq in inn.
          apply countable_inv_sound in H.
          apply countable_inv_sound in H1.
          assert (n = x0) by congruence.
          subst.
          lia.
        - apply FinFun.Injective_map_NoDup.
          + red; congruence.
          + apply NoDup_nodup.
        - intros so; split; intros inn.
          + apply filter_In in inn.
            destruct inn as [??].
            destruct so; try discriminate.
            apply in_map.
            apply nodup_In.
            apply finite.
          + apply in_map_iff in inn.
            destruct inn as [s [? inn]]; subst.
            apply filter_In.
            split; trivial.
            apply in_map_iff.
            exists (@countable_index _ (countable_finite_eqdec _ eqdec) s).
            split.
            * apply countable_inv_index.
            * apply in_seq.
              split; try lia.
              simpl.
              destruct (Nat.lt_ge_cases (@countable_index _ (countable_finite_eqdec _ eqdec) s) x); trivial.
              specialize (H _ H0).
              rewrite countable_inv_index in H.
              discriminate.
     Qed.


  Lemma fun_space_pmf_one : countable_sum fun_space_pmf_pmf 1.
  Proof.
    destruct (finite_countable_inv_sum fun_space_pmf_pmf _ _) as [? [? ?]].
    unfold countable_sum.
    assert ((sum_f_R0'
               (fun k : nat =>
                  match (@countable_inv fun_space (countable_finite_eqdec _ fun_space_eqdec) k) with
                  | Some a => fun_space_pmf_pmf a
                  | None => 0
                  end) x) = 1).
    {
      generalize fun_space_pmf_finite_sum_one; intros.
      rewrite sum_f_R0'_list_sum.
      rewrite <- H1.
      rewrite list_sum_perm_eq_nzero
        with (l2 := (map fun_space_pmf_pmf (nodup fun_space_eqdec elms))); trivial.
      generalize (perm_countable_inv_elms x fun_space_finite fun_space_eqdec H0); intro perm1.
      assert (perm2:
               Permutation
                 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s => fun_space_pmf_pmf s
                         end)
                       (filter (fun x => match x with | Some _ => true | None => false end)
                         (map (@countable_inv _ (countable_finite_eqdec _ fun_space_eqdec)) (seq 0 x))))
                 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s => fun_space_pmf_pmf s
                         end)
                      (map Some (nodup fun_space_eqdec elms)))).
      {
        now apply Permutation_map.
      }
      assert (perm3:
               Permutation
                 (remove Req_EM_T 0
                 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s => fun_space_pmf_pmf s
                         end)
                       (filter (fun x => match x with | Some _ => true | None => false end)
                         (map (@countable_inv _ (countable_finite_eqdec _ fun_space_eqdec)) (seq 0 x)))))
                 (remove Req_EM_T 0 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s => fun_space_pmf_pmf s
                         end)
                      (map Some (nodup fun_space_eqdec elms))))).
      {
        now apply Permutation_remove.
      }

     rewrite map_map in perm3.
      rewrite <- perm3.
      apply refl_refl.
      generalize (seq 0 x); intros l.
      clear.
      induction l; simpl; trivial.
      match_option; simpl
      ; destruct (Req_EM_T _ _)
      ; trivial
      ; try lra.
      congruence.
     }
    now rewrite H1 in H.
  Qed.
  
  Definition fun_space_pmf : prob_mass_fun fun_space
    := {|
      pmf_pmf := fun_space_pmf_pmf
    ; pmf_pmf_pos := fun_space_pmf_nneg
    ; pmf_pmf_one := fun_space_pmf_one
    |}.

  Instance fun_space_ps : ProbSpace (discrete_sa fun_space) := discrete_ps fun_space_pmf.

  Lemma fun_space_s_a_s_prob :
    forall (s:M.(state)) (a : M.(act) s) (s' : M.(state)),
      ps_P (exist _ _ (sa_discrete (fun (omega : fun_space) => (omega s a) = s'))) =
      f s a s'.
   Proof.
     intros.
     unfold ps_P.
     unfold fun_space_ps.
     unfold fun_space_pmf; simpl.
     unfold ps_of_pmf; simpl.
     unfold pmf_parts; simpl.
     unfold fun_space_pmf_pmf.
     Admitted.
     
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
      rewrite list_sum_perm_eq_nzero
        with (l2 := (map (fun s' : state M => nonneg (f x0 a s')) (nodup M.(st_eqdec) elms))); trivial.
      generalize (perm_countable_inv_elms x M.(fs) M.(st_eqdec) H0); intro perm1.
      assert (perm2:
               Permutation
                 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s =>  nonneg (f x0 a s)
                         end)
                       (filter (fun x => match x with | Some _ => true | None => false end)
                         (map (@countable_inv _ (countable_finite_eqdec _ M.(st_eqdec))) (seq 0 x))))
                 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s => nonneg (f x0 a s)
                         end)
                      (map Some (nodup M.(st_eqdec) elms)))).
      {
        now apply Permutation_map.
      }

      assert (perm3:
               Permutation
                 (remove Req_EM_T 0
                 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s =>  nonneg (f x0 a s)
                         end)
                       (filter (fun x => match x with | Some _ => true | None => false end)
                         (map (@countable_inv _ (countable_finite_eqdec _ M.(st_eqdec))) (seq 0 x)))))
                 (remove Req_EM_T 0 (map (fun so =>
                         match so with
                         | None => 0
                         | Some s => nonneg (f x0 a s)
                         end)
                      (map Some (nodup M.(st_eqdec) elms))))).
      {
        now apply Permutation_remove.
      }
      rewrite map_map in perm3.
      rewrite <- perm3.
      apply refl_refl.
      generalize (seq 0 x); intros l.
      clear.
      induction l; simpl; trivial.
      match_option; simpl
      ; destruct (Req_EM_T _ _)
      ; trivial
      ; try lra.
      congruence.
    }
    now rewrite H1 in H.
  Qed.


  Definition sa_space_pmf (sa : sigT M.(act)) : prob_mass_fun M.(state)
    := {|
      pmf_pmf := sa_space_pmf_pmf sa
    ; pmf_pmf_pos := sa_space_pmf_nneg sa
    ; pmf_pmf_one := sa_space_pmf_one sa
      |}.

  Instance sa_space_ps (sa : sigT M.(act)) : ProbSpace (discrete_sa M.(state)) := discrete_ps (sa_space_pmf sa).

  Definition state_act_index (sa : sigT M.(act)) : nat :=
    (@finite_index _ (sigT_eqdec  M.(st_eqdec) act_eqdec) _ sa).
  
  Definition sa_fun_space_ps :=
    ivector_ps (ivector_from_list (map sa_space_ps (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms))).

  Definition finite_fun_to_ivector {A B} (finA : Finite A) (decA : EqDec A eq) (g : A -> B) :=
    ivector_map g (ivector_from_list (nodup decA elms)).

  Definition ivector_to_finite_fun {A B} (finA : Finite A) (decA : EqDec A eq) (vec : ivector B (length (nodup decA elms))) : A -> B :=
    (fun (a : A) => ivector_nth (finite_index _ a) (finite_index_bound _ _ ) vec).

  Definition fun_space_sa_to_ivector (g : fun_space_sa) := finite_fun_to_ivector _ (sigT_eqdec M.(st_eqdec) act_eqdec) g.

  Definition ivector_to_fun_space_sa (vec : ivector M.(state) (length (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms))) : fun_space_sa :=
    ivector_to_finite_fun _ _ vec.


  
  Lemma find_index_aux_S {A} (decA : EqDec A eq) (la : list A) (x: A) (n: nat) (x0 : nat):
    find_index_aux la x (S n) = Some (S x0) ->
    find_index_aux la x n = Some x0.
  Proof.
    revert n x0.
    induction la.
    + intros. discriminate H.
    + intros. simpl in H. match_destr_in H.
      -- simpl. match_destr.
         ++ now invcs H.
         ++ congruence.
      -- simpl. match_destr; try congruence.
         now apply IHla.
  Qed.

  Lemma find_index_aux_n {A} (decA : EqDec A eq) (x : A) (la : list A) :
    forall n1 n2, find_index_aux la x n1 = Some n2 ->
    (n2 >= n1)%nat.
  Proof.
    induction la.
    - simpl.
      discriminate.
    - intros.
      simpl in H.
      match_destr_in H.
      + invcs H.
        lia.
      + specialize (IHla (S n1) n2 H).
        lia.
   Qed.

  Lemma find_index_S {A} (decA : EqDec A eq) (la : list A) (a x: A):
    (exists x0,
        Finite.find_index (a :: la) x = Some (S x0)) ->
    In x la.
  Proof.
    induction la.
    - intros.
      destruct H.
      unfold Finite.find_index in H.
      simpl in H.
      match_destr_in H.
    - intros.
      destruct H.
      unfold Finite.find_index in *.
      simpl in *.
      match_destr_in H.
      destruct (decA a0 x); try tauto.
      match_destr_in H.
      + rewrite e in c0.
        congruence.
      + right.
        assert (S x0 >= 2)%nat.
        {
          now apply find_index_aux_n with (decA0 := decA) (la0 := la) (x1 := x).
        }
        apply IHla.
        exists (x0 - 1)%nat.
        apply find_index_aux_S in H.
        rewrite H.
        f_equal.
        lia.
   Qed.

  Lemma find_index_0 {A} (decA : EqDec A eq) (a x : A) (la : list A) :
    Finite.find_index (a :: la) x = Some 0%nat ->
    x = a.
  Proof.
    unfold Finite.find_index.
    simpl.
    match_destr.
    intros.
    apply find_index_aux_n in H.
    lia.
  Qed.

   Lemma find_index_S_x {A} (decA : EqDec A eq) (a x : A) (la : list A) (x0 x1 : nat) :
     Finite.find_index (a :: la) x = Some (S x0) ->
     Finite.find_index (la) x = Some x1 ->
     x0 = x1.
   Proof.
     intros.
     unfold Finite.find_index in *.
     simpl in H.
     match_destr_in H.
     apply find_index_aux_S in H.
     rewrite H in H0.
     now invcs H0.
   Qed.

  Lemma find_index_correct_nodup {A} (decA : EqDec A eq) 
        (l : list A) (i : nat) (x : A) :
    NoDup l ->
    nth_error l i = Some x ->
    Finite.find_index l x = Some i.
  Proof.
    Admitted.

  Lemma find_index_ivector_nth {A} (decA : EqDec A eq) 
        (l : list A) (i : nat) (pf : (i < length l)%nat):
    NoDup l ->
    Finite.find_index l
        (ivector_nth i pf (ivector_from_list l)) = 
      Some i.
   Proof.
     intro nodup.
     generalize (ivector_nth_from_list l i pf); intros.
     now apply find_index_correct_nodup.
   Qed.

  Lemma ivector_map_nth_finite {A B} (finA : Finite A) (decA : EqDec A eq) (vec : ivector B (length (nodup decA elms))) :
    ivector_map
      (fun a : A =>
         ivector_nth  (finite_index finA a)
                     (finite_index_bound finA a) vec) (ivector_from_list (nodup decA elms)) = vec.
  Proof.
    apply ivector_nth_eq; intros.
    rewrite ivector_nth_map.
    apply ivector_nth_ext'; try reflexivity.
    unfold finite_index.
    unfold proj1_sig.
    match_destr.
    simpl in e.
    rewrite find_index_ivector_nth in e.    
    now invcs e.
    apply NoDup_nodup.
  Qed.

  Lemma finite_fun_iso_f_b {A B} (finA : Finite A) (decA : EqDec A eq) :
    forall (vec : ivector B (length (nodup decA elms))), 
      finite_fun_to_ivector _ _ (ivector_to_finite_fun _ _ vec) = vec.
  Proof.
    intros.
    unfold ivector_to_finite_fun, finite_fun_to_ivector.
    now apply ivector_map_nth_finite.
  Qed.

  Lemma ivector_nth_finite_map_aux {A B} (la : list A) (decA : EqDec A eq) (g : A -> B) 
        (x : A) (inx : In x la) :
    NoDup la ->
    let find_ind := (@find_index_complete A decA la x inx) in
    ivector_nth (proj1_sig find_ind)
                (@find_index_bound A decA la x (proj1_sig find_ind) (proj2_sig find_ind))
                (ivector_map g (ivector_from_list la)) = g x.
   Proof.
     intros nodup inla.
     simpl.
     induction la.
     - tauto.
     - destruct la.
       + simpl.
         destruct inx; [| tauto].
         unfold proj1_sig.
         match_destr.
         simpl.
         match_destr.
         * now rewrite e.
         * unfold Finite.find_index in e0.
           unfold find_index_aux in e0.
           unfold equiv_dec in e0.
           generalize e0 as e0'.
           intros.
           case_eq (decA x a); intros.
           -- rewrite H in e0.
              invcs e0.
           -- rewrite H in e0.
              discriminate.
       + simpl.
         simpl in IHla.
         unfold proj1_sig.
         match_destr.
         simpl.
         match_destr.
         * apply find_index_0 in e.
           now rewrite e.
         * generalize e as e'; intros.
           generalize (find_index_S decA (a0 :: la) a x); intros.
           cut_to H.
           specialize (IHla H).
           cut_to IHla.
           -- unfold proj1_sig in IHla.
              match_destr_in IHla.
              generalize (find_index_S_x decA a x (a0 :: la) x0 x1 e' e0); intros.
              match_destr.
              ++ match_destr_in IHla.
              ++ match_destr_in IHla.
                 assert (x0 = x1) by lia.
                 rewrite <- IHla.
                 unfold proj2_sig.
                 subst.
                 apply ivector_nth_prf_irrelevance.
           -- now apply NoDup_cons_iff in nodup.
           -- exists x0.
              apply e.
        Qed.

  Lemma ivector_nth_finite_map {A B} (finA : Finite A) (decA : EqDec A eq) (g : A -> B) :
    forall (x : A),
      ivector_nth (finite_index finA x) (finite_index_bound finA x)
                  (ivector_map g (ivector_from_list (nodup decA elms))) = g x.
   Proof.
     intros.
     generalize (ivector_nth_finite_map_aux (nodup decA elms) decA g x); intros.
     assert (inx: In x (nodup decA elms)).
     {
       apply nodup_In.
       apply finite.
     }
     specialize (H inx).
     cut_to H; try apply NoDup_nodup.
     simpl in H.
     rewrite <- H.
     apply ivector_nth_ext'; trivial.
     unfold finite_index, proj1_sig.
     clear H.
     match_destr.
     match_destr.
     unfold finite_nodup in e.
     simpl in e.
     rewrite e0 in e.
     now invcs e.
   Qed.

  Lemma finite_fun_iso_b_f {A B} (finA : Finite A) (decA : EqDec A eq) :
    forall (g : A -> B),
      ivector_to_finite_fun _ _ (finite_fun_to_ivector _ _ g)  = g.
  Proof.
    intros.
    unfold ivector_to_finite_fun, finite_fun_to_ivector.
    apply functional_extensionality.
    intros.
    apply ivector_nth_finite_map.
  Qed.

End stuff.

Section FiniteDomain.
  
Context {Ts : Type}
        {fin : Finite Ts}
        {eqdec : EqDec Ts eq}
        (prts : ProbSpace (discrete_sa Ts)) .

Program Instance finite_frf (rv_X : Ts -> R) :
  FiniteRangeFunction rv_X := { frf_vals :=  map rv_X elms }.
Next Obligation.
  destruct fin.
  apply in_map.
  apply finite.
Qed.

Instance isfe_finite_domain 
        (rv_X : Ts -> R)
        {rv:RandomVariable (discrete_sa Ts) borel_sa rv_X}  :
     IsFiniteExpectation prts rv_X.
Proof.
  apply IsFiniteExpectation_simple; trivial.
  typeclasses eauto.
Qed.

Lemma discrete_finite_preimage
      (rv_X : Ts -> R)
      (frf : FiniteRangeFunction rv_X)
      {rv:RandomVariable (discrete_sa Ts) borel_sa rv_X}  :
  forall (v : R), 
    In v frf_vals ->
    ps_P (preimage_singleton rv_X v) =
    list_sum (map (fun a => ps_P (discrete_singleton a))
                  (filter (fun a => if Req_EM_T (rv_X a) v then true else false) (nodup eqdec elms))).
 Proof.
   Admitted.

Lemma Expectation_finite_domain 
      (rv_X : Ts -> R)
      {rv:RandomVariable (discrete_sa Ts) borel_sa rv_X}  :
    FiniteExpectation prts rv_X =
    list_sum (map (fun a => Rmult (rv_X a) (ps_P (discrete_singleton a)))
                  (nodup eqdec elms)).
Proof.
  generalize pmf_prob.pmf_value_FiniteExpectation; intros.
  unfold expt_value in H.
  rewrite FiniteExpectation_simple with (rvx_rv := rv) (frf := finite_frf rv_X).
  unfold SimpleExpectation.
  generalize (frf_vals_nodup_preimage_disj rv_X); intros.
  assert (Permutation (nodup Req_EM_T  (@frf_vals Ts R rv_X (finite_frf rv_X)))
                      (nodup Req_EM_T (map rv_X elms))).
  {
    apply NoDup_Permutation.
    - apply NoDup_nodup.
    - apply NoDup_nodup.
    - intros.
      do 2 rewrite nodup_In.
      destruct (finite_frf rv_X).
      destruct fin.
      split; intros.
      + apply in_map_iff.
        admit.        
      + admit.
   }
  induction (nodup Req_EM_T frf_vals).
  - admit.
  - 
Admitted.

End FiniteDomain.

