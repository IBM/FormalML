Require Import List.
Require Coquelicot.Coquelicot.
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
Require qlearn.
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

  Definition sa_reward (sa : sigT M.(act)) (s' : M.(state)) : R :=
    let (s, a) := sa in reward s a s'.

  Definition bellmanQ' : Rfct(sigT M.(act)) -> (sigT M.(act) -> M.(state)) -> Rfct(sigT M.(act))
  := fun W => fun pi sa => let s' := pi sa in
                  sa_reward sa s' + γ*Max_{act_list s'}(fun a => W (existT _ s' a)).

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
    (forall sa s', sa_reward sa s' <= max_reward) ->
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
               (alpha t sa)*(sa_reward sa (pi t sa) +
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
    (forall sa s', sa_reward sa s' >= min_reward) ->
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
               (alpha t sa)*(sa_reward sa (pi t sa) +
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
    (forall sa s', sa_reward sa s' <= max_reward) ->
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
    (forall sa s', sa_reward sa s' >= min_reward) ->
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
       (forall sa s', sa_reward sa s' <= max_reward) ->
       (forall sa s', sa_reward sa s' >= min_reward) ->
       (forall t sa, 0 <= alpha t sa < 1) ->
        exists (sigma : R),
        forall n sa,
          Rsqr ((bellmanQ' (Q n) (pi n) sa) -
                bellmanQbar γ (Q n) sa) <= Rsqr sigma.
   Proof.
     intros glim maxr minr alim.
     destruct (upper_bound glim maxr alim) as [Cmax ?].
     destruct (lower_bound glim minr alim) as [Cmin ?].
     assert (forall sa s', Rabs (sa_reward sa s') <= Rabs min_reward + Rabs max_reward).
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
         generalize (Rabs_triang  (sa_reward sa (pi n sa))
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
                unfold sa_reward in minr.
                intros.
                apply Rge_le.
                specialize (minr (existT _ x a) a0).
                apply minr.
             -- apply expt_value_bdd.
                unfold sa_reward in maxr.
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
  Definition sa_fun_space := sigT M.(act) -> M.(state).

  Instance fun_space_finite : Finite fun_space.
  Proof.
    apply (@Finite_fun_dep M.(state) M.(st_eqdec)).
    - apply M.(fs).
    - intros.
      apply Finite_fun.
      + apply M.(fa).
      + apply M.(fs).
  Qed.

  Instance sa_fun_space_finite : Finite sa_fun_space.
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
  
  Instance sa_fun_space_eqdec : EqDec sa_fun_space eq.
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

  Definition fsa (sa : sigT M.(act)) (s' : M.(state)) : nonnegreal := 
    let (s,a) := sa in f s a s'.
    
  Definition sa_fun_space_pmf_pmf (sp:sa_fun_space) : R :=
    fold_right Rmult 1 (map (fun sa => nonneg (fsa sa (sp sa)))
                            (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms)).

  Lemma sa_fun_space_pmf_equal (sp : fun_space) :
    fun_space_pmf_pmf sp = sa_fun_space_pmf_pmf  (fun (sa : sigT M.(act)) => sp (projT1 sa) (projT2 sa)).
  Proof.
    unfold fun_space_pmf_pmf, sa_fun_space_pmf_pmf.
    unfold fsa.
    Admitted.

  Lemma fsa_sum_one (sa : sigT M.(act)) :
    list_sum (map (fun s' => nonneg (fsa sa s')) 
                  (nodup M.(st_eqdec) (@elms _ M.(fs)))) = 1.
   Proof.
     unfold fsa.
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
  

  Lemma sa_fun_space_pmf_finite_sum_one :
    inhabited (sigT M.(act)) ->
    list_sum (map sa_fun_space_pmf_pmf 
                  (nodup sa_fun_space_eqdec elms)) = 1.
   Proof.
     generalize (fsa_sum_one); intros fsa_sum_one.
     unfold sa_fun_space_pmf_pmf.
     generalize (fun_finite_sum_one _ _ (sigT_eqdec  M.(st_eqdec) act_eqdec) (M.(st_eqdec)) _ _ fsa); intros.
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

    Lemma sa_fun_space_pmf_pmf_nonneg (sp:sa_fun_space) :
      0 <= sa_fun_space_pmf_pmf sp.
    Proof.
      apply fold_right_Rmult_nneg; [lra |].
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [? [??]]; subst.
      apply cond_nonneg.
    Qed.
      
    Lemma sa_fun_space_pmf_list_fst_sum_one (inh : inhabited (sigT M.(act))):
      list_fst_sum
        (map (fun fsa => (mknonnegreal _ (sa_fun_space_pmf_pmf_nonneg fsa), fsa))
             (nodup sa_fun_space_eqdec elms)) = 1.
    Proof.
      rewrite list_fst_sum_compat.
      unfold list_fst_sum'.
      generalize (sa_fun_space_pmf_finite_sum_one inh); intros.
      rewrite <- H.
      f_equal.
      rewrite pmf_prob.seqmap_map.
      rewrite map_map.
      apply map_ext.
      intros.
      now simpl.
   Qed.
    
  Definition sa_fun_space_Pmf (inh : inhabited (sigT M.(act))) : Pmf sa_fun_space :=
    mkPmf (map (fun fsa => (mknonnegreal _ (sa_fun_space_pmf_pmf_nonneg fsa), fsa))
                 (nodup sa_fun_space_eqdec elms))
          (sa_fun_space_pmf_list_fst_sum_one inh).

  Definition sa_space_pmf_pmf (sa : sigT M.(act)) : M.(state) -> R
    := let (s,a) := sa in f s a.

  Lemma sa_space_pmf_nneg sa s : 0 <= sa_space_pmf_pmf sa s.
  Proof.
    unfold sa_space_pmf_pmf.
    destruct sa.
    apply cond_nonneg.
  Qed.

  Lemma fun_space_pmf_one : countable_sum fun_space_pmf_pmf 1.
  Proof.
    destruct (finite_countable_inv_sum fun_space_pmf_pmf _ _) as [? [? ?]].
    unfold countable_sum.
    assert ((sum_f_R0'
               (fun k : nat =>
                  match (@countable_inv fun_space (finite_countable fun_space) k) with
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
                         (map (@countable_inv _ (finite_countable fun_space)) (seq 0 x))))
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
                         (map (@countable_inv _ (finite_countable fun_space)) (seq 0 x)))))
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
      ps_P (ProbSpace:=fun_space_ps) (exist _ _ (sa_discrete (fun (omega : fun_space) => (omega s a) = s'))) =
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

   Instance sa_space_ps (sa : sigT M.(act)) : ProbSpace (discrete_sa M.(state)) 
     := let (s,a) := sa in
        @finite_discrete_ps (M.(state)) _  (M.(st_eqdec))
                            (f s a) (fsum_one s a).
  

  Definition state_act_index (sa : sigT M.(act)) : nat :=
    (@finite_index _ (sigT_eqdec  M.(st_eqdec) act_eqdec) _ sa).

  Fixpoint ivector_map_length {T} {S1 S2} {l : list S1} {g : S1 -> S2} :
    (ivector T (length (map g l))) -> ivector T (length l) :=
    match l with
    | nil => fun v => v
    | x::ls => fun '(h,tl) => (h, ivector_map_length tl)
    end.

  Definition vec_sa_space_ps :=
    ivector_ps (ivector_map_length (ivector_from_list (map sa_space_ps (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms)))).

  Program Instance outer_frf_compose {A B C} (g1 : A -> B) (g2 : B -> C) (frf2 : FiniteRangeFunction g2) :
    FiniteRangeFunction (compose g2 g1)
    := { frf_vals := frf_vals }.
  Next Obligation.
    destruct frf2.
    now unfold compose.
  Qed.
  
  Lemma SimpleExpectation_proj_fst {A B} {dom1 : SigmaAlgebra A} {dom2 : SigmaAlgebra B} (ps1 : ProbSpace dom1) (ps2 : ProbSpace dom2)
        (g : A -> R) 
        (rv : RandomVariable dom1 borel_sa g)
        (frg : FiniteRangeFunction g) :

    SimpleExpectation (Prts := (product_ps ps1 ps2)) (compose g fst) = 
    SimpleExpectation g.
  Proof.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext.
    intros.
    f_equal.
    generalize (product_sa_product ps1 ps2 (preimage_singleton g a) Ω); intros HH.
    rewrite ps_all, Rmult_1_r in HH.
    rewrite <- HH.
    apply ps_proper.
    intros ?; simpl.
    destruct x; simpl.
    unfold pre_event_preimage, pre_event_singleton, compose, pre_Ω; simpl.
    tauto.
  Qed.

  Lemma SimpleExpectation_proj_snd {A B} {dom1 : SigmaAlgebra A} {dom2 : SigmaAlgebra B} (ps1 : ProbSpace dom1) (ps2 : ProbSpace dom2)
        (g : B -> R) 
        (rv : RandomVariable dom2 borel_sa g)
        (frg : FiniteRangeFunction g) :

    SimpleExpectation (Prts := (product_ps ps1 ps2)) (compose g snd) = 
    SimpleExpectation g.
  Proof.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext.
    intros.
    f_equal.
    generalize (product_sa_product ps1 ps2 Ω (preimage_singleton g a)); intros HH.
    rewrite ps_all, Rmult_1_l in HH.
    rewrite <- HH.
    apply ps_proper.
    intros ?; simpl.
    destruct x; simpl.
    unfold pre_event_preimage, pre_event_singleton, compose, pre_Ω; simpl.
    tauto.
  Qed.

   Program Instance outer_frf_vector_nth {n:nat} (i : nat) (pf : (i < n)%nat) {A B}  (g : A -> B) (frf2 : FiniteRangeFunction g) :
    FiniteRangeFunction (fun v => g (ivector_nth i pf v))
    := { frf_vals := frf_vals }.
  Next Obligation.
    destruct frf2.
    apply frf_vals_complete.
  Qed.

  Lemma ivector_nth_zip {T1 T2} {n} i pf (vec1 : ivector T1 n) (vec2 : ivector T2 n) :
    ivector_nth i pf (ivector_zip vec1 vec2) = (ivector_nth i pf vec1, ivector_nth i pf vec2).
  Proof.
    revert i pf vec1 vec2.
    induction n; intros; try lia.
    simpl.
    destruct vec1.
    destruct vec2.
    match_destr.
  Qed.

  Lemma ivector_nth_create {T} {n} (f0: forall i (pf:(i<n)%nat), T) j pf2:
    (forall i pf1 pf2, f0 i pf1 = f0 i pf2) ->
    ivector_nth j pf2 (ivector_create n f0) = f0 j pf2.
  Proof.
    intros.
    revert j pf2.
    induction n; intros; try lia.
    simpl.
    match_destr.
    rewrite IHn.
    - apply H.
    - intros.
      apply H.
  Qed.

  Lemma ivector_nth_const {A} {n} i pf (a : A) :
    ivector_nth i pf (ivector_const n a) = a.
  Proof.
    revert i pf.
    induction n; intros; try lia.
    simpl.
    match_destr.
  Qed.


  Lemma ivector_fold_left_const {n} c d : ivector_fold_left Rmult (ivector_create n (fun j _ => c)) d =
                                            c ^ n  * d.
  Proof.
    revert d.
    induction n; intros d; simpl; [lra |].
    rewrite IHn; lra.
  Qed.
  
  Lemma ivector_fold_left_ext {A B} {n} (g h:A->B->A) (v:ivector B n) c :
    (forall x y, g x y = h x y) ->
    ivector_fold_left g v c = ivector_fold_left h v c.
  Proof.
    revert c v.
    induction n; simpl; trivial; intros.
    destruct v.
    rewrite H.
    now apply IHn.
  Qed.    

  Lemma ivector_create_ext {A} n (g h:(forall i : nat, (i < n)%nat -> A)) :
    (forall x y, g x y = h x y) ->
    ivector_create n g = ivector_create n h.
  Proof.
    induction n; simpl; trivial; intros.
    f_equal; auto.
  Qed.

  Lemma ivector_fold_left_Rmult_allbut_create_ident {n} i c (pf:(i<n)%nat) :
    ivector_fold_left Rmult (ivector_create n (fun j _ => if i == j then c else 1)) 1 = c.
  Proof.
    revert i pf.
    induction n; intros; try lia; simpl.
    destruct i; simpl.
    - rewrite ivector_fold_left_const.
      rewrite pow1; lra.
    - rewrite Rmult_1_r.
      specialize (IHn i).
      cut_to IHn; [| lia].
      rewrite <- IHn at 1.
      f_equal.
      apply ivector_create_ext; intros.
      repeat match_destr; unfold equiv, complement in *; lia.
  Qed.

  Lemma ivector_fold_left_Rmult_allbut_ident {n} i pf (vec : ivector R n) :
    vec = ivector_create n (fun j _ => if i == j then (ivector_nth i pf vec) else 1) ->
    ivector_fold_left Rmult vec 1 = ivector_nth i pf vec.
  Proof.
    intros HH.
    rewrite HH at 1.
    now apply ivector_fold_left_Rmult_allbut_create_ident.
  Qed.    

  Lemma SimpleExpectation_proj_nth {T} {dom : SigmaAlgebra T} {n} i pf (g : T -> R) (vecps : ivector (ProbSpace dom) n) 
        (rvg : RandomVariable dom borel_sa g)
        (frg : FiniteRangeFunction g) 
        (rvnth: RandomVariable 
                  (ivector_sa (ivector_const n dom)) borel_sa
                  (fun tvec : ivector T n => g (ivector_nth i pf tvec))) :
    SimpleExpectation (Prts := (ivector_ps vecps)) (fun tvec => g (ivector_nth i pf tvec)) =
    SimpleExpectation (Prts := (ivector_nth i pf vecps)) (fun t => g t).
  Proof.
    unfold SimpleExpectation.
    f_equal.
    apply map_ext.
    intros.
    f_equal.
    generalize (ivector_sa_product vecps); intros.
    pose (ve := ivector_create n (fun j _ => if i == j then (preimage_singleton (fun t : T => g t) a) else  Ω)).
    specialize (H ve).
    rewrite (ivector_fold_left_Rmult_allbut_ident i pf) in H.
    - rewrite ivector_nth_map, ivector_nth_zip in H.
      unfold ve in H.
      rewrite ivector_nth_create in H; [|intros; match_destr].
      match_destr_in H; try congruence.
      rewrite <- H.
      apply ps_proper.
      intros ?; simpl.
      unfold preimage_singleton.
      unfold pre_event_preimage, pre_event_singleton; simpl.
      rewrite <- ivector_Forall2_nth_iff.
      split; intros.
      + rewrite ivector_nth_create; [|intros; match_destr].
        match_destr; simpl.
        * rewrite <- H0.
          f_equal.
          destruct e0.
          apply ivector_nth_prf_irrelevance.
        * now unfold pre_Ω.
      + specialize (H0 i pf).
        rewrite ivector_nth_create in H0; [| intros; match_destr].
        match_destr_in H0.
        congruence.
    - apply ivector_nth_eq.
      intros.
      rewrite ivector_nth_map, ivector_nth_zip, ivector_nth_create; [|intros; match_destr].
      match_destr.
      + rewrite ivector_nth_map, ivector_nth_zip.
        destruct e.
        f_equal; now apply ivector_nth_ext.
      + unfold ve.
        rewrite ivector_nth_create; [|intros; match_destr].
        match_destr; try congruence.
        apply ps_all.
   Qed.

  Lemma NonnegExpectation_proj_nth {A} {n} {dom : SigmaAlgebra A} i pf (vecps : ivector (ProbSpace dom) n) 
        (g : A -> R) 
        (rv : RandomVariable dom borel_sa g)
        (nng : NonnegativeFunction g) 
        (nnfstg : NonnegativeFunction (fun vec  => g (ivector_nth i pf vec))) :
    NonnegExpectation (Prts := (ivector_ps vecps)) (fun vec => g (ivector_nth i pf vec)) =
    NonnegExpectation (Prts := ivector_nth i pf vecps) g.
  Proof.
    symmetry.
    rewrite <- NonnegExpectation_simple_approx; trivial.
    generalize (simple_approx_lim_seq (fun a => Rbar.Finite (g a)) nng); intros approxlim.
    assert (prodlim:forall (vec : ivector A n),
               Lim_seq.is_lim_seq (fun m => simple_approx (fun (a : A) => Rbar.Finite (g a)) m (ivector_nth i pf vec)) (Rbar.Finite (g (ivector_nth i pf vec)))) by (intros; apply approxlim).
    assert (rvstg:RandomVariable (ivector_sa (ivector_const n dom)) borel_sa (fun vec : ivector A n => g (ivector_nth i pf vec))).
    {
      apply compose_rv; trivial.
      generalize (ivector_nth_rv (ivector_const n dom) i pf); intros.
      now rewrite ivector_nth_const in H.
    }
    generalize (monotone_convergence (Prts := (ivector_ps vecps))
                  (fun vec : ivector A n => g (ivector_nth i pf vec))
                  (fun m vec => simple_approx (fun (a : A) => Rbar.Finite (g a)) m (ivector_nth i pf vec)) rvstg nnfstg ); intros.
    assert (Xnrv:forall n0 : nat,
               RandomVariable (ivector_sa (ivector_const n dom)) borel_sa
         (fun vec : ivector A n => simple_approx (fun a : A => Rbar.Finite (g a)) n0 (ivector_nth i pf vec))).
    {
      intros.
      apply simple_approx_rv; trivial.
      typeclasses eauto.
    }
    assert (Xn_pos : forall n0 : nat,
               NonnegativeFunction
                  (fun vec : ivector A n => simple_approx (fun a : A => Rbar.Finite (g a)) n0 (ivector_nth i pf vec))).
    {
      intros.
      apply simple_approx_pofrf.
    }
    specialize (H Xnrv Xn_pos).
    rewrite <- H; trivial.
    - apply Lim_seq.Lim_seq_ext.
      intros.
      f_equal.
      erewrite <- simple_NonnegExpectation.
      erewrite <- simple_NonnegExpectation.
      f_equal.
      erewrite <-  SimpleExpectation_proj_nth.
      now unfold compose.
    - intros.
      generalize (simple_approx_le (fun a : A => Rbar.Finite (g a)) nng); intros.
      unfold rv_le, pointwise_relation.
      intros.
      apply H0.
    - intros.
      generalize (simple_approx_increasing (fun a : A => Rbar.Finite (g a)) nng); intros.
      unfold rv_le, pointwise_relation.
      intros.
      apply H0.
    - intros.
      erewrite <- simple_NonnegExpectation.
      unfold Rbar.is_finite.
      now simpl.
      Unshelve.
      + apply simple_approx_rv; trivial.
        typeclasses eauto.
      + apply simple_approx_frf.
      + apply simple_approx_frf.
   Qed.

  Lemma NonnegExpectation_proj_fst {A B} {dom1 : SigmaAlgebra A} {dom2 : SigmaAlgebra B} (ps1 : ProbSpace dom1) (ps2 : ProbSpace dom2)
        (g : A -> R) 
        (rv : RandomVariable dom1 borel_sa g)
        (nng : NonnegativeFunction g) 
        (nnfstg : NonnegativeFunction (fun tt  => g (fst tt))) :
    NonnegExpectation (Prts := (product_ps ps1 ps2)) (fun tt  => g (fst tt)) =
    NonnegExpectation g.
  Proof.
    symmetry.
    rewrite <- NonnegExpectation_simple_approx; trivial.
    generalize (simple_approx_lim_seq (fun a => Rbar.Finite (g a)) nng); intros approxlim.
    assert (prodlim:forall (ab : A * B),
               Lim_seq.is_lim_seq (fun n => simple_approx (fun (a : A) => Rbar.Finite (g a)) n (fst ab)) (Rbar.Finite (g (fst ab)))) by (intros; apply approxlim).
    assert (rvstg:RandomVariable (product_sa dom1 dom2) borel_sa (fun tt : A * B => g (fst tt))).
    {
      apply compose_rv; trivial.
      apply fst_rv.
    }
    generalize (monotone_convergence 
                  (fun tt : A * B => g (fst tt))
                  (fun n ab => simple_approx (fun (a : A) => Rbar.Finite (g a)) n (fst ab)) rvstg nnfstg ); intros.
    assert (Xnrv:forall n : nat,
               RandomVariable 
                 (product_sa dom1 dom2) borel_sa
                 (fun ab : A * B =>
                    simple_approx (fun a : A => Rbar.Finite (g a)) n (fst ab))).
    {
      intros.
      apply simple_approx_rv; trivial.
      typeclasses eauto.
    }
    assert (Xn_pos : forall n : nat,
                 NonnegativeFunction
                   (fun ab : A * B =>
                    simple_approx (fun a : A => Rbar.Finite (g a)) n (fst ab))).
    {
      intros.
      apply simple_approx_pofrf.
    }
    specialize (H Xnrv Xn_pos).
    rewrite <- H; trivial.
    - apply Lim_seq.Lim_seq_ext.
      intros.
      f_equal.
      erewrite <- simple_NonnegExpectation.
      erewrite <- simple_NonnegExpectation.
      f_equal.
      erewrite <-  SimpleExpectation_proj_fst.
      now unfold compose.
    - intros.
      generalize (simple_approx_le (fun a : A => Rbar.Finite (g a)) nng); intros.
      unfold rv_le, pointwise_relation.
      intros.
      apply H0.
    - intros.
      generalize (simple_approx_increasing (fun a : A => Rbar.Finite (g a)) nng); intros.
      unfold rv_le, pointwise_relation.
      intros.
      apply H0.
    - intros.
      erewrite <- simple_NonnegExpectation.
      unfold Rbar.is_finite.
      now simpl.
      Unshelve.
      + apply simple_approx_rv; trivial.
        typeclasses eauto.
      + apply simple_approx_frf.
      + apply simple_approx_frf.
   Qed.

  Lemma NonnegExpectation_proj_snd {A B} {dom1 : SigmaAlgebra A} {dom2 : SigmaAlgebra B} (ps1 : ProbSpace dom1) (ps2 : ProbSpace dom2)
        (g : B -> R) 
        (rv : RandomVariable dom2 borel_sa g)
        (nng : NonnegativeFunction g) 
        (nnsndg : NonnegativeFunction (fun tt  => g (snd tt))) :
    NonnegExpectation (Prts := (product_ps ps1 ps2)) (fun tt  => g (snd tt)) =
    NonnegExpectation g.
  Proof.
    symmetry.
    rewrite <- NonnegExpectation_simple_approx; trivial.
    generalize (simple_approx_lim_seq (fun a => Rbar.Finite (g a)) nng); intros approxlim.
    assert (prodlim:forall (ab : A * B),
               Lim_seq.is_lim_seq (fun n => simple_approx (fun (b : B) => Rbar.Finite (g b)) n (snd ab)) (Rbar.Finite (g (snd ab)))) by (intros; apply approxlim).
    assert (rvstg:RandomVariable (product_sa dom1 dom2) borel_sa (fun tt : A * B => g (snd tt))).
    {
      apply compose_rv; trivial.
      apply snd_rv.
    }
    generalize (monotone_convergence 
                  (fun tt : A * B => g (snd tt))
                  (fun n ab => simple_approx (fun (b : B) => Rbar.Finite (g b)) n (snd ab)) rvstg nnsndg ); intros.
    assert (Xnrv:forall n : nat,
               RandomVariable 
                 (product_sa dom1 dom2) borel_sa
                 (fun ab : A * B =>
                    simple_approx (fun b : B => Rbar.Finite (g b)) n (snd ab))).
    {
      intros.
      apply simple_approx_rv; trivial.
      typeclasses eauto.
    }
    assert (Xn_pos : forall n : nat,
                 NonnegativeFunction
                   (fun ab : A * B =>
                    simple_approx (fun b : B => Rbar.Finite (g b)) n (snd ab))).
    {
      intros.
      apply simple_approx_pofrf.
    }
    specialize (H Xnrv Xn_pos).
    rewrite <- H; trivial.
    - apply Lim_seq.Lim_seq_ext.
      intros.
      f_equal.
      erewrite <- simple_NonnegExpectation.
      erewrite <- simple_NonnegExpectation.
      f_equal.
      erewrite <- (SimpleExpectation_proj_snd ps1 ps2).
      now unfold compose.
    - intros.
      generalize (simple_approx_le (fun b : B => Rbar.Finite (g b)) nng); intros.
      unfold rv_le, pointwise_relation.
      intros.
      apply H0.
    - intros.
      generalize (simple_approx_increasing (fun b : B => Rbar.Finite (g b)) nng); intros.
      unfold rv_le, pointwise_relation.
      intros.
      apply H0.
    - intros.
      erewrite <- simple_NonnegExpectation.
      unfold Rbar.is_finite.
      now simpl.
      Unshelve.
      + apply simple_approx_rv; trivial.
        typeclasses eauto.
      + apply simple_approx_frf.
      + apply simple_approx_frf.
   Qed.

  Lemma Expectation_proj_fst {A B} {dom1 : SigmaAlgebra A} {dom2 : SigmaAlgebra B} (ps1 : ProbSpace dom1) (ps2 : ProbSpace dom2)
        (g : A -> R) 
        (rvg : RandomVariable dom1 borel_sa g) :
    Expectation (Prts := (product_ps ps1 ps2)) (fun tt  => g (fst tt)) =
    Expectation g.
  Proof.
    unfold Expectation.
    f_equal; (erewrite <- (NonnegExpectation_proj_fst ps1 ps2); [|typeclasses eauto]; now apply NonnegExpectation_ext).
  Qed.

  Lemma Expectation_proj_snd {A B} {dom1 : SigmaAlgebra A} {dom2 : SigmaAlgebra B} (ps1 : ProbSpace dom1) (ps2 : ProbSpace dom2)
        (g : B -> R) 
        (rvg : RandomVariable dom2 borel_sa g) :
    Expectation (Prts := (product_ps ps1 ps2)) (fun tt  => g (snd tt)) =
    Expectation g.
  Proof.
    unfold Expectation.
    f_equal; (erewrite <- (NonnegExpectation_proj_snd ps1 ps2); [|typeclasses eauto]; now apply NonnegExpectation_ext).
  Qed.

  Lemma Expectation_proj_nth {A} {n} {dom : SigmaAlgebra A} i pf (vecps : ivector (ProbSpace dom) n) 
        (g : A -> R) 
        (rv : RandomVariable dom borel_sa g) :
    Expectation (Prts := (ivector_ps vecps)) (fun vec => g (ivector_nth i pf vec)) =
    Expectation (Prts := ivector_nth i pf vecps) g.
  Proof.
    unfold Expectation.
    f_equal; (erewrite <- (NonnegExpectation_proj_nth i pf vecps); [|typeclasses eauto]; now apply NonnegExpectation_ext).
  Qed.
  
  Lemma ivector_nth_map_length_from_list {A B} (g : A -> B) (l : list A) i pf pf2:
    ivector_nth i pf2 (ivector_from_list (map g l)) =
    ivector_nth i pf (ivector_map_length (ivector_from_list (map g l))).
  Proof.
    revert i pf pf2.
    induction l; simpl; intros; [lia |].
    destruct i; simpl; trivial.
  Qed.

  Lemma ivector_nth_list_map' {A B} (a: A) (g : A -> B) (l : list A) i pf :
    nth_error l i = Some a ->
    g a = ivector_nth i pf
                       (ivector_map_length (ivector_from_list (map g l))).
  Proof.
    intros.
    assert (pf2 : (i < length (map g l))%nat).
    {
      now rewrite map_length.
    }
    rewrite <- ivector_nth_map_length_from_list with (pf3 := pf2).
    apply (map_nth_error g) in H.
    rewrite ivector_nth_from_list with (pf0 := pf2) in H.
    now inversion H.
  Qed.

  Lemma ivector_nth_list_map_sa {B} (sa: sigT M.(act)) (g : sigT M.(act) -> B) pf :
    g sa = ivector_nth (state_act_index sa) pf
                       (ivector_map_length (ivector_from_list (map g (nodup (sigT_eqdec M act_eqdec) elms)))).
  Proof.
    apply ivector_nth_list_map'.
    unfold state_act_index.
    apply finite_index_correct.
  Qed.

  Lemma Expectation_sa_proj_nth (sa: sigT M.(act)) (g : (sigT M.(act)) -> M.(state) -> R) 
      (rv : forall (sa: sigT M.(act)),
          RandomVariable (discrete_sa M.(state)) borel_sa (g sa)) :
  Expectation (Prts := vec_sa_space_ps) 
              (fun stvec => g sa (ivector_nth (state_act_index sa) 
                                              (finite_index_bound _ sa) stvec)) =
  Expectation (Prts := (sa_space_ps sa)) (g sa).
Proof.
  generalize (Expectation_proj_nth (state_act_index sa) (finite_index_bound _ sa)
                                   (ivector_map_length (ivector_from_list (map sa_space_ps (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms))))
                                   (g sa) ); intros.
  cut_to H; trivial.
  etransitivity; [etransitivity |]; [| apply H |].
  - now apply Expectation_ext.
  - rewrite <- ivector_nth_list_map_sa.
    now apply Expectation_ext.
  Qed.

  Lemma Expectation_finite_discrete_ps {A} {finA:Finite A} (decA : EqDec A eq) 
        (pmf:Pmf A)
        (g : A -> R) :
    Expectation (Prts := pmf_prob.ps_pmf pmf) g =
    Some (Rbar.Finite (list_sum (map (fun a => (g a)*(pmf_prob.pmf_PMF_fun pmf a)) 
                                     (nodup decA elms)))).
  Proof.
    generalize (pmf_prob.pmf_value_Expectation pmf g); intros.
    unfold expt_value in H.
    rewrite pmf_prob.seqmap_map in H.
    rewrite H.
    do 2 f_equal.
    apply list_sum_perm_eq.
    unfold pmf_prob.pmf_PMF_fun.
    Admitted.

  Lemma Expectation_discrete_ps {A} {countableA:Countable A} (PMF:prob_mass_fun A)
        (g : A -> R) :
    Expectation (Prts := discrete_ps PMF) g =
    Some (Lim_seq.Lim_seq (fun n =>
                       match countable_inv n with
                        | Some a => (g a)*(pmf_pmf PMF a)
                        | None => 0
                        end)).
  Proof.
    Admitted.

  Definition finite_fun_to_ivector {A B} (finA : Finite A) (decA : EqDec A eq) (g : A -> B) :=
    ivector_map g (ivector_from_list (nodup decA elms)).

  Definition ivector_to_finite_fun {A B} (finA : Finite A) (decA : EqDec A eq) (vec : ivector B (length (nodup decA elms))) : A -> B :=
    (fun (a : A) => ivector_nth (finite_index _ a) (finite_index_bound _ _ ) vec).

  Definition sa_fun_space_to_ivector (g : sa_fun_space) := finite_fun_to_ivector _ (sigT_eqdec M.(st_eqdec) act_eqdec) g.

  Definition ivector_to_sa_fun_space (vec : ivector M.(state) (length (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms))) : sa_fun_space :=
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

   Lemma find_index_aux_succ {A} (decA : EqDec A eq) (l : list A) (i n : nat) (x : A):
     find_index_aux l x n = Some i -> find_index_aux l x (S n) = Some (S i).
   Proof.
     revert i n x.
     induction l.
     -- simpl. intros; congruence.
     -- simpl. intros.
        match_destr; try congruence.
        apply IHl. assumption.
   Qed.

  Lemma find_index_correct_nodup {A} (decA : EqDec A eq)
        (l : list A) (i : nat) (x : A) :
    NoDup l ->
    nth_error l i = Some x ->
    Finite.find_index l x = Some i.
  Proof.
    revert i x.
    induction l.
    + intros. rewrite nth_error_nil in H0.
      invcs H0.
    + intros i x HN Hncons.
      rewrite NoDup_cons_iff in HN.
      destruct HN as [HN1 HN2].
      destruct i.
      -- simpl in Hncons.
         invcs Hncons. unfold Finite.find_index; simpl.
         match_destr; try congruence.
      -- simpl in Hncons. unfold Finite.find_index; simpl.
         match_destr; try congruence.
         ++ apply nth_error_In in Hncons.
            rewrite e in Hncons; congruence.
         ++ specialize (IHl i x HN2 Hncons).
            unfold Finite.find_index in IHl.
            now apply find_index_aux_succ.
 Qed.

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

  Instance finite_fun_vec_encoder {A B} (finA : Finite A) (decA :EqDec A eq):
    Isomorphism (A -> B) (ivector B (length (nodup decA elms)))
    := {
    iso_f := finite_fun_to_ivector finA decA;
    iso_b := ivector_to_finite_fun finA decA;
    iso_f_b := finite_fun_iso_f_b finA decA ;
    iso_b_f := finite_fun_iso_b_f finA decA }.

  Instance vec_finite_fun_encoder {A B} (finA : Finite A) (decA :EqDec A eq):
    Isomorphism  (ivector B (length (nodup decA elms))) (A -> B)
    := {
    iso_b := finite_fun_to_ivector finA decA;
    iso_f := ivector_to_finite_fun finA decA;
    iso_b_f := finite_fun_iso_f_b finA decA ;
    iso_f_b := finite_fun_iso_b_f finA decA }.

  Instance vec_finite_fun_encoder_alt :
    Isomorphism (ivector (M.(state)) (length (nodup (sigT_eqdec  M.(st_eqdec) act_eqdec) elms))) ((sigT (M.(act))) -> M.(state)).
  Proof.
    apply vec_finite_fun_encoder.
  Defined.

  Definition finite_fun_sa : SigmaAlgebra sa_fun_space :=
    (iso_sa
       (ivector_sa
          (ivector_const
             (length (nodup (sigT_eqdec M act_eqdec) elms))
             (discrete_sa (state M))))).

  Definition finite_fun_ps : ProbSpace finite_fun_sa := iso_ps vec_sa_space_ps vec_finite_fun_encoder_alt.
  
  Existing Instance finite_fun_ps.

End stuff.

Section converge.
Context {Ts : Type}
        {dom : SigmaAlgebra Ts}
        (prts : ProbSpace dom).


Lemma Dvoretzky_converge_Y (C : R) (Y : nat -> Ts -> R) (alpha : nat -> Ts -> R) 
      {F : nat -> SigmaAlgebra Ts} (isfilt : IsFiltration F) (filt_sub : forall n, sa_sub (F n) dom)
      {adaptY : IsAdapted borel_sa Y F} (adapt_alpha : IsAdapted borel_sa alpha F) 
      (alpha_pos:forall n x, 0 <= alpha n x) 
      (alpha_one:forall n x, 0 < 1 - alpha n x ) :
   almost prts (fun omega : Ts => Lim_seq.is_lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => alpha n omega)) 
                                                     Rbar.p_infty)  ->
  rv_eq (Y 0%nat) (const C) ->
  (forall n, rv_eq (Y (S n)) (rvplus (rvmult (rvminus (const 1) (alpha n)) (Y n)) (rvscale C (alpha n)))) ->
  almost _ (fun omega => Lim_seq.is_lim_seq (fun n => Y n omega) (Rbar.Finite C)).
Proof.
  intros alpha_inf Y0 Yrel.
  assert (forall (n:nat) (x:Ts), 0 <= (fun n x => 0) n x).
  {
    intros.
    lra.
  }
  generalize (Dvoretzky_DS_extended_alt (fun n => rvminus (Y n) (const C)) 
                                        (fun n => const 0) (fun n => rvmult (rvminus (const 1) (alpha n)) 
                                                                            (rvminus (Y n) (const C)))
                                        isfilt filt_sub H H alpha_pos (fun n => rvconst dom borel_sa 0)); intros.
  cut_to H0; trivial.
  - revert H0.
    apply almost_impl, all_almost.
    intros; unfold impl.
    intros.
    apply Lim_seq.is_lim_seq_ext with (u:= fun n => (rvminus (Y n) (const C) x) + C).
    + intros; rv_unfold; lra.
    + replace (Rbar.Finite C) with (Rbar.Finite (0 + C)).
      * apply Lim_seq.is_lim_seq_plus'; trivial.
        apply Lim_seq.is_lim_seq_const.
      * now rewrite Rplus_0_l.
  - intros ??.
    rv_unfold.
    rewrite Yrel.
    lra.
  - intros.
    apply all_almost; intros.
    rewrite ConditionalExpectation.Condexp_const.
    now unfold const.
  - intros.
    rv_unfold.
    rewrite Rplus_0_r.
    rewrite Rmax_right.
    + rewrite Rabs_mult.
      apply Rmult_le_compat_r.
      * apply Rabs_pos.
      * rewrite Rabs_pos_eq; try lra.
        specialize (alpha_one n omega); lra.
    + apply Rmult_le_pos.
      * specialize (alpha_one n omega); lra.
      * apply Rabs_pos.
  - apply Series.ex_series_ext with (a := const 0).
    + intros.
      erewrite FiniteExpectation_ext with (rv_X2 := const 0).
      * rewrite FiniteExpectation_const.
        now unfold const.
      * intro z.
        unfold rvsqr, const.
        unfold Rsqr.
        lra.
    + apply ex_series_const0.
  - apply all_almost; intros.
    apply Lim_seq.is_lim_seq_const.
  - apply all_almost; intros.
    apply ex_series_const0.
  Qed.

Lemma Dvoretzky_converge_Z  (Z BB: nat -> Ts -> R) (alpha : nat -> Ts -> R) 
      {F : nat -> SigmaAlgebra Ts} (isfilt : IsFiltration F) (filt_sub : forall n, sa_sub (F n) dom)
      {adaptZ : IsAdapted borel_sa Z F} (adapt_alpha : IsAdapted borel_sa alpha F) 
      {rvBB : forall n, RandomVariable dom borel_sa (BB n)}
      {rvalpha : forall n, RandomVariable dom borel_sa (alpha n)}      
      {svy1 : forall n : nat, IsFiniteExpectation prts (rvsqr (alpha n))}
      {svy2 : forall n : nat, IsFiniteExpectation prts (rvsqr (rvmult (alpha n) (BB n)))}
      (alpha_pos:forall n x, 0 <= alpha n x) 
      (alpha_one:forall n x, 0 < 1 - alpha n x ) :
   (forall n, Expectation (BB n) = Some (Rbar.Finite 0)) ->
   almost prts (fun omega : Ts => Lim_seq.is_lim_seq (@Hierarchy.sum_n Hierarchy.R_AbelianGroup (fun n : nat => alpha n omega)) 
                                                     Rbar.p_infty)  ->
   almost prts (fun omega => @Series.ex_series Hierarchy.R_AbsRing Hierarchy.R_NormedModule (fun n : nat => Rsqr (alpha n omega))) -> 
   (exists (sigma : R), forall n, rv_le (rvsqr (BB n)) (const (Rsqr sigma))) ->
  rv_eq (Z 0%nat) (const 0) ->
  (forall n, rv_eq (Z (S n)) (rvplus (rvmult (rvminus (const 1) (alpha n)) (Z n)) (rvmult (alpha n) (BB n)))) ->
  almost _ (fun omega => Lim_seq.is_lim_seq (fun n => Z n omega) (Rbar.Finite 0)).
Proof.
  intros expBB alpha_inf alpha_sqr sigma_BB Z0 Zrel.
  assert (forall (n:nat) (x:Ts), 0 <= (fun n x => 0) n x).
  {
    intros.
    lra.
  }
  assert (forall n, RandomVariable dom borel_sa (rvmult (alpha n) (BB n))).
  {
    intros.
    typeclasses eauto.
  }
  generalize (Dvoretzky_DS_extended_alt Z (fun n => rvmult (alpha n) (BB n)) 
                                        (fun n => rvmult (rvminus (const 1) (alpha n)) (Z n)) 
                                        isfilt filt_sub H H alpha_pos H0 Zrel); intros.
  apply H1.
  - intros.
    admit.
  - intros ??.
    rv_unfold.
    unfold Rabs, Rmax.
    match_destr; match_destr.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 <= (1 + -1 * alpha n omega)).
      {
        specialize (alpha_one n omega).
        lra.
      }
      apply Rge_le in r0.
      generalize (Rmult_le_pos _ _ H2 r0).
      lra.
    + match_destr; try lra.
    + match_destr_in n0; try lra.
      assert (0 < (1 + -1 * alpha n omega)).
      {
        specialize (alpha_one n omega).
        lra.
      }
      apply Rlt_gt in r0.
      generalize (Rmult_lt_gt_compat_neg_l _ _ _ r0 H2); intros.
      rewrite Rmult_0_r in H3.
      rewrite Rmult_comm in H3.
      lra.
  - destruct sigma_BB as [sigma ?].
    assert (forall n,
               FiniteExpectation prts (rvsqr (rvmult (alpha n) (BB n))) <= sigma^2 * FiniteExpectation prts (rvsqr (alpha n))).
    {
      intros.
      apply Rle_trans with (r2 := FiniteExpectation prts (rvscale (sigma^2) (rvsqr (alpha n)))).
      - apply FiniteExpectation_le.
        intro z.
        rv_unfold.
        rewrite Rsqr_mult.
        rewrite Rmult_comm.
        apply Rmult_le_compat_r.
        + apply Rle_0_sqr.
        + specialize (H2 n z).
          simpl in H2.
          eapply Rle_trans.
          apply H2.
          right.
          unfold Rsqr, pow.
          lra.
     - now rewrite FiniteExpectation_scale.
    }
    apply (@Series.ex_series_le Hierarchy.R_AbsRing Hierarchy.R_CompleteNormedModule ) with 
        (b := fun n => sigma^2 * FiniteExpectation prts (rvsqr (alpha n))).
    + intros.
      unfold Hierarchy.norm; simpl.
      unfold Hierarchy.abs; simpl.
      rewrite Rabs_right.
      * eapply Rle_trans.
        apply H3.
        unfold pow; lra.
      * apply Rle_ge, (FiniteExpectation_sq_nneg prts (rvmult (alpha n) (BB n)) (svy2 n)).
    + apply (@Series.ex_series_scal Hierarchy.R_AbsRing).
      admit.
  - apply all_almost; intros.
    apply Lim_seq.is_lim_seq_const.
  - apply all_almost; intros.
    apply ex_series_const0.
  - trivial.
 Admitted.

Lemma conv_as_prob_sup_delta_eps (f : nat->Ts->R) (eps : posreal)
      {rv: forall n, RandomVariable dom borel_sa (f n)} :
  almost prts (fun omega => Lim_seq.is_lim_seq (fun n => f n omega) (Rbar.Finite 0)) ->
  forall (delta : posreal),
  exists (NN:nat),
    forall N, (N >= NN)%nat ->
    ps_P (qlearn.event_Rbar_le (fun omega => Lim_seq.Sup_seq (fun n => Rbar.Finite (f (N + n)%nat omega))) (Rbar.Finite (eps))) >= 1 - delta.
  Proof.
    intros alm.
    generalize (qlearn.conv_as_prob_sup_1_alt f alm eps); intros.
    rewrite <- Lim_seq.is_lim_seq_spec in H.
    unfold Lim_seq.is_lim_seq' in H.
    specialize (H delta).
    unfold Hierarchy.eventually in H.
    destruct H.
    exists x.
    intros.
    specialize (H N).
    cut_to H; try lia.
    apply Rabs_def2 in H.
    lra.
  Qed.
    
Lemma conv_as_prob_inf_delta_eps (f : nat->Ts->R) (eps : posreal)
      {rv: forall n, RandomVariable dom borel_sa (f n)} :
  almost prts (fun omega => Lim_seq.is_lim_seq (fun n => f n omega) (Rbar.Finite 0)) ->
  forall (delta : posreal),
  exists (NN:nat),
    forall N, (N >= NN)%nat ->
    ps_P (qlearn.event_Rbar_ge (fun omega => Lim_seq.Inf_seq (fun n => Rbar.Finite (f (N + n)%nat omega))) (Rbar.Finite (-eps))) >= 1 - delta.
Proof.
  intros alm.
  generalize (qlearn.conv_as_prob_inf_1_alt f alm eps); intros.
  rewrite <- Lim_seq.is_lim_seq_spec in H.
  unfold Lim_seq.is_lim_seq' in H.
  specialize (H delta).
  unfold Hierarchy.eventually in H.
  destruct H.
  exists x.
  intros.
  specialize (H N).
  cut_to H; try lia.
  apply Rabs_def2 in H.
  lra.
 Qed.

Lemma conv_pair_as_prob_inf_delta_eps (f g : nat->Ts->R) (eps : posreal)
      {rvf: forall n, RandomVariable dom borel_sa (f n)} 
      {rvg: forall n, RandomVariable dom borel_sa (g n)} :  
  almost prts (fun omega => Lim_seq.is_lim_seq (fun n => f n omega) (Rbar.Finite 0)) ->
  almost prts (fun omega => Lim_seq.is_lim_seq (fun n => g n omega) (Rbar.Finite 0)) ->    
  forall (delta : posreal),
  exists (NN:nat),
    forall N, (N >= NN)%nat ->
    ps_P (event_inter
            (qlearn.event_Rbar_ge (fun omega => Lim_seq.Inf_seq (fun n => Rbar.Finite (g (N + n)%nat omega))) (Rbar.Finite (-eps)))
            (qlearn.event_Rbar_le (fun omega => Lim_seq.Sup_seq (fun n => Rbar.Finite (f (N + n)%nat omega))) (Rbar.Finite (eps)))) >= 1 - delta.
  Proof.
    intros limf limg delta.
    assert (0 < delta / 2).
    {
      generalize (cond_pos delta); intros.
      lra.
    }
    destruct (conv_as_prob_sup_delta_eps f eps limf (mkposreal _ H)).
    destruct (conv_as_prob_inf_delta_eps g eps limg (mkposreal _ H)).
    exists (max x x0).
    intros.
    eapply Rge_trans.
    apply qlearn.ps_inter_bound.
    specialize (H0 N).
    specialize (H1 N).
    cut_to H0; try lia.
    cut_to H1; try lia.
    simpl in H0.
    simpl in H1.
    lra.
  Qed.

 Lemma Sup_seq_minus_const (f : nat -> R) (c : R):
   Lim_seq.Sup_seq (fun n : nat => Rbar.Finite (f n - c)) =
   Rbar.Rbar_minus (Lim_seq.Sup_seq (fun n : nat => Rbar.Finite (f n))) (Rbar.Finite c).
 Proof.
   unfold Lim_seq.Sup_seq, proj1_sig.
   match_destr; match_destr.
   apply is_sub_seq_lub_R in i.
   apply is_sub_seq_lub_R in i0.   
   unfold Lub.is_lub_Rbar in *.
   unfold Lub.is_ub_Rbar in *.
   destruct i; destruct i0.
   apply Rbar.Rbar_le_antisym.
   - apply H0.
     intros.
     destruct x0; simpl; try tauto; destruct H3; specialize (H1 (x1 + c)); simpl in H1.
     + cut_to H1; try lra.
       exists x0.
       lra.
     + apply H1.
       exists x0.
       lra.
  - unfold Rbar.Rbar_minus.
    simpl.
    replace x with (Rbar.Rbar_plus (Rbar.Rbar_plus x (Rbar.Finite c)) (Rbar.Finite (- c))).
    + apply Rbar.Rbar_plus_le_compat; simpl; try lra.
      apply H2.
      intros.
      destruct x; simpl; try tauto; destruct H3; specialize (H (x1 - c)); simpl in H.
      * cut_to H; try lra.
        exists x.
        lra.
      * apply H.
        exists x.
        lra.
    + rewrite Rbar_plus_assoc.
      * simpl.
        replace (c + -c) with 0 by lra.
        now rewrite Rbar.Rbar_plus_0_r.
      * apply ex_Rbar_plus_Finite_r.
      * apply ex_Rbar_plus_Finite_r.
  Qed.

 Lemma Inf_seq_minus_const (f : nat -> R) (c : R):
   Lim_seq.Inf_seq (fun n : nat => Rbar.Finite (f n - c)) =
   Rbar.Rbar_minus (Lim_seq.Inf_seq (fun n : nat => Rbar.Finite (f n))) (Rbar.Finite c).
 Proof.
   unfold Lim_seq.Inf_seq, proj1_sig.
   match_destr; match_destr.
   apply Lim_seq.is_inf_seq_glb in i.
   apply Lim_seq.is_inf_seq_glb in i0.   
   unfold Lub.Rbar_is_glb in *.
   destruct i; destruct i0.
   unfold Lub.Rbar_is_lower_bound in *.
   apply Rbar.Rbar_le_antisym.
   - unfold Rbar.Rbar_minus.
     simpl.
     replace x with (Rbar.Rbar_plus (Rbar.Rbar_plus x (Rbar.Finite c)) (Rbar.Finite (- c))).
     + apply Rbar.Rbar_plus_le_compat; simpl; try lra.
       apply H2.
       intros.
       destruct H3.
       rewrite H3.
       destruct x; simpl; try tauto; specialize (H (Rbar.Finite (f x2 - c))); simpl in H.
         cut_to H; try lra.
         now exists x2.
       * apply H.
         now exists x2.
    + rewrite Rbar_plus_assoc.
      * simpl.
        replace (c + -c) with 0 by lra.
        now rewrite Rbar.Rbar_plus_0_r.
      * apply ex_Rbar_plus_Finite_r.
      * apply ex_Rbar_plus_Finite_r.
  - apply H0.
    intros.
    destruct H3.
    rewrite H3.
    destruct x0; simpl; try tauto; specialize (H1 (Rbar.Finite (f x2))); simpl in H1.
      cut_to H1; try lra.
      now exists x2.
    + apply H1.
      now exists x2.
  Qed.

Lemma conv_pair_as_prob_inf_delta_eps_lim (f g : nat->Ts->R) (eps : posreal) (flim glim : R)
      {rvf: forall n, RandomVariable dom borel_sa (f n)} 
      {rvg: forall n, RandomVariable dom borel_sa (g n)} :  
  almost prts (fun omega => Lim_seq.is_lim_seq (fun n => f n omega) (Rbar.Finite flim)) ->
  almost prts (fun omega => Lim_seq.is_lim_seq (fun n => g n omega) (Rbar.Finite glim)) ->    
  forall (delta : posreal),
  exists (NN:nat),
    forall N, (N >= NN)%nat ->
    ps_P (event_inter
            (qlearn.event_Rbar_ge (fun omega => Lim_seq.Inf_seq (fun n => Rbar.Finite (g (N + n)%nat omega))) (Rbar.Finite (glim-eps)))
            (qlearn.event_Rbar_le (fun omega => Lim_seq.Sup_seq (fun n => Rbar.Finite (f (N + n)%nat omega))) (Rbar.Finite (flim+eps)))) >= 1 - delta.
  Proof.
    intros limf limg delta.
    assert (0 < delta / 2).
    {
      generalize (cond_pos delta); intros.
      lra.
    }
    assert (limf0:almost prts (fun omega => Lim_seq.is_lim_seq (fun n => f n omega - flim) (Rbar.Finite 0))).
    {
      revert limf.
      apply almost_impl.
      apply all_almost.
      unfold impl.
      intros.
      replace (Rbar.Finite 0) with (Rbar.Finite (flim - flim)).
      - apply Lim_seq.is_lim_seq_minus'; trivial.
        apply Lim_seq.is_lim_seq_const.
      - f_equal.
        lra.
    }
    assert (limg0:almost prts (fun omega => Lim_seq.is_lim_seq (fun n => g n omega - glim) (Rbar.Finite 0))).    
    {
      revert limg.
      apply almost_impl.
      apply all_almost.
      unfold impl.
      intros.
      replace (Rbar.Finite 0) with (Rbar.Finite (glim - glim)).
      - apply Lim_seq.is_lim_seq_minus'; trivial.
        apply Lim_seq.is_lim_seq_const.
      - f_equal.
        lra.
    }
    assert (rvf0:forall n : nat, RandomVariable dom borel_sa ((fun (n0 : nat) (omega : Ts) => f n0 omega - flim) n)).
    {
      intros.
      assert (rv_eq
                (fun omega : Ts => f n omega - flim)
                (rvminus (f n) (const flim))).
      {
        intro x.
        rv_unfold.
        lra.
      }
      rewrite H0.
      typeclasses eauto.
    }
    assert (rvg0:forall n : nat, RandomVariable dom borel_sa ((fun (n0 : nat) (omega : Ts) => g n0 omega - glim) n)).
    {
      intros.
      assert (rv_eq
                (fun omega : Ts => g n omega - glim)
                (rvminus (g n) (const glim))).
      {
        intro x.
        rv_unfold.
        lra.
      }
      rewrite H0.
      typeclasses eauto.
    }
    destruct (conv_as_prob_sup_delta_eps _ eps limf0 (mkposreal _ H)).
    destruct (conv_as_prob_inf_delta_eps _ eps limg0 (mkposreal _ H)).
    exists (max x x0).
    intros.
    eapply Rge_trans.
    apply qlearn.ps_inter_bound.
    specialize (H0 N).
    specialize (H1 N).
    cut_to H0; try lia.
    cut_to H1; try lia.
    simpl in H0.
    simpl in H1.
    assert (event_equiv
               (qlearn.event_Rbar_le (fun omega : Ts => Lim_seq.Sup_seq (fun n : nat => Rbar.Finite (f (N + n)%nat omega - flim))) 
                                     (Rbar.Finite eps))
               (qlearn.event_Rbar_le (fun omega : Ts => Lim_seq.Sup_seq (fun n : nat => Rbar.Finite (f (N + n)%nat omega)))
                                     (Rbar.Finite (flim + eps)))).
    {
     intro z.
     simpl.
     rewrite Sup_seq_minus_const.
     destruct (Lim_seq.Sup_seq (fun n : nat => Rbar.Finite (f (N + n)%nat z))); simpl; try tauto.
     lra.
    }
    rewrite H3 in H0.
    assert (event_equiv
               (qlearn.event_Rbar_ge (fun omega : Ts => Lim_seq.Inf_seq (fun n : nat => Rbar.Finite (g (N + n)%nat omega - glim))) 
                                     (Rbar.Finite (-eps)))
               (qlearn.event_Rbar_ge (fun omega : Ts => Lim_seq.Inf_seq (fun n : nat => Rbar.Finite (g (N + n)%nat omega)))
                                     (Rbar.Finite (glim - eps)))).
    {
      intro z.
      simpl.
      rewrite Inf_seq_minus_const.
      destruct (Lim_seq.Inf_seq (fun n : nat => Rbar.Finite (g (N + n)%nat z))); simpl; try tauto.
      lra.
    }
    rewrite H4 in H1.
    lra.
  Qed.

  Lemma event_complement_Rbar_le (f : Ts -> Rbar.Rbar) (c : Rbar.Rbar) 
        {rv : RandomVariable dom Rbar_borel_sa f} :
    event_equiv
      (event_complement
         (qlearn.event_Rbar_le f c))
      (qlearn.event_Rbar_gt f c).
  Proof.
    intro x.
    simpl.
    unfold pre_event_complement.
    unfold Rbar_gt.
    split; intros.
    - now apply Rbar.Rbar_not_le_lt.
    - now apply Rbar.Rbar_lt_not_le.
  Qed.

   Lemma conv_prob_sup_1_as (f : nat -> Ts -> R)
        {rv : forall n, RandomVariable dom borel_sa (f n)} 
        {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Lim_seq.Sup_seq (fun m => Rbar.Finite (Rabs (f (n + m)%nat x))))}:
    (forall (eps:posreal),
        Lim_seq.is_lim_seq (fun n => ps_P (qlearn.event_Rbar_le (fun x => Lim_seq.Sup_seq (fun m => Rbar.Finite (Rabs (f (n + m)%nat x)))) (Rbar.Finite eps))) (Rbar.Finite 1)) ->
    almost prts (fun x => Lim_seq.is_lim_seq (fun n => f n x) (Rbar.Finite 0)).
  Proof.
    intros.
    apply qlearn.conv_prob_sup_0_as with (rv3 := rv2); trivial.
    intros.
    specialize (H eps).
    apply Lim_seq.is_lim_seq_ext with
        (u :=  (fun n : nat =>
         1- ps_P
           (qlearn.event_Rbar_le (fun x : Ts => Lim_seq.Sup_seq (fun m : nat => Rbar.Finite (Rabs (f (n + m)%nat x))))
              (Rbar.Finite eps)))).
    - intros.
      rewrite <- ps_complement.
      apply ps_proper.
      apply event_complement_Rbar_le.
    - replace (Rbar.Finite 0) with (Rbar.Finite (1 - 1)).
      + apply Lim_seq.is_lim_seq_minus'; trivial.
        apply Lim_seq.is_lim_seq_const.
      + f_equal.
        lra.
  Qed.

  (* theorem 16 *)
  Lemma box_log_lim_Delta_Eps (f : nat -> Ts -> R) (geps C0 : posreal) 
        {rv : forall n, RandomVariable dom borel_sa (f n)} 
        {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Lim_seq.Sup_seq (fun m => Rbar.Finite (Rabs (f (n + m)%nat x))))}:

    geps < 1 ->
    (forall (delta : posreal) (k : nat), 
        exists (NN : nat),
          forall N, (N >= NN)%nat ->
          ps_P (qlearn.event_Rbar_le (fun omega => Lim_seq.Sup_seq (fun n => Rbar.Finite (Rabs (f (N + n)%nat omega)))) (Rbar.Finite (C0 * geps ^ k))) >=
          1 - (INR k) * delta) ->
    forall (Eps Delta : posreal),
    Delta < 1 ->
    exists (NN : nat),
      forall N, (N >= NN)%nat ->
      ps_P (qlearn.event_Rbar_le (fun omega => Lim_seq.Sup_seq (fun n => Rbar.Finite (Rabs (f (N + n)%nat omega)))) (Rbar.Finite Eps)) >=
      1 - Delta.
  Proof.
    intros geps1 lim.
    intros.
    generalize (cond_pos C0); intros C0pos.
    generalize (cond_pos Eps); intros Epspos.
    generalize (cond_pos Delta); intros Deltapos.
    assert (gepslim: 0 < geps < 1).
    {
      split; trivial.
      apply cond_pos.
    }
    pose (kstar := ln (Eps / C0) / ln geps).
    destruct (Rgt_dec kstar 0).
    - pose (khat := Z.to_nat (up kstar)).
      assert (0 < Delta / INR khat).
      {
        apply Rdiv_lt_0_compat; trivial.
        subst khat.
        rewrite INR_up_pos; try lra.
        apply IZR_lt.
        generalize (up_pos _ r); intros.
        lia.
      }
      specialize (lim (mkposreal _ H0) khat).
      destruct lim.
      exists x.
      intros ? Nge.
      specialize (H1 N Nge).
      simpl in H1.
      field_simplify in H1.
      + eapply Rge_trans.
        shelve.
        replace (1 - Delta) with (- Delta + 1) by lra.
        apply H1.
        Unshelve.
        apply Rle_ge.
        apply ps_sub.
        intro z.
        simpl.
        intros.
        eapply Rbar.Rbar_le_trans.
        apply H2.
        simpl.
        subst khat.
        assert (0 < Eps / C0).
        {
          now apply Rdiv_lt_0_compat.
        }
        generalize (qlearn.up_pow_ln (mkposreal _ H3) geps geps1); intros.      
        simpl in H4.
        assert (Eps / C0 < 1).
        {
          subst kstar.
          assert (ln geps < 0).
          {
            apply ln_lt_0.
            split; lra.
          }
            
          generalize Rmult_lt_gt_compat_neg_l; intros.
          apply Rgt_lt in r.
          apply Rmult_lt_gt_compat_neg_l with (r := ln geps) in r; trivial.
          field_simplify in r; try lra.
          rewrite Rcomplements.ln_div in r; try lra.
          assert (ln Eps < ln C0) by lra.
          apply ln_lt_inv in H7; try lra.
          apply Rmult_lt_reg_r with (r := C0); trivial.
          field_simplify; trivial.
          apply Rgt_not_eq.
          lra.
        }
            
        specialize (H4 H5).
        apply Rmult_le_reg_l with (r := /C0).
        * now apply Rinv_0_lt_compat.
        * rewrite <- Rmult_assoc.
          assert (pos C0 <> 0).
          {
            now apply Rgt_not_eq.
          }
          subst kstar.
          field_simplify; try lra.
      + subst khat.
        rewrite INR_up_pos in H1; try lra.
        generalize (up_pos _ r); intros.        
        assert (0 < up kstar)%Z by lia.
        apply IZR_lt in H3.
        lra.
    -  specialize (lim Delta 0%nat).
       destruct lim.
       exists x.
       intros ? Nge.
       specialize (H0 N Nge).
       simpl in H0.
       replace (1 - 0 * Delta) with 1 in H0 by lra.
       apply Rge_trans with (r2 := 1); try lra.
       eapply Rge_trans.
       shelve.
       apply H0.
       Unshelve.
       apply Rle_ge.
       apply ps_sub.
       intro z.
       simpl.
       intros.
       eapply Rbar.Rbar_le_trans.
       apply H1.
       simpl.
       rewrite Rmult_1_r.
       subst kstar.
       assert (ln (Eps / C0)/ln geps <= 0) by lra.
       assert (ln (Eps / C0) >= 0).
       {
         assert (ln geps < 0).
         {
           now apply ln_lt_0.
         }
         unfold Rdiv at 1 in H2.
         assert (ln geps <= 0) by lra.
         generalize (Rmult_le_pos_from_neg _ _ H2 H4); intros.
         rewrite Rmult_assoc in H5.
         rewrite Rinv_l in H5; lra.
       }
       rewrite Rcomplements.ln_div in H3; try lra.
       assert (ln C0 <= ln Eps) by lra.
       destruct (Rlt_dec (ln C0) (ln Eps)).
       + apply ln_lt_inv in r; lra.
       + assert (ln C0 = ln Eps) by lra.
         apply ln_inv in H5; lra.
  Qed.
          
  (* Theorem 16 *)
  Lemma box_log_lim (f : nat -> Ts -> R) (geps C0 : posreal) 
        {rv : forall n, RandomVariable dom borel_sa (f n)} 
        {rv2 : forall n, RandomVariable dom Rbar_borel_sa (fun x => Lim_seq.Sup_seq (fun m => Rbar.Finite (Rabs (f (n + m)%nat x))))}:

    geps < 1 ->
    (forall (delta : posreal) (k : nat), 
        exists (NN : nat),
          forall N, (N >= NN)%nat ->
          ps_P (qlearn.event_Rbar_le (fun omega => Lim_seq.Sup_seq (fun n => Rbar.Finite (Rabs (f (N + n)%nat omega)))) (Rbar.Finite (C0 * geps ^ k))) >=
          1 - (INR k) * delta) ->
    almost prts (fun x => Lim_seq.is_lim_seq (fun n => f n x) (Rbar.Finite 0)).
  Proof.
    intros.
    apply conv_prob_sup_1_as with (rv2 := rv2); trivial.
    intros.
    apply Lim_seq.is_lim_seq_spec.
    unfold Lim_seq.is_lim_seq'.
    intros.
    unfold Hierarchy.eventually.
    generalize (box_log_lim_Delta_Eps f geps C0 H H0 eps); intros.
    destruct (Rlt_dec eps0 1).
    - generalize (cond_pos eps0); intros eps0pos.
      assert (0 < eps0/2) by lra.
      assert (eps0/2 < 1) by lra.
      specialize (H1 (mkposreal _ H2) H3).
      destruct H1.
      exists x.
      intros ? xlim.
      specialize (H1 n xlim).
      apply Rabs_def1.
      + apply Rle_lt_trans with (r2 := 0).
        * apply Rplus_le_reg_r with (r := 1).
          ring_simplify.
          apply ps_le1.
        * apply cond_pos.
      + simpl in H1.
        lra.
   - assert (0 < 1/2) by lra.
     assert (1/2 < 1) by lra.
     specialize (H1 (mkposreal _ H2) H3).
     destruct H1.
     exists x.
     intros ? xlim.
     specialize (H1 n0 xlim).
     apply Rabs_def1.
      + apply Rle_lt_trans with (r2 := 0).
        * apply Rplus_le_reg_r with (r := 1).
          ring_simplify.
          apply ps_le1.
        * apply cond_pos.
      + simpl in H1.
        lra.
  Qed.     

Lemma list_inter_prob_bound (l : list (event dom * nonnegreal)) :
  (forall ep, 
      In ep l ->
      ps_P (fst ep) >= snd ep) ->
  ps_P (list_inter (map fst l)) >= list_sum (map (fun x => nonneg (snd x)) l)
                                   - INR (length l) + 1.
 Proof.
   induction l; intros; simpl.
   - rewrite list_inter_nil.
     rewrite ps_all.
     lra.
   - cut_to IHl.
     + rewrite list_inter_cons.
       eapply Rge_trans.
       apply qlearn.ps_inter_bound.
       unfold Rminus.
       do 3 rewrite Rplus_assoc.
       apply Rplus_ge_compat.
       * apply H.
         simpl; tauto.
       * apply Rplus_ge_reg_l with (r := 1).
         ring_simplify.
         eapply Rge_trans.
         apply IHl.
         unfold Rminus.
         do 2 rewrite Rplus_assoc.
         apply Rplus_ge_compat_l.
         match_destr.
         -- simpl.
            lra.
         -- lra.
     + intros.
       apply H.
       now apply in_cons.
  Qed.

End converge.

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

