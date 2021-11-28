Require Import mdp fixed_point pmf_monad Finite ListAdd Reals.
Require Import Coq.Lists.List LibUtils.
Require Import micromega.Lra.
Require Import RealAdd LibUtilsListAdd EquivDec.

Import ListNotations.
Set Bullet Behavior "Strict Subproofs".



Section bellmanQbar.
Open Scope R_scope.
Context {M : MDP} (γ : R).
Context (σ : dec_rule M) (init : M.(state)) (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Definition act_expt_reward : forall s : M.(state), M.(act) s -> R :=
  (fun s a => expt_value (t s a) (reward s a)).

Definition Qvalue : forall s: M.(state), (M.(act) s) -> R :=
  fun s a => act_expt_reward s a + γ*expt_value (t s a) (ltv γ σ).

Lemma Qvalue_expt_value : forall s a,
    Qvalue s a = expt_value (t s a) (fun s' => reward s a s' + γ*(ltv γ σ s')).
Proof.
  intros; unfold Qvalue.
  unfold act_expt_reward.
  rewrite <-expt_value_const_mul.
  now rewrite expt_value_add.
Qed.

Lemma ltv_Qvalue : ltv γ σ init = Qvalue init (σ init).
Proof.
  now rewrite ltv_corec.
Qed.

Definition bellmanQbar : Rfct (sigT M.(act)) -> Rfct (sigT M.(act))
  := fun W => fun sa => let (s,a) := sa in
                  act_expt_reward s a +
                  γ*expt_value (t s a)(fun s' => Max_{act_list s'}(fun a => W (existT _ s' a) ) ).

Definition bellmanQbar_expt_value : forall s a W,
    bellmanQbar W (existT _ s a) =
    expt_value (t s a) (fun s' => reward s a s' + γ*(Max_{act_list s'}(fun a => W (existT _ s' a)))).
Proof.
  intros; unfold bellmanQbar.
  unfold act_expt_reward.
  rewrite <-expt_value_const_mul.
  now rewrite expt_value_add.
Qed.

Lemma Rabs_helper : forall a b c : R, Rabs ( (a + b) + -(a + c)) = Rabs (b - c).
Proof.
  intros.
  f_equal. lra.
Qed.

Theorem is_contraction_bellmanQbar :
  @is_contraction (Rfct_UniformSpace (sigT M.(act))) (Rfct_UniformSpace (sigT M.(act)))
                  bellmanQbar.
Proof.
  unfold is_contraction.
  destruct (Req_EM_T γ 0).
  ++ unfold bellmanQbar.
     exists (1/2). split; [lra |].
     unfold is_Lipschitz. split;trivial;[lra |].
     destruct (fs M) as [ls ?].
     intros f g r Hr Hfgr.
     rewrite e. unfold ball_x,ball_y in *.
     simpl in *. unfold Rmax_ball,Rmax_norm in *.
     destruct act_finite as [acts ?].
     rewrite Rmax_list_lt_iff; intros ;
       try (apply map_not_nil; apply not_nil_exists ;
            exists (existT _ (ne M) ((na M) (ne M))); auto).
     rewrite in_map_iff in H.
     destruct H.
     unfold minus,plus,opp in H.
     destruct x0 as [s a].
     simpl in H. destruct H as [H1 H2].
     do 2 rewrite Rmult_0_l in H1.
     subst.
     apply Rabs_def1 ; ring_simplify.
     replace (0) with ((1/2)*0) by lra.
     apply Rmult_lt_compat_l; trivial; lra.
     rewrite Ropp_mult_distr_l_reverse.
     eapply Ropp_lt_gt_0_contravar with (r := (1/2)*r).
     replace (0) with ((1/2)*0) by lra.
     apply Rmult_lt_compat_l; trivial; lra.
  ++ exists γ ; split.
  - now destruct hγ.
  - unfold is_Lipschitz.
    unfold ball_x,ball_y. simpl.
    destruct (fs M) as [ls Hls].
    split.
    -- now destruct hγ.
    -- intros f g r Hr Hx.
       repeat red in Hx |-.
       unfold Rmax_ball, Rmax_norm.
       destruct (act_finite M) as [la Hla].
       rewrite Rmax_list_lt_iff; intros; try(apply map_not_nil; apply not_nil_exists).
       rewrite in_map_iff in H.
       destruct H as [sa [Q HQ]]; subst.
       unfold minus, plus, opp. simpl.
       unfold bellmanQbar; destruct sa. rewrite Rabs_helper.
       rewrite <-Rmult_minus_distr_l.
       rewrite Rabs_mult.
       assert (Hrγ : Rabs γ = γ) by (apply Rabs_pos_eq; lra). rewrite Hrγ.
       apply Rmult_lt_compat_l; try (destruct hγ; lra).
       rewrite <-expt_value_sub.
       eapply Rle_lt_trans; eauto.
       unfold Rmax_norm.
       eapply Rle_trans. apply expt_value_Rabs_Rle.
       apply expt_value_bdd; intro s0.
       unfold act_list.
       destruct (M s0).
       eapply Rle_trans. apply Rmax_list_minus_le_abs.
       rewrite Rmax_list_le_iff; try (rewrite map_not_nil).
       intros r'.
       rewrite in_map_iff; intros.
       destruct H as [a0 [Ha0 Helms]].
       subst. apply Rmax_spec.
       rewrite in_map_iff.
       exists (existT _ s0 a0); now split.
       rewrite not_nil_exists.
       generalize (na _ s0); intros a0; now exists a0.
       generalize (ne M); intros s0.
       generalize (na M); intros a0.
       specialize (a0 s0). now exists (existT _ s0 a0).
Qed.

End bellmanQbar.

Section bellmanQ.
Open Scope R_scope.
Context {M : MDP} (γ : R).
Context (σ : dec_rule M) (init : M.(state)) (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.


Definition fun_inner_prod {A : Type} (f g : A -> R) (ls : list A) : R :=
  (list_sum (map (fun a => (f a)*(g a)) ls)).

Lemma fun_inner_prod_self {A : Type} (l : list A) (f : A -> R) :
  fun_inner_prod f f l = list_sum (map (fun a => Rsqr (f a)) l).
Proof.
  unfold fun_inner_prod.
  now apply list_sum_map_ext.
Qed.

Definition Rfct_inner {A : Type} (finA : Finite A) (f g : Rfct A) : R :=
  let (ls, _) := finA in fun_inner_prod f g ls.


Lemma Rfct_expt_inner {A B : Type} (finA : Finite A)
      (f : B -> Rfct A) (p : Pmf B):
  let (la, _) := finA in
  expt_value p (fun b => Rfct_inner _ (f b) (f b)) =
  list_sum (List.map (fun a => expt_value p (fun b => (f b a)*(f b a))) la).
Proof.
  unfold Rfct_inner.
  destruct finA.
  destruct p as [lp Hlp]. unfold expt_value.
  simpl. clear Hlp.
  revert lp.
  induction lp.
  + simpl. symmetry.
    apply list_sum_map_zero.
  + simpl. rewrite IHlp.
    rewrite list_sum_map_add.
    f_equal. rewrite Rmult_comm.
    unfold fun_inner_prod.
    rewrite <-list_sum_const_mul.
    f_equal. apply List.map_ext; intros.
    lra.
Qed.


Definition bellmanQ : Rfct(sigT M.(act)) -> M.(state) -> Rfct(sigT M.(act))
  := fun W => fun s' sa => let (s,a) := sa in
                  reward s a s' + γ*Max_{act_list s'}(fun a => W (existT _ s' a)).

(* Move this to somewhere nice.*)
Lemma expt_value_le_max {A : Type} (finA : Finite A) (p : Pmf A) (f : A -> R):
  let (la,_) := finA in
  expt_value p f <= Max_{la}(f).
Proof.
  destruct finA.
  apply expt_value_bdd.
  intros. apply Rmax_spec.
  rewrite List.in_map_iff.
  exists a. split; auto.
Qed.

Lemma Rmax_list_Rsqr_Rabs_1 {A : Type} (f : A -> R) (l : list A):
[] <> l -> Max_{l}(fun a => Rsqr (f a)) <= Max_{l}(fun a => Rsqr (Rabs (f a))).
Proof.
  intros Hn.
  apply Rmax_spec.
  rewrite in_map_iff.
  destruct (Rmax_list_map_exist (fun a => Rsqr (f a)) l Hn) as [a [Ha1 Ha2]].
  exists a.  rewrite <-Rsqr_abs.
  split; trivial.
Qed.

Lemma Rmax_list_Rsqr_Rabs_2 {A : Type} (f : A -> R) (l : list A):
  [] <> l -> Max_{l}(fun a => Rsqr (Rabs (f a))) <= Rsqr(Max_{l}(fun a => Rabs(f a))).
Proof.
  intros Hn.
  destruct (Rmax_list_map_exist (fun a => Rsqr (Rabs (f a))) l Hn) as [a [Ha1 Ha2]].
  rewrite <-Ha2.
  apply neg_pos_Rsqr_le; try (apply Rmax_spec ; rewrite in_map_iff ; exists a; split; trivial).
  replace (Rabs (f a)) with (- (- (Rabs (f a)))) by lra.
  apply Ropp_le_contravar.
  transitivity (Rabs (f a)) ; try (apply Rmax_spec ; rewrite in_map_iff ; exists a; split; trivial).
  rewrite Rminus_le_0.
  ring_simplify.
  apply Rmult_le_pos; try (left; apply Rlt_0_2).
  apply Rabs_pos.
Qed.

Lemma Rmax_list_Rsqr_Rabs_3 {A : Type} (f g : A -> R) (l : list A):
  [] <> l -> (Max_{l}(fun a => Rabs (f a + g a)))² <=
           (Max_{l}(fun a => Rabs(f a)) + Max_{l}(fun a => Rabs (g a)))².
Proof.
  intros Hn.
  apply Rsqr_incr_1; try (apply Rmax_list_map_nonneg).
  + apply Rmax_list_map_triangle.
  + intros a.
    apply Rabs_pos.
  + replace 0 with (0+0) by lra.
    apply Rplus_le_compat; apply Rmax_list_map_nonneg; intros; apply Rabs_pos.
Qed.

Definition summand_bound W := fun (s : M.(state)) a => let (ls,_) := fs M in
                      (Max_{ ls}(fun a0 : state M => Rabs ((fun _ : state M => act_expt_reward s a) a0)) +
     (Max_{ ls} (fun a0 : state M => Rabs ((fun a1 : state M => γ * (Max_{ act_list a1}(fun a2 : act M a1 => W (existT (act M) a1 a2)))) a0))))².

(* Proves that each individual summand is bounded. *)
Lemma summand_bounded W :
  forall (s : M.(state)) (a: M.(act) s),
    let (ls,_) := fs M in
    variance (t s a) (fun s' => act_expt_reward s a + γ*Max_{act_list s'} (fun a => W (existT _ s' a)))
             <= summand_bound W s a.
Proof.
  intros s a.
  unfold summand_bound.
  generalize (expt_value_le_max (fs M) (t s a)); intros.
  destruct (fs M) as [ls ?].
  assert (Hls: [] <> ls) by (apply not_nil_exists; exists (ne M); trivial).
  eapply Rle_trans; try apply variance_le_expt_value_sqr.
  eapply Rle_trans; try eapply H.
  eapply Rle_trans; try (eapply (Rmax_list_Rsqr_Rabs_1) ; trivial).
  eapply Rle_trans; try (eapply (Rmax_list_Rsqr_Rabs_2) ; trivial).
  eapply Rle_trans; try (eapply (Rmax_list_Rsqr_Rabs_3) ; trivial).
  right; trivial.
Qed.

  Lemma Rmax_list_map_add {A} (f g : A -> R) (l : list A):
    Max_{ l}(fun a : A => (f a + g a)) <=
    Max_{ l}(fun a : A => (f a)) + (Max_{ l}(fun a : A => (g a))).
  Proof.
    destruct (is_nil_dec l).
    - subst; simpl. lra.
    - rewrite Rmax_list_le_iff.
      intros x Hx. rewrite in_map_iff in Hx.
      destruct Hx as [a [Ha Hina]].
      rewrite <-Ha.
      apply Rplus_le_compat; try (apply Rmax_spec; rewrite in_map_iff; exists a; split ; trivial).
      rewrite map_not_nil.
      congruence.
  Qed.

  Lemma Rmax_list_map_indep {A} (l : list A) (c : R):
    Max_{l}(fun _ => c) = if is_nil_dec l then 0 else c.
  Proof.
    destruct (is_nil_dec l); try now subst.
    apply Rle_antisym.
    + rewrite Rmax_list_le_iff; try rewrite map_not_nil; try easy.
      intros x Hx. rewrite in_map_iff in Hx.
      destruct Hx as [x0 [Hx0 Hx0']].
      now subst. congruence.
    + apply Rmax_spec.
      rewrite in_map_iff.
      rewrite BasicUtils.ne_symm in n.
      rewrite not_nil_exists in n.
      destruct n as [x Hx].
      exists x; easy.
  Qed.


Lemma Rmax_list_const_add' {A}(l : list A) (f : A -> R) (d : R) :
    Rmax_list (List.map (fun x => f x + d) l) =
    if (is_nil_dec l) then 0 else ((Rmax_list (map f l)) + d).
Proof.
  destruct (is_nil_dec l); subst; try easy.
  induction l.
    - simpl; intuition reflexivity.
    - simpl in *.
      destruct l.
      + simpl ; reflexivity.
      + simpl in * ; rewrite IHl.
        now rewrite Rcomplements.Rplus_max_distr_r.
        rewrite BasicUtils.ne_symm. rewrite not_nil_exists.
        exists a0; simpl. now left.
  Qed.

Lemma Q_is_bounded W :
    let (ls, _) := fs M in
    let (las,_) := act_finite M in
    Max_{ls}(fun s' => Max_{las}(bellmanQ W s')) <= Max_{ ls}
  (fun s' : state M =>
   Max_{ las}(fun sa : {x : state M & act M x} => let (s, a) := sa in reward s a s')) + γ*Max_{las}(W).
Proof.
  destruct (fs M) as [states ?].
  destruct (act_finite M) as [stacts ?].
  unfold bellmanQ.
  assert (G1 : [] <> states) by (rewrite not_nil_exists; now exists (@ne M)).
  assert (H0 : [] <> stacts) by (rewrite not_nil_exists; now exists (existT _ (@ne M) (@na M (@ne M)))).
  assert (G2 : forall s : M.(state), [] <> act_list s) by (intros s; apply act_list_not_nil).
  assert (H1 : Max_{states} (fun s' =>
              Max_{stacts}(fun sa : {x : state M & act M x} => let (s,a):= sa in
                           reward s a s' + γ*(Max_{ act_list s' }(fun a => W(existT _ s' a))))) <=
               Max_{states} (fun s' => Max_{stacts}(fun sa : {x : state M & act M x} =>
                                                   let (s,a):= sa in reward s a s'))
              +  γ*( Max_{states}(fun s' => Max_{stacts}(fun sa => Max_{ act_list s' }(fun a => W(existT _ s' a)))))).
  {
    setoid_rewrite <-Rmax_list_map_const_mul; try lra.
    eapply Rle_trans.
    2: apply Rmax_list_map_add. simpl.
    apply Rmax_list_fun_le; intros s.
    setoid_rewrite Rmax_list_map_indep; trivial.
    destruct (is_nil_dec stacts); try subst. intuition.
    generalize  (γ *(Max_{ act_list s}
                         (fun a0 : act M s => W (existT (act M) s a0)))); intros.
    generalize (Rmax_list_map_add (fun sa : {x : state M & act M x} => let (s0, a) := sa in reward s0 a s) (fun _ => r) stacts); intros.
    rewrite (Rmax_list_map_indep) with (c := r) in H; trivial.
    match_destr_in H; simpl. intuition.
    eapply Rle_trans. 2: apply H.
    right. apply Rmax_list_map_ext.
    intros a.
    now destruct a.
  }
  eapply Rle_trans; eauto. clear H1.
  apply Rplus_le_compat.
  + now right.
  + apply Rmult_le_compat_l; try lra.
    setoid_rewrite Rmax_list_map_indep.
    match_destr; subst. intuition.
    apply Rmax_spec. rewrite in_map_iff.
    generalize (Rmax_list_map_exist (fun s' => Max_{ act_list s'}(fun a => W (existT _ s' a))) _ G1); intros.
    destruct H as [s0 [Hs0 Heq1]].
    generalize (Rmax_list_map_exist (fun a => W (existT _ s0 a)) _ (G2 s0)); intros.
    destruct H as [a [Ha1 Heq2]].
    exists (existT _ s0 a).
    rewrite <-Heq1. rewrite Heq2.
    split; trivial.
Qed.



End bellmanQ.
