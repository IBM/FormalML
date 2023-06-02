Require Import mdp fixed_point pmf_monad FiniteType ListAdd Reals.
Require Import Coq.Lists.List LibUtils.
Require Import micromega.Lra. (*  qlearn. *)
Require Import micromega.Lia. (*  qlearn. *)
Require Import ClassicalDescription.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RealAdd LibUtilsListAdd EquivDec.
Require Import IndefiniteDescription ClassicalDescription.
Require Import utils.Utils.

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

Theorem isContraction_bellmanQbar_gamma (Hg : 0 < γ) :
  @is_Lipschitz (Rfct_NormedModule (sigT M.(act))) (Rfct_NormedModule (sigT M.(act)))
                                      bellmanQbar γ.
  Proof.
  unfold is_Lipschitz.
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

Lemma bellmanQbar_bellman_max_op_fixpt Q' :
  bellmanQbar Q' = Q' ->
  let V' := fun s => let (la,_) := fa M s in
                Max_{la}(fun a => Q' (existT _ s a)) in
  bellman_max_op γ V' = V'.
 Proof.
   unfold bellmanQbar, bellman_max_op; intros.
   apply functional_extensionality.
   intros.
   destruct (M x).
   apply Rmax_list_Proper.
   apply refl_refl.
   apply map_ext.
   intros.
   apply (f_equal (fun v => (v (existT _ x a)))) in H.
   rewrite <- H.
   do 2 f_equal.
   apply expt_value_Proper; trivial.
   intros ?.
   unfold act_list.
   now destruct (M a0).
 Qed.

Lemma bellmanQbar_bellman_max_op_fixpt' Q' :
  bellmanQbar Q' = Q' ->
  let V' := fun s => let (la,_) := fa M s in
                Max_{la}(fun a => Q' (existT _ s a)) in
  forall init,                
    fixpt (bellman_max_op γ) init = V'.
Proof.
  intros.
  generalize (is_contraction_bellman_max_op γ hγ (M := M)); intros.
  generalize (fixpt_is_unique H0 (fun x => True)); intros.
  cut_to H1; trivial.
  - specialize (H1 V').
    cut_to H1; trivial.
    specialize (H1 V').
    generalize (bellmanQbar_bellman_max_op_fixpt Q' H); intros.
    cut_to H1; trivial.
    rewrite H1.
    apply (fixpt_init_unique H0 (fun x => True)); trivial.
    apply closed_true.
   - apply closed_true.
 Qed.

 Theorem max_ltv_eq_fixpt' Q' :
   bellmanQbar Q' = Q' ->
   let V' := fun s => let (la,_) := fa M s in
                      Max_{la}(fun a => Q' (existT _ s a)) in
   V' = max_ltv γ.
 Proof.
   intros.
   generalize (max_ltv_eq_fixpt γ hγ V'); intros.
   rewrite <- H0.
   now rewrite (bellmanQbar_bellman_max_op_fixpt' Q').
 Qed.

 Definition greedy' Q' :=
   fun s => 
        let (la,Hla) := fa M s in
        let pt := na M s in  
        @argmax (act M s) la (proj2 (not_nil_exists _) (ex_intro _ pt (Hla pt)))
          (fun a => Q' (existT _ s a)).

 Lemma greedy_Qbar Q' :
   bellmanQbar Q' = Q' ->
   forall (init : Rfct M.(state)),
     greedy γ init = greedy' Q'.
  Proof.
    intros.
    apply functional_extensionality_dep.
    intros.
    unfold greedy, greedy'.
    destruct (M x).
    f_equal.
    apply functional_extensionality.    
    intros.
    rewrite <- H.
    unfold bellmanQbar.
    unfold act_expt_reward.
    do 2 f_equal.
    apply expt_value_Proper; trivial.
    intros ?.
    rewrite (bellmanQbar_bellman_max_op_fixpt' Q' H).
    unfold act_list.
    now destruct (M a).
  Qed.

  Lemma exists_fixpt_policy' Q'  : 
    bellmanQbar Q' = Q' ->
    let V' := fun s => let (la,_) := fa M s in
                       Max_{la}(fun a => Q' (existT _ s a)) in
    let σ' := greedy' Q' in
    ltv γ σ' = V'.
Proof.
  intros bQ' V' σ'.
  generalize (exists_fixpt_policy γ hγ (M := M) V'); intros.
  simpl in H.
  rewrite (bellmanQbar_bellman_max_op_fixpt' Q') in H; trivial.
  subst V'.
  rewrite <- H.
  f_equal.
  subst σ'.
  now rewrite (greedy_Qbar Q').
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

Definition Rfct_inner {A : Type} (finA : FiniteType A) (f g : Rfct A) : R :=
  let (ls, _) := finA in fun_inner_prod f g ls.


Lemma Rfct_expt_inner {A B : Type} (finA : FiniteType A)
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
Lemma expt_value_le_max {A : Type} (finA : FiniteType A) (p : Pmf A) (f : A -> R):
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

Lemma minus_Rsqr_le (a b : R):
  a - b² <= a.
Proof.
  rewrite <-Rminus_0_r.
  unfold Rminus. apply Rplus_le_compat_l.
  apply Ropp_le_contravar.
  rewrite Rsqr_pow2. apply pow2_ge_0.
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

Local Instance EqDecsigT : EqDec (sigT M.(act)) eq.
Proof.
  intros x y.
  apply ClassicalDescription.excluded_middle_informative.
Qed.

Definition bellmanQ' (sa0 : sigT M.(act)) : Rfct(sigT M.(act)) -> M.(state) -> Rfct(sigT M.(act))
  := fun W => fun s' sa => if (sa == sa0) then
                       let (s,a) := sa in
                       reward s a s' + γ*Max_{act_list s'}(fun a => W (existT _ s' a))
                       else W sa.

Definition bellmanQbar' (sa0 : sigT M.(act)) : Rfct (sigT M.(act)) -> Rfct (sigT M.(act))
  := fun W => fun sa => if (sa == sa0) then
                  let (s,a) := sa in
                  act_expt_reward s a +
                  γ*expt_value (t s a)(fun s' => Max_{act_list s'}(fun a => W (existT _ s' a)))
                  else let (s,a) := sa in W (existT _ s a).

(* This is w. *)
Definition stochasticBellmanQ' (sa0 : sigT M.(act)) :=
  fun W => fun s' sa => (bellmanQ' sa0 W s' sa - bellmanQbar' sa0 W sa).

(* Lemma 12 *)
Theorem expt_value_stochasticBellmanQ' W :
  forall (sa sa0 : sigT M.(act)),
    let (s,a) := sa in
    expt_value (t s a) (fun s' => stochasticBellmanQ' sa0 W s' sa) = 0.
Proof.
  intros.
  destruct sa.
  unfold stochasticBellmanQ'.
  rewrite expt_value_sub.
  rewrite expt_value_const.
  unfold bellmanQbar', bellmanQ'.
  match_destr.
  + rewrite expt_value_add.
    rewrite expt_value_const_mul. unfold act_expt_reward. lra.
  + rewrite expt_value_const; lra.
Qed.


 Theorem expt_value_bellmanQbar sa0 W :
   forall sa : sigT M.(act), let (s,a) := sa in
                        expt_value (t s a) (fun a0 : state M => bellmanQ' sa0 W a0 (existT (act M) s a)) =
                        (bellmanQbar' sa0 W (existT (act M) s a)).
 Proof.
   intros [s a].
   unfold bellmanQbar'.
   unfold bellmanQ'.
   match_destr.
   + now rewrite expt_value_add, expt_value_const_mul.
   + now rewrite expt_value_const.
 Qed.

Theorem expt_value_rsqr_stochasticBellmanQ' W :
  forall (sa sa0 : sigT M.(act)),
    let (s,a) := sa in
    expt_value (t s a) (fun s' => (stochasticBellmanQ' sa0 W s' sa)²) =
    expt_value (t s a) (fun s' => (bellmanQ' sa0 W s' sa)²) - (bellmanQbar' sa0 W sa)².
Proof.
  intros [s a] sa0.
  unfold stochasticBellmanQ'.
  setoid_rewrite Rsqr_minus.
  rewrite expt_value_sub.
  rewrite expt_value_add.
  rewrite expt_value_const.
  setoid_rewrite Rmult_assoc.
  rewrite expt_value_const_mul.
  setoid_rewrite Rmult_comm at 4.
  rewrite expt_value_const_mul.
  rewrite (expt_value_bellmanQbar sa0 W (existT _ s a)).
  rewrite <-Rmult_assoc. unfold Rsqr. ring.
Qed.

Lemma Rmax_list_const {A : Type} (r : R) (l : list A):
  [] <> l -> Max_{l}(fun _ => r) = r.
Proof.
  intros Hl.
  symmetry.
  apply Rle_antisym.
  + apply Rmax_spec.
    rewrite in_map_iff.
    rewrite not_nil_exists in Hl.
    destruct Hl as [a Ha].
    exists a. split; trivial.
  + rewrite Rmax_list_le_iff.
    -- intros a Ha.
       rewrite in_map_iff in Ha.
       destruct Ha as [b [? ?]].
       subst; lra.
    -- now rewrite map_not_nil.
Qed.

Lemma Rmax_list_Rabs_pos {A : Type} (l : list A) (f : A -> R) :
  0 <= Max_{l} (fun a => Rabs (f a)).
Proof.
  destruct (is_nil_dec l); try subst.
  + now simpl.
  + rewrite BasicUtils.ne_symm in n.
    generalize (Rmax_list_map_exist (fun a => Rabs(f a)) l n).
    intros [a [Ha1 Ha2]].
    rewrite <-Ha2.
    apply Rabs_pos.
Qed.

Lemma Rplus_le_compat_Rsqr {a b c d : R} (hab : 0 <= a <= c) (hbd : 0 <= b <= d) :
  (a + b)² <= (c + d)².
Proof.
  do 2 rewrite Rsqr_plus.
  apply Rplus_le_compat.
  apply Rplus_le_compat.
  + apply Rsqr_le_abs_1.
    rewrite Rabs_right; try rewrite Rabs_right; try intuition lra.
  + apply Rsqr_le_abs_1.
    rewrite Rabs_right; try rewrite Rabs_right; try intuition lra.
  + apply Rmult_le_compat; try intuition lra.
Qed.

(* Move this somewhere else. *)
Lemma Rmax_list_map_dep_prod {A : Type} {B : A -> Type} (la : list A) (lb : forall a, list (B a))
      (Hb : forall a, [] <> lb a) (f : forall x :A, B x -> R):
         Max_{ la}(fun a => Max_{lb a} (fun b => f a b)) =
         Max_{list_dep_prod la lb}(fun ab : {x : A & B x} => let (a,b) := ab in f a b).
 Proof.
   destruct (is_nil_dec la); subst; try simpl; try easy.
   assert (Ha : [] <> la) by congruence. clear n.
   apply Rle_antisym.
    ++  rewrite Rmax_list_le_iff.
    -- intros x Hx. eapply (@Rmax_list_ge _ _ x).
       ** rewrite in_map_iff in *.
          destruct Hx as [a [Hx' HInx']].
          set (Hmax := Rmax_list_map_exist (fun b : B a=> f a b) (lb a) (Hb a)).
          destruct Hmax as [b [Hb1 Hb2]].
          exists (existT _ a b). simpl. split; [now rewrite <-Hx' |].
          apply in_dep_prod; trivial.
       ** now right.
    -- now rewrite map_not_nil.
       ++ rewrite Rmax_list_le_iff.
    * intros x Hx.
      rewrite in_map_iff in Hx.
      destruct Hx as [ab [Hab1 HInab1]].
      eapply Rmax_list_ge.
      --- rewrite in_map_iff.
          exists (projT1 ab). split ; trivial.
          destruct ab; simpl.
          setoid_rewrite in_dep_prod_iff in HInab1.
          destruct HInab1 ; trivial.
      --- eapply (Rmax_list_ge _ _ (f (projT1 ab) (projT2 ab))).
          +++ rewrite in_map_iff. exists (projT2 ab). split ; trivial.
              destruct ab as [a b]; simpl.
              rewrite in_dep_prod_iff in HInab1.
              destruct HInab1 ; trivial.
          +++ rewrite <-Hab1; destruct ab; simpl. right ; trivial.
    * rewrite map_not_nil.
      rewrite not_nil_exists in Ha.
      destruct Ha as [a H]. specialize (Hb a).
      rewrite not_nil_exists in Hb.
      destruct Hb as [b Hb].
      rewrite not_nil_exists.
      exists (existT _ a b). rewrite in_dep_prod_iff; split; trivial.
 Qed.


(* Lemma 13. *)
Theorem noise_variance_bound' (sa0 : sigT M.(act)) W :
  forall sa : sigT M.(act), let (s,a) := sa in
                       let (ls,_) := fs M in
                       variance (t s a) (fun s' => stochasticBellmanQ' sa0 W s' sa) <=
                       (Max_{ls}(fun s' => Max_{ls}(fun s => Max_{act_list s}( fun a => Rabs (reward s a s')))) +
                        γ*(Max_{ ls} (fun a0 : state M => Rabs (Max_{ act_list a0}(fun a1 : act M a0 => W (existT (act M) a0 a1))))))².
Proof.
  intros [s a].
  assert (Ha : forall s : M.(state), [] <> act_list s) by (intros s0; apply act_list_not_nil).
  generalize (expt_value_le_max (fs M) (t s a)); intros.
  destruct (fs M) as [ls ?].
  assert (Hls: [] <> ls) by (apply not_nil_exists; exists (ne M); trivial).
  assert (Hγ1 : Rabs (γ) = γ) by (apply Rabs_pos_eq; lra).
  assert (Hγ2 : 0 <= Rabs γ) by (apply Rabs_pos).
  destruct (existT _ s a == sa0).
  rewrite variance_eq.
  rewrite (expt_value_rsqr_stochasticBellmanQ' W (existT _ s a) sa0).
  unfold stochasticBellmanQ'. rewrite expt_value_sub.
  rewrite expt_value_const. rewrite Rsqr_minus at 1.
  rewrite (expt_value_bellmanQbar sa0 W (existT _ s a)).
  rewrite Rsqr_pow2. ring_simplify.
  rewrite <-Rsqr_pow2.
  eapply Rle_trans; try apply minus_Rsqr_le.
  eapply Rle_trans; try apply H.
  eapply Rle_trans; try (eapply (Rmax_list_Rsqr_Rabs_1) ; trivial).
  eapply Rle_trans; try (eapply (Rmax_list_Rsqr_Rabs_2) ; trivial).
  unfold bellmanQ'; match_destr.
  + eapply Rle_trans; try (eapply (Rmax_list_Rsqr_Rabs_3) ; trivial).
    apply Rplus_le_compat_Rsqr.
    -- split; [apply Rmax_list_Rabs_pos|].
       apply Rmax_list_fun_le; intros s'.
       unfold act_list.
       rewrite Rmax_list_map_dep_prod.
       +++  apply Rmax_spec; rewrite in_map_iff.
            exists (existT _ s a). split; trivial.
            rewrite in_dep_prod_iff; split; trivial.
            apply fa.
       +++ intros. apply act_list_not_nil.
    -- split; [apply Rmax_list_Rabs_pos|].
       setoid_rewrite Rabs_mult.
       rewrite Hγ1. rewrite Rmax_list_map_const_mul; lra.
  + intuition.
  + rewrite variance_eq.
    unfold stochasticBellmanQ', bellmanQ', bellmanQbar'.
    match_destr. intuition.
    do 2 rewrite expt_value_const.
    rewrite Rminus_eq_0.
    rewrite Rsqr_pow2. apply pow2_ge_0.
Qed.

Theorem noise_total_variance_bound (sa0 : sigT M.(act)) W : exists c : R,
  let (lsa,_) := act_finite M in
  list_sum (map (fun sa : {x : state M & _}  => let (s,a) := sa in
                variance (t s a) (fun s' => stochasticBellmanQ' sa0 W s' sa)) lsa)
  <= c.
Proof.
  generalize (noise_variance_bound' sa0 W); intros Hnvb.
  destruct (fs M) as [ls ?].
  destruct (act_finite M) as [lsa ?].
  exists (list_sum (map (fun _ => (Max_{ls}(fun s' => Max_{ls}(fun s => Max_{act_list s}( fun a => Rabs (reward s a s')))) +
                        γ*(Max_{ ls} (fun a0 : state M => Rabs (Max_{ act_list a0}(fun a1 : act M a0 => W (existT (act M) a0 a1))))))²) lsa)).
  apply list_sum_le; intros sa.
  specialize (Hnvb sa).
  destruct sa as [s a].
  apply Hnvb.
Qed.


Theorem stochasticBellmanQ'_false W :
  forall (sa sa0 : sigT M.(act)), (sa =/= sa0) -> (forall s', stochasticBellmanQ' sa0 W s' sa = 0).
Proof.
  intros.
  unfold stochasticBellmanQ', bellmanQbar'.
  match_destr. intuition.
  unfold bellmanQ'.
  match_destr. intuition.
  destruct sa; lra.
Qed.

Lemma list_sum_split_ind {A : Type} {eq : EqDec A eq} (l : list A) (a0 : A)
  (f : A -> R):
  list_sum (map (fun a => if (a == a0) then f a else 0) l) =
  f a0 * list_sum (map (fun a => if (a == a0) then 1 else 0) l).
Proof.
  induction l.
  + simpl. lra.
  + simpl. match_destr.
    rewrite Rmult_plus_distr_l.
    rewrite IHl. rewrite Rmult_1_r.
    rewrite e. reflexivity.
    rewrite IHl. lra.
Qed.

Lemma list_sum_split {A : Type} {eq : EqDec A eq} (l : list A) (a0 : A)
  (f : A -> R):
  list_sum (map f l) = list_sum (map (fun a => if (a == a0) then f a0 else 0) l) +
                       list_sum (map (fun a => if (a <> a0) then f a else 0) l).
Proof.
  induction l.
  + simpl. lra.
  + simpl. match_destr; case (a <> a0); intros; try intuition; try lra.
    rewrite IHl. rewrite e; lra.
Qed.

Lemma list_sum_ind_count_occ {A : Type} {eq : EqDec A eq}(l : list A)(a0 : A):
  list_sum (map (fun a => if (a == a0) then 1 else 0) l) =
  INR (count_occ eq l a0).
Proof.
  induction l; try now simpl.
  simpl; match_destr.
  + match_destr.
    -- rewrite IHl.
       rewrite S_INR; lra.
    -- intuition.
  + match_destr.
    -- intuition.
    -- rewrite Rplus_0_l.
       assumption.
Qed.

Theorem total_variance_stochasticBellmanQ' (sa0 : sigT M.(act)) W :
  let (lsa,_) := act_finite M in
  let lsa_nodup := nodup EqDecsigT lsa in
  list_sum (map (fun sa : {x : M.(state) & _} => let (s,a) := sa in
                                              variance (t s a) (fun s' => stochasticBellmanQ' sa0 W s' sa)) lsa_nodup) =
  let (s0,a0) := sa0 in
variance (t s0 a0) (fun s' => stochasticBellmanQ' (existT _ s0 a0) W s' (existT _ s0 a0)).
Proof.
  destruct (act_finite M) as [lsa ?].
  intros lsa_nodup.
  rewrite list_sum_split with (a0 := sa0).
  rewrite <-Rplus_0_r.
  f_equal.
  + destruct sa0 as [s0 a0].
    rewrite list_sum_split_ind.
    rewrite <-Rmult_1_r. f_equal.
    rewrite list_sum_ind_count_occ.
    replace 1 with (INR 1) by reflexivity.
    f_equal.
    generalize (nodup_In EqDecsigT lsa); intros.
    assert (Hf : forall x, In x (nodup EqDecsigT lsa)).
    {
      intros x. rewrite H. apply fin_finite.
    }
    revert Hf.
    generalize (NoDup_count_occ' EqDecsigT lsa_nodup); intros.
    assert (Hnd : NoDup lsa_nodup) by (apply NoDup_nodup).
    rewrite H0 in Hnd. apply Hnd.
    unfold lsa_nodup.
    rewrite nodup_In. apply fin_finite.
  + apply list_sum0_is0.
    rewrite Forall_map.
    rewrite Forall_forall; intros sa Hsa.
    match_destr.
    generalize (stochasticBellmanQ'_false W sa sa0 c); intros Hz.
    destruct sa as [s a].
    unfold variance. setoid_rewrite Hz.
    setoid_rewrite expt_value_zero.
    setoid_rewrite Rminus_eq_0.
    setoid_rewrite Rsqr_0. apply expt_value_zero.
Qed.

(* Move these.*)
Ltac solve_exists_in :=
  match goal with
  | [a : ?A, fin : forall x : ?A, In x ?ls |- exists a : ?A, In a ?ls] => exists a; try (apply fin)
  end.

Ltac rmax_compare :=
  match goal with
    | [ |- Rmax_list _ <= _] => rewrite Rmax_list_le_iff;
                    [intros ?x [?s [<-?Hs]] %in_map_iff |
                     rewrite map_not_nil, not_nil_exists; solve_exists_in]
    | [ |- _ <= Rmax_list _ ] =>  apply Rmax_spec; rewrite in_map_iff; try solve_exists_in
  end.


Lemma Q_is_bounded' W sa0 :
    let (ls, _) := fs M in
    let (las,_) := act_finite M in
    Max_{ls} (fun s' => Max_{las}(fun sa => bellmanQ' sa0 W s' sa)) <=
    Rmax(Max_{ ls}
  (fun s' : state M =>
     Max_{ las}(fun sa : {x : state M & act M x} => let (s, a) := sa in reward s a s')) +
    γ*Max_{las}(W)) (Max_{las}(W)).
Proof.
  destruct act_finite as [lsa ?].
  destruct fs as [ls ?].
  rmax_compare.
  rmax_compare.
  unfold bellmanQ'.
  match_destr.
  + rewrite e.
    destruct sa0 as [s1 a1].
    rewrite Rmax_Rle. left.
    apply Rplus_le_compat.
    -- rewrite Rmax_list_map_dep_prod.
       rmax_compare. exists (existT _ s (existT _ s1 a1)).
       split; [trivial | intuition].
       apply in_dep_prod; trivial.
       intros. rewrite not_nil_exists.
       now exists s0.
    -- apply Rmult_le_compat_l; try intuition lra.
       rmax_compare.
       generalize (Rmax_list_map_exist (fun a => W (existT _ s a)) (act_list s) (act_list_not_nil s)); intros [a [Ha1 Ha2]].
       exists (existT _ s a). split; trivial.
  + rewrite Rmax_Rle. right.
    rmax_compare. exists s0.
    split; trivial.
Qed.

End bellmanQ.
