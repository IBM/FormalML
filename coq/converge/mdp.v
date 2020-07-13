
Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy.
Require Import pmf_monad.
Require Import domfct.
Require Import Sums.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.


Section extra.
Open Scope list_scope.
Open Scope R_scope.

Import ListNotations.
  
Fixpoint Rmax_list (l : list R) : R :=
  match l with
  | nil => 0
  | (x :: xs) => Rmax x (Rmax_list xs)
  end.

Lemma list_sum_mult_const (c : R) (l : list R) :
  list_sum (map (fun z => c*z) l) = c*list_sum (map (fun z => z) l).
Proof. 
  induction l.
  simpl; lra.
  simpl in *. rewrite IHl. 
  lra. 
Qed.   

Lemma list_sum_const_mult_le {x y : R} (l : list R) (hl : list_sum l = R1) (hxy : x <= y) :
  list_sum (map (fun z => x*z) l) <= y.
Proof.
  rewrite list_sum_mult_const. rewrite map_id. 
  rewrite hl. lra. 
Qed. 

Lemma list_sum_fun_mult_le {x y D : R} {f g : R -> R}(l : list R)(hf : forall z, f z <= D) (hg : forall z , 0 <= g z) :
  list_sum (map (fun z => (f z)*(g z)) l) <= D*list_sum (map (fun z => g z) l).
Proof.
  induction l.
  simpl. lra.
  simpl. rewrite Rmult_plus_distr_l.
  assert (f a * g a <= D * g a). apply Rmult_le_compat_r. exact (hg a). exact (hf a).
  exact (Rplus_le_compat _ _ _ _ H IHl).   
Qed. 

Lemma abs_convg_implies_convg : forall (a : nat -> R), ex_series (fun n => Rabs(a n)) -> ex_series a. 
Proof.
intros a Habs.   
refine (ex_series_le_Reals a (fun n => Rabs(a n)) _ Habs).
intros n. now right.
Qed.

(* Applies a function to an initial argument n times *)
Fixpoint applyn {A} (init : A) (g : A -> A) (n : nat) : A :=
  match n with
  | 0 => init
  | S k => g (applyn init g k)
  end.

End extra.

Definition bind_iter {M:Type->Type} {Mm:Monad M} {A:Type} (unit:A) (f : A -> M A) :=
  applyn (ret unit) (fun y => bind y f).

Section MDPs.

Open Scope monad_scope.
Open Scope R_scope.

Record MDP := mkMDP {
 (* State and action spaces. *)
 state : Type;
 act  : Type;
 (* Probabilistic transition structure. 
    t(s,a,s') is the probability that the next state is s' given that you take action a in state s.
    One can also consider to to be an act-indexed collection of Kliesli arrows of Pmf. 
 *)
 t :  state -> act -> Pmf state;
 (* Reward when you are at state s. *)
 reward : state -> R                                
}.

Arguments outcomes {_}.
Arguments t {_}.
Arguments reward {_}. 

Definition policy (M : MDP) := M.(state) -> M.(act).

Context {M : MDP}.
Context (σ : policy M).

(* Construction of a Kliesli arrow out of a policy. 
   This can be interpreted as a |S| × |S| stochastic matrix. *)

(*Definition state_policy_kleisli : M.(state) -> Pmf M.(state) := fun s => t s (σ s).*)

Definition bind_stoch_iter (n : nat) (init : M.(state)):=
  applyn (ret init) (fun y => Pmf_bind y (fun s => t s (σ s))) n.

(* 
   It is helpful to see what happens in the above definition for n=1, and starting at init.
   We get the transition probability structure applied to the initial state, init, and upon
   taking the action σ(init) as prescribed by the policy sigma. So we recover the entire 
   transition structure after one step. Similar remarks apply for n-steps.
*)

Lemma bind_stoch_iter_1 (init : M.(state)) : bind_stoch_iter 1 init = t init (σ init).
Proof. 
  unfold bind_stoch_iter.
  unfold bind_iter. 
  simpl. rewrite Pmf_bind_of_ret.
  reflexivity.
Qed.


(* Expected reward after n-steps, starting at initial state, following policy sigma. *)
Definition expt_reward (init : M.(state)) (n : nat) : R :=
 expt_value (bind_stoch_iter n init) reward.

  
(* Expected reward at time 0 is equal to the reward. *)
Lemma expt_reward0_eq_reward : forall init : M.(state), expt_reward init 0 = reward init.
Proof.
  intros init.
  unfold expt_reward ; simpl.
  unfold expt_value ; simpl. 
  lra.
Qed.

(*
 With every iteration, the reward changes to the average of the rewards of the previous transition states.
*)
Lemma expt_reward_succ (n : nat) : forall init : M.(state), expt_reward init (S n) =  expt_value (bind_stoch_iter n init) (fun s : state M => expt_value (t s (σ s)) reward).
Proof.
  intros init. 
  unfold expt_reward. unfold bind_stoch_iter. 
  simpl.
  rewrite expt_value_bind. reflexivity. 
Qed.

(* Bounded rewards (in absolute value) imply bounded expected rewards for all iterations and all states. *)
Lemma expt_reward_le_max_Rabs {D : R} (init : M.(state)) :
  (forall s : M.(state),Rabs (reward s) <= D)  ->
  (forall n:nat, Rabs (expt_reward init n) <= D). 
Proof. 
  intros H. 
  unfold expt_reward ; unfold expt_value. intros n. 
  generalize (bind_stoch_iter n init) as l.
  intros l.
  rewrite <- Rmult_1_r.
  change (D*1) with (D*R1). 
  rewrite <- (sum1_compat l). 
  induction l.(outcomes). 
  * simpl. right. rewrite Rabs_R0. lra. 
  * simpl in *. rewrite Rmult_plus_distr_l.
    assert (reward (snd a) * fst a  <=  D * fst a). apply Rmult_le_compat_r. apply cond_nonneg.
    refine (Rle_trans _ _ _ _ _).
    apply Rle_abs. 
    apply H.
    refine (Rle_trans _ _ _ _ _).
    apply Rabs_triang. rewrite Rabs_mult.
    apply Rplus_le_compat.
    enough (Rabs (fst a) = fst a).  rewrite H1. apply Rmult_le_compat_r. 
    apply cond_nonneg. apply H. apply Rabs_pos_eq. apply cond_nonneg.
    apply IHl0.  
Qed.


End MDPs.

Section egs.

(* This defines a "unit reward" MDP.*)
Definition unitMDP {st0 act0 : Type} (t0 : st0 -> act0 -> Pmf st0) : MDP :=
{|
    state := st0;
    act := act0;
    t := t0;
    reward := fun s => R1
|}.

(* The expected reward for an arbitrary initial state and arbitrary policy is unity for a unit MDP. *)
Lemma expt_reward_unitMDP {t0 : R -> R -> Pmf R} :
  let M0 := unitMDP t0 in
  forall (σ0 : policy M0) (init0 : M0.(state)) (n:nat), expt_reward σ0 init0 n = R1. 
Proof.
  intros M0 σ0 init0 n. unfold expt_reward ; unfold expt_value.
  simpl. rewrite <- (sum1_compat (bind_stoch_iter σ0 n init0)).
  f_equal. apply map_ext. rewrite sum1_compat.
  intros a. now rewrite Rmult_1_l.
Qed. 

End egs.

Section ltv.

Open Scope R_scope. 
Context {M : MDP} {γ : R}.
Context (σ : policy M) (init : M.(state)) (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Definition ltv_part (N : nat) := sum_n (fun n => γ^n * (expt_reward σ init n)) N. 

Lemma ltv_part0_eq_reward : ltv_part 0 = reward init.
Proof.
  unfold ltv_part. rewrite sum_n_Reals. simpl.  
  rewrite expt_reward0_eq_reward. lra.
Qed.

Lemma sum_mult_geom (D : R) : infinite_sum (fun n => D*γ^n) (D/(1 - γ)).
Proof.
  rewrite infinite_sum_infinite_sum'.
  apply infinite_sum'_mult_const.
  rewrite <- infinite_sum_infinite_sum'.
  apply is_series_Reals. apply is_series_geom.
  rewrite Rabs_pos_eq. lra. lra. 
Qed.

Lemma ex_series_mult_geom (D:R) : ex_series (fun n => D*γ^n).
Proof.
  exists (D/(1-γ)). 
  rewrite is_series_Reals. 
  apply sum_mult_geom.
Qed.


Lemma ltv_part_le_norm {D : R} (N : nat) :
  (forall s : M.(state), Rabs (reward s) <= D) -> Rabs(ltv_part N) <= sum_f_R0 (fun n => γ^n * D) N.
Proof.
  intros Hd.
  unfold ltv_part. rewrite sum_n_Reals.
  refine (Rle_trans _ _ _ _ _ ).
  apply sum_f_R0_triangle. 
  apply sum_Rle. 
  intros n0 Hn0. 
  rewrite Rabs_mult.
  enough (Hγ : Rabs (γ^n0) = γ^n0). rewrite Hγ.
  apply Rmult_le_compat_l.
  apply pow_le ; firstorder.
  apply expt_reward_le_max_Rabs ; try assumption.
  apply Rabs_pos_eq. apply pow_le. firstorder. 
Qed.

Theorem ex_series_ltv {D : R} :
  (forall s : M.(state), Rabs (reward s) <= D) -> ex_series (fun n => γ^n * (expt_reward σ init n)).
Proof.
  intros Hbdd. 
  refine (ex_series_le_Reals _ _ _ _). 
  intros n. rewrite Rabs_mult.
  enough (Rabs (γ ^ n) * Rabs (expt_reward σ init n) <= D*γ^n). apply H.
  enough (Hγ : Rabs (γ^n) = γ^n). rewrite Hγ.
  rewrite Rmult_comm. apply Rmult_le_compat_r.
  apply pow_le; firstorder.
  apply (expt_reward_le_max_Rabs) ; try assumption. 
  apply Rabs_pos_eq ; apply pow_le; firstorder.
  apply (ex_series_mult_geom D). 
Qed.

Definition ltv (init : M.(state)) : R := Series (fun n => γ^n * (expt_reward σ init n)).


End ltv.

Definition expt_ltv {M : MDP} {γ : R} (σ : policy M) (p : Pmf M.(state)) (hγ : 0 <= γ < 1): R :=
  expt_value p (@ltv _ γ σ). 

Lemma ltv_corec {M : MDP} {γ D : R} (σ : policy M) (hγ : 0 <= γ < 1) (init : M.(state)) :
  (forall s : M.(state), Rabs (reward _ s) <= D) -> @ltv _ γ σ init = (reward _ init) + γ*expt_value (t M init (σ init)) (@ltv _ γ σ). 
Proof.
  intros bdd.
  rewrite <-(@expt_reward0_eq_reward _ σ init).
  unfold ltv.
  rewrite Series_incr_1. simpl. rewrite Rmult_1_l.
  assert (Series (fun k : nat => γ * γ ^ k * expt_reward σ init (S k))  =  Series (fun k : nat => γ * (γ ^ k * expt_reward σ init (S k)))).   apply Series_ext. intros n. now rewrite Rmult_assoc.
  rewrite H. clear H.
  rewrite Series_scal_l. f_equal. f_equal. 
  rewrite expt_value_Series.
  apply Series_ext. intros n.
  rewrite expt_reward_succ. rewrite expt_value_const_mul.
  f_equal. unfold expt_reward.
  rewrite <-expt_value_bind.
  rewrite <-expt_value_bind. 
  f_equal.
  induction n.
  * unfold bind_stoch_iter. simpl. rewrite Pmf_bind_of_ret.  now rewrite Pmf_ret_of_bind.
  * unfold bind_stoch_iter in *. simpl.  setoid_rewrite IHn.
    rewrite Pmf_bind_of_bind. reflexivity.
    intros a. apply (ex_series_ltv σ _ hγ bdd).
    apply (ex_series_ltv σ _  hγ bdd). 
Qed. 
