
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
(* Applies a function to an initial argument n times *)
Fixpoint applyn {A} (init : A) (g : A -> A) (n : nat) : A :=
  match n with
  | 0 => init
  | S k => g (applyn init g k)
  end.


  
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

(*
Context {M:Type->Type}.
Context {Mm:Monad M}.
Context {A:Type}.
Context (unit:A) (f:A->M A).
*)

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
 t :>  state -> act -> Pmf state;
 (* Reward when you are at state s. *)
 reward : state -> R                                
}.

Arguments outcomes {_}.

Definition policy (M : MDP) := M.(state) -> M.(act).

Context {M : MDP}.
Context (σ : policy M).

(* Construction of a Kliesli arrow out of a policy. 
   This can be interpreted as a |S| × |S| stochastic matrix. *)

Definition stoch_mx : M.(state) -> Pmf M.(state) := fun s => t _ s (σ s).

Definition bind_stoch_iter (n : nat) (init : M.(state)):= bind_iter init (stoch_mx) n.

Definition expt_reward (init : M.(state)) (n : nat) : R :=
 list_sum (map (fun y : nonnegreal * state _ => reward _ (snd y) * (fst y)) (bind_stoch_iter n init).(outcomes)).

  
(* Expected reward at time 0 is equal to the reward. *)
Lemma expt_reward0_eq_reward : forall init : M.(state), expt_reward init 0 = reward _ init.
Proof.
  intros init.
  unfold expt_reward ; simpl.
  lra.
Qed.

(* Bounded rewards imply bounded expected rewards for all iterations and all states. *)
Lemma expt_reward_le_max {D : R} (init : M.(state)) :
  (forall s : M.(state), reward _ s <= D)  ->
  (forall n:nat, expt_reward init n <= D). 
Proof. 
  intros H. 
  unfold expt_reward. intros n. 
  generalize (bind_stoch_iter n init) as l.
  intros l.
  rewrite <- Rmult_1_r.
  change (D*1) with (D*R1). 
  rewrite <- (sum1_compat l). 
  induction l.(outcomes). 
  * simpl; lra.
  * simpl in *. rewrite Rmult_plus_distr_l.
    assert (reward M (snd a) * fst a  <=  D * fst a). apply Rmult_le_compat_r. apply cond_nonneg.
    apply H. 
    now apply Rplus_le_compat. 
Qed.

(* Bounded rewards imply bounded expected rewards for all iterations and all states. *)
Lemma expt_reward_le_max_Rabs {D : R} (init : M.(state)) :
  (forall s : M.(state),Rabs (reward _ s) <= D)  ->
  (forall n:nat, Rabs (expt_reward init n) <= D). 
Proof. 
  intros H. 
  unfold expt_reward. intros n. 
  generalize (bind_stoch_iter n init) as l.
  intros l.
  rewrite <- Rmult_1_r.
  change (D*1) with (D*R1). 
  rewrite <- (sum1_compat l). 
  induction l.(outcomes). 
  * simpl. right. rewrite Rabs_R0. lra. 
  * simpl in *. rewrite Rmult_plus_distr_l.
    assert (reward M (snd a) * fst a  <=  D * fst a). apply Rmult_le_compat_r. apply cond_nonneg.
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
  intros M0 σ0 init0 n. unfold expt_reward.
  simpl. rewrite <- (sum1_compat (bind_stoch_iter σ0 n init0)).
  f_equal. apply map_ext. rewrite sum1_compat.
  intros a. now rewrite Rmult_1_l.
Qed. 

End egs.

Section ltv.

Open Scope R_scope. 
Context {M : MDP} {γ : R}.
Context (σ : policy M) (init : M.(state)) (hγ : (0 <= γ < 1)%R).

Definition ltv_part (N : nat) := sum_n (fun n => γ^n * (expt_reward σ init n)) N. 
Definition ltv_part' (N : nat) := sum_f_R0' (fun n => γ^n * (expt_reward σ init n)) N. 

Lemma ltv_part0_eq_reward : ltv_part 0 = reward _ init.
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

Lemma ltv_part_le {D : R} (N : nat) :  (forall s : M.(state), reward _ s <= D) -> ltv_part N <= sum_f_R0 (fun n => γ^n * D) N.
Proof.
  intros Hd.
  unfold ltv_part.  rewrite sum_n_Reals. apply sum_Rle. 
  intros n0 Hn0. 
  apply Rmult_le_compat_l.
  apply pow_le ; firstorder.
  now apply (expt_reward_le_max).
Qed. 


Lemma ex_series_le_Reals
     : forall (a : nat -> R) (b : nat -> R),
    (forall n : nat, Rabs (a n) <= b n) -> ex_series b -> ex_series a.
Proof.
  intros a b Hab Hexb.  
  apply (@ex_series_le _ _ a b).
  now apply Hab. assumption.
Qed.


Lemma abs_convg_implies_convg : forall (a : nat -> R), ex_series (fun n => Rabs(a n)) -> ex_series a. 
Proof.
intros a Habs.   
refine (ex_series_le_Reals a (fun n => Rabs(a n)) _ Habs).
intros n. now right.
Qed.

Lemma ltv_part_le_norm {D : R} (N : nat) :  (forall s : M.(state), Rabs (reward _ s) <= D) -> Rabs(ltv_part N) <= sum_f_R0 (fun n => γ^n * D) N.
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

Theorem ex_series_ltv : ex_series ltv_part.
Proof.   


End ltv.

  



        
