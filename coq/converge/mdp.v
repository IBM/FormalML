Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad Permutation orderfun.
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import ExtLib.Structures.Monad LibUtils.


Import MonadNotation.
Import ListNotations. 
Set Bullet Behavior "Strict Subproofs".


(*
****************************************************************************************
This file defines Markov Decision Processes (MDP) and proves various properties about 
them. Included are definitions of long-term values (LTVs), proofs that LTVs are convergent
and proofs that they satisfy the Bellman equation. 
We also include definitions of V* and Q* and proofs about them. The goal is to prove 
policy and value iteration algorithms correct. 
****************************************************************************************
*)


Section extra.
Open Scope list_scope. 
Lemma ne_symm {A} (x y : A) : x <> y <-> y <> x.
Proof.
  split; intros.
  * intros Hxy ; symmetry in Hxy ; firstorder.
  * intros Hxy ; symmetry in Hxy ; firstorder.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) :
    List.map f l = (@nil B) <-> l = (@nil A).
Proof.
    split; intros.
    - induction l; try reflexivity; simpl in *.
    congruence.
    - rewrite H; reflexivity.
Qed.

Lemma map_not_nil {A B} (l : list A) (f : A -> B):
  [] <> List.map f l <-> [] <> l.  
Proof.
   rewrite ne_symm ; rewrite (ne_symm _ l).
   split ; intros.
   * intro Hl. rewrite <-(map_nil f) in Hl ; firstorder.
   * intro Hl. rewrite (map_nil f) in Hl ; firstorder.
Qed.

Lemma not_nil_exists {A} (l : list A) :
  [] <> l <-> exists a, In a l.
Proof.
  split.
  * intros Hl. 
    induction l.
    - firstorder.
    - destruct l.
      -- exists a. simpl; now left. 
      -- set (Hnc := @nil_cons _ a0 l). specialize (IHl Hnc).
         destruct IHl as [a1 Ha1]. 
         exists a1. simpl in * ; intuition.
  * intros [a Ha] not. rewrite <-not in Ha ; firstorder. 
Qed.

Lemma list_prod_not_nil {A B} {la : list A} {lb : list B}(Hla : [] <> la) (Hlb : [] <> lb) :
  [] <> list_prod la lb.
Proof.
  rewrite not_nil_exists.
  rewrite not_nil_exists in Hla.
  rewrite not_nil_exists in Hlb.
  destruct Hla as [a Hla].
  destruct Hlb as [b Hlb].
  exists (a,b). now apply in_prod. 
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


Section list_sum.
  Lemma list_sum_map_zero {A} (s : list A)  :
  list_sum (map (fun _ => 0) s) = 0. 
Proof.
  induction s.
  - simpl; reflexivity.
  - simpl. rewrite IHs ; lra. 
Qed.


Lemma list_sum_le {A} (l : list A) (f g : A -> R) :
  (forall a, f a <= g a) ->
  list_sum (map f l) <= list_sum (map g l).
Proof.
  intros Hfg.
  induction l.
  - simpl ; right ; trivial.
  - simpl. specialize (Hfg a). 
    apply Rplus_le_compat ; trivial. 
Qed.

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

End list_sum.

Class NonEmpty (A : Type) :=
  ex : A.
    
Class Finite (A:Type) : Prop :=
  finite : exists l : list A, forall x:A, In x l.

Section Rmax_list.
  
Open Scope list_scope.
Open Scope R_scope.

Instance EqDecR : @EqDec R eq _ := Req_EM_T. 

Import ListNotations.

Fixpoint Rmax_list (l : list R) : R :=
  match l with
  | nil => 0
  | a :: nil => a
  | a :: l1 => Rmax a (Rmax_list l1)
  end.


Fixpoint Rmax_list' (l : list R) : R :=
  match l with
    | nil => 0
    | a :: l1 =>
      match l1 with
        | nil => a
        | a' :: l2 => Rmax a (Rmax_list' l1)
      end
  end.

Lemma Rmax_list_Rmax_list' (l : list R) :
  Rmax_list l = Rmax_list' l.
Proof.
  induction l. 
  - simpl ; trivial.
  - simpl. rewrite IHl.
    trivial. 
Qed.

Lemma Rmax_spec_map {A} (l : list A) (f : A -> R) : forall a:A, In a l -> f a <= Rmax_list (map f l).
Proof.
  intros a Ha. 
  induction l.
  - simpl ; firstorder.
  - simpl in *. intuition.
    + rewrite H. destruct l. simpl. right; reflexivity. 
      simpl. apply Rmax_l. 
    + destruct l. simpl in *; firstorder.
      simpl in *. eapply Rle_trans ; eauto. apply Rmax_r.
Qed.

Lemma Rmax_spec {l : list R} : forall a:R, In a l -> a <= Rmax_list l.
Proof.
  intros a Ha. 
  induction l.
  - simpl ; firstorder.
  - simpl in *. intuition.
    + rewrite H. destruct l. simpl. right; reflexivity. 
      simpl. apply Rmax_l. 
    + destruct l. simpl in *; firstorder.
      simpl in *. eapply Rle_trans ; eauto. apply Rmax_r.
Qed.

    
Lemma Rmax_list_const_mul (l : list R) {r : R} (hr : 0 <= r) :
  Rmax_list (map (fun x => r*x) l) = r*(Rmax_list l).
Proof.
  induction l. 
  - simpl ; lra.
  - simpl. rewrite IHl.
    rewrite RmaxRmult ; trivial.
    destruct l.  
    + simpl ; reflexivity.
    + simpl in *. f_equal ; trivial. 
Qed.


Lemma Rmax_list_const_add (l : list R) (d : R) :
  Rmax_list (map (fun x => x + d) l) =
  if (l <> []) then ((Rmax_list l) + d) else 0. 
Proof.
  induction l. 
  - simpl ; reflexivity.
  - simpl in *.
    destruct l.
    + simpl ; reflexivity.
    + simpl in * ; rewrite IHl. 
      now rewrite Rcomplements.Rplus_max_distr_r.
Qed.

Lemma Rmax_list_ge (l : list R) (r : R) :
  forall x, In x l -> r <= x -> r <= Rmax_list l.
Proof.
  intros x Hx Hrx. 
  eapply Rle_trans ; eauto.
  now apply Rmax_spec.
Qed.

Lemma Rmax_list_le (l : list R) (r : R) :
  Rmax_list l <= r -> forall x, In x l -> x <= r.
Proof.
  intros H x Hx.
  set (Rmax_spec x Hx). 
  eapply Rle_trans; eauto.
Qed.


Lemma Rmax_list_In (l : list R):
  ([] <> l) -> In (Rmax_list l) l. 
Proof.
  induction l.
  - simpl ; firstorder.
  - intros H. simpl in *.
    destruct l.
    -- now left. 
    -- assert ([] <> r :: l)  by apply nil_cons. 
       specialize (IHl H0) ; clear H0.
       destruct (Rle_dec a (Rmax_list (r :: l))).
       ++ rewrite Rmax_right. now right ; assumption. assumption. 
       ++ rewrite Rmax_left. now left.
          left ; apply ROrder.not_ge_lt ; assumption. 
Qed.

Lemma Rmax_list_lub (l : list R) (r : R):
  ([] <> l) -> (forall x, In x l -> x <= r) -> Rmax_list l <= r. 
Proof.
  intros Hl H.
  apply H. eapply Rmax_list_In ; auto.
Qed.

Lemma Rmax_list_le_iff {l : list R} (hl : [] <> l) (r : R):
  Rmax_list l <= r <-> (forall x, In x l -> x <= r)  .
Proof.
  split. 
  apply Rmax_list_le.
  apply Rmax_list_lub ; auto.
Qed.

Lemma Rmax_list_sum {A B} {la : list A} (lb : list B) (f : A -> B -> R) (Hla : [] <> la):
  Rmax_list (map (fun a => list_sum (map (f a) lb)) la) <=
  list_sum (map (fun b => Rmax_list (map (fun a => f a b) la)) lb). 
Proof.
  rewrite Rmax_list_le_iff. 
  * intro x. rewrite in_map_iff. 
    intros [x0 [Hlsx Hin]].
    rewrite <-Hlsx. apply list_sum_le. 
    intro b. apply (Rmax_spec_map la (fun a => f a b) x0 Hin). 
  * now rewrite map_not_nil. 
Qed.


Lemma Rmax_list_cons_cons (l : list R) (a b : R) :
  Rmax_list (a :: b :: l) = Rmax a (Rmax_list (b :: l)).
Proof.
  constructor.
Qed.

Lemma Rmax_list_Rmax_swap (l : list R) (a b : R) :
  Rmax a (Rmax_list (b :: l)) = Rmax b (Rmax_list (a :: l)).
Proof.
  induction l.
  - simpl ; apply Rmax_comm.
  - do 2 rewrite Rmax_list_cons_cons.
    do 2 rewrite Rmax_assoc. 
    now rewrite (Rmax_comm _ b).
Qed. 
 
Lemma Rmax_list_cons (x0 : R)  (l1 l2 : list R) :
  Permutation l1 l2 -> (Rmax_list l1 = Rmax_list l2) -> Rmax_list (x0 :: l1) = Rmax_list(x0 :: l2).
Proof.
  intros Hpl Hrl. 
  case_eq l1.
  * intro Hl. rewrite Hl in Hpl. set (Permutation_nil Hpl).
    now rewrite e.
  * case_eq l2.
    ++ intro Hl2. rewrite Hl2 in Hpl. symmetry in Hpl. set (Permutation_nil Hpl).
       now rewrite e.
    ++ intros r l H r0 l0 H0. 
       rewrite <-H0, <-H. simpl ; rewrite Hrl.
       now rewrite H0, H.  
Qed.

Lemma Rmax_list_cons_swap (x0 y0 : R)  (l1 l2 : list R) :
  Permutation l1 l2 -> (Rmax_list l1 = Rmax_list l2) ->
  Rmax_list (x0 :: y0 :: l1) = Rmax_list(y0 :: x0 :: l2).
Proof.
  intros Hpl Hrl.
  rewrite Rmax_list_cons_cons. rewrite Rmax_list_Rmax_swap.
  rewrite <-Rmax_list_cons_cons.  
  case_eq l1.
  * intro Hl. rewrite Hl in Hpl. set (Permutation_nil Hpl).
    now rewrite e.
  * case_eq l2.
    ++ intro Hl2. rewrite Hl2 in Hpl. symmetry in Hpl. set (Permutation_nil Hpl).
       now rewrite e.  
    ++ intros r l H r0 l0 H0.  rewrite <-H0, <-H. simpl ; rewrite Hrl.
       now rewrite H0, H.
Qed.

Global Instance Rmax_list_Proper : Proper (@Permutation R ++> eq) Rmax_list.
Proof.
  unfold Proper. intros x y H. 
  apply (@Permutation_ind_bis R (fun a b => Rmax_list a = Rmax_list b)). 
  - simpl ; lra. 
  - intros x0. apply Rmax_list_cons.  
  - intros x0 y0 l l' H0 H1. apply Rmax_list_cons_swap ; trivial. 
  - intros l l' l'' H0 H1 H2 H3. rewrite H1. rewrite <-H3. reflexivity. 
  - assumption. 
Qed.

Notation "Max_{ l } ( f )" := (Rmax_list (map f l)) (at level 50).


(* This is very important to prove existence of an optimal policy. *)
Lemma Rmax_list_map_exist {A} (f : A -> R) (l : list A) :
  [] <> l -> exists a:A, In a l /\ f a = Max_{l}(f). 
Proof.
  intro Hne. 
  set (Hmap := Rmax_list_In (map f l)).
  rewrite <-(map_not_nil l f) in Hne.
  specialize (Hmap Hne).
  rewrite in_map_iff in Hmap.
  destruct Hmap as  [a [Hfa Hin]].
  now exists a. 
Qed.

Lemma Rmax_list_prod_le {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  Max_{la}(fun a => Max_{lb} (fun b => f a b)) =
  Max_{list_prod la lb} (fun ab => f (fst ab) (snd ab)). 
Proof.
  apply Rle_antisym.
  ++  rewrite Rmax_list_le_iff.
      -- intros x Hx. eapply (@Rmax_list_ge _ _ x).
         ** rewrite in_map_iff in *. 
            destruct Hx as [a [Hx' HInx']]. 
            set (Hmax := Rmax_list_map_exist (fun b => f a b) lb). 
            specialize (Hmax Hlb).
            destruct Hmax as [b Hb].
            exists (a,b). simpl. split; [now rewrite <-Hx' |].
            apply in_prod ; trivial; intuition.
         ** now right.
      -- now rewrite map_not_nil.
  ++ rewrite Rmax_list_le_iff.
     * intros x Hx.
       rewrite in_map_iff in Hx.
       destruct Hx as [ab [Hab HInab]].
       eapply (@Rmax_list_ge _ _ (Rmax_list (map (fun b : B => f (fst ab) b) lb))).
       --- rewrite in_map_iff. 
           exists (fst ab). split ; trivial.
           setoid_rewrite surjective_pairing in HInab. 
           rewrite in_prod_iff in HInab. destruct HInab ; trivial.
       --- eapply (Rmax_list_ge _ _ (f (fst ab) (snd ab))).
           +++ rewrite in_map_iff. exists (snd ab). split ; trivial.
               setoid_rewrite surjective_pairing in HInab. 
               rewrite in_prod_iff in HInab. destruct HInab ; trivial.
           +++ rewrite <-Hab. right ; trivial.
     * rewrite map_not_nil. now apply list_prod_not_nil. 
Qed.

(* There has to be a better way of doing this... *)
Lemma Rmax_list_prod_le' {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
   Max_{lb}(fun b => Max_{la} (fun a => f a b))  =
   Max_{list_prod la lb} (fun ab => f (fst ab) (snd ab)).
Proof.
  apply Rle_antisym.
  ++  rewrite Rmax_list_le_iff.
      -- intros x Hx. eapply (@Rmax_list_ge _ _ x).
         ** rewrite in_map_iff in *. 
            destruct Hx as [b [Hx' HInx']]. 
            set (Hmax := Rmax_list_map_exist (fun a => f a b) la). 
            specialize (Hmax Hla).
            destruct Hmax as [a Ha].
            exists (a,b). simpl. split; [now rewrite <-Hx' |].
            apply in_prod ; trivial; intuition.
         ** now right.
      -- now rewrite map_not_nil.
  ++ rewrite Rmax_list_le_iff.
     * intros x Hx.
       rewrite in_map_iff in Hx.
       destruct Hx as [ab [Hab HInab]].
       eapply (@Rmax_list_ge _ _ (Rmax_list (map (fun a : A  => f a (snd ab)) la))).
       --- rewrite in_map_iff. 
           exists (snd ab). split ; trivial.
           setoid_rewrite surjective_pairing in HInab. 
           rewrite in_prod_iff in HInab. destruct HInab ; trivial.
       --- eapply (Rmax_list_ge _ _ (f (fst ab) (snd ab))).
           +++ rewrite in_map_iff. exists (fst ab). split ; trivial.
               setoid_rewrite surjective_pairing in HInab. 
               rewrite in_prod_iff in HInab. destruct HInab ; trivial.
           +++ rewrite <-Hab. right ; trivial.
     * rewrite map_not_nil. now apply list_prod_not_nil. 
Qed.

Lemma Rmax_list_map_comm {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  Max_{la}(fun a => Max_{lb} (fun b => f a b)) = Max_{lb}(fun b => Max_{la} (fun a => f a b)) .
Proof.
  etransitivity; [|symmetry].
  - apply Rmax_list_prod_le ; trivial. 
  - apply Rmax_list_prod_le'; trivial.   
Qed.


Lemma Rmax_list_abstr {A} (la : list A) {l : list(A -> R)} (hl : [] <> l) :
  forall x, In x la -> Max_{l}(fun f => f x) <= Max_{l} (fun f => Max_{la} (f) ).
Proof.
  intros x Hx.
  rewrite Rmax_list_map_comm.
  *  rewrite Rmax_list_le_iff.
     -- intros x0 Hx0. eapply Rmax_list_ge.
        rewrite in_map_iff. exists x. split ; trivial. 
        now apply Rmax_spec. 
     -- now apply map_not_nil.
  *  assumption.                                                       
  * rewrite not_nil_exists. now exists x.                                                  Qed.


(* max_{x:A} (max_{f:A->B}(g (f a) f)) = max_{f:A->B} (max_{a:map f A} (g (a,f))) *)

Lemma Rmax_list_fun_swap {A B} {l : list(A -> B)}{la : list A}
      (g :B -> (A -> B) -> R)
      (hl : [] <> l) (hla : [] <> la)  :
      Max_{la} (fun s => Max_{l} (fun f => g (f s) f))  =
      Max_{l} (fun f => Max_{map f la} (fun b => g b f)).
Proof. 
  rewrite Rmax_list_map_comm; trivial.
  f_equal. apply map_ext.
  intros a.  
  now rewrite map_map.
Qed.


(*Lemma Rmax_list_fun_filter {A B} {l : list(A -> B)}{la : list A}
      (g :B -> (A -> B) -> R)
      (hl : [] <> l) (hla : [] <> la) (s : A) :
  Max_{l} (fun f => g (f s) f) = Max_{filter (fun  => la}*)
  


End Rmax_list.

Definition bind_iter {M:Type->Type} {Mm:Monad M} {A:Type} (unit:A) (f : A -> M A) :=
  applyn (ret unit) (fun y => Monad.bind y f).

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
 (* Reward when you move to s' from s by taking action a. *)
 reward : state -> act -> state -> R                                
}.

Arguments outcomes {_}.
Arguments t {_}.
Arguments reward {_}. 

(* 
   A decision rule is a mapping from states to actions.
*)
Definition dec_rule (M : MDP) := M.(state) -> M.(act).

(*
   In general,a policy is a *stream* of decision rules. 
   A stream of constant decision rules is called a *stationary policy*. 
   Henceforth, we shall only work with stationary policies. 

Definition policy (M : MDP) := Stream (dec_rule M).
 *)

Context {M : MDP}.
Context (σ : dec_rule M).

(* Constructing a Kliesli arrow out of a stationary policy by n-iterated binds.
   This can be interpreted as as n-multiplications of an
   |S| × |S| stochastic matrix. 
   We don't explicitly construct a stationary stream -- for that we would have to 
   update the σ after each bind.
*)

Definition bind_stoch_iter (n : nat) (init : M.(state)) : Pmf M.(state):=
  applyn (ret init) (fun y => Pmf_bind y (fun s => t s (σ s))) n.

(* 
   It is helpful to see what happens in the above definition for n=1, and starting at init.
   We get the transition probability structure applied to the initial state, init, and upon
   taking the action σ(init) as prescribed by the policy sigma. So we recover the entire 
   transition structure after one step. Similar remarks apply for n-steps.
*)

Lemma bind_stoch_iter_1 (init : M.(state)) :
  bind_stoch_iter 1 init = t init (σ init).
Proof. 
  unfold bind_stoch_iter.
  unfold bind_iter. 
  simpl. rewrite Pmf_bind_of_ret.
  reflexivity.
Qed.

(* Expected immediate reward for performing action (σ s) when at state s. *)
Definition step_expt_reward : state M -> R :=
  (fun s => expt_value (t s (σ s)) (reward s (σ s))).


(* Expected reward after n-steps, starting at initial state, following policy sigma. *)
Definition expt_reward (init : M.(state)) (n : nat) : R :=
 expt_value (bind_stoch_iter n init) (step_expt_reward).

  
(* Expected reward at time 0 is equal to the reward. *)
Lemma expt_reward0_eq_reward : forall init : M.(state), expt_reward init 0 = (step_expt_reward init).
Proof.
  intros init.
  unfold expt_reward. unfold bind_stoch_iter ; simpl.
  now rewrite expt_value_pure. 
Qed.

(*
 With every iteration, the reward changes to the average of the rewards of the previous transition states.
*)
Lemma expt_reward_succ (n : nat) : forall init : M.(state), expt_reward init (S n) =  expt_value (bind_stoch_iter n init) (fun s : state M => expt_value (t s (σ s)) (step_expt_reward)).
Proof.
  intros init. 
  unfold expt_reward. unfold bind_stoch_iter. 
  simpl. rewrite expt_value_bind.
  f_equal.
Qed.


(* Bounded rewards (in absolute value) imply bounded expected rewards for all iterations and all states. *)
Lemma expt_reward_le_max_Rabs {D : R} (init : M.(state)) :
  (forall s s': M.(state), Rabs (reward s (σ s) s') <= D)  ->
  (forall n:nat, Rabs (expt_reward init n) <= D). 
Proof. 
  intros H. 
  unfold expt_reward. intros n. apply expt_value_Rle.
  unfold step_expt_reward. intros s.
  apply expt_value_Rle. apply H. 
Qed.


End MDPs.

Section egs.

(* This defines a "unit reward" MDP.*)
Definition unitMDP {st0 act0 : Type} (t0 : st0 -> act0 -> Pmf st0) : MDP :=
{|
    state := st0;
    act := act0;
    t := t0;
    reward := fun s a s' => R0
|}.

(* The expected reward for an arbitrary initial state and arbitrary policy is unity for a unit MDP. *)
Lemma expt_reward_unitMDP {t0 : R -> R -> Pmf R} :
  let M0 := unitMDP t0 in
  forall (σ0 : dec_rule M0) (init0 : M0.(state)) (n:nat), expt_reward σ0 init0 n = R0. 
Proof.
  intros M0 σ0 init0 n.
  assert (expt_value (bind_stoch_iter σ0 n init0) (fun s => R0) = R0). apply expt_value_zero.
  rewrite <-H.
  unfold expt_reward.
  unfold step_expt_reward. simpl.
  f_equal. apply functional_extensionality. intros x.
  apply expt_value_zero. 
Qed.

End egs.

Section ltv.

Open Scope R_scope. 
Context {M : MDP} (γ : R).
Context (σ : dec_rule M) (init : M.(state)) (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.


Global Instance Series_proper :
  Proper (pointwise_relation _ eq  ==> eq) (Series).
Proof.
  unfold Proper, pointwise_relation, respectful.
  apply Series_ext.
Qed.

Definition ltv_part (N : nat) := sum_n (fun n => γ^n * (expt_reward σ init n)) N. 

Lemma ltv_part0_eq_reward : ltv_part 0 = (step_expt_reward σ init).
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
   (forall s s': M.(state), Rabs (reward s (σ s) s') <= D) -> Rabs(ltv_part N) <= sum_f_R0 (fun n => γ^n * D) N.
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
   (forall s s': M.(state), Rabs (reward s (σ s) s') <= D) -> (forall s0, ex_series (fun n => γ^n * (expt_reward σ s0 n))).
Proof.
  intros Hbdd s0. 
  refine (ex_series_le_Reals _ _ _ _). 
  intros n. rewrite Rabs_mult.
  enough (Rabs (γ ^ n) * Rabs (expt_reward σ s0 n) <= D*γ^n). apply H.
  enough (Hγ : Rabs (γ^n) = γ^n). rewrite Hγ.
  rewrite Rmult_comm. apply Rmult_le_compat_r.
  apply pow_le; firstorder.
  apply (expt_reward_le_max_Rabs) ; try assumption. 
  apply Rabs_pos_eq ; apply pow_le; firstorder.
  apply (ex_series_mult_geom D). 
Qed.

Definition ltv : M.(state) -> R := fun s => Series (fun n => γ^n * (expt_reward σ s n)).

Definition expt_ltv (p : Pmf M.(state)) : R :=
  expt_value p ltv.

Lemma Pmf_bind_comm_stoch_bind (n : nat) :
  Pmf_bind (bind_stoch_iter σ n init) (fun a : state M => t a (σ a)) =
  Pmf_bind (t init (σ init)) (fun a : state M => bind_stoch_iter σ n a).
Proof.
    induction n.
  * unfold bind_stoch_iter. simpl. rewrite Pmf_bind_of_ret.  now rewrite Pmf_ret_of_bind.
  * unfold bind_stoch_iter in *. simpl.  setoid_rewrite IHn.
    rewrite Pmf_bind_of_bind. reflexivity.
Qed.

(* Long-Term Values satisfy the Bellman equation. *)
Lemma ltv_corec {D : R} :
   (forall s s': M.(state), Rabs (reward s (σ s) s') <= D) ->
  ltv init = (step_expt_reward σ init) + γ*expt_value (t init (σ init)) ltv. 
Proof.
  intros bdd. 
  rewrite <-(@expt_reward0_eq_reward _ σ init).
  unfold ltv.
  rewrite Series_incr_1. simpl. rewrite Rmult_1_l. setoid_rewrite Rmult_assoc.   
  rewrite Series_scal_l. f_equal. 
  setoid_rewrite expt_reward_succ. 
  rewrite expt_value_Series. f_equal.  
  apply Series_ext. intros n.
  rewrite expt_value_const_mul. f_equal. 
  rewrite <-expt_value_bind. rewrite Pmf_bind_comm_stoch_bind.
  unfold expt_reward. 
  rewrite expt_value_bind.  reflexivity.
  apply (ex_series_ltv bdd).
  apply (ex_series_ltv bdd). 
Qed.

End ltv.

Axiom lem : forall p : Prop, p \/ not p.

Lemma finite_has_max_aux {A:Type} (l1 l2:list A) (R:A->A->Prop) (sub:forall x, In x l2 -> In x l1) :
((forall x, In x l1) ->  exists x:A, forall y:A, R y x) -> ((forall x, In x l2) -> exists x:A, forall y:A, R y x).
Proof.
  intros H hl2.
  apply H. intro x. 
  apply sub. apply hl2.
Qed. 

Lemma sub_cons {A : Type} (l : list A) (a : A) : forall x, In x l -> In x (a :: l).
Proof.
  intros x Hx.
  simpl. now right. 
Qed. 

Lemma aux {A : Type} (l l0 : list A) (R : A -> A -> Prop) (sub : forall x, In x l0 -> In x l) :
  exists a, (forall x, In x l0 -> R x a).
Proof.
Admitted.


Theorem finite_has_max' {A:Type} (R:A->A->Prop) `{part: PartialOrder _ eq R} :
 (exists x:A, forall y:A, R y x) -> (exists x:A, forall y:A, R x y -> x = y)  .
Proof.
  intros [x  H].
  exists x. intros y Hxy.
  specialize (H y).
  now apply antisymmetry. 
Qed.

Theorem finite_has_max {A:Type} {ne : NonEmpty A} {fin:Finite A} (R:A->A->Prop) `{part: PartialOrder _ eq R} :
  exists x:A, forall y:A, R x y -> x = y.
Admitted.

Section order.
  
Open Scope R_scope. 
Context {M : MDP} (γ : R).
Context (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Definition policy_eq (σ τ : state M -> act M) : Prop
  := forall s, (@ltv M γ σ s) = (@ltv M γ τ s).

Global Instance policy_eq_equiv : Equivalence policy_eq.
Proof.
  constructor; repeat red; intros.
  reflexivity.
  now symmetry.
  etransitivity; eauto.
Qed.

Definition policy_le (σ τ : state M -> act M) : Prop
  := forall s, (ltv γ σ s) <= (ltv γ τ s).

Global Instance policy_equiv_sub : subrelation policy_eq policy_le.
Proof.
  unfold policy_eq, policy_le, subrelation; intros.
  specialize (H s); lra.
Qed.

Global Instance Rle_trans : Transitive Rle.
Proof.
  repeat red; intros.
  eapply Rle_trans; eauto.
Qed.

Global Instance policy_le_pre : PreOrder policy_le.
Proof.
  unfold policy_eq, policy_le.
  constructor; red; intros.
  - lra.
  - etransitivity; eauto. 
Qed.

Global Instance policy_le_part : PartialOrder policy_eq policy_le.
Proof.
  unfold policy_eq, policy_le.
  unfold PartialOrder, relation_equivalence, predicate_equivalence, relation_conjunction, Basics.flip, predicate_intersection; simpl.
  intuition.
Qed.

(* Optimal value of an MDP, given a list of policies. 
   Gives for each state the best long-term value that can be obtained for any policy. *)
Definition max_ltv_on (l : list (dec_rule M)) : M.(state) -> R :=
  fun s => Rmax_list (map (fun σ => ltv γ σ s) l).

(* Proceed with the assumption that rewards are bounded for any policy and 
   that the set of actions is finite. *)
Context {D : R}.
Context (fina : Finite M.(act)). 
Context (bdd :  (forall s s': M.(state), forall σ : dec_rule M, Rabs (reward s (σ s) s') <= D)).

Lemma max_ltv_aux1 (l : list (dec_rule M)): 
  forall s : M.(state),
    max_ltv_on l s =
    Rmax_list (map (fun σ => (step_expt_reward σ s) + γ*expt_value (t s (σ s)) (ltv γ σ)) l).
Proof.
  intros s. unfold step_expt_reward. 
  unfold max_ltv_on.
  f_equal. apply List.map_ext.
  intros π.
  eapply ltv_corec ; eauto.
Qed.



Lemma max_ltv_aux2 (l : list (dec_rule M)) :
  exists la : list (act M), 
  forall s : M.(state),
    let Q π := (expt_value (t s (fst π)) (reward s (fst π))) + γ*expt_value (t s (fst π)) (ltv γ (snd π)) in
    Rmax_list (map (fun σ => (step_expt_reward σ s) + γ*expt_value (t s (σ s)) (ltv γ σ)) l) = Rmax_list
        ((map (fun π => Q π)) (list_prod la l)).
Proof.
  destruct fina as [la _].
  exists la. 
  intros s Q. unfold step_expt_reward.
  rewrite <-(@Rmax_list_prod_le (act M) (policy M) (fun a b =>
        expt_value (t s a) (reward s a) +
        γ * expt_value (t s a) (ltv γ b)) la l).
  
End order.
