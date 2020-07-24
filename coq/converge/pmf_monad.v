Require Import Reals Coquelicot.Coquelicot Coquelicot.Series.
Require Import ProofIrrelevance EquivDec.
Require Import Sums.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun seq.
Require Import ExtLib.Structures.Monad ExtLib.Structures.MonadLaws. 

Import MonadNotation. 
Set Bullet Behavior "Strict Subproofs".

(*

****************************************************************************************
This file defines the pmf monad (also called the finitary Giry monad) which is a monad 
of finitely supported probability measures on a set. The construction is very general, 
and we don't need to work in that generality. Our main application is to use this monad 
to define and reason about Markov Decision Processes. 

We also add results on conditional probability and conditional expectation, everything 
tailored to the discrete case. 
****************************************************************************************

 *)

(* Helper lemmas. *)

Fixpoint list_sum (l : list R) : R :=
  match l with
  | nil => 0
  | x :: xs => x + list_sum xs
  end.

Fixpoint list_fst_sum {A : Type} (l : list (nonnegreal*A)): R  :=
  match l with
  | nil => 0
  | (n,_) :: ns => n + list_fst_sum ns                
  end.

Definition list_fst_sum' {A : Type} (l : list (nonnegreal*A)) : R :=
  list_sum (map (fun x => nonneg (fst x)) l).

Lemma list_fst_sum_compat {A : Type} (l : list (nonnegreal*A)) : list_fst_sum l = list_fst_sum' l.
Proof.
  induction l.
  * unfold list_fst_sum' ; simpl ; reflexivity.
  * unfold list_fst_sum'. destruct a. simpl.
    rewrite IHl. f_equal. 
Qed. 

Lemma list_sum_is_nonneg {A : Type} (l : list(nonnegreal*A)) : 0 <= list_fst_sum l. 
Proof.
  induction l.
  simpl ; lra.
  simpl. destruct a as [n].
  assert (0 <= n) by apply (cond_nonneg n).
  apply (Rplus_le_le_0_compat _ _ H).
  lra.
Qed.


Lemma prod_nonnegreal : forall (a b : nonnegreal), 0 <= a*b.
Proof.
  intros (a,ha) (b,hb).
  exact (Rmult_le_pos _ _ ha hb).
Qed.

Lemma div_nonnegreal : forall (a b : nonnegreal), 0 <> b -> 0 <= a/b.
Proof.
  intros (a,ha) (b,hb) Hb.
  apply (Rdiv_le_0_compat).
  apply ha. simpl in *. case hb. 
  trivial. intros H. firstorder.
Qed.

Lemma nonneg_pf_irrel r1 (cond1 cond2:0 <= r1) : 
  mknonnegreal r1 cond1 = mknonnegreal r1 cond2.
Proof.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma nonneg_ext r1 cond1 r2 cond2: 
  r1 = r2 ->
  mknonnegreal r1 cond1 = mknonnegreal r2 cond2.
Proof.
  intros; subst.
  apply nonneg_pf_irrel.
Qed.

Lemma mknonnegreal_assoc (r1 r2 r3 : nonnegreal) :
  mknonnegreal _ (prod_nonnegreal (mknonnegreal _ (prod_nonnegreal r1 r2) ) r3) = mknonnegreal _ (prod_nonnegreal r1 (mknonnegreal _ (prod_nonnegreal r2 r3))).
Proof.
  apply nonneg_ext; simpl.
  lra.
Qed.

Lemma Rone_mult_nonnegreal (r : nonnegreal) (hr : 0 <= R1*r) : mknonnegreal (R1*r) hr = r.
Proof. 
  destruct r as [r hr'].
  simpl. assert (r = R1 * r) by lra.
  simpl in hr. revert hr.
  rewrite <- H. intros.
  f_equal. apply proof_irrelevance.
Qed.

Lemma list_sum_cat (l1 l2 : list R) :
  list_sum (l1 ++ l2) = (list_sum l1) + (list_sum l2).
Proof.
  induction l1.
  * simpl ; nra.
  * simpl.  nra.
Qed.

Lemma list_fst_sum_cat {A : Type} (l1 l2 : list (nonnegreal * A)) :
  list_fst_sum (l1 ++ l2) = (list_fst_sum l1) + (list_fst_sum l2).
Proof.
  induction l1.
  * simpl ; nra.
  * simpl ; destruct a; nra.
Qed.


Definition nonneg_list_sum {A : Type} (l : list (nonnegreal * A)) : nonnegreal
  := {|
  nonneg := list_fst_sum l;
  cond_nonneg := (list_sum_is_nonneg l)
|}.

Section Pmf.
  
(* Defines the record of discrete probability measures on a type. *)
Record Pmf (A : Type) := mkPmf {
  outcomes :> list (nonnegreal * A);
  sum1 : list_fst_sum outcomes = R1
 }.

 Arguments outcomes {_}.
 Arguments sum1 {_}.
 Arguments mkPmf {_}.

Lemma Pmf_ext  {A} (p q : Pmf A)  : outcomes p = outcomes q -> p = q.
Proof.
destruct p as [op sp].
destruct q as [oq sq].
rewrite /outcomes => ?. (* what's happening here? *)
subst. f_equal. apply proof_irrelevance.
Qed.

Lemma sum1_compat {B} (p : Pmf B) :
  list_sum (map (fun y : nonnegreal * B => nonneg (fst y)) (p.(outcomes))) = R1. 
Proof.
  rewrite <- p.(sum1).
  rewrite list_fst_sum_compat.
  unfold list_fst_sum'. reflexivity.
Qed. 


Lemma pure_sum1 {A} (a : A) : list_fst_sum [::(mknonnegreal R1 (Rlt_le _ _ Rlt_0_1),a)] = R1. 
Proof.
  simpl. lra.
Qed.
 

Definition Pmf_pure : forall {A : Type}, A -> Pmf A := fun {A} (a:A) => {|
outcomes := [::(mknonnegreal R1 (Rlt_le _ _ Rlt_0_1),a)];
sum1 := pure_sum1 _
|}.



Fixpoint dist_bind_outcomes
         {A B : Type} (f : A -> Pmf B) (p : list (nonnegreal*A)) : list(nonnegreal*B) :=
  match p with
   | nil => nil
   | (n,a) :: ps =>
     map (fun (py:nonnegreal*B) => (mknonnegreal _ (prod_nonnegreal n py.1),py.2)) (f a).(outcomes) ++ (dist_bind_outcomes f ps)
  end.

Lemma dist_bind_outcomes_cat {A B : Type} (f : A -> Pmf B) (l1 l2 : list(nonnegreal*A)) :
  dist_bind_outcomes f (l1 ++ l2) = (dist_bind_outcomes f l1) ++ (dist_bind_outcomes f l2).
Proof.
  induction l1.
  * simpl; easy.
  * destruct a as [an aa]. simpl.
    rewrite <- catA. rewrite IHl1.
    reflexivity.
Qed.

Lemma list_fst_sum_const_mult {A B : Type} (f : A -> Pmf B) (n : nonnegreal) (a : A):
  list_fst_sum [seq (mknonnegreal _ (prod_nonnegreal n py.1), py.2) | py <- f a]
  = n*list_fst_sum [seq py | py <- f a].
Proof.
  destruct (f a) as [fa Hfa]. simpl. revert Hfa.
  generalize R1 as t. induction fa. 
  * firstorder.
  *
    simpl in *. destruct a0. intros t Htn0.
    rewrite (IHfa (t - n0)).
    specialize (IHfa (t-n0)). firstorder.
    rewrite <- Htn0. lra.
Qed.


Lemma list_fst_sum_const_div {A : Type} (l : list (nonnegreal*A)) {n : nonnegreal} (hn : 0 <> nonneg n) :
  list_fst_sum [seq (mknonnegreal _ (div_nonnegreal py.1 _ hn), py.2) | py <- l]
  = list_fst_sum [seq py | py <- l]/n.
Proof.
  generalize R1 as t. induction l. 
  * simpl. intros H. lra. 
  * simpl in *. destruct a. intros t. simpl. 
    rewrite (IHl (t - n)).
    specialize (IHl (t-n)). simpl. 
    lra.  
Qed.


Lemma dist_bind_sum1 {A B : Type} (f : A -> Pmf B) (p : Pmf A) :
  list_fst_sum (dist_bind_outcomes f p.(outcomes)) = R1.
Proof.
  destruct p as [p Hp]. simpl.
  revert Hp. generalize R1 as t.
  induction p.
 *  simpl; intuition. 
 *  simpl in *. destruct a as [n a]. intros t0 Hnt0.
    rewrite list_fst_sum_cat.  rewrite (IHp (t0-n)). 
    rewrite list_fst_sum_const_mult. destruct (f a) as [fp Hfp]. simpl.
    rewrite map_id Hfp. lra.
    lra.
Qed.

Lemma dist_bind_sum1_compat {A B : Type} (f : A -> Pmf B) (p : Pmf A) :
  list_fst_sum' (dist_bind_outcomes f p.(outcomes)) = R1.
Proof.
  rewrite <-list_fst_sum_compat. apply dist_bind_sum1.
Qed.



Definition Pmf_bind {A B : Type} (p : Pmf A) (f : A -> Pmf B)  : Pmf B :={|
  outcomes := dist_bind_outcomes f p.(outcomes);
  sum1 := dist_bind_sum1 f p
  |}.

Global Instance Monad_Pmf : Monad Pmf := {|
  ret := @Pmf_pure;
  bind := @Pmf_bind;
|}.


Open Scope monad_scope.


(*We can use the nice bind and return syntax, since Pmf is now part of the Monad typeclass.

Variable (A B : Type).
Variable (p : Pmf A).
Variable (b : B).
Variable (f g : A -> Pmf B). 
Check (p >>= f).*)


Lemma Pmf_ret_of_bind {A : Type} (p : Pmf A) : p >>= (fun a => ret a) = p.
Proof.
  apply Pmf_ext ; simpl.
  induction p.(outcomes). 
  simpl. reflexivity.
  simpl. destruct a. rewrite IHl. 
  f_equal. f_equal.
  destruct n.  apply nonneg_ext.
  apply Rmult_1_r. 
Qed.

Lemma Pmf_bind_of_ret {A B : Type} (a : A) (f : A -> Pmf B) : (ret a) >>= f = f a.
Proof.
  apply Pmf_ext.
  simpl. rewrite cats0.
  rewrite <- map_id. apply eq_map.
  intros (n,b). simpl.
  now rewrite Rone_mult_nonnegreal.
Qed.

Lemma Pmf_bind_of_bind {A B C : Type} (p : Pmf A) (f : A -> Pmf B) (g : B -> Pmf C) :
  (p >>= f) >>= g = p >>= (fun a => (f a) >>= g).
Proof.
  apply Pmf_ext.
  destruct p as [pout Hp].
  revert Hp. simpl. generalize R1 as t.
  induction pout.
  * simpl ; easy.
  * simpl. destruct a as [an aa].
    intros t Ht. rewrite dist_bind_outcomes_cat. simpl.
    rewrite <- (IHpout (t-an)). 
    destruct (f aa) as [faa Hfaa]. f_equal.
    revert Hfaa. simpl. generalize R1 as u.
    induction faa.
    - simpl. reflexivity.
    - destruct a as [an1 aa1].
      simpl. intros u Hu. rewrite map_cat.
      rewrite (IHfaa (u-an1)); clear IHfaa. f_equal. rewrite <- map_comp.
      unfold comp. simpl.
      apply List.map_ext; intros.
      f_equal.
      apply nonneg_ext. apply Rmult_assoc.
      lra.
    -
      lra.
Qed.

Global Instance Pmf_MonadLaws : MonadLaws Monad_Pmf := {|
  bind_of_return := @Pmf_bind_of_ret;
  bind_associativity := @Pmf_bind_of_bind;
|}.


(*Lemma Pmf_bind_comm {A B C : Type} (p : Pmf A) (q : Pmf B) (f : A -> B -> Pmf C) :
  Pmf_bind p (fun a => Pmf_bind q (f a)) = Pmf_bind q (fun b => Pmf_bind p (fun a => f a b)).
Proof.
  apply Pmf_ext ; simpl.
  revert q.
  induction p.(outcomes).
  simpl. intros q. induction q.(outcomes). simpl. reflexivity.
  simpl. rewrite <-IHl. destruct a. 
Admitted.*)


End Pmf.


Definition prob {A : Type} (l : seq(nonnegreal*A)) : nonnegreal :=
 mknonnegreal (list_fst_sum l) (list_sum_is_nonneg _).

Notation "𝕡[ x ]" := (nonneg (prob x)) (at level 75, right associativity).

Section expected_value.

Open Scope fun_scope. 
Arguments outcomes {_}. 

(* TODO(Kody): Notation 𝔼_{} [ _ ] to make this nicer? *)

Definition expt_value {A : Type} (p : Pmf A) (f : A -> R): R :=
  list_sum (map (fun x => (f x.2) * nonneg x.1) p.(outcomes)).

Lemma expt_value_zero {A : Type} (p : Pmf A) :
  expt_value p (fun a => 0) = 0.
Proof.
  unfold expt_value. 
  induction p.(outcomes).
  - simpl;lra.
  - simpl. rewrite IHl. lra.
Qed. 
    
Lemma expt_value_const_mul {A : Type} (p : Pmf A) (f : A -> R) (c : R):
  expt_value p (fun a => c * (f a)) = c * expt_value p (fun a => f a).
Proof. 
  unfold expt_value.
  induction p.(outcomes).
  simpl ; lra.
  simpl. rewrite IHl. lra. 
Qed.

Lemma expt_value_add {A : Type} (p : Pmf A) (f1 f2 : A -> R) :
  expt_value p (fun x => f1 x + f2 x) = (expt_value p f1) + (expt_value p f2).
Proof.
  unfold expt_value.
  induction p.(outcomes).
  * simpl ; lra.
  * simpl. rewrite IHl. lra. 
Qed.

Lemma expt_value_sub {A : Type} (p : Pmf A) (f1 f2 : A -> R) :
  expt_value p (fun x => f1 x - f2 x) = (expt_value p f1) - (expt_value p f2).
Proof.
  unfold expt_value.
  induction p.(outcomes).
  * simpl ; lra.
  * simpl. rewrite IHl. lra. 
Qed.



Lemma expt_value_le {A : Type} (p : Pmf A) (f1 f2 : A -> R) :
  (forall a : A, f1 a <= f2 a) -> expt_value p f1 <= expt_value p f2.
Proof.
  intros Hf1f2. unfold expt_value. 
  induction p.(outcomes). 
  * simpl ; lra.
  * simpl. enough (f1 a.2 * a.1 <= f2 a.2 * a.1). 
    apply (Rplus_le_compat _ _ _ _ H IHl).
    apply Rmult_le_compat_r. apply cond_nonneg. 
    exact (Hf1f2 a.2).
Qed.


Lemma expt_value_sum_f_R0 {A : Type} (p : Pmf A) (f : nat -> A -> R) (N : nat) :
  expt_value p (fun a => sum_f_R0 (fun n => f n a) N) = sum_f_R0 (fun n => expt_value p (f n)) N.
Proof.
  unfold expt_value.
  induction p.(outcomes).
  * simpl. now rewrite sum_eq_R0.
  * simpl. rewrite IHl. rewrite sum_plus. f_equal.
    destruct a. simpl. rewrite <- scal_sum. apply Rmult_comm.
Qed.

Lemma sum_f_R0_Rabs_Series_aux_1 {A : Type} (p : Pmf A) (f : nat -> A -> R) (N : nat):
  sum_f_R0 (fun n => expt_value p (fun a => f n a)) N <= Rabs (sum_f_R0 (fun n => expt_value p (fun a => f n a)) N).
Proof.
  apply Rle_abs. 
Qed.

Lemma sum_f_R0_Rabs_Series_aux_2 {A : Type} (p : Pmf A) (f : nat -> A -> R) (N : nat):
  Rabs (sum_f_R0 (fun n => expt_value p (fun a => f n a)) N) <= sum_f_R0 (fun n => Rabs (expt_value p (fun a => f n a))) N.
Proof.
  apply Rabs_triang_gen. 
Qed.

Lemma expt_value_Rabs_Rle {A : Type} (p : Pmf A) (f : A -> R):
  Rabs (expt_value p f) <= expt_value p (fun a => Rabs (f a)).
Proof.
  unfold expt_value.
  induction p.(outcomes).
  * simpl. rewrite Rabs_R0 ; lra.
  * simpl. refine (Rle_trans _ _ _ _ _). 
    apply Rabs_triang. rewrite Rabs_mult. 
    rewrite (Rabs_pos_eq a.1). apply Rplus_le_compat.
    apply Rmult_le_compat_r. apply cond_nonneg. now right.
    apply IHl. apply cond_nonneg.
Qed.


Lemma ex_series_le_Reals
     : forall (a : nat -> R) (b : nat -> R),
    (forall n : nat, Rabs (a n) <= b n) -> ex_series b -> ex_series a.
Proof.
  intros a b Hab Hexb.  
  apply (@ex_series_le _ _ a b).
  now apply Hab. assumption.
Qed.


Lemma expt_value_ex_series {A : Type} (p : Pmf A) (f : nat -> A -> R) :
  ex_series (fun n => expt_value p (fun a => Rabs (f n a))) ->
         ex_series (fun n => expt_value p (f n)).
Proof.
  intros Hex.
  refine (@ex_series_le_Reals _ _ _ _).
  intros n. apply expt_value_Rabs_Rle.  
  assumption.
Qed. 

Lemma expt_val_bdd_aux {A : Type} (g : nat -> A -> R) (p : Pmf A):
  (forall (a : A), is_lim_seq (fun n => g n a) 0) -> is_lim_seq (fun n => expt_value p (fun x => g n x)) 0.
Proof.
  intros H. 
  unfold expt_value. rewrite is_lim_seq_Reals.
  unfold Un_cv. 
  induction p.(outcomes). 
  * simpl. intros eps0 H0. exists 0%nat.  rewrite R_dist_eq. intros n Hn. apply H0. 
  * simpl in *. intros eps0 H0.
    enough (H0': eps0/4 > 0). 
    specialize (IHl (eps0/4)%R H0').  destruct IHl as [N0 HN0].
    specialize (H a.2).
    revert H. rewrite is_lim_seq_Reals.
    intros H. unfold Un_cv in H.
    set (Ha := cond_nonneg a.1). case Ha.
    intro Ha1. clear Ha.
    enough (H1': eps0/(4 * a.1) > 0). 
    specialize (H (eps0/(4 * a.1))%R H1').
    destruct H as [N1 HN1].
    exists (N0 + N1)%nat. intros n Hn.
    specialize (HN0 n).
    specialize (HN1 n). 
    assert (Hn0 : (n >= N0)%nat) by firstorder.
    assert (Hn1 : (n >= N1)%nat) by firstorder. 
    specialize (HN1 Hn1). specialize (HN0 Hn0).
    clear Hn0 ; clear Hn1.
    revert HN0. revert HN1. 
    unfold R_dist. rewrite Rminus_0_r ; rewrite Rminus_0_r ; rewrite Rminus_0_r.
    intros HN0 HN1. refine (Rle_lt_trans _ _ _ _ _).
    apply Rabs_triang. rewrite Rabs_mult. rewrite (Rabs_pos_eq a.1).
    eapply Rlt_trans. 
    assert ((eps0 / (4 * a.1))*a.1 + (eps0 / 4) = eps0/2). field ; lra.
    assert (Rabs (g n a.2) * a.1 + Rabs (list_sum [seq g n x.2 * nonneg (x.1) | x <- l])  < eps0/2).
    rewrite <-H. 
    refine (Rplus_lt_compat _ _ _ _ _ _).
    now apply Rmult_lt_compat_r. assumption. 
    apply H1. lra.
    now left. apply Rlt_gt. apply RIneq.Rdiv_lt_0_compat. assumption.
    lra. 
    intros Ha1. rewrite <-Ha1. setoid_rewrite Rmult_0_r. 
    setoid_rewrite Rplus_0_l. exists N0. intros n Hn. 
    eapply Rlt_trans. specialize (HN0 n Hn). apply HN0. 
    lra. lra. 
Qed. 

Lemma expt_value_Series {A : Type} (p : Pmf A) (f : nat -> A -> R) :
  (forall a:A, ex_series (fun n => f n a)) ->
         expt_value p (fun a => Series (fun n => f n a)) = Series (fun n => expt_value p (f n)).
Proof.
  intros Hex. 
  symmetry. 
  apply is_series_unique.   
  rewrite is_series_Reals. 
  unfold infinite_sum.
  intros eps Heps. 
  setoid_rewrite <- expt_value_sum_f_R0.
  unfold R_dist. unfold Series. setoid_rewrite <-expt_value_sub.
  assert (Ha : forall a:A, is_series (fun n => f n a) (Series (fun n => f n a)) ).
  intros a. eapply (Series_correct _). apply (Hex a).
  assert (Hinf : forall a:A, infinite_sum (fun n => f n a) (Series (fun n => f n a)) ).
  intros a. rewrite <- is_series_Reals. apply Ha. clear Ha.
  unfold infinite_sum in Hinf. unfold Series in Hinf. unfold R_dist in Hinf.
  assert (H : forall x, Rabs x = R_dist x 0). intros x. unfold R_dist. f_equal ; lra. 
  setoid_rewrite H. 
  setoid_rewrite H in Hinf.
  set (He := @expt_val_bdd_aux A).
  setoid_rewrite is_lim_seq_Reals in He. 
  unfold Un_cv in He. apply He. apply Hinf. assumption. 
Qed. 

Lemma expt_value_pure {A : Type} (a : A) (f : A -> R) :
  expt_value (Pmf_pure a) f = f a.
Proof. 
  unfold expt_value ; unfold Pmf_pure ; simpl. 
  lra.
Qed. 


Lemma expt_value_Series_aux_2 {A : Type} (p : Pmf A) (f : nat -> A -> R) (N : nat):
  expt_value p (fun a => sum_f_R0 (fun n => f n a) N) <= expt_value p (fun a => sum_f_R0 (fun n => Rabs (f n a)) N).
Proof. 
  apply expt_value_le. 
  intros a. induction N. 
  * simpl. apply Rle_abs. 
  * simpl. apply Rplus_le_compat ; try assumption. 
    apply Rle_abs.
Qed.

Lemma expt_value_bind_aux {A B : Type} (p : Pmf A) (g : A -> Pmf B) (f : B -> R) (n : nonnegreal) :
forall a : A,  list_sum [seq (f x.2) * nonneg(x.1) * n | x <- (g a).(outcomes)] = list_sum [seq (f x.2) * nonneg(x.1) | x <- (g a).(outcomes)] * n. 
Proof.
  intros a. 
  induction (g a).(outcomes).
  * simpl ; lra. 
  * rewrite map_cons. simpl. rewrite IHl. lra. 
Qed.

Lemma expt_value_bind {A B : Type} (p : Pmf A) (g : A -> Pmf B) (f : B -> R) :
  expt_value (Pmf_bind p g) f = expt_value p (fun a => expt_value (g a) f).
Proof.
  unfold Pmf_bind.
  unfold expt_value. simpl. 
  induction (p.(outcomes)).
  * simpl ; reflexivity.
  * destruct a. simpl. rewrite <-IHl. rewrite map_cat.
    rewrite list_sum_cat. f_equal. 
    rewrite <-map_comp. rewrite <- (expt_value_bind_aux p). 
    f_equal. apply List.map_ext.
    intros a0. simpl. lra.
Qed.

Lemma expt_value_bind' {A B : Type} (p : Pmf A) (g : A -> Pmf B) (f : A -> B -> R) :
 forall init:A, expt_value (Pmf_bind p g) (f init) = expt_value p (fun a => expt_value (g a) (f init)).
Proof.
  intros init. 
  unfold Pmf_bind.
  unfold expt_value. simpl. 
  induction (p.(outcomes)).
  * simpl ; reflexivity.
  * destruct a. simpl. rewrite <-IHl. rewrite map_cat.
    rewrite list_sum_cat. f_equal. 
    rewrite <-map_comp. rewrite <- (expt_value_bind_aux p). 
    f_equal. apply List.map_ext.
    intros a0. simpl. lra.
Qed.

Lemma expt_value_bind_ret {A B : Type} (a : A) (g : A -> Pmf B) (f : B -> R) :
  expt_value (Pmf_bind (Pmf_pure a) g) f = expt_value (g a) f.
Proof.   
  rewrite expt_value_bind. 
  rewrite expt_value_pure.
  reflexivity.
Qed.

Lemma expt_value_expt_value {A : Type} (p q : Pmf A) (f : A -> R) :
  expt_value p (fun a => expt_value q f) = (expt_value q f)*(expt_value p (fun a => 1)).
Proof.
  unfold expt_value. 
  induction p.(outcomes).
  simpl ; lra.
  simpl. rewrite IHl. lra.
Qed.

Lemma expt_value_expt_value_pure {A : Type} (a : A) (p : Pmf A) (f : A -> R):
  expt_value p (fun a => expt_value (Pmf_pure a) f) = (expt_value p f).
Proof.
  f_equal. apply functional_extensionality. intros x. 
  now rewrite expt_value_pure.
Qed.

Lemma expt_value_Rle {A : Type} {D : R} {f : A -> R} (hf : forall a:A, Rabs (f a) <= D) (p : Pmf A) :
  Rabs(expt_value p f) <= D.
Proof.
  eapply Rle_trans. 
  apply expt_value_Rabs_Rle.
  unfold expt_value. rewrite <- Rmult_1_r.
  change (D*1) with (D*R1).  rewrite <- (sum1_compat p). 
  induction p.(outcomes).
  * simpl ; lra.
  * simpl in *. rewrite Rmult_plus_distr_l.
    assert ( Rabs (f a.2) * a.1  <=  D * a.1). apply Rmult_le_compat_r. apply cond_nonneg.
    refine (Rle_trans _ _ _ _ _).
    apply Rle_abs. rewrite Rabs_Rabsolu. 
    apply hf.
    refine (Rle_trans _ _ _ _ _).
    apply Rplus_le_compat.
    apply Rmult_le_compat_r. 
    apply cond_nonneg. apply hf. apply IHl.
    now right.
Qed.


End expected_value. 

Section events.

Arguments outcomes {_}.
    
Instance EqDecR : EqDec R eq := Req_EM_T. 

(* All p.(outcomes) which are preimages of a fixed r in R under the random variable g. *)
Definition preim_outcomes_of {A : Type} (p : Pmf A) (g : A -> R) (r : R) :=
  filter (fun x => (g x.2 ==b r)) p.(outcomes).

Definition preim_outcomes_of_And {A : Type} (p : Pmf A) (f g: A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2 ==b r1) (g x.2 ==b r2)) p.(outcomes).

Definition independent {A : Type} (p : Pmf A) (f g : A -> R):=
  forall r1 r2 : R, 𝕡[preim_outcomes_of_And p f g r1 r2] = 𝕡[preim_outcomes_of p f r1]*𝕡[preim_outcomes_of p g r2].


Lemma filter_true {A} :  forall p:list A, filter (fun _ => true) p = p.
Proof.
  induction p.
    - simpl; reflexivity.
    - simpl. rewrite IHp. reflexivity.
Qed.

Lemma filter_false {A} :  forall p:list A, filter (fun _ => false) p = [::].
Proof.
  induction p.
    - simpl; reflexivity.
    - simpl. rewrite IHp. reflexivity.
Qed.

Lemma independent_const_fun {A : Type} (p : Pmf A) (g : A -> R) (c : R) : 
  independent p (fun _ => c) g.
Proof.
  unfold independent.
  intros r1 r2. 
  unfold prob,preim_outcomes_of,preim_outcomes_of_And ; simpl.
  unfold equiv_decb. destruct (equiv_dec c r1).
  + simpl. 
    enough (filter (fun _ => true) p = p). 
    rewrite H. destruct p as [s0 s1]. rewrite s1 ; lra.
    induction p.(outcomes).
    - simpl; reflexivity.
    - simpl. rewrite IHl. reflexivity.
  + simpl.
    enough (filter (fun _ => false) p = [::]). 
    rewrite H. simpl;lra. 
    induction p.(outcomes).
    - simpl;reflexivity.
    - simpl; assumption.
Qed.


(* A ∩ Ω = A *)
Lemma prim_outcomes_of_And_cancel {A : Type} (p : Pmf A) (g : A -> R) (r1 r2 : R) :
  preim_outcomes_of_And p (fun _ => r1) g r1 r2 =  preim_outcomes_of p g r2.
Proof.
  unfold preim_outcomes_of, preim_outcomes_of_And.
  unfold equiv_decb. destruct (equiv_dec r1 r1); [| congruence].
  simpl. reflexivity.
Qed.

        

Lemma tot_prob_eq_prob_of {A : Type} (p : Pmf A) (g : A -> R) (r1 r2 : R) :
   𝕡[preim_outcomes_of_And p (fun _ => r1) g r1 r2] =  𝕡[preim_outcomes_of p g r2].
Proof.
  rewrite prim_outcomes_of_And_cancel. reflexivity.
Qed.


Lemma tot_prob_eq_prob_of_const_fun
  {A : Type} {p : Pmf A} {g : A -> R} {r : R} (hne : 0 <> 𝕡[preim_outcomes_of p g r]) (r1 : R):
  list_fst_sum [seq py | py <- preim_outcomes_of_And p (fun _ => r1) g r1 r] =  𝕡[preim_outcomes_of p g r].
Proof.
  unfold prob,preim_outcomes_of,preim_outcomes_of_And.
  simpl.
  f_equal.
  induction p.(outcomes).
  - simpl. reflexivity.
  - simpl. rewrite <-IHl. 
    unfold equiv_decb. destruct (equiv_dec r1 r1); [| congruence].
    destruct equiv_dec. reflexivity.
    simpl. reflexivity.
Qed.


End events.

Section cond_prob.
(*
 This section defines conditional probabilities. The formulation is slightly awkward, since 
 we deal only with random variables and not sets, as is done classically. The reason for this is that 
 we started out with the definition of Pmf as a list of events, paired with probabilities which sum to
 1. So the events are given to us a priori, and we have to make use of them. 

 Sets (events) of the underlying space are now defined as preimages of real random variables. For 
 example, to talk of the universal set Ω, we fix a real number r and work with it's preimage under 
 the constant function (fun _ => r). 
*)
Arguments outcomes {_}.

(* Assigning the actual probability weights to events. We divide by the total probability that g=r2.*)
Definition cond_prob_outcomes
           {A : Type} {p : Pmf A} {g : A -> R} {r2 : R} (hne : 0 <> 𝕡[preim_outcomes_of p g r2])
           (f : A -> R) (r1 : R) : seq (nonnegreal*A) :=
map
(fun y : nonnegreal*A => (mknonnegreal (y.1 / 𝕡[preim_outcomes_of p g r2]) (div_nonnegreal _ _ hne), y.2))
(preim_outcomes_of_And p f g r1 r2).


Lemma cond_prob_sum1 {A : Type} {p : Pmf A} {g : A -> R} {r : R} (hne : 0 <> 𝕡[preim_outcomes_of p g r])
   :
  𝕡[cond_prob_outcomes hne (fun _ => r) r] = 1.
Proof.
  unfold cond_prob_outcomes,prob ; simpl. 
  simpl. 
  rewrite (list_fst_sum_const_div (preim_outcomes_of_And p (fun _ => r) g r r) hne). 
  rewrite (tot_prob_eq_prob_of_const_fun hne r).  
  field. firstorder.
Qed. 


(* 
   Conditional probability measure. Depends on a random variable, a real number and 
   a proof that the random variable attains that value almost surely. 
*)
Definition Pmf_cond {A : Type} {p : Pmf A} {r : R} {g : A -> R} (hne : 0 <> 𝕡[preim_outcomes_of p g r])
  : Pmf A :={|
  outcomes := cond_prob_outcomes hne (fun _ => r) r;
  sum1 := cond_prob_sum1 hne
  |}.

(* Conditional expectation of f given that g(a) = r. *)
Definition cond_expt_value{A : Type}{r : R} {g : A -> R}{p : Pmf A} (hne : 0 <> 𝕡[preim_outcomes_of p g r])(f : A -> R)  : R :=
  let p:= cond_prob_outcomes hne f r in
  list_sum [seq f x.2 * nonneg (x.1) | x <- p].

Lemma list_sum_const_div {A:Type}{n : nonnegreal} (hne : 0 <> nonneg n)
      (l : seq(nonnegreal*A))(f : A -> R) :
      list_sum [seq f x.2 * (nonneg(x.1) / nonneg(n)) | x <- l] = list_sum [seq (f x.2 * nonneg (x.1)) | x <- l]/nonneg(n).
Proof.
  induction l. 
  simpl. lra.
  simpl. rewrite IHl. lra.
Qed.



Lemma list_sum_outcomes_And {A : Type} {f g : A -> R} (r: R) (p : Pmf A) (hfg : independent p f g) :
   list_sum [seq f x.2 *nonneg(x.1) | x <- preim_outcomes_of_And p f g r r] = r*list_fst_sum (preim_outcomes_of_And p f g r r).
Proof.
rewrite list_fst_sum_compat. unfold list_fst_sum'.
unfold preim_outcomes_of, preim_outcomes_of_And in *.
unfold prob in hfg. simpl in *. 
revert hfg. induction p.(outcomes).
- simpl ; lra.
- simpl. intro Hi.  specialize (IHl Hi). unfold equiv_decb. destruct (equiv_dec (f a.2) r).
  unfold equiv_decb. destruct (equiv_dec (g a.2) r). destruct a as [n a0]. simpl.
  rewrite IHl. simpl in e. rewrite e. rewrite Rmult_plus_distr_l. reflexivity.
  simpl. rewrite IHl. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma cond_expt_value_indep
{A : Type} {r : R} {f g : A -> R} {p : Pmf A}(hne : 0 <> 𝕡[preim_outcomes_of p g r]) (Hi : independent p f g) :
cond_expt_value hne f = r*expt_value p f.
Proof.
  unfold cond_expt_value, expt_value, Pmf_cond; simpl.
  unfold independent in Hi. unfold cond_prob_outcomes.
  rewrite <-map_comp. unfold comp; simpl.
  rewrite (list_sum_const_div hne (preim_outcomes_of_And p f g r r) f).
  unfold prob in *. simpl in *.
  specialize (Hi r r).
  rewrite list_fst_sum_compat. unfold list_fst_sum'.
  rewrite list_fst_sum_compat in Hi.   rewrite list_fst_sum_compat in Hi. 
  rewrite list_fst_sum_compat in Hi. unfold list_fst_sum' in Hi. 
  unfold preim_outcomes_of_And. 
  Admitted.

  
         
(* Lemma cond_expt_value_const_fun  {A : Type}{r : R} {g : A -> R}{p : Pmf A}(hne : 0 <> nonneg(prob_of p g r)) (f : A -> R)  :
  cond_expt_value hne f = expt_value p f. 
Proof.
  unfold cond_expt_value; unfold expt_value.
  f_equal. f_equal.
  induction p.(outcomes). 
  - simpl ; reflexivity.
  - simpl. rewrite IHl.
  unfold equiv_decb. destruct (equiv_dec r r); [ | congruence].
  reflexivity. 
Qed. *)



End cond_prob. 
