Require Import Reals Coquelicot.Coquelicot.
Require Import ProofIrrelevance.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
Require Import ExtLib.Structures.Monad.

Import MonadNotation. 
Set Bullet Behavior "Strict Subproofs".

Set Universe Polymorphism.

(*

****************************************************************************************
This file defines the pmf monad (also called the finitary Giry monad) which is a monad 
of finitely supported probability measures on a set. The construction is very general, 
and we don't need to work in that generality. Our main application is to use this monad 
to define and reason about Markov Decision Processes. 
****************************************************************************************

 *)

(* Helper lemmas. *)

Fixpoint list_fst_sum {A : Type} (l : list (nonnegreal*A)): R  :=
  match l with
  | nil => 0
  | (n,_) :: ns => n + list_fst_sum ns                
  end.

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


Lemma list_sum_cat {A : Type} (l1 l2 : list (nonnegreal * A)) :
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

Lemma list_fst_sum_eq {A B : Type} (f : A -> Pmf B) (n : nonnegreal) (a : A):
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


Lemma dist_bind_sum1 {A B : Type} (f : A -> Pmf B) (p : Pmf A) :
  list_fst_sum (dist_bind_outcomes f p.(outcomes)) = R1.
Proof.
  destruct p as [p Hp]. simpl.
  revert Hp. generalize R1 as t.
  induction p.
 *  simpl; intuition. 
 *  simpl in *. destruct a as [n a]. intros t0 Hnt0.
    rewrite list_sum_cat.  rewrite (IHp (t0-n)). 
    rewrite list_fst_sum_eq. destruct (f a) as [fp Hfp]. simpl.
    rewrite map_id Hfp. lra.
    lra.
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

(*
We can use the nice bind and return syntax, since Pmf is now part of the Monad typeclass. 

Variable (A B : Type).
Variable (p : Pmf A).
Variable (f g : A -> Pmf B). 
Check (p >>= f).
*)


Lemma Pmf_bind_of_ret {A B : Type} (a : A) (f : A -> Pmf B) : (ret a) >>= f = f a.
Proof.
  apply Pmf_ext.
  simpl. rewrite cats0.
  rewrite <- map_id. apply eq_map.
  assert (forall a : nonnegreal, R1 * a = a). intros a0 ; lra.
  intros py. destruct py. simpl. f_equal.
  destruct n. simpl.
Admitted.

  
End Pmf.
