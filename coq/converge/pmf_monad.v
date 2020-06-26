Require Import Reals Coquelicot.Coquelicot Sums.
Require Import Fourier FunctionalExtensionality Psatz ProofIrrelevance.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.


Set Bullet Behavior "Strict Subproofs".


(*

****************************************************************************************
This file defines the pmf monad (also called the finitary Giry monad) which is a monad 
of finitely supported probability measures on a set. The construction is very general, 
and we don't need to work in that generality. We instead work with a finite state space, 
since that is what we will use in our construction of MDPs. 
****************************************************************************************

 *)

Check finset.
Check powerset.
Check cond_pos.

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


Definition nonneg_list_sum {A : Type} (l : list (nonnegreal * A)) : nonnegreal
  := {|
  nonneg := list_fst_sum l;
  cond_nonneg := (list_sum_is_nonneg l)
|}.
                                                                         
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


Lemma pure_sum1 {A} (a : A) : list_fst_sum [:: ({| nonneg := R1; cond_nonneg := Rlt_le 0 1 Rlt_0_1 |}, a)] = R1. 
Proof.
  simpl. nra.
Qed.

Definition Pmf_pure {A} (a : A) : Pmf A := {|
outcomes := [::(mknonnegreal R1 (Rlt_le _ _ Rlt_0_1),a)];
sum1 := pure_sum1 _
|}.


Fixpoint dist_bind_outcomes
         {A B : Type} (f : A -> list(nonnegreal*B)) (p : list (nonnegreal*A)) : list(R*B) :=
  match p with
   | nil => nil
   | (n,a) :: ps => map (fun (py:nonnegreal*B) => (n*py.1,py.2)) (f a) ++ (dist_bind_outcomes f ps)
  end.
