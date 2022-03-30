Require Import Program.Basics.
Require Import Coq.Reals.Rbase.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.

Require Import Classical ClassicalFacts.

Require Import utils.Utils.
Import ListNotations.
Require Export Event ProbSpace SigmaAlgebras.

Set Bullet Behavior "Strict Subproofs".

Section sigma_indep.
  
  Local Open Scope R.
  Local Open Scope prob.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom).

  Definition independent_sas {dom1} (sub1:sa_sub dom1 dom) {dom2} (sub2:sa_sub dom2 dom) 
    := forall (A:event dom1) (B:event dom2),
      independent_events prts (event_sa_sub sub1 A) (event_sa_sub sub2 B).

  Definition independent_sa_collection (doms:nat->SigmaAlgebra Ts) {sub:IsSubAlgebras dom doms}
    := 
    forall (l:forall n, event (doms n)),
      independent_event_collection prts (fun n => event_sa_sub (sub n) (l n)).
  
  Definition pairwise_independent_sa_collection (doms:nat->SigmaAlgebra Ts) {sub:IsSubAlgebras dom doms}
    := forall (l:forall n, event (doms n)),
      pairwise_independent_event_collection prts (fun n => event_sa_sub (sub n) (l n)).

End sigma_indep.

  

