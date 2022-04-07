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

  Definition independent_sa_collection {Idx} (doms:Idx->SigmaAlgebra Ts) {sub:IsSubAlgebras dom doms}
    := 
    forall (l:forall n, event (doms n)),
      independent_event_collection prts (fun n => event_sa_sub (sub n) (l n)).
  
  Definition pairwise_independent_sa_collection {Idx} (doms:Idx->SigmaAlgebra Ts) {sub:IsSubAlgebras dom doms}
    := forall (l:forall n, event (doms n)),
      pairwise_independent_event_collection prts (fun n => event_sa_sub (sub n) (l n)).

  Lemma independent_sas_proper
        {dom1} (sub1:sa_sub dom1 dom)
        {dom1'} (sub1':sa_sub dom1' dom)
        (eqq1:sa_equiv dom1 dom1')
        {dom2} (sub2:sa_sub dom2 dom)
        {dom2'} (sub2':sa_sub dom2' dom) 
        (eqq2:sa_equiv dom2 dom2') :
    independent_sas sub1 sub2 <-> independent_sas sub1' sub2'.
  Proof.
    split; intros HH A B.
    - red in HH.
      destruct (eqq1 A).
      destruct (eqq2 B).
      generalize (HH (exist _ _ (H0 (proj2_sig A)))
                     (exist _ _ (H2 (proj2_sig B)))).
      now apply independent_events_proper; intros ?; simpl.
    - red in HH.
      destruct (eqq1 A).
      destruct (eqq2 B).
      generalize (HH (exist _ _ (H (proj2_sig A)))
                     (exist _ _ (H1 (proj2_sig B)))).
      now apply independent_events_proper; intros ?; simpl.
  Qed.      

  Lemma independent_sa_collection_proper {Idx}
        (doms:Idx->SigmaAlgebra Ts) {sub:IsSubAlgebras dom doms}
        (doms':Idx->SigmaAlgebra Ts) {sub':IsSubAlgebras dom doms'}
    (eqq:pointwise_relation _ sa_equiv doms doms') :
    independent_sa_collection doms <-> independent_sa_collection doms'.
  Proof.
    split; intros HH l.
    - generalize (HH (fun n => exist _ _ (proj2 (eqq n _) (proj2_sig (l n))))).
      now apply independent_event_collection_proper; intros ??; simpl.
    - generalize (HH (fun n => exist _ _ (proj1 (eqq n _) (proj2_sig (l n))))).
      now apply independent_event_collection_proper; intros ??; simpl.
  Qed.

    Lemma pairwise_independent_sa_collection_proper {Idx}
        (doms:Idx->SigmaAlgebra Ts) {sub:IsSubAlgebras dom doms}
        (doms':Idx->SigmaAlgebra Ts) {sub':IsSubAlgebras dom doms'}
    (eqq:pointwise_relation _ sa_equiv doms doms') :
    pairwise_independent_sa_collection doms <-> pairwise_independent_sa_collection doms'.
  Proof.
    split; intros HH l.
    - generalize (HH (fun n => exist _ _ (proj2 (eqq n _) (proj2_sig (l n))))).
      now apply pairwise_independent_event_collection_proper; intros ??; simpl.
    - generalize (HH (fun n => exist _ _ (proj1 (eqq n _) (proj2_sig (l n))))).
      now apply pairwise_independent_event_collection_proper; intros ??; simpl.
  Qed.

End sigma_indep.

  

