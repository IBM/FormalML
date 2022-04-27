Require Import Program.Basics.
Require Import Coq.Reals.Rbase.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.

Require Import Classical ClassicalFacts.

Require Import utils.Utils.
Import ListNotations.
Require Export Event ProbSpace SigmaAlgebras.

Require Import Dynkin.

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

  Definition independent_eventcoll (dom1 : pre_event Ts -> Prop) (dom2 : pre_event Ts -> Prop)
    := forall (A:event dom) (B:event dom),
      dom1 A -> dom2 B ->
      independent_events prts A B.
  
  Lemma independent_sas_eventcoll {dom1} (sub1:sa_sub dom1 dom) {dom2} (sub2:sa_sub dom2 dom) :
    independent_sas sub1 sub2 <-> independent_eventcoll (@sa_sigma _ dom1) (@sa_sigma _ dom2).
  Proof.
    split; intros HH A B.
    - intros.
      specialize (HH (exist _ _ H) (exist _ _ H0)).
      revert HH.
      apply independent_events_proper
      ; now intros ?; simpl.
    - apply HH.
      + now destruct A; simpl.
      + now destruct B; simpl.
  Qed.
    
  Lemma independent_eventcoll_union (dom1 dom2 dom3: pre_event Ts -> Prop) :
    independent_eventcoll dom1 dom3 ->
    independent_eventcoll dom2 dom3 ->
    independent_eventcoll (pre_event_union dom1 dom2) dom3.
  Proof.
    intros.
    now intros A B [C|C]; [apply H | apply H0].
  Qed.

  Lemma independent_eventcoll_inter_l (dom1 dom2 dom3: pre_event Ts -> Prop) :
    independent_eventcoll dom1 dom3 ->
    independent_eventcoll (pre_event_inter dom1 dom2) dom3.
  Proof.
    intros.
    intros A B [C1 C2] ?.
    now apply H.
  Qed.

  Lemma independent_eventcoll_inter_r (dom1 dom2 dom3: pre_event Ts -> Prop) :
    independent_eventcoll dom2 dom3 ->
    independent_eventcoll (pre_event_inter dom1 dom2) dom3.
  Proof.
    intros.
    intros A B [C1 C2] ?.
    now apply H.
  Qed.

  Definition independent_eventcoll_class domr : (pre_event Ts) -> Prop
    := fun x => exists pf,
         forall y, domr y ->
              independent_events prts (exist _ x pf) y.
                                          
  Instance independent_eventcoll_class_lambda domr :
    Lambda_system (independent_eventcoll_class (fun x : event dom => domr x)).
  Proof.
    constructor.
    - exists sa_all. intros ??.
      generalize (independent_events_all_l _ y)
      ; apply independent_events_proper; intros ?; simpl; reflexivity.
    - unfold independent_eventcoll_class; intros ???; intros.
      split; intros [pf HH].
      + assert (pf':sa_sigma y).
        {
          now generalize pf; apply sa_proper.
        }
        exists pf'.
        intros B saB.
        generalize (HH B saB).
        apply independent_events_proper; intros ?; simpl; try reflexivity.
        symmetry; apply H.
      + assert (pf':sa_sigma x).
        {
          now generalize pf; apply sa_proper.
        }
        exists pf'.
        intros B saB.
        generalize (HH B saB).
        apply independent_events_proper; intros ?; simpl; try reflexivity.
        apply H.
    - unfold independent_eventcoll_class.
      intros ? [pf HH].
      exists (sa_complement _ pf); intros B saB.
      specialize (HH B saB).
      apply independent_events_complement_l in HH.
      revert HH.
      apply independent_events_proper; intros ?; simpl; reflexivity.
    - unfold independent_eventcoll_class.
      intros ???.
      assert (sas:forall x, sa_sigma (an x)).
      {
        now intros x; destruct (H x).
      } 
      exists (sa_countable_union an sas); intros B saB.
      assert (forall x,
                 independent_events prts
                                    (exist _ _ (sas x)) B).
      {
        intros x; destruct (H x) as [pf HH].
        generalize (HH B saB).
        apply independent_events_proper; intros ?; simpl; reflexivity.
      }

      generalize (independent_events_disjoint_countable_union prts (fun n => exist _ _ (sas n)) B H1)
      ; intros HH.
      cut_to HH.
      + revert HH.
        apply independent_events_proper; intros ?; simpl; reflexivity.
      + apply collection_is_pairwise_disjoint_pre.
        apply H0.
  Qed.
      
  Lemma independent_eventcoll_generated_l (dom1 dom2: pre_event Ts -> Prop)
        (sub1:pre_event_sub dom1 (@sa_sigma _ dom))
        {pi1 : Pi_system dom1}
    :
    independent_eventcoll dom1 dom2 ->
    independent_eventcoll (@sa_sigma _ (generated_sa dom1)) dom2.
  Proof.
    intros.
    generalize (@Dynkin _ dom1 (independent_eventcoll_class dom2))
    ; intros HH.
    cut_to HH; trivial.
    - unfold independent_eventcoll_class, independent_eventcoll in *.
      intros.
      red in HH.
      destruct (HH _ H0) as [pf HH2].
      generalize (HH2 _ H1).
      apply independent_events_proper; intros ?; simpl; reflexivity.
    - apply independent_eventcoll_class_lambda.
    - intros ??.
      red.
      exists (sub1 _ H0); intros.
      apply H; trivial.
  Qed.

  Lemma independent_eventcoll_symm (dom1 dom2: pre_event Ts -> Prop) :
        independent_eventcoll dom1 dom2 ->
        independent_eventcoll dom2 dom1.
  Proof.
    intros ?????.
    apply independent_events_symm.
    now apply H.
  Qed.

  Lemma independent_eventcoll_generated_r (dom1 dom2: pre_event Ts -> Prop)
        (sub1:pre_event_sub dom2 (@sa_sigma _ dom))
        {pi2 : Pi_system dom2}
    :
    independent_eventcoll dom1 dom2 ->
    independent_eventcoll dom1 (@sa_sigma _ (generated_sa dom2)).
  Proof.
    intros.
    apply independent_eventcoll_symm.
    apply independent_eventcoll_generated_l; trivial.
    now apply independent_eventcoll_symm.
  Qed.    

  (*
  Lemma independent_coll_generated_union (dom1 dom2 dom3: pre_event Ts -> Prop)
        (sub1:pre_event_sub dom1 (@sa_sigma _ dom))
        (sub2:pre_event_sub dom2 (@sa_sigma _ dom))
        {pi1 : Pi_system dom1}
        {pi2 : Pi_system dom2} :
    independent_eventcoll dom1 dom3 ->
    independent_eventcoll dom2 dom3 ->
    independent_eventcoll (@sa_sigma _ (generated_sa (pre_event_union dom1 dom2))) dom3.
  Proof.
    intros indep1 indep2.
    generalize (independent_eventcoll_union dom1 dom2 dom3 indep1 indep2).
    apply independent_eventcoll_generated_l.
    - intros ? [?|?]; auto.
    - intros ????.
      red.

    generalize (@Dynkin _ (fun _ => True) (independent_eventcoll_class dom3))
    ; intros HH.
    apply HH; trivial.

    
    
    4: simpl.
    
    Set Printing All.

    
  Qed.


  
  Lemma independent_sas_union {dom1} (sub1:sa_sub dom1 dom) {dom2} (sub2:sa_sub dom2 dom)
        {dom3} (sub3:sa_sub dom3 dom) :
    independent_sas sub1 sub3 ->
    independent_sas sub2 sub3 ->
    independent_sas (union_sa_sub_both sub1 sub2) sub3.
   *)


  Lemma independent_coll_inter3 (dom1 dom2 dom3: pre_event Ts -> Prop)
        (sub1:pre_event_sub dom1 (@sa_sigma _ dom))
        (sub2:pre_event_sub dom2 (@sa_sigma _ dom)) :

    (forall A B C : event dom, dom1 A -> dom2 B -> dom3 C -> 
                              ps_P ((A ∩ B)  ∩ C ) = ps_P A * ps_P B * ps_P C) ->
    independent_eventcoll dom1 dom2 ->
    independent_eventcoll (fun x => exists e1 e2, dom1 e1 /\ dom2 e2 /\ pre_event_equiv x (pre_event_inter e1 e2)) dom3.
  Proof.
    unfold independent_eventcoll in *.
    intros.
    unfold independent_events.
    destruct H1 as [? [? [? [? ?]]]].
    specialize (sub1 x H1).
    specialize (sub2 x0 H3).
    assert (event_equiv A (event_inter (exist _ _ sub1) (exist _ _ sub2))).
    {
      destruct A.
      simpl in H4.
      intro z; simpl.
      now specialize (H4 z).
    }
    rewrite H5.
    specialize (H0 (exist _ _ sub1) (exist _ _ sub2) H1 H3).
    rewrite H0.
    now rewrite H.
  Qed.
    

End sigma_indep.

  

