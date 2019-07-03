Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Lra.
Require Import List.

Require Import BasicTactics Sums.
Import ListNotations.
  

Section ev.
  Definition event T := T -> Prop.

  (* also written Ω *)
  Definition event_True {T}
    := fun x: T => True. 

  (* also written Ø *)
  Definition event_False {T}
    := fun x: T => False.
  
  Definition event_union {T} (A B:T->Prop)
    := fun x:T => A x \/ B x.
  
  Definition event_inter {T} (A B:T->Prop)
    := fun x:T => A x /\ B x.
  
  Definition event_complement {T} (A:T->Prop)
    := fun x:T => not (A x).
End ev.
  
Notation "a ∪ b" := (event_union a b) (at level 50) : prob. (* \cup *)
Notation "a ∩ b" := (event_inter a b) (at level 50) : prob. (* \cap *)
Notation "¬ a" := (event_complement a) (at level 75) : prob. (* \neg *)
  
  (* Collections are *countable* sequences of subsets of the powerset of T. *)

Local Open Scope prob.


Definition collection_is_pairwise_disjoint (T: Type) (collection: nat -> event T) :=
  forall n1 n2 : nat, n1 <> n2 ->
                      forall x : T, (collection n1) x -> ~((collection n2) x).

(* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
Definition union_of_collection {T: Type} (collection: nat -> event T) : event T :=
  fun t:T => (exists n, (collection n) t).

Class SigmaAlgebra (T:Set) :=
  {
    sa_sigma : event T -> Prop;
    
    (* alternative to assuming functional extensionality *)
    sa_ext (A1 A2:event T) : (forall x,  A1 x <-> A2 x) -> sa_sigma A1 <-> sa_sigma A2;
    
    sa_countable_union (collection: nat -> event T) :
      (forall n, sa_sigma (collection n)) ->
      sa_sigma (union_of_collection collection);
    
    sa_complement (A:event T) :
        sa_sigma A -> sa_sigma (¬ A) ;
    
    sa_True : sa_sigma event_True 
               
  }.

  Lemma sa_False {T} {s: SigmaAlgebra T} : sa_sigma (event_False).
  Proof.
    eapply sa_ext
    ; [ | eapply sa_complement; eapply sa_True].
    unfold event_False, event_True, event_complement; tauto.
  Qed.

  Definition list_collection {T} {s : SigmaAlgebra T} (l:list (event T)) : nat -> event T
    := fun n => nth n l event_False.

  Definition list_union {T} {s : SigmaAlgebra T} (l:list (event T)) : event T
    := fun x => exists a, In a l /\ a x.

  Lemma list_union_union {T} {s : SigmaAlgebra T} (l:list (event T)) :
    forall x, union_of_collection (list_collection l) x <-> list_union l x.
  Proof.
    unfold union_of_collection, list_collection, list_union.
    intros x.
    split; intros H.
    - destruct H as [n nnth].
      destruct (nth_in_or_default n l event_False).
      + eauto.
      + rewrite e in nnth.
        red in nnth; intuition.
    - destruct H as [a [inn ax]].
      eapply In_nth in inn.
      destruct inn as [n [_ nnth]].
      exists n.
      rewrite nnth.
      trivial.
  Qed.

  Lemma list_collection_sigma {T} {s : SigmaAlgebra T} (l:list (event T)) :
    (forall x : event T, In x l -> sa_sigma x) <->
    (forall n : nat, sa_sigma (list_collection l n)).
  Proof.
    unfold list_collection.
    split; intros.
    - destruct (nth_in_or_default n l event_False).
      + eauto.
      + rewrite e.
        apply sa_False.
    - eapply In_nth in H0.
      destruct H0 as [n [_ nnth]].
      specialize (H n).
      rewrite nnth in H; trivial.
  Qed.

  Lemma sa_list_union {T} {s: SigmaAlgebra T} (l:list (event T)) :
    (forall x, In x l -> sa_sigma x) ->
    sa_sigma (list_union l).
  Proof.
    intros.
    generalize (sa_countable_union (list_collection l)); intros.
    erewrite sa_ext.
    - apply H0.
      apply list_collection_sigma; trivial.
    - intros.
      symmetry.
      apply list_union_union.
  Qed.

  Lemma sa_union {T} {s: SigmaAlgebra T} {A₁ A₂} :
    sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ ∪ A₂).
  Proof.
    intros.
    generalize (sa_list_union [A₁ ; A₂]); intros.
    erewrite sa_ext; [eapply H1 | ].
    - simpl; intuition congruence.
    - unfold list_union, event_union; simpl.
      intuition; try eauto.
      destruct H2 as [a [inn ax]].
      intuition congruence.
  Qed.

  (* TODO: best way to solve this
  Lemma sa_inter {T} {s: SigmaAlgebra T} {A₁ A₂} :
    sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ ∩ A₂).
  Proof.
    intros sa1 sa2.
    unfold event_inter.
    apply sa_complement in sa1.
    apply sa_complement in sa2.
    generalize (sa_union sa1 sa2); intros sa3.
    apply sa_complement in sa3.
    unfold event_union in sa3.
    unfold event_complement in *.
    eapply sa_ext; [| eapply sa3].
    intros; simpl.
    split; intros.
    - tauto.
    - apply Decidable.not_or in H.
      destruct H.
  Qed.
*)

  (* Prop: the sum of probabilities for everything in the collection == R. *)
Definition sum_of_probs_equals {T:Type}
             (p : event T -> R)
             (collection: nat -> event T) (result: R) :=
    infinite_sum' (fun n:nat => p (collection n)) result.

Class ProbSpace {T:Set} (S:SigmaAlgebra T) :=
  {
    ps_P: event T -> R;
    ps_P_ext : forall x1 x2, (forall z, x1 z <-> x2 z) -> ps_P x1 = ps_P x2 ;
    
    ps_P_sum (collection: nat -> event T) :
      (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
      (forall n:nat, sa_sigma (collection n)) -> 
      collection_is_pairwise_disjoint T collection ->
      sum_of_probs_equals ps_P collection (ps_P (union_of_collection collection));
    
    ps_P_one : ps_P event_True = R1;
    
    ps_sample_space_nonnegative : inhabited T
  }.

Lemma ps_True {T:Set} {S:SigmaAlgebra T} (ps:ProbSpace S) : ps_P event_True = R1.
Proof.
  apply ps_P_one.
Qed.

Lemma ps_False {T:Set} {S:SigmaAlgebra T} (ps:ProbSpace S) : ps_P event_False = R0.
Proof.
  generalize (ps_P_sum
                (fun n => match n with
                          | 0 => event_True
                          | _ => event_False
                          end))
  ; intros HH.
  cut_to HH.
  - simpl in HH.
    red in HH.
    apply (infinite_sum'_split 1) in HH.
    simpl in HH.

    apply (infinite_sum'_ext (fun x : nat => ps_P match (x + 1)%nat with
                                                  | 0%nat => event_True
                                                  | S _ => event_False
                                                  end)
                             (fun x : nat => ps_P event_False)) in HH.
    + rewrite (ps_P_ext (union_of_collection
                           (fun n : nat => match n with
                                           | 0%nat => event_True
                                           | S _ => event_False
                                           end)) (event_True)) in HH.
      * replace (ps_P (ProbSpace:=ps) event_True) with R1 in HH
          by (symmetry; apply ps_P_one).
        replace (R1 - (0 + R1))%R with R0 in HH by lra.
        apply infinite_sum'_const_to_0 in HH.
        trivial.
      * unfold event_True; intuition.
        red.
        exists 0%nat; trivial.
    + destruct x; simpl; trivial.
  - destruct n.
    + apply sa_True.
    + apply sa_False. 
  - unfold collection_is_pairwise_disjoint.
    destruct n1; destruct n2; unfold event_True, event_False; try tauto.
Qed.

Section RandomVariable.

  (* A sigma algebra **over the same domain T as the ProbSpace! *)
  
  (* and now I give up on a proper measure-theoretic definition because I don't think we'll be able to do anything with it... *)
  Class RandomVariable {Ts:Set} {Td:Set}
        {doms: SigmaAlgebra Ts}
        (dom: ProbSpace doms)
          (cod: SigmaAlgebra Td) :=
    {
      
      (* the actual variable. *)
      rv_X: Ts -> Td
    }.
  
End RandomVariable.

Section prob.
  Local Open Scope R.
  Local Open Scope prob.

  Definition Pr {Ts:Set} {Td:Set}
             {doms: SigmaAlgebra Ts}
             {dom: ProbSpace doms}
             {cod: SigmaAlgebra Td}
             {rv:RandomVariable dom cod}
             (S:Td->Prop)
    := ps_P (fun x:Ts => S (rv_X x)).

  Context {Ts:Set} {Td:Set}
          {doms: SigmaAlgebra Ts}
          {dom: ProbSpace doms}
          {cod: SigmaAlgebra Td}
          {rv:RandomVariable dom cod}.

  Definition independent (A B:Td->Prop) :=
    Pr (A ∩ B) = (Pr A * Pr B).

  Notation "a ⊥ b" := (independent a b) (at level 50) : prob. (* \perp *)

  (* Introduce a make_finite_collection : list -> collection and lemmas about it *)

  Lemma pr_True : Pr event_True = R1.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_P_ext _ event_True) by (unfold event_True; tauto).
    apply ps_True.
  Qed.
  
  Lemma pr_False : Pr event_False = R0.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_P_ext _ event_False) by (unfold event_False; tauto).
    apply ps_False.
  Qed.

  (*
    Lemma pr_plus (A B:Td->Prop) :
      Pr (A ∪ B) = Pr A  + Pr B - Pr (A ∩ B).
    Proof.
      generalize (ps_P_sum
                    (fun n => match n with
                              | 0 => A
                              | 1 => B
                              | _ => event_False
                              end)).
      
   *)

End prob.


Notation "a ∪ b" := (event_union a b) (at level 50) : prob. (* \cup *)
Notation "a ∩ b" := (event_inter a b) (at level 50) : prob. (* \cap *)
Notation "¬ a" := (event_complement a) (at level 75) : prob. (* \neg *)
Notation "a ⊥ b" := (independent a b) (at level 50) : prob. (* \perp *)
