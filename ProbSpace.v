Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Lra.

Require Import BasicTactics Sums.

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
Definition union_of_collection (T: Type) (collection: nat -> event T) :=
  fun t:T => (exists n, (collection n) t).

Class SigmaAlgebra (T:Set) :=
  {
    sa_sigma : event T -> Prop;
    
    (* alternative to assuming functional extensionality *)
    sa_sigma_ext : forall T1 T2, (forall x,  T1 x <-> T2 x) -> sa_sigma T1 <-> sa_sigma T2;
    
    sa_closed_under_intersections :
      forall A_1 A_2: event T,
        sa_sigma A_1 /\ sa_sigma A_2 -> sa_sigma (A_1 ∩ A_2) ;
    
    sa_closed_under_complements :
      forall A_1 : event T,
        sa_sigma A_1 -> sa_sigma (¬ A_1) ;
    
    sa_contains_sample_space :
      sa_sigma event_True 
               
  }.

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
      sum_of_probs_equals ps_P collection (ps_P (union_of_collection T collection));
    
    ps_P_one : ps_P event_True = R1;
    
    ps_sample_space_nonnegative : inhabited T
  }.

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

  Lemma sa_sigma_True {T} {s: SigmaAlgebra T} : sa_sigma (event_True).
  Proof.
    apply sa_contains_sample_space.
  Qed.

  Lemma sa_sigma_False {T} {s: SigmaAlgebra T} : sa_sigma (event_False).
  Proof.
    eapply sa_sigma_ext
    ; [ | eapply sa_closed_under_complements; eapply sa_contains_sample_space].
    unfold event_False, event_True, event_complement; tauto.
  Qed.

  (* Introduce a make_finite_collection : list -> collection and lemmas about it *)

  Lemma pr_True : Pr event_True = R1.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_P_ext _ event_True) by (unfold event_True; tauto).
    apply ps_P_one.
  Qed.
  
  Lemma pr_False : Pr event_False = R0.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_P_ext _ event_False) by (unfold event_False; tauto).
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
      + rewrite (ps_P_ext (union_of_collection Ts
                                               (fun n : nat => match n with
                                                               | 0%nat => event_True
                                                               | S _ => event_False
                                                               end)) (event_True)) in HH.
        * replace (ps_P (ProbSpace:=dom) event_True) with R1 in HH
            by (symmetry; apply ps_P_one).
          replace (R1 - (0 + R1)) with 0 in HH by lra.
          apply infinite_sum'_const_to_0 in HH.
          trivial.
        * unfold event_True; intuition.
          red.
          exists 0%nat; trivial.
      + destruct x; simpl; trivial.
    - destruct n.
      + apply sa_sigma_True.
      + apply sa_sigma_False. 
    - unfold collection_is_pairwise_disjoint.
      destruct n1; destruct n2; unfold event_True, event_False; try tauto.
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
