Require Import Reals EquivDec List LibUtils Permutation Morphisms.
Require Import pmf_monad.
Require Import micromega.Lra.
From mathcomp Require Import ssreflect ssrfun seq.

Set Bullet Behavior "Strict Subproofs".


Import ListNotations.
Local Open Scope list_scope.
Open Scope R_scope.


Section aux.


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


Lemma list_sum_const_div {A:Type}{n : nonnegreal} (hne : 0 <> nonneg n)
      (l : seq(nonnegreal*A))(f : A -> R) :
      list_sum [seq f x.2 * (nonneg(x.1) / nonneg(n)) | x <- l] = list_sum [seq (f x.2 * nonneg (x.1)) | x <- l]/nonneg(n).
Proof.
  induction l. 
  simpl. lra.
  simpl. rewrite IHl. lra.
Qed.


End aux.

Section quotient.

  Context {A} {R} {equiv:Equivalence R}  {dec:EqDec A R}.

  Fixpoint add_to_bucket (x:A) (ll:list (list A)) : list (list A)
    := match ll with
       | [] => [[x]]
       | nil::ll' =>
         add_to_bucket x ll'
       | (y::l)::ll' =>
         match x == y with
         | left _ => (x::y::l)::ll'
         | right_ => (y::l)::(add_to_bucket x ll')
         end
       end.

  Fixpoint quotient (l:list A) : list (list A)
    := match l with
       | nil => nil
       | x::l' =>
         let q' := quotient l' in
         add_to_bucket x q'
       end.

  Lemma add_to_bucket_perm a l :
    Permutation (concat (add_to_bucket a l)) (a::concat l).
  Proof.
    induction l;simpl;trivial.
    destruct a0.
    - simpl; trivial.
    - match_destr.
      simpl.
      rewrite IHl.
      rewrite perm_swap.
      apply perm_skip.
      now rewrite Permutation_middle; simpl.
  Qed.

  Lemma unquotient_quotient l : Permutation (concat (quotient l)) l.
  Proof.
    induction l; simpl; trivial.
    rewrite add_to_bucket_perm.
    rewrite IHl.
    reflexivity.
  Qed.

  Corollary quotient_in x l : In x l -> exists l', In l' (quotient l) /\ In x l'.
  Proof.
    intros.
    apply concat_In.
    now rewrite unquotient_quotient.
  Qed.

  Corollary in_quotient x l l' : In l' (quotient l) /\ In x l' -> In x l.
  Proof.
    intro H. 
    rewrite <-unquotient_quotient. rewrite concat_In. 
    exists l'. apply H. 
  Qed.  

  Definition is_equiv_class (l:list A) := ForallPairs R l.

  Definition is_partition (l:list (list A)) := Forall (is_equiv_class) l.


  Lemma is_partition_nil : is_partition nil.
  Proof.
    now red.
  Qed.

  Lemma add_to_bucket_partition a l : is_partition l -> is_partition (add_to_bucket a l).
  Proof.
    unfold is_partition, is_equiv_class, is_equiv_class, ForallPairs.
    induction l; simpl; intros isp.
    - (repeat constructor); simpl ; intros ; intuition. subst ; reflexivity. 
    - invcs isp.  
      specialize (IHl H2).
      match_destr.
      match_destr.
      + constructor; trivial; intros.
        simpl in *.
        intuition; subst; trivial.
        * reflexivity.
        * rewrite e ; auto.
        * rewrite <- e; reflexivity.
        * rewrite e; auto.
      + constructor; trivial.
  Qed.

 Lemma quotient_partitions l : is_partition (quotient l).
  Proof.
    Hint Resolve is_partition_nil : ml.
    Hint Resolve add_to_bucket_partition : ml.

    induction l; simpl; auto with ml.
  Qed.

  Hint Resolve quotient_partitions : ml.
  
  Definition different_buckets l1 l2 := forall x y, In x l1 -> In y l2 -> ~ R x y.

  Definition all_different l := ForallOrdPairs different_buckets l.

  Lemma all_different_nil : all_different nil.
  Proof.
    constructor.
  Qed.

  (*Lemma add_to_buckets_in_one {x a l} :
    In x (add_to_bucket a l) -> In a x \/ In x l.
  Proof.
    induction l.
    - simpl ; intuition. invcs H0 ; intuition.  
    - simpl in *.
      match_destr.
       -- intro H ; intuition. 
       -- match_destr ; intuition. 
          + invcs H ; intuition.
          + invcs H ; intuition. 
  Qed.*)
  
  Lemma add_to_buckets_in_one {x a l} :
    In x (add_to_bucket a l) -> In a x \/ In x l.
  Proof.
    induction l; simpl; intros inn.
    - destruct inn as [inn|inn]; [ | intuition].
      invcs inn ; simpl ; intuition.
    - match_destr_in inn.
      + intuition. 
      + match_destr_in inn
        ; simpl in inn.
        * destruct inn as [inn|inn].
          -- invcs inn.
             simpl ; eauto.
          -- eauto.
        * intuition.
  Qed.

  Lemma add_to_bucket_all_different a l :
    is_partition l ->
    all_different l ->
    all_different (add_to_bucket a l).
  Proof.
    unfold all_different.
    induction l; simpl.
    - repeat constructor.
    - intros isp ordp; invcs isp; invcs ordp.
      specialize (IHl H2 H4).
      match_destr.
      match_destr.
      + constructor; trivial.
        revert H3.
        apply Forall_impl; intros.
        red in e.
        unfold different_buckets in *; simpl in *.
        intuition; subst; eauto 3.
        * eapply H; eauto.
          now rewrite <- e.
      + constructor; trivial.
        rewrite Forall_forall; intros.
        generalize (add_to_bucket_partition a l H2); intros.
        red in H0.
        eapply Forall_forall in H0; eauto.
        repeat red in H0.
        destruct (add_to_buckets_in_one H).
        * red; simpl; intros.
          rewrite (H0 _ _ H7 H5).
          destruct H6.
          -- subst.
             intuition.
          -- repeat red in H1.
             rewrite (H1 x0 a0); simpl; intuition.
        * eapply Forall_forall in H3; eauto.
  Qed.
  
  Hint Resolve all_different_nil : ml.
  Hint Resolve add_to_bucket_all_different : ml.
                     
  Lemma quotient_all_different l : all_different (quotient l).
  Proof.
    induction l; simpl; auto with ml.
  Qed.

  Hint Resolve quotient_all_different : ml.


  Lemma quotient_buckets_disjoint l ll1 l2 ll3 l4 ll5  :
    quotient l = ll1 ++ l2 :: ll3 ++ l4 :: ll5 ->
    forall x y, In x l2 /\ In y l4 -> ~ R x y.
  Admitted.
  
    
Lemma quotient_buckets_disjoint_ l ll1 ll2 :
    quotient l = ll1 ++ ll2 ->
    forall l1 l2 x y, In l1 ll1 /\ In l2 ll2 ->
                 In x l1 /\ In y l2 -> ~ R x y.
  Admitted.


End quotient.

Section image_equiv.
Context {A : Type}. 
Definition im_eq (f : A -> R) : A -> A -> Prop := fun x y => (f x = f y). 

Global Instance im_eq_equiv (f : A -> R) : Equivalence (im_eq f). 
Proof.
  unfold im_eq.
  constructor.
  - reduce_goal. solve_relation.
  - reduce_goal. solve_relation.
  - reduce_goal. etransitivity. apply H. assumption. 
Qed.


Global Instance Eq_dec_im_eq (f : A -> R) : EqDec A (im_eq f) := 
{
  equiv_dec := fun a b => Req_EM_T (f a) (f b)
}.

End image_equiv.



Section list_sum.

Definition group_by_image {A} (f : A -> R) := @quotient _ _ _ (Eq_dec_im_eq f).                                                                   
    
Global Instance list_sum_Proper : Proper (@Permutation R ==> eq) list_sum.
Proof.
  unfold Proper. intros x y H. 
  apply (@Permutation_ind_bis R (fun a b => list_sum a = list_sum b)). 
  - simpl ; lra. 
  - intros x0 l l' Hpll' Hll'. simpl ; f_equal. assumption.
  - intros x0 y0 l l' H0 H1. simpl. rewrite H1 ; lra. 
  - intros l l' l'' H0 H1 H2 H3. rewrite H1. rewrite <-H3. reflexivity. 
  - assumption. 
Qed.

Lemma list_sum_perm_eq (l1 l2 : list R) : Permutation l1 l2 -> list_sum l1 = list_sum l2.
Proof.
  intro H. 
  now rewrite H.
Qed.
      
Lemma list_sum_map_concat (l : list(list R)) :
  list_sum (map list_sum l) = list_sum (concat l).
Proof.   
  induction l. 
  - simpl ; reflexivity.
  - simpl ; rewrite list_sum_cat. now rewrite IHl. 
Qed.

Definition map_map {A} (f : A -> R) (l : list(list A))  : list(list R) := map (map f) l. 

Lemma In_group_by_image {A} (l : list A) (f : A -> R) :
 Forall (fun l0 => (forall a b, In a l0 -> In b l0 -> (f a = f b))) (group_by_image f l). 
Proof.
  apply quotient_partitions. 
Qed.



Lemma list_sum_eq_class {A : Type} (l : list A) (f : A -> R) :
  forall l0, In l0 (group_by_image f l) -> list_sum (map f l0) = INR(length l0)*match l0 with
                                                                          | [] => 0
                                                                          | x :: xs => f x
                                                                          end.
Proof.   
  intros l0 Hl0.
  assert (forall x y, In x l -> In y l -> f x = f y).
  set (In_group_by_image l f).
Admitted.
  

      
End list_sum.
  

Section range.

Instance EqDecR : EqDec R eq := Req_EM_T. 

Arguments outcomes {_}.

(* Range of a random variable together with the atomic probabilities.*)
Definition range {A : Type} (l : list(nonnegreal*A)) (f : A -> R) : list (nonnegreal*R) :=
  map (fun x => (x.1, f x.2)) l.

(* All p.(outcomes) which are preimages of a fixed r in R under the random variable g. *)
Definition preim_outcomes_of {A : Type} (p : Pmf A) (g : A -> R) (r : R) :=
  filter (fun x => (g x.2 ==b r)) p.(outcomes).

Definition preim_outcomes_of_And {A : Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2 ==b r1) (g x.2 ==b r2)) (p).(outcomes).


Lemma expt_value_range_sum {A : Type} (p : Pmf A) (f : A -> R) :
  expt_value p f = list_sum (map (fun p => nonneg(p.1)*p.2) (range p.(outcomes) f)).
Proof.
  unfold comp, expt_value,range. 
  rewrite <-map_comp. unfold comp. simpl. f_equal.
  apply List.map_ext. intro a. apply Rmult_comm. 
Qed.


(* p(f = r) *)
Definition prob_of_event {A : Type} (p : Pmf A) (f : A -> R) (r : R) :=
  𝕡[[seq s <- range p f | s.2 ==b r]].

(* p(f = r1 /\ g = r2) *)
Definition and_prob {A : Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :=
  𝕡[[seq s <- range (preim_outcomes_of p g r2) f | s.2 ==b r1]].


(* The function f doesn't matter here as we're only summing over the probabilities (first indices)*)
Lemma list_sum_outcomes_And {A : Type} (f : A -> R) (l : list (nonnegreal*A)) :
   𝕡[l] = list_fst_sum (range l f).
Proof.
unfold prob ; simpl.
rewrite list_fst_sum_compat. unfold list_fst_sum'.
rewrite list_fst_sum_compat. unfold list_fst_sum'.
simpl in *.  induction l.
- simpl ; lra.
- simpl. rewrite IHl. reflexivity.
Qed.

Lemma preim_outcomes_of_range {A:Type}(p : Pmf A) (f : A -> R) (r : R) :
  𝕡[preim_outcomes_of p f r] = 𝕡[[seq s <- (range p f) | (s.2 ==b r)]].
Proof.
  unfold prob, preim_outcomes_of. simpl.
  repeat (rewrite list_fst_sum_compat ; unfold list_fst_sum').
  f_equal. unfold range.  
  induction p.(outcomes).
  - simpl. reflexivity.          
  - simpl.
    unfold equiv_decb; destruct (equiv_dec (f a.2) r).
    simpl. rewrite IHl. f_equal.
    rewrite IHl. reflexivity.
Qed.


Lemma preim_outcomes_of_range_And {A : Type} (p : Pmf A) (f g: A -> R) (r1 r2 : R) :
 𝕡[preim_outcomes_of_And p f g r1 r2] = 𝕡[[seq s <- range (preim_outcomes_of p g r2) f | s.2 ==b r1]].
Proof.
  unfold prob, preim_outcomes_of,range,preim_outcomes_of_And. simpl.
  repeat (rewrite list_fst_sum_compat ; unfold list_fst_sum').
  f_equal. rewrite map_comp.  rewrite map_comp. f_equal.
  induction p.(outcomes).
  simpl ; reflexivity.
  simpl. unfold equiv_decb. destruct (equiv_dec (g a.2) r2) ; [simpl| simpl].
  unfold equiv_decb ; destruct (equiv_dec (f a.2) r1) ; [simpl | rewrite IHl].
  rewrite IHl.  reflexivity.
  simpl.  reflexivity.
  destruct (equiv_dec (f a.2) r1) ; [simpl; now rewrite IHl | simpl; now rewrite IHl].
Qed.

Definition cond_prob {A : Type}(p : Pmf A) (f g : A -> R)(r1 r2 : R) := 𝕡[preim_outcomes_of_And p f g r1 r2]/ 𝕡[preim_outcomes_of p g r2].
  
           
Definition cond_expt_value {A : Type}(p : Pmf A)(f g : A -> R) (r : R) : R := 
  list_sum (map (fun x => (cond_prob p f g x.2 r)*(x.2)) (range p.(outcomes) f)).


Definition independent {A : Type}(p : Pmf A) (f g : A -> R) :=
  forall r1 r2,  𝕡[preim_outcomes_of_And p f g r1 r2] = 𝕡[preim_outcomes_of p f r1]*𝕡[preim_outcomes_of p g r2].

Lemma cond_prob_eq_prob_independent {A : Type}(p : Pmf A) {f g : A -> R} (hi : independent p f g) :
  forall r1 r2, 𝕡[preim_outcomes_of p g r2] <> 0 -> cond_prob p f g r1 r2 = 𝕡[preim_outcomes_of p f r1].
Proof.
  intros r1 r2 H. 
  unfold cond_prob. specialize (hi r1 r2).
  rewrite hi. field_simplify. reflexivity.
  assumption.
Qed.


Lemma cond_expt_value_expt_value_aux {A : Type}{p : Pmf A}{f g : A -> R} (l : list(nonnegreal*R))(hi : independent p f g) :
 forall r, 𝕡[preim_outcomes_of p g r] <> 0 -> map (fun x => (cond_prob p f g x.2 r)*(x.2)) l = map (fun x => (𝕡[preim_outcomes_of p f x.2])*(x.2)) l.
Proof.
  intros r Hr.   
  apply List.map_ext.
  intro a. f_equal.
  apply (cond_prob_eq_prob_independent p hi).
  assumption.
Qed.


Lemma list_sum_const_mul {A : Type} (l : list (nonnegreal*R)) :
  forall r, list_sum (map (fun x => r*x.2) l)  = r*list_sum(map (fun x => x.2) l).
Proof.
  intro r.
  induction l.
  simpl; lra.
  simpl. rewrite IHl ; lra.
Qed.



(*Lemma cond_expt_value_range {A : Type}{r : R} {g : A -> R}{p : Pmf A} (hne : 0 <> 𝕡[preim_outcomes_of p g r])(f : A -> R):
  cond_expt_value p f g r =
  list_sum ([seq nonneg(x.1) * x.2 | x <- range (preim_outcomes_of p g r) f])/𝕡[preim_outcomes_of p g r].
Proof.
  unfold cond_expt_value. unfold cond_prob.
  unfold range.  
  rewrite <-map_comp. unfold comp.  simpl. unfold cond_prob. f_equal.
  apply List.map_ext. intro a. apply Rmult_comm.
Qed.*)


  
(*Lemma cond_expt_value_expt_value_aux {A : Type}{r2 : R} {g : A -> R}{p : Pmf A} (hne : 0 <> 𝕡[preim_outcomes_of p g r2])(f : A -> R) (r1:R): list_sum ([seq nonneg(x.1) * x.2 | x <- range (preim_outcomes_of p g r2) f]) = _.*)
  
End range.



(*Section product_measure.
Open Scope monad_scope.

(* Not able to use the cool do notation. :-(  *)
Definition product_measure {A:Type} (p q : Pmf A) : Pmf(A*A) :=
 Pmf_bind p (fun (x:A) => Pmf_bind q (fun (y:A) => Pmf_pure (pair x y))).

End product_measure.

Notation "p ⊗ q" := (product_measure p q) (at level 80, right associativity).

Section crap.

Arguments outcomes {_}. 
Definition preim_outcomes_of_And {A : Type} (p : Pmf A) (f g: A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2 ==b r1) (g x.2 ==b r2)) p.(outcomes).

Lemma preim_outcomes_of_And_split {A : Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :
  preim_outcomes_of_And p f g r1 r2 = filter (fun x => f x.2 ==b r1) (preim_outcomes_of p g r2).
Proof.
  unfold preim_outcomes_of, preim_outcomes_of_And.
  induction p.(outcomes).
  - simpl ; reflexivity. 
  - simpl.  unfold equiv_decb. destruct (equiv_dec (g a.2) r2).
    unfold equiv_decb. destruct (equiv_dec (f a.2) r1). simpl. rewrite e0.
    unfold equiv_decb. destruct (equiv_dec r1 r1) ; [| congruence]. 
    rewrite IHl. reflexivity.
    simpl. rewrite IHl. unfold equiv_decb.
    destruct (equiv_dec (f a.2) r1) ; [contradiction|congruence].
    unfold equiv_decb.
    destruct (equiv_dec (f a.2) r1). simpl. rewrite IHl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed. 

Definition independent_aux_prop {A : Type} (p : Pmf A) (f g : A -> R):=
  forall r : R,
    list_sum [seq f x.2 * nonneg(x.1) | x <- p & g x.2 ==b r] =
    list_sum [seq f x.2 * nonneg(x.1) | x <- p.(outcomes)]*list_sum [seq nonneg(x.1) | x<-p.(outcomes) & g x.2 ==b r].


Lemma independent_aux_prop_const_fun {A : Type} (p : Pmf A) (g : A -> R) (c : R) : 
  independent_aux_prop p (fun _ => c) g.
Proof.
  unfold independent.
  intros r. 
  enough (H :  list_sum [seq c * nonneg(x.1) | x <- p.(outcomes) & g x.2 ==b r] = c* list_sum [seq nonneg(x.1) | x <- p.(outcomes) & g x.2 ==b r]).
  rewrite H.
  enough (H1 : forall p:Pmf A, list_sum [seq c * nonneg(x.1) | x <- p] = c*list_sum [seq nonneg(x.1) | x <- p]).
  rewrite (H1 p). f_equal. destruct p as [p0 sum1]. simpl in *.
  revert sum1. rewrite list_fst_sum_compat. unfold list_fst_sum'. intro H2. rewrite H2 ;lra.
  intro p0.
  induction p0.(outcomes). 
  simpl ; lra.
  simpl. simpl in H. rewrite IHl. lra.
  induction p.(outcomes).
  simpl ; lra.
  simpl. unfold equiv_decb ; destruct (equiv_dec (g a.2) r);[ | rewrite IHl;reflexivity].
  simpl. rewrite IHl. rewrite Rmult_plus_distr_l. reflexivity.
Qed.

End crap.



Section events.

Arguments outcomes {_}.
    
(* All (p⊗p).(outcomes) which are preimages of a fixed r in R under the random variable g. *)
Definition preim_outcomes_of_fst {A : Type} (p : Pmf A) (f : A -> R) (r : R) :=
  filter (fun x => (f x.2.1 ==b r)) (p ⊗ p).(outcomes).

Definition preim_outcomes_of_snd {A : Type} (p : Pmf A) (g : A -> R) (r : R) :=
  filter (fun x => (g x.2.2 ==b r)) (p ⊗ p).(outcomes).


Definition preim_outcomes_of_pair_And {A:Type} (p : Pmf A) (f g : A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2.1 ==b r1) (g x.2.2 ==b r2)) (p ⊗ p).(outcomes).


Theorem independent {A:Type} (p:Pmf A) (f g : A -> R) :
  forall r1 r2, 𝕡[ preim_outcomes_of_pair_And p f g r1 r2] = 𝕡[preim_outcomes_of_fst p f r1]*𝕡[preim_outcomes_of_snd p g r2].
  
End events.

Section cond_prob.

Arguments outcomes {_}.


(* Conditional expectation of f given that g(a) = r. *)
Definition cond_expt_value{A : Type}{r : R} {g : A -> R}{p : Pmf A} (hne : 0 <> 𝕡[preim_outcomes_of_snd p g r])(f : A -> R)  : R :=
  let q:= preim_outcomes_of_snd p g r in
  list_sum [seq f x.2.1 * nonneg (x.1) | x <- q]/𝕡[preim_outcomes_of_snd p g r].

Lemma cond_expt_value_indep
{A : Type} {r : R} {f g : A -> R} {p : Pmf A}(hne : 0 <> 𝕡[preim_outcomes_of_snd p g r]) (Hi : independent p f g) :
  cond_expt_value hne f = expt_value p f.
Proof.
  unfold cond_expt_value. unfold prob,preim_outcomes_of_snd.
  simpl. rewrite list_fst_sum_compat. unfold list_fst_sum'.
  field_simplify.
  induction p.(outcomes).
  - simpl. admit.
  - simpl. destruct a. simpl. 
    rewrite filter_cat. rewrite filter_comp. rewrite IHl. 
      reflexivity.
  intro H. unfold prob in hne. simpl in hne.
  rewrite list_fst_sum_compat in hne. unfold list_fst_sum' in hne. firstorder.
Qed.   
 *)

