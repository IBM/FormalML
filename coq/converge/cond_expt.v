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


Lemma list_sum_const_mul {A : Type} (l : list (nonnegreal*R)) :
  forall r, list_sum (map (fun x => r*x.2) l)  = r*list_sum(map (fun x => x.2) l).
Proof.
  intro r.
  induction l.
  simpl; lra.
  simpl. rewrite IHl ; lra.
Qed.

End aux.

Section quotient.

  Context {A} R {equiv:Equivalence R}  {dec:EqDec A R}.

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

  Definition all_equivs (l:list (list A)) := Forall (is_equiv_class) l.


  Lemma all_equivs_nil : all_equivs nil.
  Proof.
    now red.
  Qed.

  Lemma add_to_bucket_all_equivs a l : all_equivs l -> all_equivs (add_to_bucket a l).
  Proof.
    unfold all_equivs, is_equiv_class, is_equiv_class, ForallPairs.
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

 Lemma quotient_all_equivs l : all_equivs (quotient l).
  Proof.
    Hint Resolve all_equivs_nil : ml.
    Hint Resolve add_to_bucket_all_equivs : ml.

    induction l; simpl; auto with ml.
  Qed.

  Hint Resolve quotient_all_equivs : ml.
  
  Definition different_buckets l1 l2 := forall x y, In x l1 -> In y l2 -> ~ R x y.

  Definition all_different l := ForallOrdPairs different_buckets l.

  Lemma all_different_nil : all_different nil.
  Proof.
    constructor.
  Qed.
  
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
    all_equivs l ->
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
        generalize (add_to_bucket_all_equivs a l H2); intros.
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
    induction l ; simpl ; auto with ml.
  Qed.

  Hint Resolve quotient_all_different : ml.

  Definition is_partition l := all_equivs l /\ all_different l.

  Lemma quotient_partitions l : is_partition (quotient l).
  Proof.
    red; auto with ml.
  Qed.

  Hint Resolve quotient_partitions : ml.

  Lemma quotient_buckets_disjoint l ll1 l2 ll3 l4 ll5  :
    quotient l = ll1 ++ l2 :: ll3 ++ l4 :: ll5 ->
    forall x y, In x l2 /\ In y l4 -> ~ R x y.
  Proof.
    set (quotient_all_different l). 
    intro H.
    setoid_rewrite H in a. 
    unfold all_different in a. unfold different_buckets in a.
    set (ForallOrdPairs_In a).  simpl in o. clear H. 
    intros x y H0. 
    specialize (o l2 l4). 
    enough (h2 : In l2 (ll1 ++ l2 :: ll3 ++ l4 :: ll5)).
    enough (h4 : In l4 (ll1 ++ l2 :: ll3 ++ l4 :: ll5)).
    specialize (o h2 h4).
    case o.
    - intro H. rewrite H in H0. admit. 
    - intro H. case H. intro H1. apply H1. now destruct H0. now destruct H0.  
      intro G. apply G. 
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


Local Instance Eq_dec_im_eq (f : A -> R) : EqDec A (im_eq f) := 
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
      
Lemma Forall_group_by_image {A} (l : list A) (f : A -> R) :
 Forall (fun l0 => (forall a b, In a l0 -> In b l0 -> (f a = f b))) (group_by_image f l). 
Proof.
  apply quotient_partitions. 
Qed.

Lemma In_group_by_image {A} {l : list A} {f : A -> R} :
  forall l0, In l0 (group_by_image f l) -> (forall a b, In a l0 -> In b l0 -> (f a = f b)).
Proof.
  rewrite <- Forall_forall.
  apply Forall_group_by_image.
Qed.

Lemma In_group_by_image_sublist {A} {l : list A} {f : A -> R}  :
  forall {l0 l0'}, In l0 (group_by_image f l) -> (forall c, In c l0' -> In c l0)
            -> (forall a b, In a l0 -> In b l0' -> (f a = f b)).
Proof.
  intros l0 l0' H H0 a b H1 H2.
  set (Hin := In_group_by_image _ H).
  specialize (H0 b H2).
  now specialize (Hin a b H1 H0).
Qed.

Lemma cons_In_group_by_image {A} {l : list A} {f : A -> R} {a : A} :
 forall l0, In (a :: l0) (group_by_image f l) -> (forall b, In b l0 -> (f a = f b)).
Proof.
  intros l0 Hl0 b Hb.
  set (In_group_by_image (a :: l0) Hl0). 
  eapply e ; eauto. 
  simpl ; intuition.
  simpl ; intuition. 
Qed.
 
Lemma map_rep {A} {l0 : list A} {f : A -> R} {a0 : A} :
(forall b : A, In b l0 -> f a0 = f b) -> map (fun x => f x) l0 = map (fun x => f a0) l0.
Proof.
  intro H.
  induction l0.
  - simpl ; easy.
  - simpl in *. rewrite IHl0. 
    f_equal. symmetry. 
    apply H. left. reflexivity. 
    intros b Hb.
    apply H. right. assumption.
Qed.

Lemma eq_class_eq_rep_hd {A : Type} {l : list A} {f : A -> R} :
  forall {l0}, In l0 (group_by_image f l) ->
        let a := match l0 with
                 | [] => 0
                 | x :: xs => f x
                 end in 
        (map f l0) = (map (fun x => a) l0).
Proof.
  intros l0 Hl0 a.
  induction l0.  
  - simpl; easy.  
  - simpl. f_equal. apply map_rep. 
    apply (cons_In_group_by_image _ Hl0). 
Qed. 

Lemma list_sum_map_const {A} (l : list A) (a : A) (f : A -> R) :
  list_sum (map (fun x => f a) l) = INR(length l)* (f a).
Proof.   
  induction l.
  - simpl ; lra. 
  - simpl. rewrite IHl.
    enough (match length l with
            | 0%nat => 1
            | S _ => INR (length l) + 1
            end = INR(length l) + 1). 
    rewrite H ; lra.
    generalize (length l) as n.
    intro n.  induction n.
    + simpl ; lra.
    + lra. 
Qed.

Lemma list_sum_eq_class {A : Type} (l : list A) (f : A -> R) :
  forall l0, In l0 (group_by_image f l) -> list_sum (map f l0) = INR(length l0)*match l0 with
                                                                          | [] => 0
                                                                          | x :: xs => f x
                                                                          end.
Proof.   
  intros l0 Hl0. 
  rewrite (eq_class_eq_rep_hd Hl0).
  destruct l0. 
  - simpl ; lra.
  - simpl. rewrite (list_sum_map_const l0).
    enough (match length l0 with
            | 0%nat => 1
            | S _ => INR (length l0) + 1
            end = INR(length l0) + 1). 
    rewrite H ; lra.
    generalize (length l0) as n.
    intro n.  induction n.
    + simpl ; lra.
    + lra. 
Qed.

Lemma list_sum_eq_list_sum_quotient {A : Type} (l : list A) (f : A -> R):
  list_sum (map f l) = list_sum (map f (concat (group_by_image f l))). 
Proof.
  now rewrite unquotient_quotient.   
Qed.

Lemma concat_map_map {A} (l : list(list A)) (f : A -> R) :
  concat (map (map f) l) = map f (concat l).
Proof.
  induction l. 
  simpl ; reflexivity. 
  simpl. rewrite map_cat. rewrite IHl. 
  reflexivity.
Qed.

Lemma list_sum_map_concat (l : list(list R)) :
  list_sum (concat l) = list_sum (map list_sum l).
Proof.   
  induction l. 
  - simpl ; reflexivity.
  - simpl ; rewrite list_sum_cat. now rewrite IHl. 
Qed.

Theorem list_sum_map_sum_eq_class {A} (l : list A) (f : A -> R) :
  list_sum (map f l) = list_sum (map (fun l0 => INR(length l0)*match l0 with
                                                          | [] => 0
                                                          | x :: xs => f x
                                                          end) (group_by_image f l)).
Proof.
  rewrite list_sum_eq_list_sum_quotient.
  rewrite <-concat_map_map.
  rewrite list_sum_map_concat.
  rewrite <-map_comp. f_equal.
  apply List.map_ext_in.
  apply list_sum_eq_class. 
Qed.


End list_sum.


Section expt_value_quotient.

Arguments outcomes {_}. 


Lemma expt_value_eq_class_aux {A : Type} {f : A -> R} {p : Pmf A} :
  forall {l0}, In l0 (group_by_image (fun x : nonnegreal * A => f x.2) p.(outcomes)) ->
        let a := match l0 with
                 | [] => 0
                 | x :: xs => f x.2
                 end in 
        (map (fun x => f x.2 * nonneg(x.1)) l0) = (map (fun x => a*nonneg(x.1)) l0).
Proof.
  intros l0 Hl0 a.
    destruct l0.  
  - simpl; easy.  
  - simpl. f_equal. apply List.map_ext_in.
    intros a0 Ha0. f_equal. symmetry. 
    apply (cons_In_group_by_image _ Hl0).  assumption. 
Qed.

Lemma list_sum_const_mul' {A:Type} (l : list (nonnegreal*A)) (a : R) :
  list_sum [seq a* nonneg(x.1) | x <- l] = a*list_sum[seq nonneg(x.1) | x <- l].
Proof.
  induction l.
  + simpl ; lra.
  + simpl. rewrite IHl. lra.
Qed.

Lemma expt_value_summand {A} (p : Pmf A) (f : A -> R) : 
forall l0, In l0 (group_by_image (fun x : nonnegreal * A => f x.2) p.(outcomes)) -> 
      list_sum [seq f x.2 * nonneg(x.1) | x <- l0]  = 𝕡[l0]*match l0 with
                              | [] => 0
                              | x :: xs => f x.2 
                              end.
Proof.
  intros l0 Hl0.
  unfold prob. simpl. rewrite list_fst_sum_compat ; unfold list_fst_sum'.
  rewrite (expt_value_eq_class_aux Hl0).
  destruct l0.
  - simpl ; lra.
  - simpl in *. rewrite list_sum_const_mul'. lra. 
Qed.    


Lemma expt_value_eq_list_sum_quotient {A : Type} (p : Pmf A) (f : A -> R):
  expt_value p f = list_sum (map (fun x => f x.2 * nonneg(x.1)) (concat (group_by_image (fun x => f x.2) p.(outcomes)))). 
Proof.
  unfold expt_value.
  now rewrite unquotient_quotient.   
Qed.

(* Rewriting expected value of f as a sum grouped by range values of f. *)
Theorem expt_value_eq_class {A} (f : A -> R) (p : Pmf A) :
  expt_value p f = list_sum (map (fun l => 𝕡[l]*match l with
                                             | [] => 0
                                             | x :: xs => f x.2
                                             end) (group_by_image (fun x => f x.2) p.(outcomes))).
Proof.
  rewrite expt_value_eq_list_sum_quotient.
  rewrite <-concat_map_map.
  rewrite list_sum_map_concat.
  rewrite <-map_comp. f_equal.
  apply List.map_ext_in.  apply expt_value_summand. 
Qed.

End expt_value_quotient.

Section conditional.
  Local Instance EqDecR : EqDec R eq := Req_EM_T. 
  Arguments outcomes {_}.

  (* All p.(outcomes) which are preimages of a fixed r in R under the random variable g. *)
  Definition preim_outcomes_of {A : Type} (p : Pmf A) (g : A -> R) (r : R) :=
  filter (fun x => (g x.2 ==b r)) p.(outcomes).

  Definition preim_outcomes_of_And {A : Type} (l : list(nonnegreal*A)) (f g : A -> R) (r1 r2 : R) :=
  filter (fun x => andb (f x.2 ==b r1) (g x.2 ==b r2)) l.

  Definition hd' {A} (f : A -> R) (l : seq(nonnegreal*A)) :=
    match l with
    | [] => 0
    | x :: xs => f x.2
    end .
  
  Definition cond_expt {A} (p : Pmf A) (f : A -> R) (g : A -> R) (r : R) : R :=
    list_sum (map (fun l => 𝕡[l]*(hd' f l)) (group_by_image (fun x => f x.2) (preim_outcomes_of p g r))).


  Definition preserves_partitions {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} (f:list (list A)->list (list A))
    := forall (l:list (list A)), is_partition R l ->
            is_partition R (f l).

  Lemma In_filter_In_list {A}{l : list A} {p : A -> bool} {a : A} :
    In a (filter p l) -> In a l.
  Proof.
    intros H.
    induction l.
    - simpl in H ; firstorder.
    - simpl in *.
      match_destr_in H.  
      -- simpl in H ; intuition.
      -- right ; intuition.
  Qed.
  
  Lemma In_list_In_filter {A} {l : list A} {p : A -> bool} {a : A} :
    p a = true -> In a l -> In a (filter p l).
  Proof.
    intros pa Ha. 
    induction l.
    - simpl in Ha ; exfalso ; assumption.
    - simpl in Ha. simpl. case_eq (p a0).
      intro pa0. simpl ; intuition.
      intro pa0 ; intuition.
      rewrite <-H in pa. rewrite pa0 in pa.
      firstorder. 
  Qed.
  
    Lemma ForallPairs_filter {A} R (l : list A) (p : A -> bool) :
    ForallPairs R l -> ForallPairs R (filter p l).
  Proof.
    intros H. unfold ForallPairs in *.
    intros a b Ha Hb.
    set (ha := In_filter_In_list Ha).
    set (hb := In_filter_In_list Hb).
    now specialize (H a b ha hb).
  Qed. 
  
  Lemma ForallOrdPairs_filter {A} R (l : list A) (p : A -> bool) :
    ForallOrdPairs R l -> ForallOrdPairs R (filter p l).
  Proof.
    intros H.
    induction l. 
    - simpl ; constructor.
    - simpl. case_eq (p a).
      + invcs H. specialize (IHl H3).
        intro Hpa. constructor ; trivial.
        apply Forall_filter ; trivial.
      + intro Hpa.
        invcs H. specialize (IHl H3). assumption. 
  Qed.

    Lemma Forall_map_filter {A} R (l : list(list A)) (p : A -> bool) :
     Forall (is_equiv_class R) l -> Forall (is_equiv_class R) (map (filter p) l).
  Proof.
    intros H.
    induction l. 
    - simpl ; constructor.
    - simpl. constructor. 
      + invcs H. specialize (IHl H3).
        revert IHl. 
        rewrite Forall_forall. intro IHl.
        specialize (IHl a).
        intros a0 b Ha0 Hb.
        apply H2. apply (In_filter_In_list Ha0).
        apply (In_filter_In_list Hb).
      + invcs H. specialize (IHl H3).
        assumption.
   Qed.       

      Lemma ForallOrdPairs_map_filter {A} R (l : list(list A)) (p : A -> bool):
     ForallOrdPairs (different_buckets R) l -> ForallOrdPairs (different_buckets R) (map (filter p) l).
  Proof.
    intros H.
    apply ListAdd.ForallOrdPairs_impl ; trivial.
    induction  l. invcs H.
    - simpl ; constructor.
    - simpl in *. constructor.
      -- invcs H. intuition.
         rewrite Forall_forall. 
         intros x Hxl Hax. 
         unfold different_buckets in *. 
         intros x0 y H0 H1.
         specialize (Hax x0 y).
         apply Hax. apply (In_filter_In_list H0).
         apply (In_filter_In_list H1).
      -- invcs H. now apply IHl. 
  Qed.
  
  Lemma filter_preserves_partitions {A} {R} {equiv:Equivalence R}  {dec:EqDec A R}
  (p:list A -> bool) :
  preserves_partitions (filter p).
  Proof.
    intros l pl.
    split. destruct pl as [Heq Had]. 
    - apply Forall_filter ; trivial. 
    - apply ForallOrdPairs_filter. destruct pl ; trivial. 
  Qed.


  Lemma map_filter_preserves_partitions {A} {R} {equiv:Equivalence R}  {dec:EqDec A R}
        (p:A -> bool) :
    preserves_partitions (map (filter p)).
  Proof.
    intros l pl.
    split. 
    destruct pl as [Heq Had].
    - unfold all_equivs in *. rewrite Forall_map. 
      revert Heq. 
      do 2 rewrite Forall_forall.
      intros Heq x Hin. specialize (Heq x Hin).
      now apply ForallPairs_filter. 
    - destruct pl as [Heq Hed].
      apply ForallOrdPairs_map_filter. assumption.
   Qed.

  Import Permutation. 
  Lemma Permutation_concat_is_partition {A} R {equiv:Equivalence R}  {dec:EqDec A R} l l' :
    is_partition R l ->
    is_partition R l'->
    Permutation (concat l) (concat l') ->
    Permutation l l'.
  Proof.
    intros Hl Hl' Hcll'.
    invcs Hcll'. 
    - assert (Forall (eq []) l') by now rewrite <-concat_nil_r. 
      assert (Forall (eq []) l) by now rewrite <-concat_nil_r. 
      admit.
    - admit. 
    - admit.
    - admit.
  Admitted. 

  Lemma add_to_bucket_is_partition {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} a :
    preserves_partitions (add_to_bucket R a).
  Proof.
    intros ? [??].
    split.
    - now apply add_to_bucket_all_equivs.
    - now apply add_to_bucket_all_different.
  Qed.
  
     Lemma add_to_bucket_filter_true {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} (l : list(list A)) (p : A -> bool) (a : A):
    p a = true ->
    is_partition R l ->
    Permutation (add_to_bucket R a (map (filter p) l)) (map (filter p) (add_to_bucket R a l)).
  Proof.
    intros pa isp.
    apply (Permutation_concat_is_partition R).
    - apply add_to_bucket_is_partition.
      now apply map_filter_preserves_partitions.
    - apply map_filter_preserves_partitions.
      now apply add_to_bucket_is_partition.
    - rewrite add_to_bucket_perm.
      do 2 rewrite <- concat_filter.
      rewrite add_to_bucket_perm.
      simpl.
      rewrite pa.
      reflexivity.
  Qed.

  Lemma add_to_bucket_filter_false {A} R {equiv:Equivalence R}  {dec:EqDec A R} (l : list(list A)) (p : A -> bool) (a : A):
    p a = false ->
    filter_nil (map (filter p) l) = filter_nil (map (filter p) (add_to_bucket R a l)).
  Proof.
    intros pa.
    induction l; simpl.
    - rewrite pa; simpl; trivial.
    - destruct a0; simpl; trivial.
      case_eq (p a0); intros pa0; simpl.
      + destruct (equiv_dec a a0); simpl.
        * rewrite pa.
          rewrite pa0; simpl; trivial.
        * rewrite pa0; simpl.
          now rewrite IHl.
      + destruct (equiv_dec a a0); simpl.
        * rewrite pa.
          rewrite pa0; simpl; trivial.
        * rewrite pa0; simpl.
          now rewrite IHl.
  Qed.

  Lemma add_to_bucket_filter_nil {A} {R0} {equiv:Equivalence R0}  {dec:EqDec A R0} (l : list (list A)) (a:A) :
   add_to_bucket R0 a (filter_nil l) =
  filter_nil (add_to_bucket R0 a l). 
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. destruct a0. 
      simpl;  trivial.
      simpl. match_destr. simpl. rewrite IHl.
      reflexivity.
  Qed.
  
  Lemma group_by_image_filter_nil_perm {A : Type} (f : A -> R) (l : list A) (p : A -> bool):
    Permutation (group_by_image f (filter p l))
                (filter_nil (map (filter p) (group_by_image f l))).
  Proof.
    induction l.
    - simpl. reflexivity. 
    - simpl.
      match_case; intros pa.
      + rewrite <- add_to_bucket_filter_true; trivial.
        *  simpl.
           rewrite <- add_to_bucket_filter_nil.
           eapply (Permutation_concat_is_partition (im_eq f)).
           -- apply add_to_bucket_is_partition.
              apply quotient_partitions.
           -- apply add_to_bucket_is_partition.
              eapply filter_preserves_partitions.
              eapply map_filter_preserves_partitions.
              apply quotient_partitions.
           -- do 2 rewrite add_to_bucket_perm.
              rewrite IHl.
              reflexivity.
        * apply quotient_partitions.
      + erewrite <- (add_to_bucket_filter_false (im_eq f)) by eassumption.
        trivial.
        Unshelve.
        all: try apply im_eq_equiv.
        all: try apply Eq_dec_im_eq.
  Qed.

  Definition is_nil {A} (l : list A) :=
    negb (not_nil l).

  Lemma is_nil_def {A} (l : list A) :
    is_nil l = true <-> l = [].
  Proof.
    induction l.
    * intuition.
    * unfold is_nil. 
      split.
      -- simpl ; firstorder.
      -- intro H. symmetry in H. exfalso. apply (nil_cons H). 
  Qed. 
     
  Lemma list_sum_map_filter_split {A} (f : (list A) -> R) (l : list(list A)):
    list_sum(map f l) = list_sum(map f (filter_nil l)) + list_sum (map f (filter (is_nil) l)).
  Proof.
    unfold is_nil.
    induction l. 
    - simpl ; lra.
    - simpl. match_case.
      + intro Ha.
        simpl; rewrite IHl;lra.
      + intro Ha.
        simpl; rewrite IHl;lra.
  Qed.

  Lemma list_sum_is_nil {A} {f : (list A) -> R} (l : list(list A)) :
    (f nil = 0) -> list_sum (map f (filter (is_nil) l)) = 0.
  Proof. 
    induction l.
    - simpl ; reflexivity.
    - simpl. match_case.
      rewrite is_nil_def.
      intros Ha Hf.
      rewrite Ha. simpl. specialize (IHl Hf).
      rewrite IHl ; lra. 
  Qed.

  Lemma list_sum_filter_nil {A} {f : (list A) -> R} (l : list(list A)) :
    (f nil = 0) -> list_sum(map f l) = list_sum(map f (filter_nil l)).
  Proof.
    intro H.
    rewrite list_sum_map_filter_split.
    rewrite (list_sum_is_nil l H). 
    lra. 
  Qed.

  Lemma In_group_by_image_hd' {A} {f : A -> R}{l : seq(nonnegreal*A)}{l0 : seq (nonnegreal * A)}: 
    In l0 (group_by_image (fun x : nonnegreal * A => f x.2) l) ->
    forall a, In a l0 -> f a.2 = hd' f l0.
  Proof.
    intros H a Ha.
    induction l0.
    * simpl in Ha ; firstorder.
    * simpl in *. intuition. now rewrite H0.
      set (cons_In_group_by_image _ H). specialize (e a).
      simpl in e. symmetry. now apply e.
   Qed. 

   Lemma In_filter_hd' {A} {f : A -> R}{l : seq(nonnegreal*A)}{l0 : seq (nonnegreal * A)} p: 
    In l0 (group_by_image (fun x : nonnegreal * A => f x.2) l) ->
    forall a, In a (filter p l0) -> f a.2 = hd' f l0.
   Proof.
     intros H a Hin.
     apply (In_group_by_image_hd' H).
     apply (In_filter_In_list Hin). 
   Qed.

  Check In_group_by_image_sublist. 

  Lemma In_group_by_image_sublist_hd'{A} {l : list (nonnegreal*A)} {f : A -> R} : 
    forall {l0 l0' : seq(nonnegreal*A)}, In l0 (group_by_image (fun x : nonnegreal * A => f x.2) l)
                                    -> (forall c, In c l0' -> In c l0)
                                    -> (hd' f l0) = (hd' f l0').
  Proof.
    move=> l0 l0' H H0.
    induction l0.
    induction l0'.
    - reflexivity. 
    - simpl in *.  admit.
    - simpl. 
      
  Admitted.
  
   Lemma In_filter_hd'_filter {A} {f : A -> R}{l : seq(nonnegreal*A)}{l0 : seq (nonnegreal * A)} p: 
    In l0 (group_by_image (fun x : nonnegreal * A => f x.2) l) ->
     hd' f l0 = hd' f (filter p l0).
   Proof.
     intros H. 
     induction l0.
     - simpl ; reflexivity.
     - simpl in *. 
       set (cons_In_group_by_image _ H). simpl in e. 
       match_destr.
   Admitted.
   


   Lemma In_filter_hd'_eq {A} {f : A -> R}{l : seq(nonnegreal*A)}{l0 : seq (nonnegreal * A)} p: 
    In l0 (group_by_image (fun x : nonnegreal * A => f x.2) l) ->
     hd' f (filter p l0) = hd' f l0.
   Proof.
     intros Hin.
     induction l0.
     - simpl ; reflexivity.
     - simpl. match_destr.
       set (Hl := In_group_by_image_hd' Hin). 
       set (Hfil := In_filter_hd' p Hin).
       specialize (Hl a). specialize (Hfil a).
       simpl in *.
       
   Qed.
Lemma cond_expt_def {A} (p : Pmf A) (f : A -> R) (g : A -> R) (r : R) :
    cond_expt p f g r =
    list_sum
      ((map (fun l => 𝕡[(preim_outcomes_of_And l f g (hd' f l) r)]*(hd' f l)))
         (group_by_image (fun x => f x.2) p.(outcomes))).
  Proof.
    unfold cond_expt,preim_outcomes_of_And, preim_outcomes_of.
    rewrite group_by_image_filter_nil_perm.
    rewrite <-list_sum_filter_nil.
    * rewrite <-map_comp. unfold comp. simpl. f_equal. 
      apply List.map_ext_in.
      intros a Ha. f_equal.
      -- f_equal. apply filter_ext. intros x Hx.
         rewrite (In_group_by_image_hd' Ha x Hx). rewrite <-(Bool.andb_true_l (g x.2 ==b r)).
         f_equal. unfold equiv_decb. match_destr. firstorder. 
      -- induction a.
         ** simpl ; reflexivity.
         ** simpl in *. match_destr.
            set (cons_In_group_by_image _ Ha). simpl in e.
            symmetry. 
            
    * unfold prob. simpl ; lra. 
  Admitted.
  
      
End conditional.
