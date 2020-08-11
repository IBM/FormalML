Require Import Reals EquivDec List LibUtils Permutation Morphisms.
Require Import pmf_monad.
Require Import micromega.Lra.
From mathcomp Require Import ssreflect ssrfun seq.

Set Bullet Behavior "Strict Subproofs".


Import ListNotations.
Local Open Scope list_scope.

Open Scope R_scope.

Section aux.

  Lemma ForallOrdPairs_app_in {A R} {l1 l2:list A} : ForallOrdPairs R (l1 ++ l2) ->
                                                     forall x y, In x l1 -> In y l2 -> R x y.
  Proof.
    revert l2.
    induction l1; simpl; intros.
    - intuition.
    - invcs H.
      destruct H0.
      + subst.
        eapply (Forall_forall _ _) in H4; try eassumption.
        rewrite in_app_iff; eauto.
      + eapply IHl1; eauto.
  Qed.
  
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

  Lemma quotient_buckets_disjoint_app l ll1 ll2 :
    quotient l = ll1 ++ ll2 ->
    forall l1 l2 x y, In l1 ll1 -> In l2 ll2 ->
                 In x l1 -> In y l2 -> ~ R x y.
  Proof.
    intros eqq.
    generalize (quotient_all_different l); intros HH.
    rewrite eqq in HH.
    red in HH.
    intros.
    generalize (ForallOrdPairs_app_in HH); intros HH2.
    specialize (HH2 _ _ H H0).
    apply (HH2 _ _ H1 H2).
  Qed.
  
  Lemma quotient_buckets_disjoint_cons l ll1 l2 ll3 l4 ll5  :
    quotient l = ll1 ++ l2 :: ll3 ++ l4 :: ll5 ->
    forall x y, In x l2 -> In y l4 -> ~ R x y.
  Proof.
    intros.
    eapply (quotient_buckets_disjoint_app l (ll1++(l2::ll3)) (l4::ll5)); simpl; try eassumption.
    - rewrite app_ass; simpl; trivial.
    - rewrite in_app_iff; simpl; eauto.
    - eauto.
  Qed.

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

  Lemma filter_nil_quotient {A} R {equiv:Equivalence R}  {dec:EqDec A R} (l:list A) :
    filter_nil (quotient R l) = quotient R l.
  Proof.
    induction l; simpl; trivial.
    rewrite <- add_to_bucket_filter_nil.
    now rewrite IHl.
  Qed.

  Lemma add_to_bucket_nnil {A} {R0} {equiv:Equivalence R0}  {dec:EqDec A R0} (l : list (list A)) (a:A) :
    Forall (fun x => not_nil x = true) l ->
    Forall (fun x => not_nil x = true) (add_to_bucket R0 a l).
  Proof.
    induction l; simpl; intros HH.
    - eauto.
    - invcs HH.
      destruct a0; simpl; [eauto | ].
      destruct (equiv_dec a a0); simpl; eauto.
  Qed.

  Lemma quotient_nnil {A} R {equiv:Equivalence R}  {dec:EqDec A R} (l:list A) :
    Forall (fun x => not_nil x = true) (quotient R l).
  Proof.
    induction l; simpl; trivial.
    now apply add_to_bucket_nnil.
  Qed.
  
  Lemma is_partition_cons_inv {A} {R} {x:list A} {l} :
    is_partition R (x :: l) -> is_partition R l.
  Proof.
    intros [HH1 HH2]; red.
    invcs HH1; invcs HH2.
    auto.
  Qed.

  Global Instance filter_nil_perm_proper  {A} : Proper ((@Permutation (list A)) ==> (@Permutation (list A))) (@filter_nil A).
  Proof.
    unfold Proper, respectful.
    apply Permutation_ind_bis; simpl; intros.
    - trivial.
    - match_destr; auto.
    - repeat match_destr; auto.
      rewrite H0.
      apply perm_swap.
    - rewrite H0; trivial.
  Qed.

  Global Instance all_equivs_perm {A} R : Proper (@Permutation (list A) ==> iff) (all_equivs R).
  Proof.
    unfold all_equivs; intros l1 l2 perm.
    rewrite perm.
    intuition.
  Qed.

  Global Instance ForallOrdPairs_perm {A} R {sym:Symmetric R} : Proper (@Permutation A ==> iff) (ForallOrdPairs R).
  Proof.
    cut (forall l l', Permutation l l' -> (fun l l' => ForallOrdPairs R l -> ForallOrdPairs R l') l l').
    {
      unfold Proper, respectful; simpl; split; intros.
      - eapply H; try eapply H1; eauto.
      - eapply H; try eapply H1.
        symmetry; eauto.
    } 
    apply Permutation_ind_bis; simpl; intros.
    - trivial.
    - invcs H1.
      constructor; auto 2.
      now rewrite <- H.
    - invcs H1.
      invcs H5.
      invcs H4.
      constructor.
      + rewrite <- H.
        constructor; trivial.
        now symmetry.
      + constructor.
        * now rewrite <- H.
        * eauto.
    - eauto.
  Qed.

  Instance different_buckets_symmetric {A} (R:A->A->Prop) {sym:Symmetric R} : Symmetric (different_buckets R).
  Proof.
    unfold Symmetric, different_buckets; intros.
    intros rr.
    apply (H _ _ H1 H0).
    now symmetry.
  Qed.
  
  Instance all_different_perm {A} R {equiv:Equivalence R} : Proper (@Permutation (list A) ==> iff) (all_different R).
  Proof.
    unfold all_different; intros HH1 HH2 perm.
    rewrite perm.
    intuition.
  Qed.

  Instance is_partition_perm {A} R {equiv:Equivalence R} : Proper (@Permutation (list A) ==> iff) (is_partition R).
  Proof.
    unfold is_partition; intros l l1 perm.
    repeat rewrite perm.
    intuition.
  Qed.
  
  Lemma add_to_bucket_perm_preserved {A} R {equiv:Equivalence R}  {dec:EqDec A R} x l l' :
    Permutation l l' ->
    is_partition R l ->
    Permutation (filter_nil (add_to_bucket R x l)) (filter_nil (add_to_bucket R x l')).
  Proof.
    Hint Resolve is_partition_cons_inv : ml.
    cut (forall l l' : seq (seq A),
            Permutation l l' ->
            (fun l l' => (is_partition R l -> Permutation (filter_nil (add_to_bucket R x l)) (filter_nil (add_to_bucket R x l')))) l l')
    ; [intuition | ].
    apply Permutation_ind_bis; simpl; intros.
    - trivial.
    - destruct x0.
      + apply H0; eauto with ml.
      + destruct (equiv_dec x a); simpl.
        * now rewrite H.
        * rewrite H0; eauto with ml.
    - destruct y; simpl.
      + destruct x0; simpl.
        * apply H0; eauto with ml.
        * destruct (equiv_dec x a); simpl.
          -- now rewrite H. 
          -- rewrite H0; eauto with ml.
      + destruct (equiv_dec x a); simpl.
        -- destruct x0; simpl.
           ++ now rewrite H.
           ++ destruct (equiv_dec x a0); simpl.
              ** (* show a contradiction *)
                destruct H1 as [? isdiff].
                invcs isdiff.
                invcs H4.
                elim (H6 a a0); simpl; eauto 2.
                now rewrite <- e.
              ** rewrite H.
                 apply perm_swap.
        -- destruct x0; simpl.
           ++ eauto with ml.
           ++ destruct (equiv_dec x a0); simpl.
              ** rewrite H.
                 apply perm_swap.
              ** rewrite H0 ; [| eauto with ml].
                 apply perm_swap.
    - rewrite H0; trivial.
      apply H2.
      now rewrite <- H.
  Qed.

  Hint Resolve quotient_partitions : ml.

  Definition same_subsets {A} (l1 l2:list (list A))
    := exists l1', Permutation l1 l1' /\ Forall2 (@Permutation A) l1' l2.

  Lemma filter_nil_nnil {A} (l:list (list A)) : Forall (fun x => not_nil x = true) (filter_nil l).
  Proof.
    induction l; simpl; trivial.
    destruct a; simpl; trivial.
    constructor; trivial.
  Qed.

  Lemma nnil_filter_nil_id {A} (l:list (list A)) : Forall (fun x => not_nil x = true) l ->
                                                   filter_nil l = l.
  Proof.
    induction l; simpl; trivial.
    intros HH; invcs HH.
    destruct a; simpl.
    - simpl in *; discriminate.
    - now rewrite IHl.
  Qed.

  Lemma add_to_bucket_nnil_perm_preserved {A} R {equiv:Equivalence R}  {dec:EqDec A R} x l l' :
    Forall (fun x => not_nil x = true) l ->
    Permutation l l' ->
    is_partition R l ->
    Permutation (add_to_bucket R x l) (add_to_bucket R x l').
  Proof.
    intros.
    cut (Permutation (filter_nil (add_to_bucket R x l)) (filter_nil (add_to_bucket R x l'))).
    - repeat rewrite <- add_to_bucket_filter_nil.
      repeat rewrite nnil_filter_nil_id; trivial.
      now rewrite <- H0.
    - now apply add_to_bucket_perm_preserved.
  Qed.
    
  (*
  Lemma filter_nil_id_perm {A} (l1 l2:list (list A)) : Permutation l1 l2 -> filter_nil l1 = l1 -> filter_nil l2 = l2.
  Proof.
    revert l1 l2.
    cut (forall l1 l2:list (list A), Permutation l1 l2 -> (fun l1 l2 => filter_nil l1 = l1 -> filter_nil l2 = l2) l1 l2)
    ; [eauto | ].
    apply Permutation_ind_bis; simpl; intros.
    - trivial.
    - destruct x; simpl in *.
      + invcs H1.
        now rewrite H0.
      +     
*)

  Instance equiv_class_perm {A} R :
    Proper (Permutation (A:=A) ==> iff) (is_equiv_class R).
  Proof.
    unfold Proper, respectful, is_equiv_class, ForallPairs; intros.
    split; intros.
    - eapply H0; now rewrite H.
    - eapply H0; now rewrite <- H.
  Qed.

  Instance different_buckets_perm {A} R :
    Proper (Permutation (A:=A) ==> Permutation (A:=A) ==> iff) (different_buckets R).
  Proof.
    cut ( Proper (Permutation (A:=A) ==> Permutation (A:=A) ==> Basics.impl) (different_buckets R))
    ; unfold Proper, respectful, different_buckets, Basics.impl; intros.
    - split; intros.
      + eapply H; try eapply H3; try eapply H4; eauto.
      + eapply H.
        * symmetry; eapply H0.
        * symmetry; eapply H1.
        * eauto.
        * eauto.
        * eauto.
    - eapply H1.
      + now rewrite H.
      + now rewrite H0.
  Qed.

  Instance forall_perm_partition {A} R :
    Proper (Forall2 (Permutation (A:=A)) ==> iff) (is_partition R).
  Proof.
    unfold Proper, respectful.
    cut ( forall x y : seq (seq A), Forall2 (Permutation (A:=A)) x y -> is_partition R x -> is_partition R y).
    { intuition; eauto 2.
      eapply H; try eapply H1.
      now symmetry.
    }
    intros x y f2.
    induction f2; simpl; trivial.
    intros [HH1 HH2].
    invcs HH1.
    invcs HH2.
    destruct IHf2 as [HH1' HH2'].
    - now split.
    - split; constructor; trivial.
      + now rewrite <- H.
      + revert H4.
        apply Forall2_Forall_trans.
        revert f2.
        apply Forall2_incl; intros.
        rewrite <- H.
        now rewrite <- H4.
  Qed.

  Instance same_subsets_partition {A} (R:list (list A) -> (list (list A) -> Prop)) {equiv:Equivalence R} :
    Proper (same_subsets ==> iff) (is_partition R).
  Proof.
    unfold Proper, respectful, same_subsets.
    intros ? ? [ll [pl f2l]].
    rewrite pl.
    now eapply forall_perm_partition.
  Qed.
  
  Lemma forall_perm_add_to_bucket {A} R {equiv:Equivalence R} {dec:EqDec A R} x l1 l2 :
    is_partition R l1 ->
    Forall2 (Permutation (A:=A)) l1 l2 ->
    Forall2 (Permutation (A:=A)) (add_to_bucket R x l1) (add_to_bucket R x l2).
  Proof.
    intros isp HH1.
    induction HH1; simpl.
    - eauto.
    - specialize (IHHH1 (is_partition_cons_inv isp)).
      destruct x0; simpl.
      + destruct y; trivial.
        apply Permutation_nil in H; discriminate.
      + destruct (equiv_dec x a); simpl.
        * destruct y.
          -- symmetry in H; apply Permutation_nil in H; discriminate.
          -- destruct (equiv_dec x a0).
             ++ eauto.
             ++ destruct isp as [Req Rdiff].
                invcs Req.
                elim c.
                rewrite e.
                apply H2.
                ** simpl; eauto.
                ** rewrite H; simpl; eauto.
        * destruct y.
          -- symmetry in H; apply Permutation_nil in H; discriminate.
          -- destruct (equiv_dec x a0).
             ++ destruct isp as [Req Rdiff].
                invcs Req.
                elim c.
                rewrite e.
                apply H2.
                ** rewrite H; simpl; eauto.
                ** simpl; eauto.
             ++ eauto.
  Qed.

  Lemma Forall2_perm {A} R (l1 l1' l2:list A) :
      Forall2 R l1 l2 ->
      Permutation l1 l1' ->
      exists l2', Permutation l2 l2' /\
             Forall2 R l1' l2'.
  Proof.
    revert l2.
    cut (forall (l1 l1':list A),
      Permutation l1 l1' ->
      (fun l1 l1' => forall l2, Forall2 R l1 l2 ->
                        exists l2', Permutation l2 l2' /\
                               Forall2 R l1' l2') l1 l1')
    ; [ eauto | ].
    apply Permutation_ind_bis; simpl; intros.
    - invcs H. exists nil; eauto.
    - invcs H1.
      destruct (H0 _ H6) as [? [??]].
      exists (y::x0).
      split.
      + now rewrite H1.
      + now constructor.
    - invcs H1.
      invcs H6.
      destruct (H0 _ H7) as [? [??]].
      exists (y1 :: y0 :: x0).
      split.
      + rewrite H1.
        apply perm_swap.
      + repeat constructor; trivial.
    - destruct (H0 _ H3) as [? [??]].
      destruct (H2 _ H5) as [? [??]].
      exists x0.
      split; trivial.
      etransitivity; eauto.
  Qed.

  Instance same_subsets_equiv {A} : Equivalence (@same_subsets A).
  Proof.
    constructor; red; unfold same_subsets.
    - intros l.
      exists l.
      split; reflexivity.
    - intros l1 l2 [ll [p p2]].
      symmetry in p.
      destruct (Forall2_perm _ _ _ _ p2 p) as [xl [xp xp2]].
      exists xl.
      split; trivial.
      symmetry; trivial.
    - intros l1 l2 l3 [ll [p p2]] [ll' [p' p2']].
      symmetry in p2.
      destruct (Forall2_perm _ _ _ _ p2 p') as [xl [xp xp2]].
      exists xl.
      split.
      + now rewrite p.
      + etransitivity.
        * symmetry; eassumption.
        * assumption.
  Qed.

  
  Lemma add_to_bucket_is_partition {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} a :
    preserves_partitions (add_to_bucket R a).
  Proof.
    intros ? [??].
    split.
    - now apply add_to_bucket_all_equivs.
    - now apply add_to_bucket_all_different.
  Qed.
  

  Lemma add_to_bucket_diff_perm_swap {A} R {equiv:Equivalence R} {dec:EqDec A R} x y l :
    is_partition R l ->
    ~ R x y ->
    Permutation (add_to_bucket R y (add_to_bucket R x l)) (add_to_bucket R x (add_to_bucket R y l)).
  Proof.
    induction l; simpl; intros.
    - match_destr.
      + elim H0.
        now symmetry.
      + match_destr.
        * now elim H0.
        * apply perm_swap.
    - specialize (IHl (is_partition_cons_inv H) H0).
      destruct a; trivial.
      + destruct (x == a).
        * destruct (y == a).
          -- elim H0.
             now rewrite e.
          -- simpl.
             destruct (y == x).
             ++ elim c; now rewrite e0.
             ++ destruct (x == a); [| congruence].
                trivial.
        * destruct (y == a); simpl.
          -- destruct (y == a); [ | congruence].
             destruct (x == y); trivial.
             now elim H0.
          -- destruct (y == a); [congruence | ].
             destruct (x == a); [congruence | ].
             now rewrite IHl.
  Qed.        

  Lemma add_to_bucket_same_perm2_swap {A} R {equiv:Equivalence R} {dec:EqDec A R} x y l :
    is_partition R l ->
    R x y ->
    Forall2 (@Permutation A) (add_to_bucket R y (add_to_bucket R x l)) (add_to_bucket R x (add_to_bucket R y l)).
  Proof.
    induction l; simpl; intros.
    - destruct (y == x).
      + destruct (x == y).
        * constructor; trivial.
          apply perm_swap.
        * elim c; now symmetry.
      + elim c; now symmetry.
    - specialize (IHl (is_partition_cons_inv H) H0).
      destruct a; simpl; trivial.
      + destruct (x == a).
        * destruct (y == a).
          -- simpl.
             destruct (y == x).
             ++ destruct (x == y).
                ** constructor.
                   --- apply perm_swap.
                   --- reflexivity.
                ** elim c; now symmetry.
             ++ elim c; now symmetry.
          -- elim c.
             now rewrite <- e.
        * destruct (y == a); simpl.
          -- destruct (y == a); [ | congruence].
             destruct (x == y); trivial.
             ++ elim c.
                now rewrite e1.
             ++ reflexivity.
          -- destruct (y == a); [congruence | ].
             destruct (x == a); [congruence | ].
             constructor; trivial.
  Qed.

  Instance quotient_perm_proper {A} R {equiv:Equivalence R} {dec:EqDec A R} :
    Proper (@Permutation A ==> @same_subsets A) (quotient R).
  Proof.
    unfold Proper, respectful.
    apply Permutation_ind_bis; simpl; intros.
    - unfold same_subsets; eauto.
    - unfold same_subsets; destruct H0 as [l1 [perm1 F1]].
      exists (add_to_bucket R x l1).
      split.
      + rewrite <- filter_nil_quotient.
        rewrite add_to_bucket_filter_nil.
        symmetry in perm1.
        rewrite <- add_to_bucket_nnil_perm_preserved; try eapply perm1.
        * rewrite <- add_to_bucket_filter_nil.
          rewrite nnil_filter_nil_id; trivial.
          rewrite perm1.
          apply quotient_nnil.
        * rewrite perm1.
          apply quotient_nnil.
        * rewrite perm1.
          apply quotient_partitions.
      + apply forall_perm_add_to_bucket; trivial.
        rewrite <- perm1.
        apply quotient_partitions.
    - red.
      destruct H0 as [l1 [perm1 F1]].
      destruct (x == y).
      + (* if R x y, then they go in the same bucket *)
        exists (add_to_bucket R y (add_to_bucket R x l1)).
        split.
        * apply add_to_bucket_nnil_perm_preserved.
          -- apply add_to_bucket_nnil.
             apply quotient_nnil.
          -- apply add_to_bucket_nnil_perm_preserved; eauto with ml.
             apply quotient_nnil.
          -- apply add_to_bucket_is_partition.
             apply quotient_partitions.
        * erewrite add_to_bucket_same_perm2_swap; trivial.
          -- apply forall_perm_add_to_bucket.
             ++ apply add_to_bucket_is_partition.
                rewrite <- perm1; eauto with ml.
             ++ apply forall_perm_add_to_bucket; trivial.
                rewrite <- perm1; eauto with ml.
          -- rewrite <- perm1; eauto with ml.
      +  (* if ~ R x y, then they go in different buckets *)
        exists (add_to_bucket R x (add_to_bucket R y l1)).
        split.
        * rewrite add_to_bucket_diff_perm_swap; eauto with ml.
          apply add_to_bucket_nnil_perm_preserved.
          -- apply add_to_bucket_nnil.
             apply quotient_nnil.
          -- apply add_to_bucket_nnil_perm_preserved; eauto with ml.
             apply quotient_nnil.
          -- apply add_to_bucket_is_partition.
             apply quotient_partitions.
        * apply forall_perm_add_to_bucket.
          -- apply add_to_bucket_is_partition.
             rewrite <- perm1.
             apply quotient_partitions.
          -- apply forall_perm_add_to_bucket; trivial.
             rewrite <- perm1.
             apply quotient_partitions.
    - etransitivity; eauto.
  Qed.

  Lemma add_to_bucket_new_perm {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} (l : list (list A)) a :
    Forall (Forall (fun y => ~ R a y)) l ->
    Permutation ([a]::filter_nil l) (filter_nil (add_to_bucket R a l)).
  Proof.
    induction l; simpl; intros FF.
    - eauto.
    - invcs FF.
      specialize (IHl H2).
      destruct a0; simpl; trivial.
      invcs H1.
      destruct (a == a0).
      + now elim H3.
      + simpl.
        rewrite <- IHl.
        apply perm_swap.
  Qed.

  Instance same_subsets_perm_sub {A} : subrelation (@Permutation (list A)) same_subsets.
  Proof.
    repeat red; intros.
    exists y.
    split; trivial.
    reflexivity.
  Qed.

  Instance same_subsets_perm2_sub {A} : subrelation (Forall2 (@Permutation A)) same_subsets.
  Proof.
    repeat red; intros.
    exists x.
    eauto.
  Qed.

  Instance not_nil_perm_proper {A} : Proper (@Permutation A ==> eq) (not_nil).
  Proof.
    unfold Proper, respectful, not_nil; intros.
    destruct x; destruct y; simpl; trivial.
    - apply Permutation_nil in H; discriminate.
    - symmetry in H.
      apply Permutation_nil in H; discriminate.
  Qed.
             
  Lemma add_to_bucket_same_subsets_proper {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} a {l1 l2} :
    is_partition R l1 ->
    same_subsets (filter_nil l1) (filter_nil l2) ->
    same_subsets (filter_nil (add_to_bucket R a l1)) (filter_nil (add_to_bucket R a l2)).
  Proof.
    intros isp [ll [lp lp2]].
    assert (isp': is_partition R (filter_nil l1)) by now apply filter_preserves_partitions  .
    generalize (add_to_bucket_perm_preserved _ a _ _ lp isp'); intros HH.
    rewrite <- add_to_bucket_filter_nil in HH.
    rewrite nnil_filter_nil_id in HH; [| apply filter_nil_nnil].
    rewrite add_to_bucket_filter_nil in HH.
    rewrite HH.
    apply same_subsets_perm2_sub.
    repeat rewrite <- add_to_bucket_filter_nil.
    apply forall_perm_add_to_bucket.
    - apply filter_preserves_partitions.
      now rewrite <- lp.
    - generalize (filter_nil_nnil l1); intros HH2.
      rewrite <- lp2.
      rewrite nnil_filter_nil_id.
      + reflexivity.
      + rewrite <- lp.
        rewrite Forall_forall; intros ? inn.
        apply filter_In in inn.
        tauto.
  Qed.

  Lemma same_subsets_nnil {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} {l1 l2:list (list A)} :
    same_subsets l1 l2 ->
    Forall (fun x => not_nil x = true) l1 ->
    Forall (fun x => not_nil x = true) l2.
  Proof.
    intros [ll [lp lp2]].
    rewrite lp.
    apply Forall2_Forall_trans.
    revert lp2.
    apply Forall2_incl; intros.
    now rewrite <- H1.
  Qed.

  Lemma add_to_bucket_nnil_same_subsets_proper {A} {R} {equiv:Equivalence R} {dec:EqDec A R} a {l1 l2} :
    Forall (fun x => not_nil x = true) l1 ->
    is_partition R l1 ->
    same_subsets l1 l2 ->
    same_subsets (add_to_bucket R a l1) (add_to_bucket R a l2).
  Proof.
    intros.
    assert (nnil2: Forall (fun x : seq A => not_nil x = true) l2).
    { eapply same_subsets_nnil; eauto. }
    generalize (@add_to_bucket_same_subsets_proper _ _ _ _ a l1 l2 H0); intros HH.
    repeat rewrite nnil_filter_nil_id in HH; auto 2.
    - now apply add_to_bucket_nnil.
    - now apply add_to_bucket_nnil.
  Qed.
  
(*  Lemma add_to_bucket_same_subsets_proper {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} a {l1 l2} :
    is_partition R l1 ->
    same_subsets l1 l2 ->
    same_subsets (filter_nil (add_to_bucket R a l1)) (filter_nil (add_to_bucket R a l2)).
  Proof.
    intros isp [ll [lp lp2]].
    rewrite (add_to_bucket_perm_preserved _ a _ _ lp isp).
    apply same_subsets_perm2_sub.
    repeat rewrite <- add_to_bucket_filter_nil.
    apply forall_perm_add_to_bucket.
    - apply filter_preserves_partitions.
      now rewrite <- lp.
    - apply filter_Forall2_same; trivial.
      revert lp2; clear; intros lp2.
      induction lp2; simpl; trivial.
      f_equal; trivial.
      now apply not_nil_perm_proper.
  Qed.
 *)

  Global Instance ForallPairs_sublist {A} {R} : Proper (sublist --> Basics.impl) (@ForallPairs A R).
  Proof.
    unfold Proper, respectful, Basics.impl, ForallPairs; intros.
    apply H0;
      eapply sublist_In; eauto.
  Qed.
  
  Lemma all_equivs_cons_sublist {A} R (x y:list A) l :
    sublist x y ->
    all_equivs R (y::l) -> all_equivs R (x::l).
  Proof.
    intros subl ale.
    invcs ale.
    constructor; trivial.
    unfold is_equiv_class in *.
    eapply ForallPairs_sublist; eauto.
  Qed.

  Lemma all_equivs_forall_sublist {A} R : Proper (Forall2 sublist --> Basics.impl) (@all_equivs A R).
  Proof.
    unfold Basics.flip, Basics.impl.
    intros x y f2.
    induction f2; simpl; trivial.
    intros HH.
    eapply all_equivs_cons_sublist; try eapply H.
    invcs HH.
    constructor; trivial.
    now apply IHf2.
  Qed.

  Lemma  all_different_cons_sublist {A} R (x y:list A) l :
    sublist x y ->
     all_different R (y::l) -> all_different R (x::l).
  Proof.
    intros subl ale.
    invcs ale.
    constructor; trivial.
    revert H1.
    apply Forall_impl; intros.
    unfold different_buckets in *; intros.
    apply H; trivial.
    eapply sublist_In; eauto.
  Qed.

  Instance different_buckets_sublist {A R} : Proper (sublist --> sublist --> Basics.impl) (@different_buckets A R).
  Proof.
    unfold Basics.impl, Basics.flip, different_buckets.
    intros x1 x2 s1 y1 y2 s2 df.
    intros.
    apply df; eapply sublist_In; eauto. 
  Qed.
  
  Lemma different_buckets_forall_sublist {A} {R} (y:list A) l l' :
    Forall2 sublist l l' ->
    Forall (different_buckets R y) l' ->
    Forall (different_buckets R y) l.
  Proof.
    intros f2; induction f2; simpl; trivial.
    intros f; invcs f.
    constructor; auto.
    eapply different_buckets_sublist; eauto.
    reflexivity.    
  Qed.

  Instance all_different_forall_sublist {A} R : Proper (Forall2 sublist --> Basics.impl) (@all_different A R).
  Proof.
    unfold Basics.flip, Basics.impl.
    intros x y f2.
    induction f2; simpl; trivial.
    intros HH.
    eapply all_different_cons_sublist; try eapply H.
    invcs HH.
    constructor; trivial.
    - eapply different_buckets_forall_sublist; eauto.
    - now apply IHf2.
  Qed.

  Lemma is_partition_cons_sublist {A} R (x y:list A) l :
    sublist y x ->
    is_partition R (x::l) -> is_partition R (y::l).
  Proof.
    intros subl [leq ldiff].
    split.
    - eapply all_equivs_cons_sublist; eauto.
    - eapply all_different_cons_sublist; eauto.
  Qed.

  Instance is_partition_forall_sublist {A} R : Proper (Forall2 sublist --> Basics.impl) (@is_partition A R).
  Proof.
    unfold Basics.flip, Basics.impl.
    intros x y f2.
    intros [??]; split.
    - eapply all_equivs_forall_sublist; eauto.
    - eapply all_different_forall_sublist; eauto.
  Qed.

  Lemma all_different_forall_cons_nin {A} R a l :
    all_different R ([a] :: l) ->
    Forall (Forall (fun y : A => ~ R a y)) l.
  Proof.
    intros HH.
    invcs HH.
    revert H1.
    apply Forall_impl; intros.
    unfold different_buckets in H.
    rewrite Forall_forall.
    simpl in H.
    eauto.
  Qed.
               
  Lemma is_partition_forall_cons_nin {A} R a l :
    is_partition R ([a] :: l) ->
    Forall (Forall (fun y : A => ~ R a y)) l.
  Proof.
    intros [??].
    now apply all_different_forall_cons_nin.
  Qed.

  Lemma quotient_unquotient {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} {l} :
    is_partition R l ->
    same_subsets (filter_nil l) (quotient R (concat l)).
  Proof.
    induction l; simpl; intros.
    - reflexivity.
    - specialize (IHl (is_partition_cons_inv H)).
      induction a; simpl; trivial.
      cut_to IHa.
      + destruct a0; simpl in *.    
        * rewrite add_to_bucket_new_perm; trivial.
          -- rewrite <- filter_nil_quotient.
             rewrite add_to_bucket_filter_nil.
             apply add_to_bucket_same_subsets_proper; trivial.
             ++ eapply is_partition_cons_inv; eauto.
             ++ now rewrite filter_nil_quotient.
          -- now apply is_partition_forall_cons_nin.
        * rewrite add_to_bucket_nnil_same_subsets_proper; trivial.
          4: symmetry; apply IHa.
          -- simpl.
             destruct (a == a0).
             ++ reflexivity.
             ++ invcs H.
                invcs H0.
                elim c.
                apply H3; simpl; intuition.
          -- apply add_to_bucket_nnil.
             apply quotient_nnil.
          -- apply add_to_bucket_is_partition.
             apply quotient_partitions.
      + eapply is_partition_cons_sublist; try eapply H.
        apply sublist_skip.
        reflexivity.
  Qed.

  Lemma Permutation_concat_is_same_subsets {A} R {equiv:Equivalence R}  {dec:EqDec A R} l1 l2 :
    is_partition R l1 ->
    is_partition R l2 ->
    Permutation (concat l1) (concat l2) ->
    same_subsets (filter_nil l1) (filter_nil l2).
  Proof.
    intros.
    generalize (quotient_unquotient H); intros HH1.
    generalize (quotient_unquotient H0); intros HH2.
    rewrite HH1.
    rewrite HH2.
    now apply quotient_perm_proper.
  Qed.

  Lemma Permutation_concat_nnil_is_same_subsets {A} R {equiv:Equivalence R}  {dec:EqDec A R} l1 l2 :
    Forall (fun x => not_nil x = true) l1 ->
    Forall (fun x => not_nil x = true) l2 ->
    is_partition R l1 ->
    is_partition R l2 ->
    Permutation (concat l1) (concat l2) ->
    same_subsets l1 l2.
  Proof.
    intros.
    cut (same_subsets (filter_nil l1) (filter_nil l2)).
    - repeat rewrite nnil_filter_nil_id; trivial.
    - eapply Permutation_concat_is_same_subsets; eauto.
  Qed.

  Instance is_equiv_class_f2R {A R} {equiv:Equivalence R} : Proper (Forall2 R ==> iff) (@is_equiv_class A R).
  Proof.
    cut (Proper (Forall2 R ==> Basics.impl) (@is_equiv_class A R))
    ; unfold Basics.impl, Proper, respectful.
    - simpl; intros; split; intros.
      + eauto.
      + symmetry in H0.
        eauto.
    - intros x y HH.
      unfold is_equiv_class, ForallPairs; intros.
      destruct (Forall2_In_r HH H0) as [?[? re1]].
      destruct (Forall2_In_r HH H1) as [?[? re2]].
      rewrite <- re1.
      rewrite <- re2.
      eauto.
  Qed.
                       
  Instance all_equivs_ff2R {A R} {equiv:Equivalence R} : Proper (Forall2 (Forall2 R) ==> iff) (@all_equivs A R).
  Proof.
    cut (Proper (Forall2 (Forall2 R) ==> Basics.impl) (@all_equivs A R))
    ; unfold Basics.impl, Proper, respectful.
    - simpl; intros; split; intros.
      + eauto.
      + symmetry in H0.
        eauto.
    - intros x y ff2.
      induction ff2; trivial.
      intros HH; invcs HH.
      constructor.
      + symmetry in H.
        eapply is_equiv_class_f2R; eauto.
      + now apply IHff2.
  Qed.

  Instance different_buckets_f2R {A R} {equiv:Equivalence R} : Proper (Forall2 R ==> Forall2 R ==> iff) (@different_buckets A R).
  Proof.
    cut (Proper (Forall2 R ==> Forall2 R ==> Basics.impl) (@different_buckets A R))
    ; unfold Basics.impl, Proper, respectful.
    - simpl; intros; split; intros.
      + eauto.
      + symmetry in H0.
        symmetry in H1.
        eauto.
    - intros x y ff2.
      unfold different_buckets; intros.
      destruct (Forall2_In_r ff2 H1) as [?[? re1]].
      destruct (Forall2_In_r H H2) as [?[? re2]].
      rewrite <- re1.
      rewrite <- re2.
      apply H0; eauto.
  Qed.
  
  Instance all_different_ff2R {A R} {equiv:Equivalence R} : Proper (Forall2 (Forall2 R) ==> iff) (@all_different A R).
  Proof.
    cut (Proper (Forall2 (Forall2 R) ==> Basics.impl) (@all_different A R))
    ; unfold Basics.impl, Proper, respectful.
    - simpl; intros; split; intros.
      + eauto.
      + symmetry in H0.
        eauto.
    - intros x y ff2.
      unfold all_different.
      induction ff2; trivial.
      intros HH; invcs HH.
      constructor.
      + eapply Forall2_Forall_trans; [ | eapply H2].
        revert ff2.
        apply Forall2_incl; intros.
        eapply different_buckets_f2R; try eapply H5; symmetry; eauto.
      + now apply IHff2.
  Qed.

  Instance is_partition_ff2R {A R} {equiv:Equivalence R} : Proper (Forall2 (Forall2 R) ==> iff) (@is_partition A R).
  Proof.
    cut (Proper (Forall2 (Forall2 R) ==> Basics.impl) (@is_partition A R))
    ; unfold Basics.impl, Proper, respectful.
    - simpl; intros; split; intros.
      + eauto.
      + symmetry in H0.
        eauto.
    - intros x y ff2 [req rdiff].
      split.
      + eapply all_equivs_ff2R; eauto.
        symmetry; eauto.
      + eapply all_different_ff2R; eauto.
        now symmetry.
  Qed.      
    
  Lemma add_to_bucket_filter_true {A} {R} {equiv:Equivalence R} {dec:EqDec A R} (l : list(list A)) (p : A -> bool) (a : A):
    p a = true ->
    is_partition R l ->
    Permutation (filter_nil (add_to_bucket R a (map (filter p) l))) (filter_nil (map (filter p) (add_to_bucket R a l))).
  Proof.
    intros pa isp.
    induction l; simpl.
    - rewrite pa; eauto.
    - specialize (IHl (is_partition_cons_inv isp)).
      destruct a0; simpl; trivial.
      case_eq (p a0); intros pa0.
      + destruct (a == a0); simpl.
        * now rewrite pa pa0.
        * rewrite pa0; simpl; eauto.
      + 
        induction a1; simpl.
        * destruct (a == a0); simpl.
          -- rewrite pa pa0.
             rewrite IHl.
             simpl.
             symmetry.
             rewrite add_to_bucket_new_perm; trivial.
             apply is_partition_forall_cons_nin.
             apply (is_partition_forall_sublist R ([a]::l) _).
             ++ constructor.
                ** reflexivity.
                ** apply Forall2_flip.
                   apply Forall2_map_Forall.
                   rewrite Forall_forall; intros.
                   apply filter_sublist.
             ++ eapply is_partition_ff2R; try eapply isp.
                constructor.
                ** constructor; trivial.
                ** reflexivity.
          -- rewrite pa0; simpl; trivial.
        * cut_to IHa1.
          -- invcs isp.
             invcs H.
             case_eq (p a1); simpl; intros.
             ++ destruct (a == a1); simpl.
                ** destruct (a == a0); simpl.
                   --- rewrite pa pa0 H; simpl; trivial.
                   --- elim c; rewrite e.
                       apply H3; simpl; eauto.
                ** destruct (a == a0); simpl.
                   --- elim c; rewrite e.
                       apply H3; simpl; eauto.
                   --- rewrite pa0 H; simpl.
                       now rewrite IHl.
             ++ rewrite IHa1.
                destruct (a == a0).
                ** simpl.
                   now rewrite pa pa0 H; simpl.
                ** simpl.
                   now rewrite pa0 H; simpl.
          -- eapply is_partition_forall_sublist; try eapply isp.
             constructor.
             ++ apply sublist_cons.
                apply sublist_skip.
                reflexivity.
             ++ reflexivity.
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

  Instance perm2_concat_perm {A} : Proper (Forall2 (Permutation (A:=A)) ==> @Permutation A) (@concat A).
  Proof.
    unfold Proper, respectful.
    intros l1 l2 F2.
    induction F2; simpl; trivial.
    rewrite H IHF2.
    trivial.
  Qed.
          
  Instance same_subsets_concat_perm {A} : Proper (same_subsets ==> @Permutation A) (@concat A).
  Proof.
    unfold Proper, respectful, same_subsets.
    intros l1 l2 [ll [p p2]].
    rewrite p.
    now apply perm2_concat_perm.
  Qed.
  
  Lemma group_by_image_filter_nil_same_subsets {A : Type} (f : A -> R) (l : list A) (p : A -> bool):
    same_subsets (group_by_image f (filter p l))
                (filter_nil (map (filter p) (group_by_image f l))).
  Proof.
    induction l.
    - simpl. reflexivity. 
    - simpl.
      match_case; intros pa.
      + rewrite <- add_to_bucket_filter_true; trivial.
        *  simpl.
           rewrite <- add_to_bucket_filter_nil.
           eapply (Permutation_concat_nnil_is_same_subsets (im_eq f)).
           -- apply add_to_bucket_nnil.
              apply quotient_nnil.
           -- apply add_to_bucket_nnil.
              apply filter_nil_nnil.
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
   
  Import Bool.

  Lemma Forall2_map_rel {A B} (R:A->A->Prop) l1 l2 (f:A->B) :
    (forall x1 x2, In x1 l1 -> In x2 l2 -> R x1 x2 -> f x1 = f x2) ->
    Forall2 R l1 l2 ->
    map f l1 = map f l2.
  Proof.
    move=> H H0.
    induction H0.
    - simpl ; reflexivity.
    - simpl in *. rewrite IHForall2.
      specialize (H x y).
      rewrite H ; trivial.
      + left ; trivial.
      + left ; trivial.
      + move=> x1 x2 H2 H3 H4.
        apply H.
        -- now right.
        -- now right.
        -- assumption.
   Qed. 

  Instance list_fst_sum_proper {A} :Proper (Permutation (A:=nonnegreal * A) ==> eq) (list_fst_sum).
  Proof.
    unfold Proper, respectful.
    intros x y Pxy.
    do 2 rewrite list_fst_sum_compat.
    unfold list_fst_sum'.
    rewrite Pxy.
    reflexivity.
  Qed.


  
  Lemma In_eq_class_hd' {A} {f : A -> R}{l : seq(seq(nonnegreal*A))}{l0 : seq (nonnegreal * A)}: 
    In l0 l ->
    is_partition (im_eq (fun x => f x.2)) l ->
    forall a, In a l0 -> f a.2 = hd' f l0.
  Proof.
    move=> H H0 a H1.
    induction l0.
    * simpl in H1 ; firstorder.
    * simpl in *. intuition. now rewrite H2.
      destruct H0. eapply Forall_forall in H0 ; eauto.
      apply H0.
      + simpl ; now right.
      + simpl ; now left. 
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

   Lemma singleton_is_partition {A} {R} {equiv:Equivalence R}  {dec:EqDec A R} {x : list A} :
     is_equiv_class R x ->
     is_partition R [x].
   Proof.
     split.
     -- red ; rewrite Forall_forall ; intros.
        simpl in H0. intuition. now subst.
     -- red. repeat constructor.
   Qed. 
   
        
   Lemma equiv_perm_hd'_eq
         {A} {x1 x2 : list(nonnegreal*A)} {l : list(list(nonnegreal*A))} {f : A -> R} :
     all_equivs (im_eq (fun x => f x.2)) l -> (Permutation x1 x2) -> (In x1 l) -> hd' f x1 = hd' f x2.
  Proof.
    move=> H H0 H1.
    red in H.
    assert (H2 : is_equiv_class (im_eq (fun x : nonnegreal * A => f x.2)) x1).
    revert H. rewrite Forall_forall. intros H. now apply H.
    assert (H3 : is_equiv_class (im_eq (fun x : nonnegreal * A => f x.2)) x2).
    now rewrite <-H0. repeat (red in H2,H3).
    case_eq x1.
    - intros Hx1. rewrite Hx1 in H0.
      now rewrite (Permutation_nil H0).
    - move=> p l0 H5.
      simpl. eapply In_eq_class_hd'.
      -- assert (In x2 [x2]). simpl ; now left. 
         apply H4.
      -- eapply singleton_is_partition ; eauto.
      -- eapply Permutation_in ; eauto. rewrite H5. trivial.
         simpl ; now left.
     Unshelve.
     all: try apply im_eq_equiv.
     all: try apply Eq_dec_im_eq.
  Qed.

  Lemma cond_expt_def_aux {A} f {g : A -> R} {r : R} {a} {p0} {l:list (nonnegreal * A)}:
    is_equiv_class (im_eq (fun x : nonnegreal * A => f x.2)) a ->
    [seq x <- a | g x.2 ==b r] = (p0 :: l) -> (hd' f [seq x <- a | g x.2 ==b r]) = (hd' f a).
  Proof.
    intros ise Heq.
    rewrite Heq. simpl.
    destruct a; simpl; trivial.
    simpl in Heq; discriminate.
    apply ise.
    - eapply In_filter_In_list.
      erewrite Heq; simpl; eauto.
    - simpl; eauto.
  Qed.    
  
  Lemma cond_expt_def {A} (p : Pmf A) (f : A -> R) (g : A -> R) (r : R) :
    cond_expt p f g r =
    list_sum
      ((map (fun l => 𝕡[(preim_outcomes_of_And l f g (hd' f l) r)]*(hd' f l)))
         (group_by_image (fun x => f x.2) p.(outcomes))).
  Proof.
    unfold cond_expt,preim_outcomes_of_And, preim_outcomes_of.
    generalize (group_by_image_filter_nil_same_subsets (fun x : nonnegreal * A => f x.2) p (fun x => g x.2 ==b r))
    ; intros HH.
    destruct HH as [ll [lp lp2]].
    rewrite lp.
    rewrite (Forall2_map_rel _ _ _ _ _ lp2).
    - rewrite <-list_sum_filter_nil.
      * rewrite <-map_comp. unfold comp. simpl. f_equal. 
      apply List.map_ext_in.
      intros a Ha.
      assert (eqq:[seq x <- a | g x.2 ==b r] = [seq x <- a | f x.2 ==b hd' f a & g x.2 ==b r]).
      { apply filter_ext. intros x Hx.
         rewrite (In_group_by_image_hd' Ha x Hx). rewrite <-(andb_true_l (g x.2 ==b r)).
         f_equal. unfold equiv_decb. match_destr. firstorder. 
      }
      rewrite <- eqq.
      case_eq ([seq x <- a | g x.2 ==b r]).
      + simpl. lra.
      + intros. rewrite <-H.
        assert (isp2:is_partition (im_eq (fun x : nonnegreal * A => f x.2)) (group_by_image (fun x : nonnegreal * A => f x.2) p)).
        { 
          apply quotient_partitions.
        }
        destruct isp2 as [ispe _].
        unfold all_equivs in ispe.
        eapply Forall_forall in ispe; try eapply Ha.
        now rewrite <-(cond_expt_def_aux f ispe H).
      * unfold prob. simpl ; lra. 
    - intros.
      assert (is_partition (im_eq (fun x : nonnegreal * A => f x.2)) ll).
      { rewrite <- lp.
        apply quotient_partitions.
      }
      invcs H2.
      unfold prob. simpl. f_equal. now rewrite H1.
      now apply (equiv_perm_hd'_eq H3).
  Qed.  
      
End conditional.
