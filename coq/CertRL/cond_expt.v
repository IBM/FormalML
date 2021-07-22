Require Import Reals EquivDec List LibUtils Permutation Morphisms.
Require Import pmf_monad.
Require Import Utils.
Require Import micromega.Lra.
From mathcomp Require Import ssreflect ssrfun seq.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.
Local Open Scope list_scope.

Open Scope R_scope.


(*
****************************************************************************************
This file has a number of auxilary results all aimed at defining and proving properties 
about conditional expectation. In the file pmf_monad.v, we start out with a definition of 
probability mass functions as a list(nonnegreal*A) together with a predicate that the atomic
probabilities sum to 1. Defining conditional expectation of a random variable f needs us to
work with sums over the range of f.
To this end, we introduce "quotients", which is simply a bucketing operation over a type 
A into equivalence classes based on a given equivalence relation on A.  
****************************************************************************************
*)

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

Definition group_by_image (f : A -> R) := @quotient _ _ _ (Eq_dec_im_eq f).

Lemma Forall_group_by_image (l : list A) (f : A -> R) :
 Forall (fun l0 => (forall a b, In a l0 -> In b l0 -> (f a = f b))) (group_by_image f l). 
Proof.
  apply quotient_partitions. 
Qed.

Lemma In_group_by_image {l : list A} {f : A -> R} :
  forall l0, In l0 (group_by_image f l) -> (forall a b, In a l0 -> In b l0 -> (f a = f b)).
Proof.
  rewrite <- Forall_forall.
  apply Forall_group_by_image.
Qed.

Lemma In_group_by_image_sublist {l : list A} {f : A -> R}  :
  forall {l0 l0'}, In l0 (group_by_image f l) -> (forall c, In c l0' -> In c l0)
            -> (forall a b, In a l0 -> In b l0' -> (f a = f b)).
Proof.
  intros l0 l0' H H0 a b H1 H2.
  set (Hin := In_group_by_image _ H).
  specialize (H0 b H2).
  now specialize (Hin a b H1 H0).
Qed.

Lemma cons_In_group_by_image {l : list A} {f : A -> R} {a : A} :
 forall l0, In (a :: l0) (group_by_image f l) -> (forall b, In b l0 -> (f a = f b)).
Proof.
  intros l0 Hl0 b Hb.
  set (In_group_by_image (a :: l0) Hl0). 
  eapply e ; eauto. 
  simpl ; intuition.
  simpl ; intuition. 
Qed.
 
Lemma map_rep {l0 : list A} {f : A -> R} {a0 : A} :
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

Lemma eq_class_eq_rep_hd  {l : list A} {f : A -> R} :
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


End image_equiv.



Section list_sum.

                                       
    


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

Lemma list_sum_const_mul' {A:Type} (l : list (nonnegreal*A)) (a : R) :
  list_sum [seq a* nonneg(x.1) | x <- l] = a*list_sum[seq nonneg(x.1) | x <- l].
Proof.
  induction l.
  + simpl ; lra.
  + simpl. rewrite IHl. lra.
Qed.

Lemma list_sum_const_div {A:Type}{n : nonnegreal} (hne : 0 <> nonneg n)
      (l : seq(nonnegreal*A))(f : A -> R) :
      list_sum [seq f x.2 * (nonneg(x.1) / nonneg(n)) | x <- l] = list_sum [seq (f x.2 * nonneg (x.1)) | x <- l]/nonneg(n).
Proof.
  induction l. 
  simpl. lra.
  simpl. rewrite IHl. lra.
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
  Global Instance EqDecR : EqDec R eq := Req_EM_T. 
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
      -- simpl ; intuition.
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

  Instance list_fst_sum_proper {A} :Proper (Permutation (A:=nonnegreal * A) ==> eq) (list_fst_sum).
  Proof.
    unfold Proper, respectful.
    intros x y Pxy.
    do 2 rewrite list_fst_sum_compat.
    unfold list_fst_sum'.
    rewrite Pxy.
    reflexivity.
  Qed.

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
      intuition.
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
      unfold List.filter.
      erewrite Heq; simpl; eauto.
    - simpl; eauto.
  Qed.    

  Lemma Forall2_cmap_rel {A B} (R:A->A->Prop) l1 l2 (f:A->B) :
    (forall x1 x2, In x1 l1 -> In x2 l2 -> R x1 x2 -> f x1 = f x2) ->
    Forall2 R l1 l2 ->
    map f l1 = map f l2.
  Proof.
    intros H H0.
    induction H0.
    - simpl ; reflexivity.
    - simpl in *. rewrite IHForall2.
      specialize (H x y).
      rewrite H ; trivial.
      + left ; trivial.
      + left ; trivial.
      + intros x1 x2 H2 H3 H4.
        apply H.
        -- now right.
        -- now right.
        -- assumption.
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
    rewrite (Forall2_cmap_rel _ _ _ _ _ lp2).
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
