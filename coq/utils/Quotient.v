Require Import List Permutation Equivalence EquivDec Morphisms.
Require Import LibUtils BasicUtils ListAdd.

Import ListNotations.
Local Open Scope list_scope.

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

  
  Definition preserves_partitions (f:list (list A)->list (list A))
    := forall (l:list (list A)), is_partition l ->
                                 is_partition (f l).

  
  Lemma filter_preserves_partitions (p:list A -> bool) :
    preserves_partitions (filter p).
  Proof.
    intros l pl.
    split. destruct pl as [Heq Had]. 
    - apply Forall_filter ; trivial. 
    - apply ForallOrdPairs_filter. destruct pl ; trivial. 
  Qed.

  Lemma add_to_bucket_is_partition a :
    preserves_partitions (add_to_bucket a).
  Proof.
    intros ? [??].
    split.
    - now apply add_to_bucket_all_equivs.
    - now apply add_to_bucket_all_different.
  Qed.
  


  Lemma quotient_buckets_disjoint_app l ll1 ll2 :
    quotient l = ll1 ++ ll2 ->
    forall l1 l2 x y, In l1 ll1 -> In l2 ll2 ->
                      In x l1 -> In y l2 -> ~ R x y.
  Proof.
    intros eqq.
    generalize (quotient_all_different l) ; intros HH.
    rewrite eqq in HH.
    red in HH.
    intros.
    generalize (ForallOrdPairs_app_in HH) ; intros HH2.
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

  
  Lemma Forall_map_filter (l : list(list A)) (p : A -> bool) :
    Forall (is_equiv_class) l -> Forall (is_equiv_class) (map (filter p) l).
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
        apply filter_In in Ha0.
        apply filter_In in Hb.
        intuition.
      + invcs H. specialize (IHl H3).
        assumption.
  Qed.       

  Lemma ForallOrdPairs_map_filter (l : list(list A)) (p : A -> bool):
    ForallOrdPairs (different_buckets) l -> ForallOrdPairs (different_buckets) (map (filter p) l).
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
         
         apply filter_In in H0.
         apply filter_In in H1.
         intuition.
      -- invcs H. now apply IHl. 
  Qed.

  Lemma map_filter_preserves_partitions (p:A -> bool) :
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

End quotient.

Section more_quotient.
  
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

  Global Instance different_buckets_symmetric {A} (R:A->A->Prop) {sym:Symmetric R} : Symmetric (different_buckets R).
  Proof.
    unfold Symmetric, different_buckets; intros.
    intros rr.
    apply (H _ _ H1 H0).
    now symmetry.
  Qed.
  
  Global Instance all_different_perm {A} R {equiv:Equivalence R} : Proper (@Permutation (list A) ==> iff) (all_different R).
  Proof.
    unfold all_different; intros HH1 HH2 perm.
    rewrite perm.
    intuition.
  Qed.

  Global Instance is_partition_perm {A} R {equiv:Equivalence R} : Proper (@Permutation (list A) ==> iff) (is_partition R).
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
    cut (forall l l' : list (list A),
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

  Global Instance equiv_class_perm {A} R :
    Proper (Permutation (A:=A) ==> iff) (is_equiv_class R).
  Proof.
    unfold Proper, respectful, is_equiv_class, ForallPairs; intros.
    split; intros.
    - eapply H0; now rewrite H.
    - eapply H0; now rewrite <- H.
  Qed.

  Global Instance different_buckets_perm {A} R :
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

  Global Instance forall_perm_partition {A} R :
    Proper (Forall2 (Permutation (A:=A)) ==> iff) (is_partition R).
  Proof.
    unfold Proper, respectful.
    cut ( forall x y : list (list A), Forall2 (Permutation (A:=A)) x y -> is_partition R x -> is_partition R y).
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

  Global Instance same_subsets_partition {A} (R:list (list A) -> (list (list A) -> Prop)) {equiv:Equivalence R} :
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

  
  Global Instance same_subsets_equiv {A} : Equivalence (@same_subsets A).
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

  Global Instance quotient_perm_proper {A} R {equiv:Equivalence R} {dec:EqDec A R} :
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

  Global Instance same_subsets_perm_sub {A} : subrelation (@Permutation (list A)) same_subsets.
  Proof.
    repeat red; intros.
    exists y.
    split; trivial.
    reflexivity.
  Qed.

  Global Instance same_subsets_perm2_sub {A} : subrelation (Forall2 (@Permutation A)) same_subsets.
  Proof.
    repeat red; intros.
    exists x.
    eauto.
  Qed.

  Global Instance not_nil_perm_proper {A} : Proper (@Permutation A ==> eq) (not_nil).
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
    assert (nnil2: Forall (fun x : list A => not_nil x = true) l2).
    { eapply same_subsets_nnil; eauto. }
    generalize (@add_to_bucket_same_subsets_proper _ _ _ _ a l1 l2 H0); intros HH.
    do 2 (rewrite nnil_filter_nil_id in HH; auto 2).
    specialize (HH H1).
    rewrite nnil_filter_nil_id in HH.
    - rewrite nnil_filter_nil_id in HH; trivial.
      now apply add_to_bucket_nnil.
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

  Global Instance different_buckets_sublist {A R} : Proper (sublist --> sublist --> Basics.impl) (@different_buckets A R).
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

  Global Instance all_different_forall_sublist {A} R : Proper (Forall2 sublist --> Basics.impl) (@all_different A R).
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

  Global Instance is_partition_forall_sublist {A} R : Proper (Forall2 sublist --> Basics.impl) (@is_partition A R).
  Proof.
    unfold Basics.flip, Basics.impl. unfold Proper,respectful. 
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

  Global Instance is_equiv_class_f2R {A R} {equiv:Equivalence R} : Proper (Forall2 R ==> iff) (@is_equiv_class A R).
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
  
  Global Instance all_equivs_ff2R {A R} {equiv:Equivalence R} : Proper (Forall2 (Forall2 R) ==> iff) (@all_equivs A R).
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

  Global Instance different_buckets_f2R {A R} {equiv:Equivalence R} : Proper (Forall2 R ==> Forall2 R ==> iff) (@different_buckets A R).
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
  
  Global Instance all_different_ff2R {A R} {equiv:Equivalence R} : Proper (Forall2 (Forall2 R) ==> iff) (@all_different A R).
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

  Global Instance is_partition_ff2R {A R} {equiv:Equivalence R} : Proper (Forall2 (Forall2 R) ==> iff) (@is_partition A R).
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
        * now rewrite pa, pa0.
        * rewrite pa0; simpl; eauto.
      + 
        induction a1; simpl.
        * destruct (a == a0); simpl.
          -- rewrite pa, pa0.
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
                   --- rewrite pa, pa0, H; simpl; trivial.
                   --- elim c; rewrite e.
                       apply H3; simpl; eauto.
                ** destruct (a == a0); simpl.
                   --- elim c; rewrite e.
                       apply H3; simpl; eauto.
                   --- rewrite pa0, H; simpl.
                       now rewrite IHl.
             ++ rewrite IHa1.
                destruct (a == a0).
                ** simpl.
                   now rewrite pa, pa0, H; simpl.
                ** simpl.
                   now rewrite pa0, H; simpl.
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

  Global Instance perm2_concat_perm {A} : Proper (Forall2 (Permutation (A:=A)) ==> @Permutation A) (@concat A).
  Proof.
    unfold Proper, respectful.
    intros l1 l2 F2.
    induction F2; simpl; trivial.
    rewrite H, IHF2.
    trivial.
  Qed.
  
  Global Instance same_subsets_concat_perm {A} : Proper (same_subsets ==> @Permutation A) (@concat A).
  Proof.
    unfold Proper, respectful, same_subsets.
    intros l1 l2 [ll [p p2]].
    rewrite p.
    now apply perm2_concat_perm.
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

  Local Existing Instance Equivalence_pullback.
  Local Existing Instance EqDec_pullback.
  
  Lemma add_to_bucket_map {A B:Type} (R:A->A->Prop) {eqR:Equivalence R} {decR:EqDec A R} (l:list (list B)) 
        (f:B->A) b :
    add_to_bucket R (f b) (map (map f) l) = 
    map (map f) (add_to_bucket (fun x y : B => R (f x) (f y)) b l).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl.
    destruct a; simpl; trivial.
    unfold equiv_dec, EqDec_pullback.
    match_destr.
  Qed.
  
  Lemma quotient_map {A B:Type} (R:A->A->Prop) {eqR:Equivalence R} {decR:EqDec A R} (l:list B) 
        (f:B->A) :
    quotient R (map f l) = map (map f) (quotient  (fun x y : B => R (f x) (f y)) l).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl.
    apply add_to_bucket_map.
  Qed.

  Lemma add_to_bucket_eq_nin {A} (decA:EqDec A eq) a l :
    Forall (fun x : list A => not_nil x = true) l ->
    (forall l' : list A, In l' l -> ~ In a l') ->
    (add_to_bucket eq a l) = l++[[a]].
  Proof.
    intros.
    induction l; simpl; trivial.
    invcs H.
    match_destr.
    match_destr.
    - red in e; subst.
      simpl in H0.
      eelim H0; eauto.
      simpl; eauto.
    - simpl in *.
      rewrite IHl; eauto.
  Qed.

  Lemma nodup_hd_quotient {A} (decA:EqDec A eq) def (l:list A) : 
    Permutation ((map (hd def) (quotient eq l)))
                (nodup decA l).
  Proof.
    induction l; simpl; trivial.
    match_destr.
    - rewrite <- IHl.
      apply (quotient_in eq) in i.
      match goal with
      | [|- Permutation ?l1 ?l2 ] => replace l1 with l2; [reflexivity | ]
      end.
      revert i.
      clear.
      generalize (quotient_nnil eq l).
      generalize (quotient_all_equivs eq l).
      generalize (quotient_all_different eq l).
      generalize (quotient eq l); clear; intros l.
      unfold all_different, all_equivs, is_equiv_class, ForallPairs.
      repeat rewrite Forall_forall.
      unfold not_nil.
      intros alldiff alleq nnil [l' [l'in ain]].
      induction l; simpl in *.
      + tauto.
      + destruct a0.
        * specialize (nnil []); simpl in nnil; intuition.
        * match_destr.
          -- red in e; subst; trivial.
          -- destruct l'in.
             ++ subst.
                elim c.
                apply (alleq (a0::a1)); simpl; eauto.
             ++ simpl.
                rewrite <- IHl; auto.
                now invcs alldiff.
                firstorder.
    - rewrite add_to_bucket_eq_nin.
      + rewrite map_app; simpl.
        rewrite <- Permutation_cons_append.
        now apply perm_skip.
      + apply quotient_nnil.
      + intros l' inn1 inn2.
        generalize (in_quotient eq a l).
        eauto.
  Qed.

  Lemma add_to_bucket_ext {A:Type} (R1 R2:A->A->Prop) {eqR1:Equivalence R1} {decR1:EqDec A R1} {eqR2:Equivalence R2} {decR2:EqDec A R2} a (l:list (list A)) :
    (forall l' y, In y l' -> In l' l -> R1 a y <-> R2 a y) ->
    add_to_bucket R1 a l = add_to_bucket R2 a l.
  Proof.
    intros.
    induction l; simpl; trivial.
    cut_to IHl; [| firstorder].
    rewrite IHl.
    specialize (H a0); simpl in H.
    match_destr; simpl in *.
    repeat match_destr; unfold equiv, complement in *; firstorder.
  Qed.
  
  Lemma quotient_ext {A:Type} (R1 R2:A->A->Prop) {eqR1:Equivalence R1} {decR1:EqDec A R1} {eqR2:Equivalence R2} {decR2:EqDec A R2} (l:list A) :
    ForallPairs (fun x y => R1 x y <-> R2 x y) l ->
    quotient R1 l = quotient R2 l.
  Proof.
    unfold ForallPairs.
    induction l; simpl; intros; trivial.
    rewrite IHl by eauto.
    apply add_to_bucket_ext.
    intros.
    eapply H; eauto.
    right.
    eapply in_quotient; eauto.
  Qed.

  Lemma all_different_same_eq {A} R {eqR:Equivalence R} (l:list (list A)) l1 l2 a b:
    all_different R l ->
    In l1 l ->
    In l2 l ->
    In a l1 ->
    In b l2 ->
    R a b ->
    l1 = l2.
  Proof.
    induction l; simpl; intros.
    - tauto.
    - unfold all_different in H.
      invcs H.
      rewrite Forall_forall in H7.
      unfold different_buckets in H7.
      destruct H0; destruct H1; subst.
      + trivial.
      + specialize (H7 _ H0 _ _ H2 H3).
        congruence.
      + specialize (H7 _ H _ _ H3 H2).
        symmetry in H4.
        congruence.
      + apply IHl; eauto.
  Qed.

End more_quotient.
