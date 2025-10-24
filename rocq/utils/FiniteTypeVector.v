Require Import List EquivDec FunctionalExtensionality Lia Eqdep_dec.

Require Import LibUtils.
Require Import BasicUtils ListAdd Isomorphism FiniteType DVector.


Definition finite_fun_to_ivector {A B} (finA : FiniteType A) (decA : EqDec A eq) (g : A -> B) :=
  ivector_map g (ivector_from_list (nodup decA fin_elms)).

Definition ivector_to_finite_fun {A B} (finA : FiniteType A) (decA : EqDec A eq) (vec : ivector B (length (nodup decA fin_elms))) : A -> B :=
  (fun (a : A) => ivector_nth (fin_finite_index _ a) (fin_finite_index_bound _ _ ) vec).

Lemma find_index_aux_S {A} (decA : EqDec A eq) (la : list A) (x: A) (n: nat) (x0 : nat):
  find_index_aux la x (S n) = Some (S x0) ->
  find_index_aux la x n = Some x0.
Proof.
  revert n x0.
  induction la.
  + intros. discriminate H.
  + intros. simpl in H. match_destr_in H.
    -- simpl. match_destr.
       ++ now invcs H.
       ++ congruence.
    -- simpl. match_destr; try congruence.
       now apply IHla.
Qed.

Lemma find_index_aux_n {A} (decA : EqDec A eq) (x : A) (la : list A) :
  forall n1 n2, find_index_aux la x n1 = Some n2 ->
           (n2 >= n1)%nat.
Proof.
  induction la.
  - simpl.
    discriminate.
  - intros.
    simpl in H.
    match_destr_in H.
    + invcs H.
      lia.
    + specialize (IHla (S n1) n2 H).
      lia.
Qed.

Lemma find_index_S {A} (decA : EqDec A eq) (la : list A) (a x: A):
  (exists x0,
      FiniteType.find_index (a :: la) x = Some (S x0)) ->
  In x la.
Proof.
  induction la.
  - intros.
    destruct H.
    unfold FiniteType.find_index in H.
    simpl in H.
    match_destr_in H.
  - intros.
    destruct H.
    unfold FiniteType.find_index in *.
    simpl in *.
    match_destr_in H.
    destruct (decA a0 x); try tauto.
    match_destr_in H.
    + rewrite e in c0.
      congruence.
    + right.
      assert (S x0 >= 2)%nat.
      {
        now apply (find_index_aux_n decA x la).
      }
      apply IHla.
      exists (x0 - 1)%nat.
      apply find_index_aux_S in H.
      rewrite H.
      f_equal.
      lia.
Qed.

Lemma find_index_0 {A} (decA : EqDec A eq) (a x : A) (la : list A) :
  FiniteType.find_index (a :: la) x = Some 0%nat ->
  x = a.
Proof.
  unfold FiniteType.find_index.
  simpl.
  match_destr.
  intros.
  apply find_index_aux_n in H.
  lia.
Qed.

Lemma find_index_S_x {A} (decA : EqDec A eq) (a x : A) (la : list A) (x0 x1 : nat) :
  FiniteType.find_index (a :: la) x = Some (S x0) ->
  FiniteType.find_index (la) x = Some x1 ->
  x0 = x1.
Proof.
  intros.
  unfold FiniteType.find_index in *.
  simpl in H.
  match_destr_in H.
  apply find_index_aux_S in H.
  rewrite H in H0.
  now invcs H0.
Qed.

Lemma find_index_aux_succ {A} (decA : EqDec A eq) (l : list A) (i n : nat) (x : A):
  find_index_aux l x n = Some i -> find_index_aux l x (S n) = Some (S i).
Proof.
  revert i n x.
  induction l.
  -- simpl. intros; congruence.
  -- simpl. intros.
     match_destr; try congruence.
     apply IHl. assumption.
Qed.

Lemma find_index_correct_nodup {A} (decA : EqDec A eq)
  (l : list A) (i : nat) (x : A) :
  NoDup l ->
  nth_error l i = Some x ->
  FiniteType.find_index l x = Some i.
Proof.
  revert i x.
  induction l.
  + intros. rewrite nth_error_nil in H0.
    invcs H0.
  + intros i x HN Hncons.
    rewrite NoDup_cons_iff in HN.
    destruct HN as [HN1 HN2].
    destruct i.
    -- simpl in Hncons.
       invcs Hncons. unfold FiniteType.find_index; simpl.
       match_destr; try congruence.
    -- simpl in Hncons. unfold FiniteType.find_index; simpl.
       match_destr; try congruence.
       ++ apply nth_error_In in Hncons.
          rewrite e in Hncons; congruence.
       ++ specialize (IHl i x HN2 Hncons).
          unfold FiniteType.find_index in IHl.
          now apply find_index_aux_succ.
Qed.

Lemma find_index_ivector_nth {A} (decA : EqDec A eq) 
  (l : list A) (i : nat) (pf : (i < length l)%nat):
  NoDup l ->
  FiniteType.find_index l
    (ivector_nth i pf (ivector_from_list l)) = 
    Some i.
Proof.
  intro nodup.
  generalize (ivector_nth_from_list l i pf); intros.
  now apply find_index_correct_nodup.
Qed.

Lemma ivector_map_nth_finite {A B} (finA : FiniteType A) (decA : EqDec A eq) (vec : ivector B (length (nodup decA fin_elms))) :
  ivector_map
    (fun a : A =>
       ivector_nth  (fin_finite_index finA a)
         (fin_finite_index_bound finA a) vec) (ivector_from_list (nodup decA fin_elms)) = vec.
Proof.
  apply ivector_nth_eq; intros.
  rewrite ivector_nth_map.
  apply ivector_nth_ext'; try reflexivity.
  unfold fin_finite_index.
  unfold proj1_sig.
  match_destr.
  simpl in e.
  rewrite find_index_ivector_nth in e.    
  now invcs e.
  apply NoDup_nodup.
Qed.

Lemma finite_funi_iso_f_b {A B} (finA : FiniteType A) (decA : EqDec A eq) :
  forall (vec : ivector B (length (nodup decA fin_elms))), 
    finite_fun_to_ivector _ _ (ivector_to_finite_fun _ _ vec) = vec.
Proof.
  intros.
  unfold ivector_to_finite_fun, finite_fun_to_ivector.
  now apply ivector_map_nth_finite.
Qed.

Lemma ivector_nth_finite_map_aux {A B} (la : list A) (decA : EqDec A eq) (g : A -> B) 
  (x : A) (inx : In x la) :
  NoDup la ->
  let find_ind := (@find_index_complete A decA la x inx) in
  ivector_nth (proj1_sig find_ind)
    (@find_index_bound A decA la x (proj1_sig find_ind) (proj2_sig find_ind))
    (ivector_map g (ivector_from_list la)) = g x.
Proof.
  intros nodup inla.
  simpl.
  induction la.
  - simpl in *; tauto.
  - destruct la.
    + simpl.
      destruct inx; [| simpl in *; tauto].
      unfold proj1_sig.
      match_destr.
      simpl.
      match_destr.
      * now rewrite e.
      * unfold FiniteType.find_index in e0.
        unfold find_index_aux in e0.
        unfold equiv_dec in e0.
        generalize e0 as e0'.
        intros.
        case_eq (decA x a); intros.
        -- rewrite H in e0.
           invcs e0.
        -- rewrite H in e0.
           discriminate.
    + simpl.
      simpl in IHla.
      unfold proj1_sig.
      match_destr.
      simpl.
      match_destr.
      * apply find_index_0 in e.
        now rewrite e.
      * generalize e as e'; intros.
        generalize (find_index_S decA (a0 :: la) a x); intros.
        cut_to H.
        specialize (IHla H).
        cut_to IHla.
        -- unfold proj1_sig in IHla.
           match_destr_in IHla.
           generalize (find_index_S_x decA a x (a0 :: la) x0 x1 e' e0); intros.
           match_destr.
           ++ match_destr_in IHla.
           ++ match_destr_in IHla.
              assert (x0 = x1) by lia.
              rewrite <- IHla.
              unfold proj2_sig.
              subst.
              apply ivector_nth_prf_irrelevance.
        -- now apply NoDup_cons_iff in nodup.
        -- exists x0.
           apply e.
Qed.

Lemma ivector_nth_finite_map {A B} (finA : FiniteType A) (decA : EqDec A eq) (g : A -> B) :
  forall (x : A),
    ivector_nth (fin_finite_index finA x) (fin_finite_index_bound finA x)
      (ivector_map g (ivector_from_list (nodup decA fin_elms))) = g x.
Proof.
  intros.
  generalize (ivector_nth_finite_map_aux (nodup decA fin_elms) decA g x); intros.
  assert (inx: In x (nodup decA fin_elms)).
  {
    apply nodup_In.
    apply fin_finite.
  }
  specialize (H inx).
  cut_to H; try apply NoDup_nodup.
  simpl in H.
  rewrite <- H.
  apply ivector_nth_ext'; trivial.
  unfold fin_finite_index, proj1_sig.
  clear H.
  match_destr.
  match_destr.
  unfold fin_finite_nodup in e.
  simpl in e.
  rewrite e0 in e.
  now invcs e.
Qed.

Lemma finite_funi_iso_b_f {A B} (finA : FiniteType A) (decA : EqDec A eq) :
  forall (g : A -> B),
    ivector_to_finite_fun _ _ (finite_fun_to_ivector _ _ g)  = g.
Proof.
  intros.
  unfold ivector_to_finite_fun, finite_fun_to_ivector.
  apply functional_extensionality.
  intros.
  apply ivector_nth_finite_map.
Qed.

Instance finite_fun_ivec_encoder {A B} (finA : FiniteType A) (decA :EqDec A eq):
  Isomorphism (A -> B) (ivector B (length (nodup decA fin_elms)))
  := {
    iso_f := finite_fun_to_ivector finA decA;
    iso_b := ivector_to_finite_fun finA decA;
    iso_f_b := finite_funi_iso_f_b finA decA ;
    iso_b_f := finite_funi_iso_b_f finA decA }.


Definition finite_fun_to_vector {A B} (finA : FiniteType A) (decA : EqDec A eq) (g : A -> B) : vector B ((length (nodup decA fin_elms))) :=
  vector_map g (vector_from_list (nodup decA fin_elms)).

Definition vector_to_finite_fun {A B} (finA : FiniteType A) (decA : EqDec A eq) (vec : vector B (length (nodup decA fin_elms))) : A -> B :=
  (fun (a : A) => vector_nth (fin_finite_index _ a) (fin_finite_index_bound _ _ ) vec).

Lemma find_index_vector_nth {A} (decA : EqDec A eq) 
  (l : list A) (i : nat) (pf : (i < length l)%nat):
  NoDup l ->
  FiniteType.find_index l
    (vector_nth i pf (vector_from_list l)) = 
    Some i.
Proof.
  intro nodup.
  apply find_index_correct_nodup; trivial.
  now rewrite vector_nth_in.
Qed.

Lemma vector_map_nth_finite {A B} (finA : FiniteType A) (decA : EqDec A eq) (vec : vector B (length (nodup decA fin_elms))) :
  vector_map
    (fun a : A =>
       vector_nth  (fin_finite_index finA a)
         (fin_finite_index_bound finA a) vec) (vector_from_list (nodup decA fin_elms)) = vec.
Proof.
  apply vector_nth_eq; intros.
  rewrite vector_nth_map.
  apply vector_nth_ext''; try reflexivity.
  unfold fin_finite_index.
  unfold proj1_sig.
  match_destr.
  simpl in e.
  rewrite find_index_vector_nth in e.    
  now invcs e.
  apply NoDup_nodup.
Qed.

Lemma finite_fun_iso_f_b {A B} (finA : FiniteType A) (decA : EqDec A eq) :
  forall (vec : vector B (length (nodup decA fin_elms))), 
    finite_fun_to_vector _ _ (vector_to_finite_fun _ _ vec) = vec.
Proof.
  intros.
  unfold vector_to_finite_fun, finite_fun_to_vector.
  now apply vector_map_nth_finite.
Qed.

Lemma vector_nth_finite_map_aux {A B} (la : list A) (decA : EqDec A eq) (g : A -> B) 
  (x : A) (inx : In x la) :
  NoDup la ->
  let find_ind := (@find_index_complete A decA la x inx) in
  vector_nth (proj1_sig find_ind)
    (@find_index_bound A decA la x (proj1_sig find_ind) (proj2_sig find_ind))
    (vector_map g (vector_from_list la)) = g x.
Proof.
  intros nodup inla.
  simpl.
  induction la.
  - simpl in *; tauto.
  - destruct la.
    + simpl.
      destruct inx; [| simpl in *; tauto].
      unfold proj1_sig.
      unfold vector_from_list; simpl.
      match_destr.
      simpl.
      rewrite vector_nth_map; simpl.
      subst.
      generalize (find_index_bound e0); simpl; intros.
      destruct x0; [| lia].
      now unfold vector_nth; simpl.
    + simpl.
      simpl in IHla.
      unfold proj1_sig.
      match_destr.
      simpl.
      destruct x0.
      * generalize (find_index_0 _ _ _ _ e); intros; subst.
        reflexivity.
      * generalize e as e'; intros.
        generalize (find_index_S decA (a0 :: la) a x); intros.
        cut_to H.
        specialize (IHla H).
        cut_to IHla.
        -- unfold proj1_sig in IHla.
           match_destr_in IHla.
           generalize (find_index_S_x decA a x (a0 :: la) x0 x1 e' e0); intros.
           subst.
           unfold vector_from_list.
           rewrite <- IHla.
           repeat rewrite vector_nth_map.
           f_equal.
           generalize (vector_nth_cons_S a (exist _ (a0::la) (eq_refl _)) x1 (find_index_bound e'))
           ; intros HH.
           etransitivity; [| etransitivity]; [| apply HH |]
           ; apply vector_nth_ext.
        -- now apply NoDup_cons_iff in nodup.
        -- exists x0.
           apply e.
Qed.

Lemma vector_nth_finite_map {A B} (finA : FiniteType A) (decA : EqDec A eq) (g : A -> B) :
  forall (x : A),
    vector_nth (fin_finite_index finA x) (fin_finite_index_bound finA x)
      (vector_map g (vector_from_list (nodup decA fin_elms))) = g x.
Proof.
  intros.
  generalize (vector_nth_finite_map_aux (nodup decA fin_elms) decA g x); intros.
  assert (inx: In x (nodup decA fin_elms)).
  {
    apply nodup_In.
    apply fin_finite.
  }
  specialize (H inx).
  cut_to H; try apply NoDup_nodup.
  simpl in H.
  rewrite <- H.
  apply vector_nth_ext''; trivial.
  unfold fin_finite_index, proj1_sig.
  clear H.
  match_destr.
  match_destr.
  unfold fin_finite_nodup in e.
  simpl in e.
  rewrite e0 in e.
  now invcs e.
Qed.

Lemma finite_fun_iso_b_f {A B} (finA : FiniteType A) (decA : EqDec A eq) :
  forall (g : A -> B),
    vector_to_finite_fun _ _ (finite_fun_to_vector _ _ g)  = g.
Proof.
  intros.
  unfold vector_to_finite_fun, finite_fun_to_vector.
  apply functional_extensionality.
  intros.
  apply vector_nth_finite_map.
Qed.


Instance finite_fun_vec_encoder {A B} (finA : FiniteType A) (decA :EqDec A eq):
  Isomorphism (A -> B) (vector B (length (nodup decA fin_elms)))
  := {
    iso_f := finite_fun_to_vector finA decA;
    iso_b := vector_to_finite_fun finA decA;
    iso_f_b := finite_fun_iso_f_b finA decA ;
    iso_b_f := finite_fun_iso_b_f finA decA }.


Fixpoint ivector_iter_prod {A} (elems:list A) n : list (ivector A n)
  := match n with
     | 0%nat => tt :: nil
     | S n => list_prod elems (ivector_iter_prod elems n)
     end.

Lemma ivector_iter_prod_length {A} (elems:list A) n :
  length (ivector_iter_prod elems n) = Nat.pow (length elems) n.
Proof.
  induction n; simpl; trivial.
  now rewrite prod_length, IHn.
Qed.  

Lemma ivector_iter_prod_complete {A} (elems:list A) {n} (v:ivector A n) :
  (forall i pf, In (ivector_nth i pf v) elems) ->
  In v (ivector_iter_prod elems n).
Proof.
  revert v.
  induction n; intros; destruct v; simpl.
  - tauto.
  - apply in_prod.
    + apply (H _ (PeanoNat.Nat.lt_0_succ n)).
    + apply IHn; intros.
      assert (pf' : S i0 < S n) by lia.
      specialize (H _ pf').
      simpl in H.
      erewrite ivector_nth_prf_irrelevance; eauto.
Qed.

Program Instance finite_ivector_finite {A} n (finA : FiniteType A) : FiniteType (ivector A n)
  := {|
    fin_elms := ivector_iter_prod fin_elms n
  |}.
Next Obligation.
  apply ivector_iter_prod_complete; intros.
  apply fin_finite.
Qed.

Instance finite_vector_finite {A} n (finA : FiniteType A) : FiniteType (vector A n).
Proof.
  eapply @FiniteType_iso; [| apply (finite_ivector_finite n finA)].
  apply Isomorphism_symm.
  apply vec_to_ivec_encoder.
Qed.
