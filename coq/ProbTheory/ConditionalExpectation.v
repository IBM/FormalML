Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Export RandomVariableLpR RandomVariableL2.
Require Import quotient_space.
Require Import RbarExpectation.

Require Import Event.
Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.

Set Bullet Behavior "Strict Subproofs".

Section cond_exp.

Context {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom).

(* the conditional expectation of x over the sub-algebra dom2 *)

Definition event_sa_sub {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom) (x:event dom2) : event dom
    := exist _ (event_pre x) (sub _ (proj2_sig x)).

Global Instance event_sa_sub_equiv_proper {dom2 : SigmaAlgebra Ts} (sub:sa_sub dom2 dom) :
  Proper (event_equiv ==> event_equiv) (event_sa_sub sub).
Proof.
  repeat red; intros.
  simpl.
  specialize (H x0).
  destruct x; destruct y; simpl in *.
  intuition.
Qed.

Lemma collection_is_pairwise_disjoint_sa_sub
      {dom2 : SigmaAlgebra Ts} (sub:sa_sub dom2 dom) collection :
      collection_is_pairwise_disjoint collection ->
      collection_is_pairwise_disjoint (fun n : nat => event_sa_sub sub (collection n)).
Proof.
  unfold collection_is_pairwise_disjoint; intros.
  unfold event_disjoint; simpl.
  now apply H.
Qed.

Lemma union_of_collection_sa_sub {dom2 : SigmaAlgebra Ts} (sub:sa_sub dom2 dom) collection :
  event_equiv
    (event_sa_sub sub (union_of_collection collection))
    (union_of_collection (fun n : nat => event_sa_sub sub (collection n))).

Proof.
  intros x; simpl.
  reflexivity.
Qed.

Instance prob_space_sa_sub (dom2 : SigmaAlgebra Ts)
       (sub : sa_sub dom2 dom) : ProbSpace dom2.
Proof.
  exists (fun x => ps_P (event_sa_sub sub x)).
  - repeat red; intros.
    now rewrite H.
  - intros.
    generalize (ps_countable_disjoint_union (fun n => event_sa_sub sub (collection n)))
    ; intros HH.
    cut_to HH.
    + rewrite union_of_collection_sa_sub.
      unfold sum_of_probs_equals in *.
      apply HH.
    + now apply collection_is_pairwise_disjoint_sa_sub.
  - erewrite ps_proper; try eapply ps_one.
    unfold Ω, pre_Ω.
    repeat red; intros; simpl; tauto.
  - intros.
    apply ps_pos.
Defined.

Instance RandomVariable_sa_sub {Td} (dom2 : SigmaAlgebra Ts) {cod : SigmaAlgebra Td}
         (sub : sa_sub dom2 dom)
         x
         {rv_x:RandomVariable dom2 cod x}
  : RandomVariable dom cod x.
Proof.
  intros e.
  specialize (rv_x e).
  now apply sub.
Qed.

Lemma almostR2_eq_plus_inv {x y z} :
  almostR2 prts eq z (rvplus x y) ->
  exists x' y',
    almostR2 prts eq x x' /\
    almostR2 prts eq y y' /\ 
    rv_eq z (rvplus x' y').
Proof.
  intros [p [pone px]].
  exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then x a else 0).
  exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then y a else z a).
  split; [| split].
  - exists p.
    split; trivial.
    intros ??.
    match_destr.
    tauto.
  - exists p.
    split; trivial.
    intros ??.
    match_destr.
    tauto.
  - intros a; simpl.
    rv_unfold.
    match_destr.
    + auto.
    + lra.
Qed.

Lemma almostR2_eq_opp_inv {x z} :
  almostR2 prts eq z (rvopp x) ->
  exists x',
    almostR2 prts eq x x' /\
    rv_eq z (rvopp x').
Proof.
  intros [p [pone px]].

  exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then x a else - z a).
  split.
  - exists p.
    split; trivial.
    intros ??.
    match_destr.
    tauto.
  - intros ?.
    rv_unfold.
    match_destr.
    + auto.
    + lra.
Qed.


Definition ortho_phi  (dom2 : SigmaAlgebra Ts)
           : LpRRVq prts 2 -> Prop
           := (fun y:LpRRVq prts 2 =>
                    exists z, Quot _ z = y /\
                         RandomVariable dom2 borel_sa (LpRRV_rv_X prts z)).

Lemma LpRRVnorm_minus_sym  (x y : LpRRV prts 2) :
  LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) = LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) y x).
Proof.
  unfold LpRRVnorm, LpRRVminus.
  f_equal.
  apply FiniteExpectation_ext.
  intro z.
  unfold rvpower, rvabs, pack_LpRRV; f_equal; simpl.
  do 2 rewrite rvminus_unfold.
  apply Rabs_minus_sym.
 Qed.

Definition LpRRV_dist (x y : LpRRV prts 2) := 
  LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y).

Lemma LpRRV_norm_dist (x y : LpRRV prts 2) :
  LpRRV_dist x y = LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y).  
Proof.
  easy.
Qed.
  
Lemma LpRRV_dist_comm (x y : LpRRV prts 2) :
  LpRRV_dist x y = LpRRV_dist y x.
Proof.
  unfold LpRRV_dist, LpRRVnorm, LpRRVminus.
  f_equal.
  apply FiniteExpectation_ext.
  intro z.
  unfold rvpower, rvabs, pack_LpRRV.
  f_equal.
  simpl.
  do 2 rewrite rvminus_unfold.
  now rewrite Rabs_minus_sym.
Qed.

Lemma LpRRV_dist_triang (x y z : LpRRV prts 2) :
  LpRRV_dist x z <= LpRRV_dist x y + LpRRV_dist y z.
Proof.
  unfold LpRRV_dist.
  generalize (LpRRV_norm_plus prts big2 (LpRRVminus prts (p := bignneg 2 big2) x y) (LpRRVminus prts (p := bignneg 2 big2) y z)); intros.
  do 2 rewrite LpRRVminus_plus in H.
  rewrite <- LpRRV_plus_assoc in H.
  rewrite (LpRRV_plus_assoc prts (p := bignneg 2 big2) (LpRRVopp prts y) _) in H.     
  rewrite (LpRRV_plus_comm prts (p := bignneg 2 big2) _ y) in H.
  rewrite LpRRV_plus_inv in H.
  rewrite (LpRRV_plus_comm prts (p := bignneg 2 big2) (LpRRVconst prts 0) _ ) in H.
  rewrite LpRRV_plus_zero in H.
  now repeat rewrite <- LpRRVminus_plus in H.
Qed.  

Definition LpRRV_filter_from_seq {dom2:SigmaAlgebra Ts} {prts2 : ProbSpace dom2}
           (f : nat -> LpRRV prts2 2) : ((LpRRV_UniformSpace prts2 big2 -> Prop) -> Prop) :=
   fun (P : (LpRRV_UniformSpace prts2 big2 -> Prop)) => exists (N:nat), forall (n:nat), (n >= N)%nat -> P (f n).

 Lemma cauchy_filterlim_almost_unique_eps (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
       (PF : ProperFilter F)
       (x y : LpRRV prts 2) :
   (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
   (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
   forall (eps:posreal), LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) < eps.
   Proof.
     intros.
     assert (0 < eps) by apply cond_pos.
     assert (0 < eps/2) by lra.
     specialize (H (mkposreal _ H2)).
     specialize (H0 (mkposreal _ H2)).     
     generalize (Hierarchy.filter_and _ _ H H0); intros.
     apply filter_ex in H3.
     unfold LpRRVball in H3.
     destruct H3 as [? [? ?]].
     generalize (LpRRV_dist_triang x x0 y); intros.
     unfold LpRRV_dist in H5.
     eapply Rle_lt_trans.
     apply H5.
     rewrite LpRRVnorm_minus_sym in H4.
     simpl in H3; simpl in H4; simpl.
     lra.
  Qed.     

 Lemma cauchy_filterlim_almost_unique_eps_alt (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
       (PF : ProperFilter F)
       (x y : LpRRV prts 2) :
   (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
   (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
   forall (eps:posreal), LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) < eps.
   Proof.
     intros.
     assert (0 < eps) by apply cond_pos.
     assert (0 < eps/4) by lra.
     destruct (H (mkposreal _ H2)) as [x0 [? ?]].
     destruct (H0 (mkposreal _ H2)) as [y0 [? ?]].
     generalize (Hierarchy.filter_and _ _ H3 H5); intros.
     apply filter_ex in H7.
     unfold LpRRVball in H7.
     destruct H7 as [? [? ?]].
     generalize (LpRRV_dist_triang x x0 x1); intros.
     generalize (LpRRV_dist_triang x1 y0 y); intros.
     unfold LpRRV_dist in H9.
     unfold LpRRV_dist in H10.
     generalize (LpRRV_dist_triang x x1 y); intros.
     unfold LpRRV_dist in H11.
     apply LpRRV_ball_sym in H4; unfold LpRRVball in H4; simpl in H4.
     simpl in H7.
     rewrite LpRRVnorm_minus_sym in H8; simpl in H8.
     unfold LpRRVball in H6; simpl in H6.
     eapply Rle_lt_trans.
     apply H11.
     assert (LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x x1) < eps/2).
     {
       eapply Rle_lt_trans.
       apply H9.
       simpl; lra.
     }
     assert (LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x1 y) < eps/2).
     {
       eapply Rle_lt_trans.
       apply H10.
       simpl; lra.
     }
     lra.
  Qed.     

   Lemma nneg_lt_eps_zero (x : R) :
     0 <= x ->
     (forall (eps:posreal), x < eps) -> x = 0.
   Proof.
     intros.
     destruct (Rgt_dec x 0).
     - specialize (H0 (mkposreal _ r)).
       simpl in H0; lra.
     - lra.
   Qed.

 Lemma cauchy_filterlim_almost_unique_0 (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
       (PF : ProperFilter F)
       (x y : LpRRV prts 2) :
   (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
   (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
   LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) = 0.
 Proof.
   intros.
   generalize (cauchy_filterlim_almost_unique_eps _ _ _ _ H H0); intros.
   apply nneg_lt_eps_zero; trivial.
   apply power_nonneg.
  Qed.

 Lemma cauchy_filterlim_almost_unique_alt_0 (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
       (PF : ProperFilter F)
       (x y : LpRRV prts 2) :
   (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
   (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
   LpRRVnorm prts (LpRRVminus prts (p := bignneg 2 big2) x y) = 0.
  Proof.
    intros.
   generalize (cauchy_filterlim_almost_unique_eps_alt _ _ _ _ H H0); intros.
   apply nneg_lt_eps_zero; trivial.
   apply power_nonneg.
 Qed.

 Lemma cauchy_filterlim_almost_unique (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
       (PF : ProperFilter F)
       (x y : LpRRV prts 2) :
   (forall (eps:posreal), F (LpRRVball prts big2 x eps)) ->
   (forall (eps:posreal), F (LpRRVball prts big2 y eps)) ->
   almostR2 prts eq x y.
 Proof.
   intros.
   generalize (cauchy_filterlim_almost_unique_0 _ _ _ _ H H0); intros.
   apply LpRRV_norm0 in H1.
   now apply LpRRValmost_sub_zero_eq in H1.
 Qed.

 Lemma cauchy_filterlim_almost_unique_alt (F : ((LpRRV_UniformSpace prts big2 -> Prop) -> Prop))
       (PF : ProperFilter F)
       (x y : LpRRV prts 2) :
   (forall (eps:posreal), exists (x0 : LpRRV prts 2), F (LpRRVball prts big2 x0 eps) /\ (LpRRVball prts big2 x0 eps x)) ->
   (forall (eps:posreal), exists (y0 : LpRRV prts 2), F (LpRRVball prts big2 y0 eps) /\ (LpRRVball prts big2 y0 eps y)) ->
   almostR2 prts eq x y.
 Proof.
   intros.
   generalize (cauchy_filterlim_almost_unique_alt_0 _ _ _ _ H H0); intros.
   apply LpRRV_norm0 in H1.
   now apply LpRRValmost_sub_zero_eq in H1.
Qed.

 
Lemma SimpleExpectation_prob_space_sa_sub
      dom2 sub x
  {rv:RandomVariable dom borel_sa x} 
  {rv2:RandomVariable dom2 borel_sa x} 
  {frf:FiniteRangeFunction x} :
  @SimpleExpectation Ts dom prts x rv frf = 
  @SimpleExpectation Ts dom2 (prob_space_sa_sub dom2 sub) x rv2 frf.
Proof.
  unfold SimpleExpectation.
  f_equal.
  apply map_ext; intros.
  f_equal.
  simpl.
  apply ps_proper.
  intros ?.
  unfold preimage_singleton; simpl.
  tauto.
Qed.

Lemma NonnegExpectation_prob_space_sa_sub
      dom2 sub x
      {pofrf:NonnegativeFunction x}
      {rv:RandomVariable dom2 borel_sa x}
            
  :
  @NonnegExpectation Ts dom2 (prob_space_sa_sub dom2 sub)  x pofrf =
  @NonnegExpectation Ts dom prts x pofrf.
Proof.
 generalize ((RandomVariable_sa_sub _ sub x (rv_x:=rv)))
 ; intros rv1.
 

 assert (forall n, RandomVariable dom borel_sa (simple_approx (fun x0 : Ts => x x0) n)).
  {
    apply simple_approx_rv.
    * now apply positive_Rbar_positive.
    * typeclasses eauto.
  } 

  assert (forall n, RandomVariable dom2 borel_sa (simple_approx (fun x0 : Ts => x x0) n)).
  {
    apply simple_approx_rv.
    * now apply positive_Rbar_positive.
    * typeclasses eauto.
  } 

 rewrite <- (monotone_convergence x (simple_approx x)
                                  rv1 pofrf
                                  (fun n => simple_approx_rv _ _)
                                  (fun n => simple_approx_pofrf _ _)).
 rewrite <- (monotone_convergence x (simple_approx x)
                                  rv pofrf
                                  (fun n => simple_approx_rv _ _)
                                  (fun n => simple_approx_pofrf _ _)).
 - apply Lim_seq_ext; intros n.
   repeat erewrite <- simple_NonnegExpectation.
   symmetry.
   apply SimpleExpectation_prob_space_sa_sub.
 - intros n a.
   apply (simple_approx_le x pofrf n a).
 - intros n a.
   apply (simple_approx_increasing x pofrf n a).
 - intros n.
   apply simple_expectation_real; trivial.
   apply simple_approx_frf.
 - intros.
   apply (simple_approx_lim_seq x).
   now apply positive_Rbar_positive.
 - intros n a.
   apply (simple_approx_le x pofrf n a).
 - intros n a.
   apply (simple_approx_increasing x pofrf n a).
 - intros n.
   apply simple_expectation_real; trivial.
   apply simple_approx_frf.
 - intros.
   apply (simple_approx_lim_seq x).
   now apply positive_Rbar_positive.

   Unshelve.
   apply simple_approx_frf.
Qed.

Lemma Expectation_prob_space_sa_sub
      dom2 sub x
      {rv:RandomVariable dom2 borel_sa x}
            
  :
  @Expectation Ts dom2 (prob_space_sa_sub dom2 sub)  x =
  @Expectation Ts dom prts x.
Proof.
  generalize ((RandomVariable_sa_sub _ sub x (rv_x:=rv)))
  ; intros rv1.

  unfold Expectation.
  repeat rewrite NonnegExpectation_prob_space_sa_sub by typeclasses eauto.
  reflexivity.
Qed.

Lemma IsLp_prob_space_sa_sub
      p dom2 sub x
  {rv:RandomVariable dom2 borel_sa x} :
  IsLp prts p x <->
  IsLp (prob_space_sa_sub dom2 sub) p x.
Proof.
  unfold IsLp, IsFiniteExpectation; intros.
  now rewrite Expectation_prob_space_sa_sub by typeclasses eauto.
Qed.

Definition subset_to_sa_sub   (dom2 : SigmaAlgebra Ts) 
           (sub : sa_sub dom2 dom)
           (set:LpRRV_UniformSpace (prob_space_sa_sub dom2 sub) big2 -> Prop) :
  {x : LpRRV_UniformSpace prts big2 | RandomVariable dom2 borel_sa x} -> Prop.
Proof.
  intros [x pfx].
  apply set.
  simpl.
  destruct x; simpl in *.
  exists LpRRV_rv_X; trivial.
  apply IsLp_prob_space_sa_sub; trivial.
Defined.

 Definition subset_filter_to_sa_sub_filter
            (dom2 : SigmaAlgebra Ts) 
            (sub : sa_sub dom2 dom)
            (F:({x : LpRRV_UniformSpace prts big2 | RandomVariable dom2 borel_sa x} -> Prop) -> Prop) :
   (LpRRV_UniformSpace (prob_space_sa_sub dom2 sub) big2 -> Prop) -> Prop.
 Proof.
   intros sa.
   apply F.
   eapply subset_to_sa_sub; eauto.
 Defined.

  Lemma subset_filter_to_sa_sub_filter_Filter dom2 sub F :
   Filter F ->
   Filter (subset_filter_to_sa_sub_filter dom2 sub F).
  Proof.
   intros [FF1 FF2 FF3].
   unfold subset_filter_to_sa_sub_filter, subset_to_sa_sub.
   split.
   - eapply FF3; try eapply FF1; intros.
     destruct x; trivial.
   - intros.
     eapply FF3; try eapply FF2; [| eapply H | eapply H0].
     intros [??]; simpl; intros.
     tauto.
   - intros.
     eapply FF3; [| eapply H0].
     intros [??].
     eapply H.
  Qed.

 Lemma subset_filter_to_sa_sub_filter_proper dom2 sub F :
   ProperFilter F ->
   ProperFilter (subset_filter_to_sa_sub_filter dom2 sub F).
 Proof.
   intros pf.
   unfold subset_filter_to_sa_sub_filter; simpl.
   constructor.
   - intros.
     destruct pf.
     destruct (filter_ex _ H).
     destruct x; simpl in *.
     eexists; eapply H0.
   - destruct pf.
     now apply subset_filter_to_sa_sub_filter_Filter.
 Qed.

Definition prob_space_sa_sub_set_lift
           dom2 sub
           (s:LpRRV (prob_space_sa_sub dom2 sub) 2 -> Prop)
           (x:LpRRV prts 2) : Prop.
Proof.
  destruct x.
  destruct (ClassicalDescription.excluded_middle_informative (RandomVariable dom2 borel_sa LpRRV_rv_X)).
  - apply s.
    exists LpRRV_rv_X; trivial.
    now apply IsLp_prob_space_sa_sub.
  - exact False.
Defined.

Definition prob_space_sa_sub_LpRRV_lift
           dom2 sub
           (s:LpRRV (prob_space_sa_sub dom2 sub) 2)
           : LpRRV prts 2.
Proof.
  destruct s.
  exists LpRRV_rv_X.
  - eapply RandomVariable_sa_sub; eauto.
  - eapply IsLp_prob_space_sa_sub; eauto.
Defined.

Instance prob_space_sa_sub_LpRRV_lift_rv dom2 sub (X:LpRRV (prob_space_sa_sub dom2 sub) 2)
      {rvx:RandomVariable dom2 borel_sa X} :
  RandomVariable dom2 borel_sa (prob_space_sa_sub_LpRRV_lift dom2 sub X).
Proof.
  now destruct X; simpl in *.
Qed.

Lemma IsFiniteExpectation_prob_space_sa_sub
      dom2 sub x
      {rv:RandomVariable dom2 borel_sa x}
      {isfe:IsFiniteExpectation (prob_space_sa_sub dom2 sub) x} :
  IsFiniteExpectation prts x.
Proof.
  unfold IsFiniteExpectation in *.
  now rewrite Expectation_prob_space_sa_sub in isfe by trivial.
Qed.

Lemma IsFiniteExpectation_prob_space_sa_sub_f
      dom2 sub x
      {rv:RandomVariable dom2 borel_sa x}
      {isfe:IsFiniteExpectation prts x} :
      IsFiniteExpectation (prob_space_sa_sub dom2 sub) x.
Proof.
  unfold IsFiniteExpectation in *.
  now erewrite Expectation_prob_space_sa_sub.
Qed.
  
Lemma FiniteExpectation_prob_space_sa_sub
      dom2 sub x
      {rv:RandomVariable dom2 borel_sa x}
      {isfe1:IsFiniteExpectation (prob_space_sa_sub dom2 sub) x}
      {isfe2:IsFiniteExpectation prts x} :
  FiniteExpectation (prob_space_sa_sub dom2 sub) x =
  FiniteExpectation prts x.
Proof.
  unfold FiniteExpectation, proj1_sig.
  repeat match_destr.
  rewrite Expectation_prob_space_sa_sub in e by trivial.
  congruence.
Qed.

Lemma ortho_phi_closed 
      (dom2 : SigmaAlgebra Ts) 
      (sub : sa_sub dom2 dom) :
  @closed (LpRRVq_UniformSpace prts 2 big2) (ortho_phi dom2).
Proof.
  unfold closed, ortho_phi, locally.
  intros.
  destruct (Quot_inv x); subst.
  generalize (not_ex_all_not _ _ H)
  ; intros HH1; clear H.
  generalize (fun n => not_all_ex_not _ _ (HH1 n))
  ; intros HH2; clear HH1.

  assert (HH3: forall n : posreal,
        exists n0 : LpRRVq_UniformSpace prts 2 big2,
          @Hierarchy.ball  (LpRRVq_UniformSpace prts 2 big2) (Quot (LpRRV_eq prts) x0) n n0 /\
           (exists z : LpRRV prts 2,
               Quot (LpRRV_eq prts) z = n0 /\ RandomVariable dom2 borel_sa z)).
  {
    intros n.
    destruct (HH2 n).
    exists x.
    apply not_all_not_ex in H.
    destruct H.
    tauto.
  }
  clear HH2.
  
  assert (HH4: forall eps : posreal,
      exists z : LpRRV prts 2,
        (@Hierarchy.ball (LpRRVq_UniformSpace prts 2 big2)
                         (Quot (LpRRV_eq prts) x0) eps
                         (Quot (LpRRV_eq prts) z)) /\
        (RandomVariable dom2 borel_sa z)).
  {
    intros eps.
    destruct (HH3 eps) as [x [xH1 [z [xH2 xH3]]]]; subst.
    eauto.
  }
  clear HH3.
  assert (HH5: forall eps : posreal,
      exists z : LpRRV prts 2,
        (@Hierarchy.ball (LpRRV_UniformSpace prts big2)
                         x0 eps z) /\
        (RandomVariable dom2 borel_sa z)).
  {
    intros eps.
    destruct (HH4 eps) as [x [? ?]].
    red in H; simpl in H.
    rewrite LpRRVq_ballE in H.
    eauto.
  }
  assert (forall (n : nat), 0 < (/ (INR (S n)))).
  {
    intros.
    apply Rinv_0_lt_compat.
    apply lt_0_INR.
    lia.
  }
  assert (forall (n:nat),
             {z:LpRRV prts 2 |
               (LpRRVball prts big2 x0 (mkposreal _ (H n)) z) /\
               (RandomVariable dom2 borel_sa z)}).
  {
    intros.
    destruct (constructive_indefinite_description _ (HH5 (mkposreal _ (H n))))
      as [x Fx].
    now exists x.
  }
  pose (f := fun (n : nat) => proj1_sig (X n)).
  assert (is_lim_seq (fun n => LpRRV_dist (f n) x0) 0).
  {
    apply is_lim_seq_spec.
    unfold is_lim_seq'.
    intros.
    assert (0 < eps) by apply cond_pos.
    generalize (archimed_cor1 eps H0); intros.
    destruct H1 as [? [? ?]].
    exists x.
    intros.
    rewrite Rminus_0_r, Rabs_pos_eq.
    - unfold f.
      destruct (X n) as [? [? ?]].
      simpl.
      apply LpRRV_ball_sym in l.
      unfold LpRRVball in l.
      eapply Rlt_trans.
      apply l.
      apply Rlt_trans with (r2 := / INR x); trivial.
      apply Rinv_lt_contravar.
      apply Rmult_lt_0_compat.
      + now apply lt_0_INR.
      + apply lt_0_INR; lia.
      + apply lt_INR; lia.
    - unfold LpRRVnorm.
      apply power_nonneg.
  }
  pose (prts2 := prob_space_sa_sub dom2 sub).

  pose (F :=  LpRRV_filter_from_seq f).
  pose (dom2pred := fun v => RandomVariable dom2 borel_sa v).
  pose (F2 := subset_filter F dom2pred ).
  pose (F3:=subset_filter_to_sa_sub_filter _ sub F2).

  generalize (L2RRV_lim_complete prts2 big2 F3); intros HH1.

  
  assert (ProperFilter F).
  {
    subst F f.
    unfold LpRRV_filter_from_seq; simpl.
    split.
    - intros P [N HP].
      exists (proj1_sig (X N)).
      apply HP.
      lia.
    - split.
      + exists 0%nat; trivial.
      + intros P Q [NP HP] [NQ HQ].
        exists (max NP NQ); intros n nN.
        split.
        * apply HP.
          generalize (Max.le_max_l NP NQ); lia.
        * apply HQ.
          generalize (Max.le_max_r NP NQ); lia.
      + intros P Q Himp [N HP].
        exists N; intros n nN.
        auto.
  }

  assert (pfsub:ProperFilter (subset_filter F (fun v : LpRRV prts 2 => dom2pred v))).
  {
    apply subset_filter_proper; intros.
    subst F.
    subst f.
    unfold LpRRV_filter_from_seq in H2.
    destruct H2 as [? HH2].
    unfold dom2pred.
    exists (proj1_sig (X x)).
    split.
    - destruct (X x); simpl.
      tauto.
    - apply HH2; lia.
  } 
    
  assert (F3proper:ProperFilter F3).
  {
    unfold F3, F2.
    now apply subset_filter_to_sa_sub_filter_proper.
  }

  assert (F3cauchy:cauchy F3).
  {
    unfold F3, F2.
    unfold subset_filter_to_sa_sub_filter.
    intros eps; simpl.
    unfold F, f.
    unfold LpRRV_filter_from_seq; simpl.
    unfold dom2pred.
    assert (eps2pos:0 < eps / 2).
    {
      destruct eps; simpl.
      lra.
    } 

    destruct (archimed_cor1 (eps/2) eps2pos) as [N [Nlt Npos]].

    destruct (X N)
      as [x [XH XR]].
    assert (xlp:IsLp (prob_space_sa_sub dom2 sub) 2 x).
    {
      apply IsLp_prob_space_sa_sub; typeclasses eauto.
    } 
    exists (pack_LpRRV (prob_space_sa_sub dom2 sub) x).
    red.
    exists N.
    simpl.
    intros n nN ?.
    destruct (X n) as [Xn [XnH XnRv]]; simpl in *.
    unfold pack_LpRRV; simpl.
    generalize (LpRRV_dist_triang x x0 Xn)
    ; intros triag.
    unfold LpRRV_dist in triag.
    unfold Hierarchy.ball; simpl.
    unfold LpRRVball; simpl.
    simpl in *.

    destruct Xn as [Xn ??]; simpl in *.
    apply LpRRV_ball_sym in XH.
    LpRRV_simpl.
    simpl in *.
    unfold LpRRVball in XnH, XH, triag.
    simpl in XnH, XH, triag.
    unfold LpRRVminus in XnH, XH, triag; simpl in XnH, XH, triag.
    
    unfold LpRRVnorm in *.
    erewrite FiniteExpectation_prob_space_sa_sub; try typeclasses eauto.
    unfold pack_LpRRV, prob_space_sa_sub in XnH, XH, triag |- *; simpl in *.
    eapply Rle_lt_trans; try eapply triag.
    replace (pos eps) with ((eps/2) + (eps/2)) by lra.
    assert (sNeps2:/ INR (S N) < eps /2).
    {
      apply Rle_lt_trans with (r2 := / INR N); trivial.
      apply Rinv_le_contravar.
      - apply lt_0_INR; lia.
      - apply le_INR; lia.
    }
    assert (sneps2:/ INR (S n) < eps /2).
    {
      apply Rle_lt_trans with (r2 := / INR (S N)); trivial.
      apply Rinv_le_contravar.
      - apply lt_0_INR; lia.
      - apply le_INR; lia.
    }
    apply Rplus_lt_compat.
    - rewrite <- sNeps2; trivial.
    - rewrite <- sneps2; trivial.
  } 
  cut_to HH1; trivial.
  exists (prob_space_sa_sub_LpRRV_lift dom2 sub (LpRRV_lim prts2 big2 F3)).
  split; [|typeclasses eauto].
  LpRRVq_simpl.
  unfold LpRRV_eq.
  apply (LpRRValmost_sub_zero_eq prts (p := bignneg 2 big2)).
  apply LpRRV_norm0.
  apply nneg_lt_eps_zero; [apply power_nonneg |].
  assert (forall (eps:posreal),
             exists (N:nat),
               forall (n:nat), (n>=N)%nat ->
                               LpRRV_dist (f n) x0 < eps).
  {
    intros.
    apply is_lim_seq_spec in H0.
    destruct (H0 eps).
    exists x; intros.
    specialize (H2 n H3).
    rewrite Rminus_0_r in H2.
    now rewrite Rabs_pos_eq in H2 by apply power_nonneg.
  }

  assert (F3limball:forall (eps:posreal),
             (LpRRV_dist (prob_space_sa_sub_LpRRV_lift dom2 sub (LpRRV_lim prts2 big2 F3)) x0) < eps).
  {
    intros.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/2) by lra.
    destruct (HH1 (mkposreal _ H4)).
    destruct (H2 (mkposreal _ H4)).
    specialize (H6 (max x x1)).
    specialize (H5 (max x x1)).
    cut_to H5; try lia.
    cut_to H6; try lia.
    unfold F3, F2, F in H5.
    unfold LpRRV_filter_from_seq in H5.
    generalize (LpRRV_dist_triang (prob_space_sa_sub_LpRRV_lift dom2 sub (LpRRV_lim prts2 big2 F3)) (f (max x x1)) x0); intros.
    rewrite Rplus_comm in H7.
    eapply Rle_lt_trans.
    apply H7.
    replace (pos eps) with ((eps/2) + (eps/2)) by lra.
    apply Rplus_lt_compat.
    apply H6.
    unfold dom2pred in H5.
    assert (frv:RandomVariable dom2 borel_sa (f (Init.Nat.max x x1))).
    {
      unfold f.
      unfold proj1_sig.
      match_destr; tauto.
    } 
    specialize (H5 frv).
    unfold subset_to_sa_sub, Hierarchy.ball in H5.
    simpl in H5.
    unfold LpRRVball, LpRRVnorm in H5.
    simpl in H5.
    unfold prts2 in H5.
    assert (isfe2:IsFiniteExpectation prts
             (rvpower
                (rvabs
                   (rvminus
                      (LpRRV_lim (prob_space_sa_sub dom2 sub) big2
                         (subset_filter_to_sa_sub_filter dom2 sub
                            (subset_filter
                               (fun P : LpRRV prts 2 -> Prop =>
                                exists N : nat, forall n : nat, (n >= N)%nat -> P (f n))
                               (fun v : LpRRV prts 2 => RandomVariable dom2 borel_sa v))))
                      (match
                         f (Init.Nat.max x x1) as l
                         return (RandomVariable dom2 borel_sa l -> LpRRV (prob_space_sa_sub dom2 sub) 2)
                       with
                       | {| LpRRV_rv_X := LpRRV_rv_X; LpRRV_lp := LpRRV_lp |} =>
                           fun pfx : RandomVariable dom2 borel_sa LpRRV_rv_X =>
                           {|
                           LpRRV_rv_X := LpRRV_rv_X;
                           LpRRV_rv := pfx;
                           LpRRV_lp := match IsLp_prob_space_sa_sub 2 dom2 sub LpRRV_rv_X with
                                       | conj x _ => x
                                       end LpRRV_lp |}
                        end frv))) (const 2))).
    {
      eapply (IsFiniteExpectation_prob_space_sa_sub _ sub); try typeclasses eauto.
      unfold FiniteExpectation, proj1_sig in H5.
      match_destr_in H5.
      red.
      now rewrite e.
    }       
    rewrite (FiniteExpectation_prob_space_sa_sub _ _ _ (isfe2:=isfe2)) in H5.
    unfold LpRRV_dist, LpRRVnorm.
    simpl.
    unfold f in *.
    eapply Rle_lt_trans; try eapply H5.
    right.
    f_equal.
    apply FiniteExpectation_ext; intros ?.
    rv_unfold.
    f_equal.
    f_equal.
    f_equal.
    - unfold prob_space_sa_sub_LpRRV_lift; simpl.
      unfold F3, F2, F.
      unfold LpRRV_filter_from_seq.
      simpl.
      unfold prts2, dom2pred.
      match_destr.
    - f_equal.
      clear H6.

      destruct (X (Init.Nat.max x x1)); simpl.
      match_destr.
  } 
  apply F3limball.
Qed.

Lemma ortho_phi_complete
           (dom2 : SigmaAlgebra Ts)
           (sub : sa_sub dom2 dom) :
  @complete_subset (@PreHilbert_NormedModule (@L2RRVq_PreHilbert Ts dom prts)) (ortho_phi dom2).
Proof.
  unfold complete_subset.
  exists (LpRRVq_lim prts big2).
  intros F PF cF HH.
  assert (HHclassic: forall P : PreHilbert_NormedModule -> Prop,
             F P -> (exists x : PreHilbert_NormedModule, P x /\ ortho_phi dom2 x)).
  {
    intros P FP.
    specialize (HH P FP).
    now apply NNPP in HH.
  }
  clear HH.
  match goal with
    [|- _ /\ ?x ] => cut x; [split; trivial |]
  end.
  - apply ortho_phi_closed; trivial.
    simpl.
    unfold locally.
    intros [eps HH].
    specialize (H eps).
    destruct (HHclassic _ H) as [? [? ?]].
    specialize (HH x).
    elim HH; trivial.
    now rewrite <- hball_pre_uniform_eq.
  - intros.
    assert (cF':@cauchy (@LpRRVq_UniformSpace Ts dom prts (IZR (Zpos (xO xH))) big2) F).
    {
      now apply cauchy_pre_uniform.
    } 
    generalize (LpRRVq_lim_complete prts big2 F PF); intros.
    eapply filter_imp; try eapply (H cF' eps).
    + intros.
      unfold Hierarchy.ball; simpl.
      now apply L2RRVq_ball_ball.
Qed.

Program Definition ortho_projection_hilbert (E:PreHilbert) 
           (phi: E -> Prop) (phi_mod: compatible_m phi) (phi_compl: complete_subset phi)
           (u : E) : {v:E |
                       unique (fun v => phi v /\ norm (minus u v) = Glb_Rbar (fun r : R => exists w : E, phi w /\ r = norm (minus u w))) v}.
  generalize (ortho_projection_subspace phi phi_mod phi_compl u);intros.
  cut_to H.
- destruct (constructive_definite_description _ H) as [x xH].
  exists x.
  split; trivial.
  destruct H as [y [yH1 yH2]].
  intros.
  transitivity y; [| eauto].
  symmetry; eauto.
- intro; apply classic.
Qed.

Lemma ortho_phi_compatible_m
      (dom2 : SigmaAlgebra Ts)
      (sub : sa_sub dom2 dom)
  : compatible_m (E:=(L2RRVq_PreHilbert prts)) (ortho_phi dom2).
Proof.
  split; [split | ]; intros.
  - destruct H as [a [eqqa rv_a]]; subst.
    destruct H0 as [b [eqqb rv_b]]; subst.
    unfold plus, opp; simpl.
    rewrite LpRRVq_oppE, LpRRVq_plusE.
    eexists.
    split.
    + reflexivity.
    + typeclasses eauto.
  - exists (LpRRVq_zero prts).
    exists (LpRRVzero prts).
    simpl.
    split.
    + reflexivity.
    + typeclasses eauto.
  - destruct H as [a [eqqa Ha]]; subst.
    exists (LpRRVscale prts l a).
    simpl.
    split.
    + unfold scal; simpl.
      rewrite LpRRVq_scaleE.
      reflexivity.
    + typeclasses eauto.
Qed.

Definition conditional_expectation_L2q
           (dom2 : SigmaAlgebra Ts)
           (sub : sa_sub dom2 dom)
           (x:LpRRVq prts 2)
  : {v : L2RRVq_PreHilbert prts
      | unique
          (fun v : L2RRVq_PreHilbert prts =>
             ortho_phi dom2 v /\
             norm (minus (G:=(PreHilbert.AbelianGroup (L2RRVq_PreHilbert prts))) x v) =
             Glb_Rbar (fun r : R => exists w : L2RRVq_PreHilbert prts,
                           ortho_phi dom2 w /\
                           r = norm (minus (G:=(PreHilbert.AbelianGroup (L2RRVq_PreHilbert  prts)))x w)))
          v}.
Proof.
  apply (ortho_projection_hilbert (L2RRVq_PreHilbert prts)
                                       (ortho_phi dom2)
                                       (ortho_phi_compatible_m _ sub)
                                       (ortho_phi_complete _ sub)
                                       x).
Qed.

Let nneg2 : nonnegreal := bignneg 2 big2.
Canonical nneg2.

(* Note that we lose uniqueness, since it only holds over the quotiented space. *)
Definition conditional_expectation_L2 (f :LpRRV prts 2)
        (dom2 : SigmaAlgebra Ts)
        (sub : sa_sub dom2 dom) :
   {v : LpRRV prts 2 
      | RandomVariable dom2 borel_sa v /\
        LpRRVnorm prts (LpRRVminus prts f v) =
        Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                      RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                      r = LpRRVnorm prts (LpRRVminus prts f w)) /\
        (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts f v) (LpRRVminus prts w v) <= 0) /\
        (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts v w = L2RRVinner prts (pack_LpRRV prts f) w) /\

        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
              (LpRRVnorm prts (LpRRVminus prts f z) =
              Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                            RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                            r = LpRRVnorm prts (LpRRVminus prts f w))) -> LpRRV_eq prts z v) /\
        
        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts f z) (LpRRVminus prts w z) <= 0) -> LpRRV_eq prts z v) /\
        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
                            (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts z w = L2RRVinner prts (pack_LpRRV prts f) w)  -> LpRRV_eq prts z v)

     }.
Proof.
  destruct ((conditional_expectation_L2q dom2 sub (Quot _ f))).
  destruct u as [[HH1 HH2] HH3].
  destruct (charac_ortho_projection_subspace1 _ (ortho_phi_compatible_m _ sub) (Quot (LpRRV_eq prts) f) _ HH1)
    as [cops1_f _].
  destruct (charac_ortho_projection_subspace2 _ (ortho_phi_compatible_m _ sub) (Quot (LpRRV_eq prts) f) _ HH1)
    as [cops2_f _].
  specialize (cops1_f HH2).
  specialize (cops2_f HH2).
  red in HH1.
  apply constructive_indefinite_description in HH1.
  destruct HH1 as [y [eqqy rvy]].
  exists y.
  split; trivial.
  subst.
  unfold norm, minus, plus, opp in *; simpl in *.
  rewrite L2RRVq_norm_norm in HH2.
  autorewrite with quot in HH2.
  rewrite LpRRVq_normE in HH2.
  rewrite LpRRVminus_plus.
  unfold nonneg in HH2 |- *; simpl in *.
  rewrite HH2.
  assert (glb_eq:
      Glb_Rbar
        (fun r : R =>
           exists w : LpRRVq prts 2,
             ortho_phi dom2 w /\ r = Hnorm (LpRRVq_plus prts (Quot (LpRRV_eq prts) f) (LpRRVq_opp prts w)))
      =
      Glb_Rbar
        (fun r : R =>
           exists w : LpRRV prts 2, RandomVariable dom2 borel_sa w /\ r = LpRRVnorm prts (LpRRVminus prts f w))).

  { 
    apply Glb_Rbar_eqset; intros.
    split; intros [w [wrv wnorm]].
    + rewrite L2RRVq_norm_norm in wnorm.
      destruct wrv as [w' [? rvw']]; subst.
      exists w'.
      split; trivial.
      autorewrite with quot.
      rewrite LpRRVq_normE.
      now rewrite LpRRVminus_plus.
    + subst.
      exists (Quot _ w).
      split.
      * exists w.
        split; trivial.
      * rewrite L2RRVq_norm_norm.
        autorewrite with quot.
        rewrite LpRRVq_normE.
        now rewrite LpRRVminus_plus.
  } 
  repeat split.
  - now f_equal.
  - intros.
    specialize (cops1_f (Quot _ w)).
    cut_to cops1_f.
    + unfold inner in cops1_f; simpl in cops1_f.
      LpRRVq_simpl.
      rewrite L2RRVq_innerE in cops1_f.
      etransitivity; try eapply cops1_f.
      right.
      apply L2RRV_inner_proper.
      * apply LpRRV_seq_eq; intros ?; simpl.
        rv_unfold; lra.
      * apply LpRRV_seq_eq; intros ?; simpl.
        rv_unfold; lra.
    + red; eauto.
  - intros.
    specialize (cops2_f (Quot _ w)).
    cut_to cops2_f.
    + unfold inner in cops2_f; simpl in cops2_f.
      repeat rewrite L2RRVq_innerE in cops2_f.
      apply cops2_f.
    + red; eauto.
  - intros x xrv xeqq.
    specialize (HH3 (Quot _ x)).
    cut_to HH3.
    + apply Quot_inj in HH3; try typeclasses eauto.
      now symmetry.
    + split.
      * unfold ortho_phi.
        eauto.
      * rewrite L2RRVq_norm_norm.
        autorewrite with quot.
        rewrite LpRRVq_normE.
        rewrite <- LpRRVminus_plus.
        unfold nonneg in *; simpl in *.
        rewrite xeqq.
        symmetry.
        now f_equal.
  - intros x xrv xeqq.
    specialize (HH3 (Quot _ x)).
    cut_to HH3.
    + apply Quot_inj in HH3; try typeclasses eauto.
      now symmetry.
    + split.
      * unfold ortho_phi.
        eauto.
      * destruct (charac_ortho_projection_subspace1 _
                                                    (ortho_phi_compatible_m _ sub)
                                                    (Quot (LpRRV_eq prts) f)
                                                    (Quot _ x))
          as [_ cops1_b].
        -- red; eauto.
        -- apply cops1_b; intros.
           destruct H as [z [? rvz]]; subst.
           specialize (xeqq _ rvz).
           etransitivity; try eapply xeqq.
           right.
           unfold inner, minus, plus, opp; simpl.
           LpRRVq_simpl.
           rewrite L2RRVq_innerE.
           apply L2RRV_inner_proper.
           ++ now rewrite <- LpRRVminus_plus.
           ++ now rewrite <- LpRRVminus_plus.
  - intros x xrv xeqq.
    specialize (HH3 (Quot _ x)).
    cut_to HH3.
    + apply Quot_inj in HH3; try typeclasses eauto.
      now symmetry.
    + split.
      * unfold ortho_phi.
        eauto.
      * destruct (charac_ortho_projection_subspace2 _
                                                    (ortho_phi_compatible_m _ sub)
                                                    (Quot (LpRRV_eq prts) f)
                                                    (Quot _ x))
          as [_ cops2_b].
        -- red; eauto.
        -- apply cops2_b; intros.
           destruct H as [z [? rvz]]; subst.
           specialize (xeqq _ rvz).
           unfold inner, minus, plus, opp; simpl.
           repeat rewrite L2RRVq_innerE.
           rewrite xeqq.
           apply L2RRV_inner_proper; try reflexivity.
           now apply LpRRV_seq_eq; intros ?; simpl.
Qed.

Definition conditional_expectation_L2fun (f : Ts -> R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
  LpRRV prts 2
  := proj1_sig (conditional_expectation_L2 (pack_LpRRV prts f) _ sub).

Instance conditional_expectation_L2fun_rv
         (f : Ts -> R) 
         (dom2 : SigmaAlgebra Ts)
         (sub : sa_sub dom2 dom)
         {rv : RandomVariable dom borel_sa f}
         {isl : IsLp prts 2 f} :
  RandomVariable dom2 borel_sa (conditional_expectation_L2fun f sub).
Proof.
  unfold conditional_expectation_L2fun, proj1_sig.
  match_destr; tauto.
Qed.

Lemma conditional_expectation_L2fun_eq
      (f : Ts -> R) 
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      {rv : RandomVariable dom borel_sa f}
      {isl : IsLp prts 2 f} :
  LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) (conditional_expectation_L2fun f sub)) =
      Glb_Rbar
        (fun r : R =>
         exists w : LpRRV prts 2,
           RandomVariable dom2 borel_sa w /\ r = LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) w)).
Proof.
  unfold conditional_expectation_L2fun, proj1_sig.
  match_destr; tauto.
Qed.

Lemma conditional_expectation_L2fun_eq1
      (f : Ts -> R) 
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      {rv : RandomVariable dom borel_sa f}
      {isl : IsLp prts 2 f} :
  (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts (pack_LpRRV prts f) (conditional_expectation_L2fun f sub)) (LpRRVminus prts w (conditional_expectation_L2fun f sub)) <= 0).
Proof.
  unfold conditional_expectation_L2fun, proj1_sig.
  match_destr; tauto.
Qed.

Lemma conditional_expectation_L2fun_eq2
      (f : Ts -> R) 
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      {rv : RandomVariable dom borel_sa f}
      {isl : IsLp prts 2 f} :
  (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (conditional_expectation_L2fun f sub) w = L2RRVinner prts (pack_LpRRV prts f) w).
Proof.
  unfold conditional_expectation_L2fun, proj1_sig.
  match_destr; tauto.
Qed.

Global Instance EventIndicator_islp (p:nonnegreal) {P} (dec : dec_pre_event P) :
  IsLp prts p (EventIndicator dec).
Proof.
  unfold IsLp.
    apply IsFiniteExpectation_bounded with (rv_X1 := const 0) (rv_X3 := const 1).
    - apply IsFiniteExpectation_const.
    - apply IsFiniteExpectation_const.
    - intro x.
      unfold const, rvpower.
      apply power_nonneg.
    - intro x.
      unfold rvpower, const.
      replace (1) with (power 1 p).
      + apply Rle_power_l.
        { apply cond_nonneg.
        } 
        unfold rvabs.
        split.
        * apply Rabs_pos.
        * unfold EventIndicator.
          match_destr.
          -- rewrite Rabs_R1; lra.
          -- rewrite Rabs_R0; lra.
      + now rewrite power_base_1.
Qed.

Definition is_conditional_expectation
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           (f ce : Ts -> R)
           {rvf : RandomVariable dom borel_sa f}
           {rvce : RandomVariable dom2 borel_sa ce}
  := forall P (dec:dec_pre_event P),
    sa_sigma (SigmaAlgebra := dom2) P ->
    Expectation (rvmult f (EventIndicator dec)) =
    Expectation (rvmult ce (EventIndicator dec)).

  Definition Rbar_rvmult (rv_X1 rv_X2 : Ts -> Rbar) :=
    (fun omega =>  Rbar_mult (rv_X1 omega) (rv_X2 omega)).

Definition is_Rbar_conditional_expectation
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           (f : Ts -> R)
           (ce : Ts -> Rbar)           
           {rvf : RandomVariable dom borel_sa f}
           {rvce : RandomVariable dom2 Rbar_borel_sa ce}
  := forall P (dec:dec_pre_event P),
    sa_sigma (SigmaAlgebra := dom2) P ->
    Expectation (rvmult f (EventIndicator dec)) =
    Rbar_Expectation (Rbar_rvmult ce (EventIndicator dec)).



Lemma is_conditional_expectation_isfe {dom2 : SigmaAlgebra Ts} (sub : sa_sub dom2 dom)
      f ce
      {rvf:RandomVariable dom borel_sa f} 
      {rvce:RandomVariable dom2 borel_sa ce} :
  is_conditional_expectation sub f ce ->
  IsFiniteExpectation prts f ->
  IsFiniteExpectation prts ce.
Proof.
  unfold is_conditional_expectation, IsFiniteExpectation; intros isce isf.
  specialize (isce _ (dsa_dec dsa_Ω)).

  assert (eqq:forall f, Expectation (rvmult f (EventIndicator (dsa_dec dsa_Ω))) = Expectation f).
  {
    intros.
    apply Expectation_proper.
    rv_unfold; intros ?; simpl.
    lra.
  }
  repeat rewrite eqq in isce.
  rewrite isce in isf.
  - apply isf.
  - simpl.
    apply sa_all.
Qed.

Lemma FiniteExpectation_plus':
  forall (rv_X1 rv_X2 : Ts -> R)
    {rv1 : RandomVariable dom borel_sa rv_X1} {rv2 : RandomVariable dom borel_sa rv_X2}
    {rv12 : RandomVariable dom borel_sa (rvplus rv_X1 rv_X2)}
    {isfe1 : IsFiniteExpectation prts rv_X1} {isfe2 : IsFiniteExpectation prts rv_X2}
   {isfe12 : IsFiniteExpectation prts (rvplus rv_X1 rv_X2)},
    FiniteExpectation prts (rvplus rv_X1 rv_X2) = FiniteExpectation prts rv_X1 + FiniteExpectation prts rv_X2.
Proof.
  intros.
  generalize (FiniteExpectation_plus prts rv_X1 rv_X2)
  ; intros eqq.
  etransitivity.
  - etransitivity; [| eapply eqq].
    apply FiniteExpectation_ext; reflexivity.
  - f_equal; apply FiniteExpectation_ext; reflexivity.
Qed.

  Lemma FiniteExpectation_scale' c rv_X 
        {isfe:IsFiniteExpectation prts rv_X} {isfe2:IsFiniteExpectation prts (rvscale c rv_X)} :
    FiniteExpectation prts (rvscale c rv_X) = c * FiniteExpectation prts rv_X.
  Proof.
    intros.
    generalize (FiniteExpectation_scale prts c rv_X)
    ; intros eqq.
    rewrite <- eqq.
    apply FiniteExpectation_ext.
    reflexivity.
  Qed.


Lemma sa_sigma_event_pre {T} {σ : SigmaAlgebra T} (E:event σ): sa_sigma E.
Proof.
  now destruct E; simpl.
Qed.
  
Lemma is_conditional_expectation_le
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      (f ce1 ce2 : Ts -> R)
      {isfe:IsFiniteExpectation prts f}
      {rvf : RandomVariable dom borel_sa f}
      {rvce1 : RandomVariable dom2 borel_sa ce1}
      {rvce2 : RandomVariable dom2 borel_sa ce2}
  : is_conditional_expectation sub f ce1 ->
    is_conditional_expectation sub f ce2 ->
    almostR2 (prob_space_sa_sub _ sub) Rle ce2 ce1.
Proof.
  unfold is_conditional_expectation.
  intros isce1 isce2.
  generalize (is_conditional_expectation_isfe sub _ _ isce1 isfe); intros isfe1.
  generalize (is_conditional_expectation_isfe sub _ _ isce2 isfe); intros isfe2.
  
  pose (An:=fun n => event_ge dom2 (rvminus ce2 ce1) (/ (INR (S n)))).
  pose (Dn:= fun n => (event_ge_pre_dec dom2 (rvminus ce2 ce1) (/ (INR (S n))))).
  pose (In:=fun n => EventIndicator (Dn n)).

  
  assert (eqq1: forall n, ps_P (ProbSpace:=(prob_space_sa_sub _ sub)) (An n) = 0).
  { 
    intros n.
     assert (npos: 0 < / INR (S n)).
     {
       apply Rinv_0_lt_compat.
       apply lt_0_INR.
       lia.
     } 
    assert (eqq2:Expectation (rvmult ce1 (In n)) = Expectation (rvmult ce2 (In n) )).
    {
      unfold In, Dn.
      rewrite <- isce1, <- isce2; trivial
      ; apply sa_sigma_event_pre.
    }
    assert (isfee:IsFiniteExpectation prts (rvmult (rvplus ce1 (const (/ (INR (S n))))) (In n))).
    {
      unfold In.
      assert (RandomVariable dom borel_sa (rvplus ce1 (const (/ INR (S n))))).
      { apply rvplus_rv; try typeclasses eauto.
        eapply RandomVariable_sa_sub; eauto.
      } 
      apply (IsFiniteExpectation_indicator _ _ (Dn n)).
      - apply sub; apply sa_sigma_event_pre. 
      - apply IsFiniteExpectation_plus; try typeclasses eauto.
        eapply RandomVariable_sa_sub; eauto.
    } 
      
    assert (eqq3:rv_eq (rvmult (rvplus ce1 (const (/ (INR (S n))))) (In n))
                       (rvplus (rvmult ce1 (In n)) (rvmult (const (/ INR (S n))) (In n)))).
    {
      rv_unfold.
      intros ?; lra.
    }
    assert (isfe1n: IsFiniteExpectation prts (rvmult ce1 (In n))).
    {
      unfold In.
      apply IsFiniteExpectation_indicator; trivial.
      - eapply RandomVariable_sa_sub; eauto.
      - apply sub; apply sa_sigma_event_pre. 
    }

    assert (isfe2n: IsFiniteExpectation prts (rvmult ce2 (In n))).
    {
      unfold In.
      apply IsFiniteExpectation_indicator; trivial.
      - eapply RandomVariable_sa_sub; eauto.
      - apply sub; apply sa_sigma_event_pre. 
    }
    assert (eqq4:Rge (FiniteExpectation prts (rvmult ce2 (In n))) (FiniteExpectation prts (rvmult (rvplus ce1 (const (/ (INR (S n))))) (In n)))).
    {
      apply Rle_ge.
      apply FiniteExpectation_le.
      intros ?.
      unfold In, Dn.
      rv_unfold.
      match_destr; try lra.
      simpl in *.
      lra.
    }
    assert (isfe3n: IsFiniteExpectation prts (rvmult (const (/ INR (S n))) (EventIndicator (Dn n)))).
    {
      apply IsFiniteExpectation_indicator; try typeclasses eauto.
      apply sub; apply sa_sigma_event_pre.
    }
    
    rewrite (FiniteExpectation_ext_alt _ _ _ eqq3) in eqq4.
    erewrite FiniteExpectation_plus' in eqq4; unfold In; try typeclasses eauto.
    
    - assert (eqq5:FiniteExpectation prts (rvmult ce2 (EventIndicator (Dn n))) =
                     FiniteExpectation prts (rvmult ce1 (EventIndicator (Dn n)))).
        {
          unfold FiniteExpectation, proj1_sig.
          repeat match_destr.
          subst In.
          cut (Some (Finite x) = Some (Finite x0)); [now intros HH; invcs HH |].
          rewrite <- e, <- e0.
          etransitivity.
          - etransitivity; [| symmetry; apply eqq2].
            now apply Expectation_proper.
          - now apply Expectation_proper.
        }
        unfold In in eqq4.
        rewrite eqq5 in eqq4.
        match type of eqq4 with
          ?x >= _  => replace x with (x + 0) in eqq4 at 1 by lra
        end.
        match type of eqq4 with
          FiniteExpectation prts ?a (isfe:=?af) + _ >= FiniteExpectation prts ?b (isfe:=?bf) + _ =>
          replace (FiniteExpectation prts a (isfe:=af)) with (FiniteExpectation prts b (isfe:=bf)) in eqq4
        end.
      + 
        apply Rplus_ge_reg_l in eqq4.

        assert (eqq6:FiniteExpectation prts (rvmult (const (/ INR (S n))) (EventIndicator (Dn n))) = 0).
        {
          apply antisymmetry.
          - apply Rge_le.
            apply eqq4.
          - apply FiniteExpectation_pos.
            intros ?.
            rv_unfold.
            assert (0 <= / INR (S n)).
            {
              left.
              apply Rinv_0_lt_compat.
              apply lt_0_INR.
              lia.
            } 
            match_destr; lra.
        } 
        assert (eqq7:rv_eq (rvmult (const (/ INR (S n))) (EventIndicator (Dn n)))
                           (rvscale  (/ INR (S n)) (EventIndicator (Dn n)))).
        {
          intros ?.
          rv_unfold; lra.
        } 
        rewrite (FiniteExpectation_ext_alt _ _ _ eqq7) in eqq6.
        unfold FiniteExpectation, proj1_sig in eqq6.
        match_destr_in eqq6; subst.
        rewrite Expectation_scale in e; [| lra].
        erewrite <- (Expectation_prob_space_sa_sub _ sub) in e.
      * rewrite Expectation_EventIndicator in e.
        unfold An.
        invcs e.
        rewrite H0.
        apply Rmult_integral in H0.
        destruct H0.
        -- assert (/ INR (S n) = 0) by apply H.
          lra.
        -- apply H.
      * unfold Dn.
        typeclasses eauto.
      + apply FiniteExpectation_ext; reflexivity.
    - apply rvmult_rv.
      + eapply RandomVariable_sa_sub; eauto.
      + unfold EventIndicator.
        eapply RandomVariable_sa_sub; trivial.
        apply EventIndicator_rv.
    - apply rvmult_rv.
      + apply rvconst.
      + unfold EventIndicator.
        eapply RandomVariable_sa_sub; trivial.
        apply EventIndicator_rv.
    - { apply rvplus_rv.
        - apply rvmult_rv.
          + eapply RandomVariable_sa_sub; eauto.
          + unfold EventIndicator.
            eapply RandomVariable_sa_sub; trivial.
            apply EventIndicator_rv.
        - apply rvmult_rv.
          + apply rvconst.
          + unfold EventIndicator.
            eapply RandomVariable_sa_sub; trivial.
            apply EventIndicator_rv.
      } 
  }
  apply almost_alt_eq.
  exists (union_of_collection An).
  split.
  - apply (ps_zero_countable_union _ _ eqq1)
    ; intros HH.
  - intros x xgt.
    apply Rnot_le_gt in xgt.
    simpl.
    assert (pos:0 < ce2 x - ce1 x) by lra.
    destruct (archimed_cor1 _ pos) as [N [Nlt Npos]].
    exists N.
    rv_unfold.
    apply Rle_ge.
    assert (le1:/ (INR (S N)) <= / (INR N)).
    {
      apply Rinv_le_contravar.
      - now apply lt_0_INR.
      - rewrite S_INR; lra.
    }
    rewrite le1.
    rewrite Nlt.
    lra.
    Unshelve.
    trivial.
Qed.

Lemma is_conditional_expectation_eq
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      (f ce1 ce2 : Ts -> R)
      {rvf : RandomVariable dom borel_sa f}
      {isfe:IsFiniteExpectation prts f}
      {rvce1 : RandomVariable dom2 borel_sa ce1}
      {rvce2 : RandomVariable dom2 borel_sa ce2}
  : is_conditional_expectation sub f ce1 ->
    is_conditional_expectation sub f ce2 ->
    almostR2 (prob_space_sa_sub _ sub) eq ce1 ce2.
Proof.
  unfold is_conditional_expectation.
  intros isce1 isce2.
  apply antisymmetry
  ; eapply is_conditional_expectation_le; eauto.
Qed.

Lemma almostR2_prob_space_sa_sub_lift
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      RR
      (f1 f2:Ts -> R):
  almostR2 (prob_space_sa_sub _ sub) RR f1 f2 ->
  almostR2 prts RR f1 f2.
Proof.
  intros [p [pone peqq]].
  red.
  simpl in *.
  exists (event_sa_sub sub p).
  split; trivial.
Qed.
 
Lemma is_conditional_expectation_eq_prts
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      (f ce1 ce2 : Ts -> R)
      {rvf : RandomVariable dom borel_sa f}
      {isfe:IsFiniteExpectation prts f}
      {rvce1 : RandomVariable dom2 borel_sa ce1}
      {rvce2 : RandomVariable dom2 borel_sa ce2}
  : is_conditional_expectation sub f ce1 ->
    is_conditional_expectation sub f ce2 ->
    almostR2 prts eq ce1 ce2.
 Proof.
   intros.
   apply (almostR2_prob_space_sa_sub_lift sub).
   eapply is_conditional_expectation_eq; eauto.
 Qed.

Lemma conditional_expectation_L2fun_eq3
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      (f : Ts -> R) 
      {rv : RandomVariable dom borel_sa f}
      {isl : IsLp prts 2 f} :
  is_conditional_expectation sub f (conditional_expectation_L2fun f sub).
Proof.
  unfold is_conditional_expectation.
  intros.
  assert (RandomVariable dom2 borel_sa (EventIndicator dec)) by now apply EventIndicator_pre_rv.
  assert (RandomVariable dom borel_sa (EventIndicator dec)) by now apply RandomVariable_sa_sub with (dom3 := dom2).
  generalize (conditional_expectation_L2fun_eq2 f sub (pack_LpRRV prts (EventIndicator dec))); intros.
  cut_to H2.
  - unfold L2RRVinner in H2.
    simpl in H2.
    symmetry in H2.
    unfold FiniteExpectation, proj1_sig in H2.
    do 2 match_destr_in H2.
    subst.
    erewrite Expectation_ext; [rewrite e | reflexivity].
    erewrite Expectation_ext; [rewrite e0 | reflexivity].
    trivial.
  - now apply EventIndicator_pre_rv.
Qed.

Lemma conditional_expectation_L2fun_unique
      (f : Ts -> R) 
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      {rv : RandomVariable dom borel_sa f}
      {isl : IsLp prts 2 f}
      (z: LpRRV prts 2)
      {z_rv:RandomVariable dom2 borel_sa z} :
  (LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) z) =
   Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                 RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                 r = LpRRVnorm prts (LpRRVminus prts (pack_LpRRV prts f) w))) ->
  LpRRV_eq prts z (conditional_expectation_L2fun f sub).
Proof.
  unfold conditional_expectation_L2fun, proj1_sig.
  match_destr.
  intuition.
Qed.

Lemma conditional_expectation_L2fun_unique1
      (f : Ts -> R) 
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      {rv : RandomVariable dom borel_sa f}
      {isl : IsLp prts 2 f}
      (z: LpRRV prts 2)
      {z_rv:RandomVariable dom2 borel_sa z} :
  (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts (LpRRVminus prts (pack_LpRRV prts f) z) (LpRRVminus prts w z) <= 0) -> LpRRV_eq prts z (conditional_expectation_L2fun f sub).
Proof.
  unfold conditional_expectation_L2fun, proj1_sig.
  match_destr.
  intuition.
Qed.

Lemma conditional_expectation_L2fun_unique2
      (f : Ts -> R) 
      {dom2 : SigmaAlgebra Ts}
      (sub : sa_sub dom2 dom)
      {rv : RandomVariable dom borel_sa f}
      {isl : IsLp prts 2 f}
      (z: LpRRV prts 2)
      {z_rv:RandomVariable dom2 borel_sa z} :
  (forall w:LpRRV prts 2, RandomVariable dom2 borel_sa w -> L2RRVinner prts z w = L2RRVinner prts (pack_LpRRV prts f) w)  -> LpRRV_eq prts z (conditional_expectation_L2fun f sub).
Proof.
  unfold conditional_expectation_L2fun, proj1_sig.
  match_destr.
  intuition.
Qed.

Instance IsLp_min_const_nat (f : Ts -> R) (n : nat) 
         {nneg : NonnegativeFunction f} :
  IsLp prts 2 (rvmin f (const (INR n))).
Proof.
  intros.
  apply IsLp_bounded with (rv_X2 := const (power (INR n) 2)).
  - intro x.
    unfold rvpower, rvabs, rvmin, const.
    apply Rle_power_l; try lra.
    split.
    + apply Rabs_pos.
    + rewrite Rabs_right.
      apply Rmin_r.
      specialize (nneg x).
      apply Rmin_case; try lra.
      apply Rle_ge, pos_INR.
 - apply IsFiniteExpectation_const.
Qed.

Lemma conditional_expectation_L2fun_proper (f1 f2 : Ts -> R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
  almostR2 prts eq f1 f2 ->
  LpRRV_eq prts
           (conditional_expectation_L2fun f1 sub)
           (conditional_expectation_L2fun f2 sub).
Proof.
  intros eqq.
  unfold conditional_expectation_L2fun, proj1_sig.
  repeat match_destr.
  destruct a as [xrv [xeq [? [? [xuniq ?]]]]].
  rename x0 into y.
  destruct a0 as [yrv [yeq [? [? [yuniq ?]]]]].
  apply yuniq; trivial.
  rewrite (LpRRV_norm_proper prts _ (LpRRVminus prts (pack_LpRRV prts f2) x)) in xeq.
  - unfold nneg2, bignneg, nonneg in *.
    rewrite xeq.
    f_equal.
    apply Glb_Rbar_eqset.
    split; intros [w [wrv wnorm]].
    + subst.
      exists w.
      split; trivial.
      apply LpRRV_norm_proper.
      apply LpRRV_minus_proper; trivial.
      reflexivity.
    + subst.
      exists w.
      split; trivial.
      apply LpRRV_norm_proper.
      apply LpRRV_minus_proper; trivial.
      * now symmetry.
      * reflexivity.
  - apply LpRRV_minus_proper; trivial.
    reflexivity.
Qed.

Lemma conditional_expectation_L2fun_nonneg (f : Ts -> R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        {nneg: NonnegativeFunction f} :
  almostR2 (prob_space_sa_sub _ sub) Rle (const 0) (conditional_expectation_L2fun f sub).
Proof.
  generalize (conditional_expectation_L2fun_eq3 sub f); intros.
  unfold is_conditional_expectation in H.
  apply Expectation_mult_indicator_almost_nonneg; [typeclasses eauto|].
  intros.
  destruct P.
  specialize (H x dec s).
  rewrite Expectation_prob_space_sa_sub.
  - simpl.
    rewrite <- H.
    erewrite Expectation_pos_pofrf.
    generalize (NonnegExpectation_pos (rvmult f (EventIndicator dec))); intros.
    match_case; intros.
    + simpl in H0.
      now rewrite H1 in H0.
    + simpl in H0.
      now rewrite H1 in H0.
  - apply rvmult_rv.
    + apply conditional_expectation_L2fun_rv.
    + now apply EventIndicator_pre_rv.
  Qed.
  
Lemma conditional_expectation_L2fun_nonneg_prts (f : Ts -> R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        {nneg: NonnegativeFunction f} :
  almostR2 prts Rle (const 0) (conditional_expectation_L2fun f sub).
Proof.
  apply almostR2_prob_space_sa_sub_lift with (sub0 := sub).
  now apply conditional_expectation_L2fun_nonneg.
Qed.

    Lemma almostR2_le_split x y :
      almostR2 prts Rle x y ->
      exists x', almostR2 prts eq x x' /\
            rv_le x' y.
    Proof.
      intros [p [pone ph]].
      generalize (fun ts => sa_dec p ts).
      exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then x ts else y ts).
      split.
      - exists p.
        split; trivial; intros.
        now match_destr.
      - intros ?.
        match_destr.
        + auto.
        + reflexivity.
    Qed.

    Lemma almostR2_le_split_r x y :
      almostR2 prts Rle x y ->
      exists y', almostR2 prts eq y y' /\
            rv_le x y'.
    Proof.
      intros [p [pone ph]].
      generalize (fun ts => sa_dec p ts).
      exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then y ts else x ts).
      split.
      - exists p.
        split; trivial; intros.
        now match_destr.
      - intros ?.
        match_destr.
        + auto.
        + reflexivity.
    Qed.

    Local Existing Instance Rbar_le_pre.
    
    Lemma almostR2_Rbar_le_split x y :
      almostR2 prts Rbar_le x y ->
      exists x', almostR2 prts eq x x' /\
            Rbar_rv_le x' y.
    Proof.
      intros [p [pone ph]].
      generalize (fun ts => sa_dec p ts).
      exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then x ts else y ts).
      split.
      - exists p.
        split; trivial; intros.
        now match_destr.
      - intros ?.
        match_destr.
        + auto.
        + reflexivity.
    Qed.

    Lemma almostR2_Rbar_le_split_r x y :
      almostR2 prts Rbar_le x y ->
      exists y', almostR2 prts eq y y' /\
            Rbar_rv_le x y'.
    Proof.
      intros [p [pone ph]].
      generalize (fun ts => sa_dec p ts).
      exists (fun ts => if ClassicalDescription.excluded_middle_informative (p ts) then y ts else x ts).
      split.
      - exists p.
        split; trivial; intros.
        now match_destr.
      - intros ?.
        match_destr.
        + auto.
        + reflexivity.
    Qed.

    Lemma conditional_expectation_L2fun_plus f1 f2
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv1 : RandomVariable dom borel_sa f1}
          {rv2 : RandomVariable dom borel_sa f2}
          {isl1 : IsLp prts 2 f1}
          {isl2 : IsLp prts 2 f2} :
      LpRRV_eq prts
               (conditional_expectation_L2fun (rvplus f1 f2) sub)
               (LpRRVplus prts (conditional_expectation_L2fun f1 sub) (conditional_expectation_L2fun f2 sub)).
    Proof.
      symmetry.
    apply (conditional_expectation_L2fun_unique2)
    ; try typeclasses eauto.
    intros.
    replace (pack_LpRRV prts (rvplus f1 f2)) with
        (LpRRVplus prts (pack_LpRRV prts f1) (pack_LpRRV prts f2)) by reflexivity.
    repeat rewrite L2RRV_inner_plus.
    f_equal
    ; now apply conditional_expectation_L2fun_eq2.
  Qed.
    
 End cond_exp.
 Section cond_exp2.      

Context {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom).

Lemma conditional_expectation_L2fun_le (f1 f2 : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
  rv_le f1 f2 ->
  almostR2 (prob_space_sa_sub _ dom2 sub) Rle (conditional_expectation_L2fun prts f1 sub) 
           (conditional_expectation_L2fun prts f2 sub).
Proof.
  intros.
  generalize (conditional_expectation_L2fun_eq3 prts sub f1); intro eqq1.
  generalize (conditional_expectation_L2fun_eq3 prts sub f2); intros eqq2.
  assert (isfe1:IsFiniteExpectation prts f1) by (apply (IsLp_Finite prts 2); trivial; lra).
  assert (isfe2:IsFiniteExpectation prts f2) by (apply (IsLp_Finite prts 2); trivial; lra).
  generalize (is_conditional_expectation_isfe prts sub f2 (conditional_expectation_L2fun prts f2 sub) eqq2 isfe2); intros isce2.  
  apply Expectation_mult_indicator_almost_le;
    [apply conditional_expectation_L2fun_rv |   
     apply conditional_expectation_L2fun_rv | | ].
  apply IsFiniteExpectation_prob_space_sa_sub_f; trivial.
  apply conditional_expectation_L2fun_rv.
  intros.
  destruct P.
  specialize (eqq1 x dec s).
  specialize (eqq2 x dec s).
  assert (RandomVariable 
            dom2 borel_sa
            (rvmult (conditional_expectation_L2fun prts f1 sub) (EventIndicator dec))).
  {
    apply rvmult_rv.
    - apply conditional_expectation_L2fun_rv.
    - apply EventIndicator_pre_rv.
      simpl.
      apply s.
  }
  assert (RandomVariable dom2 borel_sa
   (rvmult (conditional_expectation_L2fun prts f2 sub) (EventIndicator dec))).
  {
    apply rvmult_rv.
    - apply conditional_expectation_L2fun_rv.
    - apply EventIndicator_pre_rv.
      simpl.
      apply s.
  }
  rewrite Expectation_prob_space_sa_sub; trivial.
  simpl; rewrite <- eqq1.
  match_case; intros.
  - rewrite Expectation_prob_space_sa_sub; trivial.
    simpl; rewrite <- eqq2.
    match_case; intros.
    + apply Expectation_le with (rv_X1 := (rvmult f1 (EventIndicator dec)))
                                (rv_X2 := (rvmult f2 (EventIndicator dec))); trivial.
      {
        intro z.
        rv_unfold.
        match_destr.
        - now do 2 rewrite Rmult_1_r.
        - lra.
      }
    + generalize (IsFiniteExpectation_indicator prts f2 dec)
      ; intros HH.
      cut_to HH; trivial.
      * red in HH.
        simpl in HH.
        now rewrite H3 in HH.
      * simpl.
        now apply sub.
  - + generalize (IsFiniteExpectation_indicator prts f1 dec)
      ; intros HH.
      cut_to HH; trivial.
      * red in HH.
        simpl in HH.
        now rewrite H2 in HH.
      * simpl.
        now apply sub.
Qed.

Lemma conditional_expectation_L2fun_le_prts (f1 f2 : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {isl1 : IsLp prts 2 f1}
        {isl2 : IsLp prts 2 f2} :
  rv_le f1 f2 ->
  almostR2 prts Rle (conditional_expectation_L2fun prts f1 sub) 
           (conditional_expectation_L2fun prts f2 sub).
Proof.
  intros.
  apply almostR2_prob_space_sa_sub_lift with (sub0 := sub).
  now apply conditional_expectation_L2fun_le.
Qed.

Existing Instance IsLp_min_const_nat.

Definition NonNegConditionalExpectation (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} : Ts -> Rbar :=
  Rbar_rvlim (fun n => conditional_expectation_L2fun prts (rvmin f (const (INR n))) sub).

(* if f has finite exp, we can discard the infinite points *)
Definition FiniteNonNegConditionalExpectation (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {isfe : IsFiniteExpectation prts f}
           {nnf : NonnegativeFunction f} : Ts -> R :=
  rvlim (fun n => conditional_expectation_L2fun prts (rvmin f (const (INR n))) sub).

Lemma NonNegCondexp_almost_increasing (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} :
  almost (prob_space_sa_sub prts _ sub)
         (fun x => 
                 forall n,
                   conditional_expectation_L2fun prts (rvmin f (const (INR n))) sub x
                   <= conditional_expectation_L2fun prts (rvmin f (const (INR (S n)))) sub x).
  Proof.
    assert (forall n,
               almostR2 (prob_space_sa_sub prts _ sub) Rle
                        (conditional_expectation_L2fun prts (rvmin f (const (INR n))) sub)
                        (conditional_expectation_L2fun prts (rvmin f (const (INR (S n)))) sub)).
    {
      intros.
      apply conditional_expectation_L2fun_le.
      intro x.
      rv_unfold.
      apply Rle_min_compat_l.
      apply le_INR.
      lia.
    }
    apply choice in H.
    destruct H as [c ?].
    exists (inter_of_collection c).
    split.
    - apply ps_one_countable_inter; intros n.
      now destruct (H n).
    - intros x icx n.
      destruct (H n) as [? HH].
      apply (HH x (icx n)).
  Qed.

Lemma NonNegCondexp_almost_rv (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} :
  exists (E: event dom2),
    ps_P (ProbSpace:=(prob_space_sa_sub prts _ sub)) E = 1 /\
    (RandomVariable (event_restricted_sigma E) Rbar_borel_sa
                    (event_restricted_function E
                                               (NonNegConditionalExpectation f sub))).
Proof.
  destruct (NonNegCondexp_almost_increasing f sub)
    as [E [Eone EH]].
  exists E.
  split; trivial.
  unfold NonNegConditionalExpectation.
Admitted.

Instance NonNegCondexp_rv (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} :
  RandomVariable dom2 Rbar_borel_sa (NonNegConditionalExpectation prts f sub).
Proof.
  apply Rbar_rvlim_rv.
Admitted.
(*
  - intros.
    typeclasses eauto.
  - intros.
    apply ex_lim_seq_incr.
    intros.
    Locate RandomVariable.


    apply conditional_expectation_L2fun_le.
    apply almostR2_le_subr.
    intro x.
    unfold rvmin, const.
    apply Rle_min_compat_l.
    apply le_INR.
    lia.
  Qed.
*)

Lemma NonNegCondexp_is_Rbar_condexp  (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} : 
  is_Rbar_conditional_expectation prts sub f (NonNegConditionalExpectation prts f sub).
Proof.
  unfold is_Rbar_conditional_expectation, NonNegConditionalExpectation.
  intros.
    Admitted.

Lemma NonNegCond_almost_finite (f : Ts -> R)
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} :
  IsFiniteExpectation prts f ->
  almost prts (fun x => is_finite ((NonNegConditionalExpectation prts f sub) x)).
Proof.
  assert (RandomVariable dom Rbar_borel_sa (NonNegConditionalExpectation prts f sub)).
  {
    apply RandomVariable_sa_sub with (dom3 := dom2); trivial.
    typeclasses eauto.
  }
  assert (Rbar_NonnegativeFunction (NonNegConditionalExpectation prts f sub)) by admit.
  generalize (finite_Rbar_NonnegExpectation_almost_finite 
                prts
                (NonNegConditionalExpectation prts f sub) H H0); intros.
  apply H1.
  generalize (NonNegCondexp_is_Rbar_condexp f sub); intros.
  unfold is_Rbar_conditional_expectation in H3.
  specialize (H3 _ (dsa_dec dsa_Ω)).
  assert (Expectation (rvmult f (EventIndicator (dsa_dec dsa_Ω))) = Expectation f).
  {
    intros.
    apply Expectation_proper.
    rv_unfold; intros ?; simpl.
    lra.
  }
  assert (forall (f : Ts -> Rbar), Rbar_Expectation (Rbar_rvmult f (EventIndicator (dsa_dec dsa_Ω))) = Rbar_Expectation f).
  {
    intros.
    apply Rbar_Expectation_proper.
    intro x.
    rv_unfold; unfold Rbar_rvmult; simpl.
    now rewrite Rbar_mult_1_r.
  }
  rewrite H4 in H3.
  rewrite H5 in H3.
  cut_to H3; [| apply sa_all].
  rewrite Expectation_pos_pofrf with (nnf0 := nnf) in H3.
  rewrite Rbar_Expectation_pos_pofrf with (nnf0 := H0) in H3.
  inversion H3.
  unfold IsFiniteExpectation in H2.
  rewrite Expectation_pos_pofrf with (nnf0 := nnf) in H2.
  match_destr_in H2; now simpl.

  Admitted.
           

Lemma FiniteNonNegCondexp_almost_eq (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {isfe : IsFiniteExpectation prts f}
           {nnf : NonnegativeFunction f} : 
  almostR2 prts eq (NonNegConditionalExpectation prts f sub) (FiniteNonNegConditionalExpectation prts f sub).
Proof.
  destruct (NonNegCond_almost_finite f sub isfe) as [? [? ?]].
  exists x.
  split; trivial.
  intros.
  specialize (H0 x0 H1).
  unfold NonNegConditionalExpectation, Rbar_rvlim in *.
  unfold FiniteNonNegConditionalExpectation, rvlim.
  now rewrite H0.
Qed.

Definition ConditionalExpectation (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f} : Ts -> Rbar :=
  Rbar_rvminus (NonNegConditionalExpectation prts (pos_fun_part f) sub)
               (NonNegConditionalExpectation prts (neg_fun_part f) sub).

Definition FiniteConditionalExpectation (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {isfep : IsFiniteExpectation prts (pos_fun_part f)}
           {isfen : IsFiniteExpectation prts (neg_fun_part f)}           
           {rv : RandomVariable dom borel_sa f} : Ts -> R :=
  rvminus (FiniteNonNegConditionalExpectation prts (pos_fun_part f) sub) 
          (FiniteNonNegConditionalExpectation prts (neg_fun_part f) sub).

Lemma Rbar_rvlim_almost_proper (f1 f2:nat->Ts->R) :
      (forall n, almostR2 prts eq (f1 n) (f2 n)) ->
      almostR2 prts eq (Rbar_rvlim f1) (Rbar_rvlim f2).
Proof.
  intros eqq.
  unfold Rbar_rvlim.
  destruct (choice _ eqq) as [coll collp].
  exists (inter_of_collection coll).
  split.
  - apply ps_one_countable_inter.
    intros n.
    now destruct (collp n).
  - intros x px.
    apply Lim_seq_ext; intros n.
    destruct (collp n) as [? eqq2].
    rewrite eqq2; trivial.
    apply px.
Qed.

Global Instance rvmin_almost_proper : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvmin.
Proof.
  intros ?? [p1[? eqq1]] ?? [p2[? eqq2]].
  exists (event_inter p1 p2).
  split.
  - rewrite ps_inter_l1; trivial.
  - intros ? [??].
    unfold rvmin.
    rewrite eqq1, eqq2; trivial.
Qed.

Global Instance Rbar_rvplus_almost_proper : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) Rbar_rvplus.
Proof.
  intros ?? [p1[? eqq1]] ?? [p2[? eqq2]].
  exists (event_inter p1 p2).
  split.
  - rewrite ps_inter_l1; trivial.
  - intros ? [??].
    unfold Rbar_rvplus.
    rewrite eqq1, eqq2; trivial.
Qed.

Global Instance Rbar_rvopp_almost_proper : Proper (almostR2 prts eq ==> almostR2 prts eq) Rbar_rvopp.
Proof.
  intros ?? [p1[? eqq1]].
  exists p1.
  split; trivial.
  - intros ??.
    unfold Rbar_rvopp.
    rewrite eqq1; trivial.
Qed.

Lemma NonNegConditionalExpectation_proper (f1 f2 : Ts -> R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2}
        {nnf1 : NonnegativeFunction f1} 
        {nnf2 : NonnegativeFunction f2} :
  almostR2 prts eq f1 f2 ->
  almostR2 prts eq
           (NonNegConditionalExpectation prts f1 sub)
           (NonNegConditionalExpectation prts f2 sub).
Proof.
  
  intros eqq.
  unfold NonNegConditionalExpectation.
  apply Rbar_rvlim_almost_proper; intros n.
  apply conditional_expectation_L2fun_proper.
  apply rvmin_almost_proper; trivial.
  reflexivity.
Qed.

Lemma ConditionalExpectation_proper (f1 f2 : Ts -> R) 
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv1 : RandomVariable dom borel_sa f1}
        {rv2 : RandomVariable dom borel_sa f2} :
  almostR2 prts eq f1 f2 ->
  almostR2 prts eq
           (ConditionalExpectation f1 sub)
           (ConditionalExpectation f2 sub).
Proof.
  intros eqq.
  unfold ConditionalExpectation.
  apply Rbar_rvplus_almost_proper.
  - apply NonNegConditionalExpectation_proper.
    now apply pos_fun_part_proper_almostR2.
  - apply Rbar_rvopp_almost_proper.
    apply NonNegConditionalExpectation_proper.
    now apply neg_fun_part_proper_almostR2.
Qed.
  

End cond_exp2.

Section cond_exp_props.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Existing Instance RandomVariable_sa_sub.
  Existing Instance conditional_expectation_L2fun_rv.

  (* prove ext theorems for the conditional expectations stuff) *)

Let nneg2 : nonnegreal := bignneg 2 big2.
Canonical nneg2.

  Lemma LpRRVnorm_const {p} c : p <> 0 -> LpRRVnorm (p:=p) prts (LpRRVconst prts c) = Rabs c.
  Proof.
    intros.
    unfold LpRRVnorm; simpl.
    rv_unfold.
    generalize (FiniteExpectation_const prts (power (Rabs c) p))
    ; intros HH.
    unfold const in HH.
    erewrite FiniteExpectation_pf_irrel.
    rewrite HH.
    apply inv_power_cancel; trivial.
    apply Rabs_pos.
  Qed.
  
  Lemma LpRRVnorm0 {p} : p <> 0 -> LpRRVnorm (p:=p) prts (LpRRVzero prts) = 0.
  Proof.
    intros.
    unfold LpRRVzero.
    rewrite LpRRVnorm_const; trivial.
    now rewrite Rabs_R0.
  Qed.
  
  Lemma conditional_expectation_L2fun_rv_eq f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {rv2 : RandomVariable dom2 borel_sa f}
        {isl : IsLp prts 2 f} :
    LpRRV_eq prts
             (conditional_expectation_L2fun prts f sub)
             (pack_LpRRV prts f).
  Proof.
    unfold conditional_expectation_L2fun, proj1_sig.
    match_destr.
    destruct a as [xrv [xeq xuniq]].
    match type of xeq with
    |  _ = (real ?x) => replace x with (Finite 0) in xeq
    end.
    - apply LpRRV_norm0 in xeq.
      apply LpRRValmost_sub_zero_eq in xeq.
      symmetry.
      apply xeq.
    - symmetry.
      unfold Glb_Rbar, proj1_sig.
      match_destr.
      destruct i as [lb glb].
      unfold is_lb_Rbar in *.
      apply Rbar_le_antisym.
      + apply lb.
        exists (pack_LpRRV prts f (rv:=RandomVariable_sa_sub _ sub f)).
        split; trivial.
        LpRRV_simpl.
        rewrite (LpRRV_norm_proper prts _ (LpRRVzero prts)).
        * rewrite LpRRVnorm0; trivial.
        * apply LpRRV_seq_eq.
          unfold LpRRV_seq; simpl.
          rewrite rvminus_self.
          reflexivity.
      + apply glb; intros y [w [rvw eqw]].
        subst.
        unfold LpRRVnorm; simpl.
        apply power_nonneg.
  Qed.

  Lemma is_lim_seq_min (x : R) :
    is_lim_seq (fun n : nat => Rmin x (INR n)) x.
  Proof.
    apply is_lim_seq_spec.
    unfold is_lim_seq'.
    intros.
    exists (Z.to_nat (up x)).
    intros.
    rewrite Rmin_left.
    - rewrite Rminus_eq_0.
      rewrite Rabs_R0.
      apply cond_pos.
    - destruct (archimed x).
      destruct (Rge_dec x 0).
      + rewrite <- INR_up_pos in H0; trivial.
        apply Rge_le.
        left.
        apply Rge_gt_trans with (r2 := INR (Z.to_nat (up x))); trivial.
        apply Rle_ge.
        now apply le_INR.
      + generalize (pos_INR n); intros.
        lra.
  Qed.

  Lemma Lim_seq_min (x : R) :
    Lim_seq (fun n => Rmin x (INR n)) = x.
  Proof.
    generalize (is_lim_seq_min x); intros.
    now apply is_lim_seq_unique in H.
  Qed.

  Lemma rvlim_rvmin (f : Ts -> R) :
    rv_eq (Rbar_rvlim (fun n => rvmin f (const (INR n)))) f.
  Proof.
    intro x.
    unfold Rbar_rvlim, rvmin, const.
    now rewrite Lim_seq_min.
  Qed.
          
  Lemma NonNegConditionalExpectation_rv_eq f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {rv2 : RandomVariable dom2 borel_sa f}
        {nnf : NonnegativeFunction f} :
    almostR2 prts eq
             (NonNegConditionalExpectation prts f sub)
             f.
  Proof.
    unfold NonNegConditionalExpectation.
    transitivity (Rbar_rvlim (fun n => (rvmin f (const (INR n))))).
    - apply Rbar_rvlim_almost_proper; intros n.
      apply conditional_expectation_L2fun_rv_eq.
      typeclasses eauto.
    - apply almostR2_eq_subr.
      apply rvlim_rvmin.
  Qed.

  Corollary NonNegConditionalExpectation_const c pf
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) :
    almostR2 prts eq
             (NonNegConditionalExpectation prts (const c) sub (nnf:=pf))
             (const c).
  Proof.
    apply NonNegConditionalExpectation_rv_eq.
    apply rvconst.
  Qed.

  (* If f is dom2-measurable, then its conditional expectation with
     respect to dom2 is almost itself *)
  Theorem ConditionalExpectation_rv_eq f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {rv2 : RandomVariable dom2 borel_sa f} :
    almostR2 prts eq
             (ConditionalExpectation prts f sub)
             f.
  Proof.
    unfold ConditionalExpectation, Rbar_rvminus.
    rewrite (NonNegConditionalExpectation_rv_eq (fun x : Ts => pos_fun_part f x))
      by typeclasses eauto.
    rewrite (NonNegConditionalExpectation_rv_eq (fun x : Ts => neg_fun_part f x))
      by typeclasses eauto.
    apply almostR2_eq_subr.
    unfold Rbar_rvplus.
    intros a.
    generalize (rv_pos_neg_id f a).
    unfold rvplus, rvopp, rvscale; simpl.
    intros eqq.
    f_equal.
    etransitivity; try (symmetry; eapply eqq).
    lra.
  Qed.

  Corollary ConditionalExpectation_const c
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom) :
    almostR2 prts eq
             (ConditionalExpectation prts (const c) sub)
             (const c).
  Proof.
    apply ConditionalExpectation_rv_eq.
    apply rvconst.
  Qed.


  Lemma conditional_expectation_L2fun_scale f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f}
        c :
    LpRRV_eq prts
             (conditional_expectation_L2fun prts (rvscale c f) sub)
             (LpRRVscale prts c (conditional_expectation_L2fun prts f sub)).
  Proof.
    symmetry.
    apply (conditional_expectation_L2fun_unique2)
    ; try typeclasses eauto.
    intros.
    transitivity (L2RRVinner prts (LpRRVscale prts c (pack_LpRRV prts f)) w); try reflexivity.
    repeat rewrite L2RRV_inner_scal.
    f_equal.
    now apply conditional_expectation_L2fun_eq2.
  Qed.

  Lemma conditional_expectation_L2fun_opp f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    LpRRV_eq prts
             (conditional_expectation_L2fun prts (rvopp f) sub)
             (LpRRVopp prts (conditional_expectation_L2fun prts f sub)).
  Proof.
    etransitivity.
    - etransitivity; [| apply (conditional_expectation_L2fun_scale f sub (-1))].
      now apply conditional_expectation_L2fun_proper.
    - apply almostR2_eq_subr; intros ?; simpl.
      reflexivity.
  Qed.

  Lemma conditional_expectation_L2fun_Expectation f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} :
    Expectation (conditional_expectation_L2fun prts f sub) = Expectation f.
  Proof.
    generalize (conditional_expectation_L2fun_eq2 prts f sub (LpRRVconst prts 1)); intros HH.
    cut_to HH; try typeclasses eauto.
    unfold L2RRVinner in HH.
    unfold LpRRVconst in HH; simpl in HH.
    rewrite (FiniteExpectation_ext prts
               (rvmult (conditional_expectation_L2fun prts f sub) (const 1))
               (conditional_expectation_L2fun prts f sub)
            ) in HH by (intros ?; rv_unfold; lra).
    rewrite (FiniteExpectation_ext prts
              (rvmult f (const 1))
               f
            ) in HH by (intros ?; rv_unfold; lra).
    unfold FiniteExpectation, proj1_sig in HH.
    repeat match_destr_in HH; congruence.
  Qed.
  
  Existing Instance IsLp_min_const_nat.

(*
  Instance NonNegCondexp_rv (f : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rvf : RandomVariable dom borel_sa f} 
        {nnf : NonnegativeFunction f} :
    RandomVariable dom2 borel_sa (NonNegConditionalExpectation prts f sub).
  Proof.
    Admitted.
 *)
  
  Lemma NonNegCondexp_prop (f g : Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {nnf : NonnegativeFunction f}
        {nng : NonnegativeFunction g}         
        {rvf : RandomVariable dom borel_sa f}
        {rvg : RandomVariable dom2 borel_sa g} :
          almostR2 prts eq g
                   (NonNegConditionalExpectation prts f sub)
          <->
          forall (E : dec_sa_event),
            Expectation (rvmult (EventIndicator (dsa_dec E)) g) =
            Expectation (rvmult (EventIndicator (dsa_dec E)) f).
    Proof.
      Admitted.
            
                   
    

  Lemma NonNegCondexp_l2fun_lim_incr (f : nat -> Ts -> R)
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : forall n, RandomVariable dom borel_sa (f n)}
        {limrv : RandomVariable dom borel_sa (Rbar_rvlim f)}        
        {nnf : forall n, NonnegativeFunction (f n)} 
        {islp : forall n, IsLp prts 2 (f n)} :
    (forall n, rv_le (f n) (f (S n))) ->
    almostR2 prts eq
             (NonNegConditionalExpectation prts (Rbar_rvlim f) sub)
             (Rbar_rvlim (fun n =>
                            (conditional_expectation_L2fun prts (f n) sub))).
  Proof.
    intros.
    Admitted.
  
  Lemma Lim_seq_min_n_scale (fx c : R) :
    Lim_seq (fun n : nat => Rmin (c * fx) (INR n)) = 
    Lim_seq (fun n : nat => c * Rmin (fx) (INR n)).
  Proof.
    rewrite Lim_seq_min.
    rewrite Lim_seq_scal_l.
    rewrite Lim_seq_min.
    now simpl.
  Qed.

  Lemma rvmin_INR_le (f : Ts -> R) :
    forall (n:nat),
      rv_le (rvmin f (const (INR n))) (rvmin f (const (INR (S n)))).
  Proof.
    intros n x.
    unfold rvmin, const.
    apply Rle_min_compat_l.
    apply le_INR.
    lia.
  Qed.

  Instance NonNeg_rvmin (f g : Ts -> R)
           {nnf: NonnegativeFunction f}
           {nng: NonnegativeFunction g} :
    NonnegativeFunction (rvmin f g).
  Proof.
    unfold NonnegativeFunction in *.
    unfold rvmin.
    intros.
    now apply Rmin_glb.
  Qed.

  Instance NonNeg_INR (n : nat) :
    @NonnegativeFunction Ts (const (INR n)).
  Proof.
    unfold NonnegativeFunction.
    intro.
    apply pos_INR.
  Qed.

  Lemma NonNegConditionalExpectation_scale f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {nnf : NonnegativeFunction f}
        (c:posreal) :
      almostR2 prts eq
               (NonNegConditionalExpectation prts (rvscale c f) sub)
             (fun omega => Rbar_mult c (NonNegConditionalExpectation prts f sub omega)).
    Proof.
      unfold NonNegConditionalExpectation.
      transitivity (Rbar_rvlim (fun n : nat => rvscale c (conditional_expectation_L2fun prts (rvmin f (const (INR n))) sub))).
      - transitivity
          (Rbar_rvlim (fun n : nat => (conditional_expectation_L2fun prts (rvscale c (rvmin f (const (INR n)))) sub))).
        + assert (RandomVariable dom borel_sa
            (fun x : Ts =>
               Rbar_rvlim (fun n : nat => rvmin (rvscale c f) 
                                                (const (INR n))) x)).
            {
              apply RandomVariable_proper with (x := rvscale c f); [|typeclasses eauto].
              intro x.
              unfold Rbar_rvlim, rvmin.
              now rewrite Lim_seq_min.
            }  
          generalize (NonNegCondexp_l2fun_lim_incr (fun n => rvmin (rvscale c f) (const (INR n))) sub); intros.
          assert (RandomVariable dom borel_sa
            (fun x : Ts =>
               Rbar_rvlim (fun n : nat => rvscale c (rvmin f (const (INR n)))) x)).
          {
            apply RandomVariable_proper with (x := rvscale c f); [|typeclasses eauto].            
            intro x.
            unfold Rbar_rvlim, rvmin, rvscale.
            rewrite Lim_seq_scal_l.
            rewrite Lim_seq_min.
            now simpl.
          }
          generalize (NonNegCondexp_l2fun_lim_incr (fun n => rvscale c (rvmin f (const (INR n)))) sub); intros.
          cut_to H0; [| intros; apply  rvmin_INR_le].
          cut_to H2; [| intros; apply rv_scale_le_proper, rvmin_INR_le].
          rewrite <- H0.
          rewrite <- H2.
          apply NonNegConditionalExpectation_proper.
          apply almostR2_eq_subr.
          intro x.
          unfold Rbar_rvlim.
          unfold rvmin, rvscale, const.
          now rewrite Lim_seq_min_n_scale.
        + apply Rbar_rvlim_almost_proper; intros n.
          apply (conditional_expectation_L2fun_scale (rvmin f (const (INR n))) sub c).
      - apply almostR2_eq_subr.
        intros ?.
        unfold Rbar_rvlim.
        unfold rvscale.
        now rewrite Lim_seq_scal_l; simpl.
    Qed.

    Lemma pos_fun_part_scale_pos_eq c f : 0 < c ->

                                                   rv_eq (fun x => nonneg (pos_fun_part (rvscale c f) x)) (rvscale c (fun x : Ts => pos_fun_part f x)).
    Proof.
      intros ??.
      unfold rvscale; simpl.
      now rewrite (scale_Rmax0 (mkposreal c H)); simpl.
    Qed.

    Lemma neg_fun_part_scale_pos_eq c f : 0 < c ->
                                               rv_eq (fun x => nonneg (neg_fun_part (rvscale c f) x)) (rvscale c (fun x : Ts => neg_fun_part f x)).
    Proof.
      intros ??.
      unfold rvscale; simpl.
      rewrite Ropp_mult_distr_r.
      now rewrite (scale_Rmax0 (mkposreal c H)); simpl.
    Qed.

    Lemma pos_fun_part_scale_neg_eq c f : 0 < c ->

                                                   rv_eq (fun x => nonneg (pos_fun_part (rvscale (- c) f) x)) (rvscale c (fun x : Ts => neg_fun_part f x)).
    Proof.
      intros ??.
      unfold rvscale; simpl.
      rewrite <- (scale_Rmax0 (mkposreal c H)); simpl.
      f_equal; lra.
    Qed.

    Lemma neg_fun_part_scale_neg_eq c f : 0 < c ->
                                               rv_eq (fun x => nonneg (neg_fun_part (rvscale (- c) f) x)) (rvscale c (fun x : Ts => pos_fun_part f x)).
    Proof.
      intros ??.
      unfold rvscale; simpl.
      rewrite Ropp_mult_distr_r.
      rewrite <- (scale_Rmax0 (mkposreal c H)); simpl.
      f_equal; lra.
    Qed.

    Lemma Rbar_mult_r_plus_distr (c:R) x y:
      Rbar_mult c (Rbar_plus x y) =
      Rbar_plus (Rbar_mult c x) (Rbar_mult c y).
    Proof.
      destruct x; destruct y; simpl;
        try
          solve [
            f_equal; lra
          |
          destruct (Rle_dec 0 c); trivial
          ; destruct (Rle_lt_or_eq_dec 0 c r0); simpl; trivial
          ; subst
          ; f_equal; lra
          |
          destruct (Rle_dec 0 c); trivial
          ; simpl; try (f_equal; lra)
          ; destruct (Rle_lt_or_eq_dec 0 c r); simpl; trivial
          ; f_equal; lra
          ].
    Qed.

  Theorem ConditionalExpectation_scale f
        {dom2 : SigmaAlgebra Ts}
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        c :
      almostR2 prts eq
               (ConditionalExpectation prts (rvscale c f) sub)
             (fun omega => Rbar_mult c (ConditionalExpectation prts f sub omega)).
  Proof.
    destruct (Rtotal_order c 0) as [?|[?|?]].
    - unfold ConditionalExpectation, Rbar_rvminus.
      assert (cpos:0 < - c) by lra.
      pose (cc:=mkposreal _ cpos).
      rewrite (NonNegConditionalExpectation_proper prts (fun x : Ts => pos_fun_part (rvscale c f) x) (rvscale cc (neg_fun_part f)))
              , (NonNegConditionalExpectation_proper prts (fun x : Ts => neg_fun_part (rvscale c f) x) (rvscale cc (pos_fun_part f))).
      + repeat rewrite NonNegConditionalExpectation_scale.
        simpl.
        apply almostR2_eq_subr; intros ?.
        unfold Rbar_rvplus, Rbar_rvopp.
        replace (Finite (- c)) with (Rbar_opp (Finite c)) by reflexivity.
        
        rewrite <- Rbar_mult_opp_l.
        rewrite Rbar_opp_involutive.
        rewrite Rbar_mult_opp_l.
        rewrite <- Rbar_mult_opp_r.
        rewrite <- Rbar_mult_r_plus_distr.
        now rewrite Rbar_plus_comm.
      + apply almostR2_eq_subr.
        rewrite <- neg_fun_part_scale_neg_eq.
        * simpl.
          now rewrite Ropp_involutive.
        * unfold cc; simpl; lra.
      + apply almostR2_eq_subr.
        rewrite <- pos_fun_part_scale_neg_eq.
        * simpl.
          now rewrite Ropp_involutive.
        * unfold cc; simpl; lra.
    - subst.
      unfold rvscale.
      rewrite (ConditionalExpectation_proper prts _ (const 0))
      ; [| apply almostR2_eq_subr; intros ?; unfold const; lra].
      rewrite ConditionalExpectation_const.
      apply almostR2_eq_subr; intros ?.
      rewrite Rbar_mult_0_l.
      reflexivity.
    - unfold ConditionalExpectation, Rbar_rvminus.
      pose (cc:=mkposreal c H).
      rewrite (NonNegConditionalExpectation_proper prts (fun x : Ts => pos_fun_part (rvscale c f) x) (rvscale cc (pos_fun_part f)))
              , (NonNegConditionalExpectation_proper prts (fun x : Ts => neg_fun_part (rvscale c f) x) (rvscale cc (neg_fun_part f))).
      + repeat rewrite NonNegConditionalExpectation_scale.
        simpl.
        apply almostR2_eq_subr; intros ?.
        unfold Rbar_rvplus, Rbar_rvopp.
        rewrite <- Rbar_mult_opp_r.
        now rewrite Rbar_mult_r_plus_distr.
      + apply almostR2_eq_subr.
        apply neg_fun_part_scale_pos_eq.
        unfold cc; simpl; lra.
      + apply almostR2_eq_subr.
        apply pos_fun_part_scale_pos_eq.
        unfold cc; simpl; lra.
  Qed.

  Lemma Rbar_rvlim_plus_min (f1 f2 : Ts -> R) :
      rv_eq
        (Rbar_rvlim
           (fun n : nat =>
              rvplus (rvmin f1 (const (INR n))) 
                     (rvmin f2 (const (INR n)))))
        (Rbar_rvlim
           (fun n : nat =>
              rvmin (rvplus f1 f2) (const (INR n)))). 
    Proof.
      intro x.
      unfold Rbar_rvlim, rvmin, rvplus, const.
      rewrite Lim_seq_plus.
      - do 3 rewrite Lim_seq_min.
        now simpl.
      - apply ex_lim_seq_incr.
        intros.
        apply Rle_min_compat_l.
        apply le_INR.
        lia.
      - apply ex_lim_seq_incr.
        intros.
        apply Rle_min_compat_l.
        apply le_INR.
        lia.
      - do 2 rewrite Lim_seq_min.
        now simpl.
    Qed.
    
    Lemma ConditionalExpectation_nonneg f
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv : RandomVariable dom borel_sa f}
          {nnf : NonnegativeFunction f}
      :
        almostR2 prts eq (ConditionalExpectation prts f sub)
                 (NonNegConditionalExpectation prts f sub).
    Proof.
      unfold ConditionalExpectation.
      transitivity ((Rbar_rvplus (NonNegConditionalExpectation prts (fun x : Ts => pos_fun_part f x) sub)
                                 (Rbar_rvopp (const 0)))).
      - apply Rbar_rvplus_almost_proper; try reflexivity.
        apply Rbar_rvopp_almost_proper.
        transitivity (NonNegConditionalExpectation prts (const 0) sub (nnf:=fun _ => z_le_z)).
        + apply NonNegConditionalExpectation_proper.
          apply almostR2_eq_subr.
          rewrite <- neg_fun_part_pos; trivial.
          reflexivity.
        + apply NonNegConditionalExpectation_const.
      - transitivity (NonNegConditionalExpectation prts (fun x : Ts => pos_fun_part f x) sub).
        + apply almostR2_eq_subr; intros ?.
          unfold Rbar_rvplus, Rbar_rvopp, const; simpl.
          rewrite Ropp_0.
          apply Rbar_plus_0_r.
        + apply NonNegConditionalExpectation_proper.
          apply almostR2_eq_subr; intros ?.
          rewrite <- pos_fun_part_pos; trivial.
    Qed.

    Lemma NonNegConditionalExpectation_L2 f
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv : RandomVariable dom borel_sa f}
          {nnf : NonnegativeFunction f}
          {isl : IsLp prts 2 f}
      :
        almostR2 prts eq (NonNegConditionalExpectation prts f sub)
                 (LpRRV_rv_X prts (conditional_expectation_L2fun prts f sub)).
    Proof.
      assert (eqq:rv_eq (fun x : Ts => Rbar_rvlim (fun _ : nat => f) x) f).
      {
        intros ?.
        unfold Rbar_rvlim.
        apply Lim_seq_const.
      }
      assert (eqq2:(rv_eq (Rbar_rvlim (fun n : nat => conditional_expectation_L2fun prts f sub)) (fun a => conditional_expectation_L2fun prts f sub a))).
      {
        intros ?.
        unfold Rbar_rvlim; simpl.
        apply Lim_seq_const.
      }
      assert (limrv : RandomVariable dom borel_sa (fun x : Ts => Rbar_rvlim (fun _ : nat => f) x)).
      {
        eapply RandomVariable_proper.
        - intros ?.
          rewrite eqq.
          reflexivity.
        - trivial.
      } 
      generalize (NonNegCondexp_l2fun_lim_incr (fun _ => f) sub (fun _ => reflexivity _))
      ; intros HH.

      transitivity (NonNegConditionalExpectation prts (fun x : Ts => Rbar_rvlim (fun _ : nat => f) x) sub).
      - apply NonNegConditionalExpectation_proper.
        apply almostR2_eq_subr.
        intros ?.
        rewrite eqq.
        reflexivity.
      - rewrite HH.
        now apply almostR2_eq_subr.
    Qed.

    Global Instance pos_fun_part_islp (p:nonnegreal) f :
      IsLp prts p f ->
      IsLp prts p (pos_fun_part f).
    Proof.
      intros islp.
      eapply IsLp_bounded; try eapply islp.
      intros ?.
      rv_unfold; simpl.
      apply Rle_power_l.
      - apply cond_nonneg.
      - split.
        + apply Rabs_pos.
        + unfold Rmax.
          match_destr.
          * rewrite Rabs_R0.
            apply Rabs_pos.
          * reflexivity.
    Qed.

    Global Instance neg_fun_part_islp (p:nonnegreal) f :
      IsLp prts p f ->
      IsLp prts p (neg_fun_part f).
    Proof.
      intros islp.
      assert (islp2:IsLp prts p (rvopp f)) by now apply IsLp_opp.
      generalize (pos_fun_part_islp p (rvopp f) islp2).
      apply IsLp_proper; trivial.
      unfold rvopp; intros a.
      generalize (pos_fun_part_scale_neg_eq 1 f).
      replace (- (1)) with (-1) by lra.
      intros HH.
      rewrite HH by lra.
      unfold rvscale.
      lra.
    Qed.

    Lemma almostR2_Finite (x y:Ts->R) :
      almostR2 prts eq (fun a => (Finite (x a))) (fun a => (Finite (y a))) <->
      almostR2 prts eq x y.
    Proof.
      split
      ; intros [p[pone peqq]]
      ; exists p; split; trivial
      ; intros a pa
      ; specialize (peqq a pa).
      - now invcs peqq.
      - now rewrite peqq.
    Qed.

    Lemma ConditionalExpectation_L2 f
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv : RandomVariable dom borel_sa f}
          {isl : IsLp prts 2 f}
      :
        almostR2 prts eq (ConditionalExpectation prts f sub)
                 (LpRRV_rv_X prts (conditional_expectation_L2fun prts f sub)).
    Proof.
      unfold ConditionalExpectation.
      unfold Rbar_rvminus.
      repeat rewrite NonNegConditionalExpectation_L2.
      assert (islp2:IsLp prts 2 (rvplus (fun x : Ts => pos_fun_part f x) (rvopp (fun x : Ts => neg_fun_part f x)))).
      {
        eapply IsLp_proper; try (symmetry; eapply rv_pos_neg_id); eauto.
      }
      generalize (conditional_expectation_L2fun_plus prts (fun x : Ts => pos_fun_part f x) (rvopp (fun x : Ts => neg_fun_part f x)) sub)
      ; intros HH.
      simpl in HH.
      apply almostR2_Finite.
      transitivity ( (fun x : Ts => conditional_expectation_L2fun prts
                                                               (rvplus (fun x : Ts => pos_fun_part f x) (rvopp (fun x : Ts => neg_fun_part f x))) sub x)).
      - red in HH.
        simpl in *.
        symmetry.
        etransitivity.
        + etransitivity; [| eapply HH].
          now apply conditional_expectation_L2fun_proper.
        + apply almostR2_eq_plus_proper; try reflexivity.
          etransitivity; [apply conditional_expectation_L2fun_opp |].
          simpl.
          apply almostR2_eq_subr; intros ?.
          unfold rvopp, rvscale.
          field_simplify.
          reflexivity.
      - apply conditional_expectation_L2fun_proper.
        apply almostR2_eq_subr.
        now rewrite <- rv_pos_neg_id.
    Qed.
    
    Lemma NonNegConditionalExpectation_le
          f1 f2
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv1 : RandomVariable dom borel_sa f1}
          {rv2 : RandomVariable dom borel_sa f2}
          {nnf1 : NonnegativeFunction f1}
          {nnf2 : NonnegativeFunction f2} :
      almostR2 prts Rle f1 f2 ->
      almostR2 prts Rbar_le (NonNegConditionalExpectation prts f1 sub) (NonNegConditionalExpectation prts f2 sub).
    Proof.
    Admitted.
    
    Theorem ConditionalExpectation_le
          f1 f2
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv1 : RandomVariable dom borel_sa f1}
          {rv2 : RandomVariable dom borel_sa f2} :
          almostR2 prts Rle f1 f2 ->
          almostR2 prts Rbar_le (ConditionalExpectation prts f1 sub) (ConditionalExpectation prts f2 sub).
    Proof.
    Admitted.

    Local Existing Instance Rbar_le_pre.
    Lemma NonNegConditionalExpectation_nonneg f
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv : RandomVariable dom borel_sa f}
          {nnf : NonnegativeFunction f}
      : almostR2 prts Rbar_le (const 0) (NonNegConditionalExpectation prts f sub).
    Proof.
      generalize (NonNegConditionalExpectation_le (const 0) f sub (nnf1:=fun _ => z_le_z))
      ; intros HH.
      cut_to HH.
      - rewrite <- HH.
        generalize (NonNegConditionalExpectation_const 0 (fun _ => z_le_z) sub)
        ; intros HH2.
        apply (almostR2_subrelation prts (R_subr:=eq_subrelation _)).
        now symmetry.
      - apply almostR2_le_subr.
        apply nnf.
    Qed.

    Instance rvmin_le_proper : Proper (rv_le ==> rv_le ==> rv_le) (@rvmin Ts).
    Proof.
      unfold rv_le, rvmin, pointwise_relation.
      intros ???????.
      unfold Rmin.
      repeat match_destr.
      - etransitivity; eauto.
      - etransitivity; try eapply H.
        lra.
    Qed.

    Instance const_le_proper : Proper (Rle ==> rv_le) (const (B:=Ts)).
    Proof.
      intros ????.
      now unfold const.
    Qed.

    Global Instance rvplus_le_proper : Proper (rv_le ==> rv_le ==> rv_le) (rvplus (Ts:=Ts)).
    Proof.
      unfold rv_le, rvplus, pointwise_relation.
      intros ???????.
      apply Rplus_le_compat; auto.
    Qed.


    Lemma NonNegConditionalExpectation_plus f1 f2
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv1 : RandomVariable dom borel_sa f1}
          {rv2 : RandomVariable dom borel_sa f2}
          {nnf1 : NonnegativeFunction f1}
          {nnf2 : NonnegativeFunction f2} :
      almostR2 prts eq
               (NonNegConditionalExpectation prts (rvplus f1 f2) sub)
               (Rbar_rvplus (NonNegConditionalExpectation prts f1 sub) (NonNegConditionalExpectation prts f2 sub)).
    Proof.
      generalize (Rbar_rvlim_plus_min f1 f2); intros plus_min.
      assert (RandomVariable dom borel_sa
            (fun x : Ts =>
             Rbar_rvlim
               (fun n : nat =>
                  rvplus (rvmin f1 (const (INR n))) (rvmin f2 (const (INR n)))) x)).
      {
        apply Rbar_real_rv.
        eapply RandomVariable_proper.
        apply plus_min.
        generalize (rvlim_rvmin (rvplus f1 f2)); intros.
        eapply RandomVariable_proper.
        apply H.
        typeclasses eauto.
      }
      assert (RandomVariable 
                dom borel_sa
                (Rbar_rvlim (fun n : nat => rvmin (rvplus f1 f2) (const (INR n))))).
      {
        generalize (rvlim_rvmin (rvplus f1 f2)); intros.
        apply Rbar_real_rv.
        eapply RandomVariable_proper.
        apply H0.
        typeclasses eauto.
      }
      generalize (NonNegCondexp_l2fun_lim_incr
                    (fun n => rvplus (rvmin f1 (const (INR n)))
                                     (rvmin f2 (const (INR n)))) sub); intros.
      cut_to H1.
      - assert 
          (almostR2 prts eq 
             (NonNegConditionalExpectation 
                prts
                (Rbar_rvlim
                   (fun n : nat =>
                      rvplus (rvmin f1 (const (INR n))) 
                             (rvmin f2 (const (INR n)))))
                sub)
             (NonNegConditionalExpectation prts (rvplus f1 f2) sub)).
        {
          apply NonNegConditionalExpectation_proper.
          etransitivity.
          - apply almostR2_eq_subr; intros ?.
            rewrite plus_min.
            reflexivity.
          - apply almostR2_eq_subr.
            intros ?; simpl.
            now rewrite rvlim_rvmin.
        }
        rewrite <- H2.
        rewrite H1.
        unfold NonNegConditionalExpectation.
        assert (
               almostR2 prts eq
                        (Rbar_rvlim
                           (fun n : nat =>
                              conditional_expectation_L2fun 
                                prts
                                (rvplus (rvmin f1 (const (INR n))) 
                                        (rvmin f2 (const (INR n)))) sub))
                        (Rbar_rvlim
                           (fun n =>
                              (rvplus
                                 (conditional_expectation_L2fun 
                                    prts (rvmin f1 (const (INR n))) sub)
                                 (conditional_expectation_L2fun 
                                    prts (rvmin f2 (const (INR n))) sub))))).
           {
             
             unfold Rbar_rvlim.
             apply Rbar_rvlim_almost_proper; intros.
             generalize (conditional_expectation_L2fun_plus prts
                           (rvmin f1 (const (INR n)))
                           (rvmin f2 (const (INR n))) sub); intros HH.
             unfold LpRRV_eq in HH.
             etransitivity; [| apply HH].
             now apply conditional_expectation_L2fun_proper.
           }
           rewrite H3.
           unfold Rbar_rvlim.
           apply almostR2_eq_subr; intros ?; simpl.
    Admitted.
    (*
           apply Lim_seq_plus.
        + apply ex_lim_seq_incr; intros n.
           generalize (conditional_expectation_L2fun_le (rvmin f1 (const (INR n))) (rvmin f1 (const (INR (S n)))))
          ; intros HH.

          rewrite le_INR; try reflexivity.
          lia.
        +

     *)

    (*
          apply ex_lim_seq_incr; intros.
          apply conditional_expectation_L2fun_le.
          rewrite le_INR; try reflexivity.
          lia.
        + generalize (NonNegConditionalExpectation_nonneg f1 sub)
          ; intros HH1.
          generalize (NonNegConditionalExpectation_nonneg f2 sub)
          ; intros HH2.
          unfold NonNegConditionalExpectation, Rbar_rvlim in HH1, HH2.
          apply ex_Rbar_plus_pos.
          * 
          * apply HH2.
      - intros.
        apply rvplus_le_proper
        ; apply rvmin_le_proper; try reflexivity
        ; apply const_le_proper
        ; apply le_INR
        ; lia.
    Qed.
*)

    Theorem ConditionalExpectation_plus f1 f2
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {rv1 : RandomVariable dom borel_sa f1}
          {rv2 : RandomVariable dom borel_sa f2} :
      almostR2 prts eq
               (ConditionalExpectation prts (rvplus f1 f2) sub)
               (Rbar_rvplus (ConditionalExpectation prts f1 sub) (ConditionalExpectation prts f2 sub)).
    Proof.
    Admitted.
    
End cond_exp_props.
    

