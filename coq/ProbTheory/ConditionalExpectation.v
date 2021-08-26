Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice.

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

Instance RandomVariable_sa_sub (dom2 : SigmaAlgebra Ts)
         (sub : sa_sub dom2 dom)
         x
         {rv_x:RandomVariable dom2 borel_sa x}
  : RandomVariable dom borel_sa x.
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

Lemma is_lim_seq_filter_ball_center f x 
  (pf :ProperFilter (LpRRV_filter_from_seq f)) 
  (cF : cauchy (LpRRV_filter_from_seq f)) :
  is_lim_seq (fun n : nat => LpRRV_dist (f n) x) 0 ->
  (forall (n:nat),  proj1_sig (LpRRV_lim_ball_center prts big2 (LpRRV_filter_from_seq f) pf cF n) x).
  Proof.
    intros.
    pose (F := (LpRRV_filter_from_seq f)).
    unfold cauchy, LpRRV_filter_from_seq in cF.
    unfold LpRRV_lim_ball_center.
    unfold proj1_sig.
    match_case; intros.
    simpl in H0.
    match_case_in H0; intros.
    destruct H1.
    match_destr_in H0.
    invcs H0.
    unfold LpRRV_filter_from_seq in l0.
    

(*
Lemma is_lim_seq_filter_lim f x:
  ProperFilter (LpRRV_filter_from_seq f) ->
  cauchy (LpRRV_filter_from_seq f) ->
  is_lim_seq (fun n : nat => LpRRV_dist (f n) x) 0 ->
  forall eps : posreal, LpRRV_dist (LpRRV_lim prts big2 (LpRRV_filter_from_seq f)) x < eps.
Proof.
  intros pf cF isl eps.
  generalize (ball_LpRRV_lim_picker prts big2 (LpRRV_filter_from_seq f) pf cF eps)
  ; intros[N HH].

  generalize (lim_picker_included prts big2 (LpRRV_filter_from_seq f) pf cF); intros.
  generalize (lim_ball_center_dist prts big2 (LpRRV_lim_picker prts big2 (LpRRV_filter_from_seq f) pf cF n) x); intros.
  
  
  admit.
  
  assert (exists N2, forall n : nat,
             (n >= N2)%nat ->
             LpRRV_dist (LpRRV_lim_picker prts big2 (LpRRV_filter_from_seq f) pf cF (S n)) x < eps/2).
  {
    clear HH.
    unfold LpRRV_dist.
    unfold LpRRV_filter_from_seq.
    unfold LpRRV_lim_picker.
    generalize (lim_picker_included prts big2 (LpRRV_filter_from_seq f) p c); intros.


     Lemma lim_ball_center_dist (x y : LpRRV prts p)
             (F : (LpRRV_UniformSpace prts pbig -> Prop) -> Prop)
             (PF:ProperFilter F)
             (cF:cauchy F)
             (N:nat) :
    unfold LpRRV_lim_ball_center_center in H0.
    admit.
  }
  
 *)

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
  assert (bounded (fun n => LpRRVnorm prts (f n))).
  {
    destruct (is_lim_seq_bounded _ _ H0).
    unfold bounded.
    exists (LpRRVnorm prts x0 + x).
    intros.
    specialize (H1 n).
    generalize (LpRRV_norm_plus prts big2 x0 (LpRRVminus prts (p := bignneg 2 big2) (f n) x0)); intros.
    rewrite Rabs_pos_eq by apply power_nonneg.
    rewrite Rabs_pos_eq in H1 by apply power_nonneg.
    rewrite LpRRV_plus_comm, LpRRVminus_plus in H2.
    rewrite <- LpRRV_plus_assoc in H2.
    rewrite (LpRRV_plus_comm prts (p := bignneg 2 big2) _ x0) in H2.
    rewrite LpRRV_plus_inv, LpRRV_plus_zero in H2.
    eapply Rle_trans.
    apply H2.
    apply Rplus_le_compat_l.
    now rewrite <- LpRRVminus_plus.
  }
  assert (forall (eps:posreal), 
             exists (N:nat), 
               forall (n m : nat), 
                 (n>=N)%nat -> (m >= N)%nat -> LpRRV_dist (f n) (f m) < eps).
  {
    intros.
    apply is_lim_seq_spec in H0.
    assert (0 < eps) by apply cond_pos.
    assert (0 < eps/2) by lra.
    destruct (H0 (mkposreal _ H3)).
    exists x; intros.
    generalize (LpRRV_dist_triang (f n) x0 (f m)); intros.
    generalize (H4 n H5); intros.
    generalize (H4 m H6); intros.
    rewrite Rminus_0_r in H8.
    rewrite Rabs_pos_eq in H8 by apply power_nonneg.
    rewrite Rminus_0_r in H9.
    rewrite Rabs_pos_eq in H9 by apply power_nonneg.
    unfold LpRRV_dist in H7.
    eapply Rle_lt_trans.
    apply H7.
    rewrite LpRRV_dist_comm in H9.
    unfold LpRRV_dist in H8; unfold LpRRV_dist in H9.
    simpl in H8; simpl in H9; simpl; lra.
  }
  pose (prts2 := prob_space_sa_sub dom2 sub).
  

  generalize (L2RRV_lim_complete prts2 big2); intros HH.

  generalize (L2RRV_lim_complete prts big2); intros.
  pose (F :=  LpRRV_filter_from_seq f).
  pose (dom2pred := fun v => RandomVariable dom2 borel_sa v).
  pose (F2 := subset_filter F dom2pred ).

  pose (F3:=subset_filter_to_sa_sub_filter _ sub F2).

  generalize (HH F3); intros HH1.
  
  specialize (H3 F).
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
  assert (cauchy F).
  {
    unfold cauchy.
    intros.
    destruct (H2 eps).
    unfold Hierarchy.ball; simpl.
    unfold LpRRVball.
    exists (f x).
    unfold F.
    unfold LpRRV_filter_from_seq.
    exists x.
    intros.
    apply H5; lia.
  }

  assert (pfsub:ProperFilter (subset_filter F (fun v : LpRRV prts 2 => dom2pred v))).
  {
    apply subset_filter_proper; intros.
    subst F.
    subst f.
    unfold LpRRV_filter_from_seq in H6.
    destruct H6 as [? HH2].
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
    specialize (H6 n H7).
    rewrite Rminus_0_r in H6.
    now rewrite Rabs_pos_eq in H6 by apply power_nonneg.
  }
    
  assert (forall (eps:posreal),
             (LpRRV_dist (LpRRV_lim prts big2 F) x0) < eps).
  {
    intros.
    unfold F.
    unfold LpRRV_filter_from_seq.
    specialize (H3 H4 H5).
    unfold LpRRV_dist.
    generalize (ball_LpRRV_lim_picker prts big2 F H4 H5 eps); intros.
    destruct (H6 eps).
    destruct H7.
    unfold Hierarchy.ball in H7; simpl in H7.
    unfold LpRRVball, LpRRV_lim_picker in H7.
    specialize (H7 (max x x1)).
    cut_to H7; try lia.
    unfold proj1_sig in H7.
    match_destr_in H7.

(*
    
    simpl in y.

    destruct y as [? [? ?]].
    
    unfold LpRRV_lim_ball_cumulative in y.

    simpl in H7.
*)    
    
    
    admit.
  }
  assert (F3limball:forall (eps:posreal),
             (LpRRV_dist (prob_space_sa_sub_LpRRV_lift dom2 sub (LpRRV_lim prts2 big2 F3)) x0) < eps).
  {
    intros.
    admit.
  }
  apply F3limball.

Admitted.


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

Lemma rvlim_rvmin (f : Ts -> R) :
  rv_eq (Rbar_rvlim (fun n => rvmin f (const (INR n)))) f.
Proof.
  intro x.
  unfold Rbar_rvlim, rvmin, const.
  generalize (is_lim_seq_min (f x)); intros.
  now apply is_lim_seq_unique in H.
Qed.

(*



almostR2 prts eq (Rbar_rvlim (fun n : nat => rvmin f (const (INR n)))) (fun x : Ts => f x)
  (prob_space_sa_sub_LpRRV_lift dom2 sub (LpRRV_lim prts2 big2 F3)) x0).
  unfold LpRRVball in H6.
  generalize 
  
  assert (forall n, 

  unfold F3, F2, F.
  unfold LpRRV_filter_from_seq.
  
  
  
  


  assert (almostR2 prts eq 
                   (prob_space_sa_sub_LpRRV_lift dom2 sub (LpRRV_lim prts2 big2 F3))
                   (LpRRV_lim prts big2 F)).
  {
    admit.
  }
  assert (almostR2 prts eq (LpRRV_lim prts big2 F) x0 ).
  {
    generalize (cauchy_filterlim_almost_unique_alt F H4 (LpRRV_lim prts big2 F) x0); intros.
    unfold F.
    unfold LpRRV_filter_from_seq.
    admit.
  }
  LpRRVq_simpl.
  unfold LpRRV_eq.
  eapply transitivity.
  apply H6.
  apply H7.
  Admitted.
*)
  
(*
  


  generalize (cauchy_filterlim_almost_unique_alt F H4 (LpRRV_lim prts big2 F) x0); intros.
  cut_to H6.
  admit.
  - intros.
    exists (LpRRV_lim prts big2 F).
    split.
    + apply H3.
    + apply LpRRV_ball_refl.
  - intros.
    exists (LpRRV_lim prts big2 F).
    split.
    + apply H3.
    + unfold LpRRVball, LpRRV_lim.
      match_destr.
      * match_destr.
        -- unfold LpRRV_lim_with_conditions.
           unfold cauchy_rvlim_fun.
           unfold pack_LpRRV.
*)  

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
        (forall z: LpRRV prts 2, RandomVariable dom2 borel_sa z ->
              (LpRRVnorm prts (LpRRVminus prts f z) =
              Glb_Rbar (fun r : R => exists w : LpRRV prts 2,
                            RandomVariable dom2 borel_sa (LpRRV_rv_X prts w) /\
                            r = LpRRVnorm prts (LpRRVminus prts f w))) -> LpRRV_eq prts z v)

     }.
Proof.
  destruct ((conditional_expectation_L2q dom2 sub (Quot _ f))).
  destruct u as [[HH1 HH2] HH3].
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
  split.
  - now f_equal.
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
  destruct a as [?[? HH]].
  now apply HH.
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
  destruct a as [xrv [xeq xuniq]].
  rename x0 into y.
  destruct a0 as [yrv [yeq yuniq]].
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

  Definition Rbar_rvopp (rv_X : Ts -> Rbar) :=
    (fun omega =>  Rbar_opp (rv_X omega)).
  
Definition NonNegConditionalExpectation (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nnf : NonnegativeFunction f} : Ts -> Rbar :=
  Rbar_rvlim (fun n => conditional_expectation_L2fun (rvmin f (const (INR n))) sub).

Definition ConditionalExpectation (f : Ts -> R) 
           {dom2 : SigmaAlgebra Ts}
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f} : Ts -> Rbar :=
  Rbar_rvplus (NonNegConditionalExpectation (pos_fun_part f) sub)
              (Rbar_rvopp (NonNegConditionalExpectation (neg_fun_part f) sub)).

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
           (NonNegConditionalExpectation f1 sub)
           (NonNegConditionalExpectation f2 sub).
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
  

End cond_exp.

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

  Lemma rvlim_rvmin (f : Ts -> R) :
    rv_eq (Rbar_rvlim (fun n => rvmin f (const (INR n)))) f.
  Proof.
    intro x.
    unfold Rbar_rvlim, rvmin, const.
    generalize (is_lim_seq_min (f x)); intros.
    now apply is_lim_seq_unique in H.
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
    unfold ConditionalExpectation.
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




End cond_exp_props.
    
