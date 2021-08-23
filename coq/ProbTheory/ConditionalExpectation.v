Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical.
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

Program Definition ortho_projection_hilbert (E:PreHilbert) 
           (phi: E -> Prop) (phi_mod: compatible_m phi) (phi_compl: complete_subset phi)
           (u : E) : E.
  generalize (ortho_projection_subspace phi phi_mod phi_compl u);intros.
  cut_to H.
  apply constructive_definite_description in H.
  exact (proj1_sig H).
  intro; apply classic.
Qed.

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
  assert (IsLp prts 2 (rvlim f)).
(*  {
    eapply islp_rvlim_bounded; eauto.
    - lra.
    - admit.
    - 
  }    
*)
  admit.
  assert (RandomVariable dom borel_sa (rvlim f)).
  admit.
  assert (RandomVariable dom2 borel_sa (rvlim f)).
  admit.
  assert (Quot (LpRRV_eq prts) (pack_LpRRV prts (rvlim f)) = Quot (LpRRV_eq prts) x0).
  admit.
  now exists (pack_LpRRV prts (rvlim f)).
  
Admitted.

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
  split.
  - admit.
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
      
      
(*
    unfold Hierarchy.ball; simpl.
    unfold ball.


  
  generalize (L2RRV_lim_complete (prob_space_sa_sub dom2 sub) big2); intros HH.
  simpl in *.
  
  specialize  (HH (fun s:(LpRRV (prob_space_sa_sub dom2 sub) 2 -> Prop)=>
                 (LpRRVq_filter_to_LpRRV_filter prts F) (prob_space_sa_sub_set_lift dom2 sub s)
              )).
  cut_to HH.
  - simpl in HH.
    split.
    + admit.
    + intros.
      specialize (HH eps).
      assert (eqq:Quot _ (prob_space_sa_sub_LpRRV_lift _ sub ((LpRRV_lim (prob_space_sa_sub dom2 sub) big2
                  (fun s : LpRRV (prob_space_sa_sub dom2 sub) 2 -> Prop =>
                     LpRRVq_filter_to_LpRRV_filter prts F (prob_space_sa_sub_set_lift dom2 sub s))))) =
              (LpRRVq_lim prts big2 F)).
      {
        admit.
      }
      rewrite <- eqq.
      eapply filter_imp; try eapply HH; intros a HHa.
      clear HH.
      destruct (Quot_inv a); subst.
      unfold Hierarchy.ball, UniformSpace.ball in *.
      simpl in *.
      unfold ball in *.
      rewrite L2RRVq_norm_norm .
      unfold minus, plus, opp; simpl.
      autorewrite with quot.
      rewrite LpRRVq_normE.
      

      

      
      unfold LpRRV_toLpRRVq_set in HHa.
      specialize (HHa _ (eq_refl _)).
      

      
      destruct x; simpl in *.
      match_destr_in HHa; try tauto.
      

      * 
      unfold prob_space_sa_sub_set_lift in HHa.
      
      
      (prob_space_sa_sub_set_lift dom2 sub
                                  (LpRRVball (prob_space_sa_sub dom2 sub) big2
                                             q eps)) =
      (prob_space_sa_sub_LpRRV_lift dom2 sub
                                             
                                             



      
      unfold LpRRV_toLpRRVq_set in HHa.
      
      unfold LpRRVball in HHa.
      simpl in HHa.

      unfold LpRRVq_filter_to_LpRRV_filter in HH.



      unfold ball, Hnorm, inner, minus, plus, opp; simpl.
      
      
      
      unfold LpRRV_toLpRRVq_set in HH.

      
      unfold LpRRVq_filter_to_LpRRV_filter in HH.
      
      unfold LpRRVq_lim.
      repeat match_destr.
      * unfold LpRRVq_lim_with_conditions2.
        rewrite LpRRVq_lim_with_conditionsE.
        unfold Hierarchy.ball in *; simpl in *.
        rewrite LpRRVq_ballE.
        unfold ball, Hnorm.

      
      assert (rv_eq (LpRRV_lim (prob_space_sa_sub dom2 sub) big2
                  (fun s : LpRRV (prob_space_sa_sub dom2 sub) 2 -> Prop =>
                   LpRRVq_filter_to_LpRRV_filter prts F (prob_space_sa_sub_set_lift dom2 sub s)))
      
    unfold LpRRVq_filter_to_LpRRV_filter, prob_space_sa_sub_set_lift in HH.
    unfold LpRRV_toLpRRVq_set in HH.
    simpl in HH.


    
(*

      generalize (L2RRV_lim_complete (LpRRVq_filter_to_LpRRV_filter F)); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_proper F H); intros.
    generalize (LpRRVq_filter_to_LpRRV_filter_cauchy F H H0); intros.

  
  

  
  

  
  pose (FF := (fun s:(LpRRVq prts 2 -> Prop) => F s /\ forall x, s x -> ortho_phi dom2 x)).
  
  generalize (L2RRV_lim_complete prts big2); intros HH2.

  split.
  - admit.
  - specialize (HH2 F PF cF).
  

  
  
  unfold ortho_phi in *.
*)
*)
  Admitted.


Definition conditional_expectation_L2q
           (dom2 : SigmaAlgebra Ts)
           (sub : sa_sub dom2 dom)
           (x:LpRRVq prts 2)
  : LpRRVq prts 2.
Proof.
  refine (ortho_projection_hilbert (L2RRVq_PreHilbert prts)
                                  (ortho_phi dom2) _ _ x).
  - split; [split | ]; intros.
    + destruct H as [a [eqqa rv_a]]; subst.
      destruct H0 as [b [eqqb rv_b]]; subst.
      unfold plus, opp; simpl.
      rewrite LpRRVq_oppE, LpRRVq_plusE.
      eexists.
      split.
      * reflexivity.
      * typeclasses eauto.
    + exists (LpRRVq_zero prts).
      exists (LpRRVzero prts).
      simpl.
      split.
      * reflexivity.
      * typeclasses eauto.
    + destruct H as [a [eqqa Ha]]; subst.
      exists (LpRRVscale prts l a).
      simpl.
      split.
      * unfold scal; simpl.
        rewrite LpRRVq_scaleE.
        reflexivity.
      * typeclasses eauto.
  - now apply ortho_phi_complete.
Qed.

Program Definition conditional_expectation_L2fun (f : Ts -> R) 
        (dom2 : SigmaAlgebra Ts)
        (sub : sa_sub dom2 dom)
        {rv : RandomVariable dom borel_sa f}
        {isl : IsLp prts 2 f} : LpRRV prts 2 :=
  _ (Quot_inv (conditional_expectation_L2q dom2 sub (Quot _ (pack_LpRRV prts f)))).
Next Obligation.
  apply constructive_indefinite_description in x.
  exact (proj1_sig x).
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

Definition NonNegConditionalExpectation (f : Ts -> R) 
           (dom2 : SigmaAlgebra Ts)
           (sub : sa_sub dom2 dom)
           {rv : RandomVariable dom borel_sa f}
           {nneg : NonnegativeFunction f} : Ts -> Rbar :=
  Rbar_rvlim (fun n => conditional_expectation_L2fun (rvmin f (const (INR n))) dom2 sub).

Definition ConditionalExpectation (f : Ts -> R) 
           (dom2 : SigmaAlgebra Ts)
           (sub : sa_sub dom2 dom)
           (rv : RandomVariable dom borel_sa f) :=
  Rbar_rvplus (NonNegConditionalExpectation (pos_fun_part f) dom2 sub)
              (fun x => Rbar_opp (NonNegConditionalExpectation (neg_fun_part f) dom2 sub x)).

End cond_exp.
