Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra Lia.
Require Import Classical ClassicalChoice RelationClasses.

Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Import ConditionalExpectation.
Require Import VectorRandomVariable.
Require Import RbarExpectation.

Require Import Event.
Require Import Almost.
Require Import utils.Utils.
Require Import List.
Require Import DVector.

Set Bullet Behavior "Strict Subproofs". 

Section vec_cond_exp.

    Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

    Definition vector_FiniteConditionalExpectation {n}
             (f : Ts -> vector R n)
             {rv : RandomVariable dom (Rvector_borel_sa n) f}
             {isfe:vector_IsFiniteExpectation prts f} : Ts -> vector R n
    := iso_b (vector_map (fun x => FiniteConditionalExpectation prts sub
                                                             (proj1_sig x)
                                                             (isfe:=proj1 (proj2_sig x))
                                                             (rv:=proj2 (proj2_sig x))
                         )
                         (vector_dep_zip _ (Forall_and isfe (vector_RandomVariable f)))).

    Lemma vector_FiniteConditionalExpectation_ext {n} (f1 f2 : Ts -> vector R n)
          {rv1 : RandomVariable dom (Rvector_borel_sa n) f1}
          {rv2 : RandomVariable dom (Rvector_borel_sa n) f2}
          {isfe1:vector_IsFiniteExpectation prts f1}
          {isfe2:vector_IsFiniteExpectation prts f2}
      : rv_eq f1 f2 ->
        vector_FiniteConditionalExpectation f1 = vector_FiniteConditionalExpectation f2.
    Proof.
      (* classically true *)
      intros.
      assert (f1 = f2) by now apply functional_extensionality.
      subst.
      f_equal; apply proof_irrelevance.
    Qed.
        
    Lemma vector_FiniteConditionalExpectation_nth' {n}
             (f : Ts -> vector R n)
             {rv : RandomVariable dom (Rvector_borel_sa n) f}
             {isfe:vector_IsFiniteExpectation prts f} i pf :
      rv_eq (vecrvnth i pf (vector_FiniteConditionalExpectation f))
            (FiniteConditionalExpectation prts sub (vecrvnth i pf f)).
    Proof.
      unfold vector_FiniteConditionalExpectation, vecrvnth; simpl; intros ?.
      rewrite vector_of_funs_vector_nth, vector_nth_map.
      apply FiniteConditionalExpectation_ext; intros ?.
      rewrite vector_dep_zip_nth_proj1.
      now rewrite vector_nth_fun_to_vector.
    Qed.

    Lemma vector_FiniteConditionalExpectation_nth {n}
             (f : Ts -> vector R n)
             {rv : RandomVariable dom (Rvector_borel_sa n) f}
             {isfe:vector_IsFiniteExpectation prts f} i pf a :
      vector_nth i pf (vector_FiniteConditionalExpectation f a) =
      FiniteConditionalExpectation prts sub (vecrvnth i pf f) a.
    Proof.
      apply vector_FiniteConditionalExpectation_nth'.
    Qed.

    Global Instance vector_FiniteCondexp_rv {n} (f : Ts -> vector R n) 
         {rv : RandomVariable dom (Rvector_borel_sa n) f}
         {isfe:vector_IsFiniteExpectation prts f} :
    RandomVariable dom2 (Rvector_borel_sa n) (vector_FiniteConditionalExpectation f).
  Proof.
    apply RandomVariable_vector.
    apply Forall_forall; intros.
    unfold vector_FiniteConditionalExpectation in H.
    rewrite iso_f_b in H.
    simpl in H.
    apply in_map_iff in H.
    destruct H as [?[??]]; subst.
    apply FiniteCondexp_rv.
  Qed.

  Theorem vector_FiniteCondexp_cond_exp {n} (f : Ts -> vector R n) 
        {rv : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe:vector_IsFiniteExpectation prts f}
        {P:pre_event Ts}
        (dec:dec_pre_event P)
        (saP:sa_sigma dom2 P) :
    vector_Expectation (vecrvmult f (fun x => (vector_const (EventIndicator dec x) n))) =
    vector_Expectation (vecrvmult (vector_FiniteConditionalExpectation f)
                                  (fun x => (vector_const (EventIndicator dec x) n))).
  Proof.
    unfold vector_Expectation.
    simpl iso_f.
    f_equal.
    apply vector_nth_eq; intros.
    repeat rewrite vector_nth_map.
    repeat rewrite vector_nth_fun_to_vector.
    transitivity (Expectation (rvmult (vecrvnth i pf f) (EventIndicator dec))).
    - apply Expectation_proper; intros ?.
      unfold vecrvmult.
      rewrite RealVectorHilbert.Rvector_nth_mult.
      now rewrite vector_nth_const.
    - rewrite (FiniteCondexp_cond_exp prts sub (vecrvnth i pf f) dec saP).
      apply Expectation_proper; intros ?.
      unfold vecrvmult.
      rewrite RealVectorHilbert.Rvector_nth_mult.
      rewrite vector_nth_const.
      rewrite vector_FiniteConditionalExpectation_nth.
      reflexivity.
  Qed.

  Corollary vector_FiniteCondexp_cond_exp_classic {n} (f : Ts -> vector R n) 
        {rv : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe:vector_IsFiniteExpectation prts f}
        {P:pre_event Ts}
        (saP:sa_sigma dom2 P) :
    vector_Expectation (vecrvmult f (fun x => (vector_const (EventIndicator (classic_dec P) x) n))) =
    vector_Expectation (vecrvmult (vector_FiniteConditionalExpectation f)
                                  (fun x => (vector_const (EventIndicator (classic_dec P) x) n))).
  Proof.
    now apply vector_FiniteCondexp_cond_exp.
  Qed.

  Corollary vector_FiniteCondexp_cond_exp_event {n} (f : Ts -> vector R n) 
        {rv : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe:vector_IsFiniteExpectation prts f}
        {P:event dom2}
        (dec:dec_event P) :
    vector_Expectation (vecrvmult f (fun x => (vector_const (EventIndicator dec x) n))) =
    vector_Expectation (vecrvmult (vector_FiniteConditionalExpectation f)
                                  (fun x => (vector_const (EventIndicator dec x) n))).
  Proof.
    apply vector_FiniteCondexp_cond_exp.
    destruct P; trivial.
  Qed.

  Corollary vector_FiniteCondexp_cond_exp_event_classic {n} (f : Ts -> vector R n) 
        {rv : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe:vector_IsFiniteExpectation prts f}
        (P:event dom2) :
    vector_Expectation (vecrvmult f (fun x => (vector_const (EventIndicator (classic_dec P) x) n))) =
    vector_Expectation (vecrvmult (vector_FiniteConditionalExpectation f)
                                  (fun x => (vector_const (EventIndicator (classic_dec P) x) n))).
  Proof.
    apply vector_FiniteCondexp_cond_exp_event.
  Qed.

  Global Instance vector_FiniteCondexp_nneg {n} (f : Ts -> vector R n) 
        {rv : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe:vector_IsFiniteExpectation prts f} :
        (forall i pf, NonnegativeFunction (fun x => vector_nth i pf (f x))) ->
        (forall i pf, NonnegativeFunction (fun x => vector_nth i pf (vector_FiniteConditionalExpectation f x))).
  Proof.
    intros ????.
    rewrite vector_FiniteConditionalExpectation_nth.
    apply FiniteCondexp_nneg.
    apply H.
  Qed.    

  Theorem vector_FiniteCondexp_id {n} (f : Ts -> vector R n)
          {rv : RandomVariable dom (Rvector_borel_sa n) f}
          {rv2 : RandomVariable dom2 (Rvector_borel_sa n) f}
          {isfe:vector_IsFiniteExpectation prts f}
    :
      rv_eq (vector_FiniteConditionalExpectation f) f.
  Proof.
    intros ?.
    apply vector_nth_eq; intros.
    rewrite vector_FiniteConditionalExpectation_nth.
    rewrite FiniteCondexp_id; trivial.
    now apply vecrvnth_rv.
  Qed.    
    
  Corollary vector_FiniteCondexp_const {n} c :
    rv_eq (vector_FiniteConditionalExpectation (n:=n) (const c)) (const c).
  Proof.
    unfold const.
    intros ?.
    apply vector_nth_eq; intros.
    rewrite vector_FiniteConditionalExpectation_nth.
    unfold vecrvnth.
    generalize (FiniteCondexp_const prts sub (vector_nth i pf c) a).
    unfold const.
    intros HH.
    rewrite <- HH.
    apply FiniteConditionalExpectation_ext; reflexivity.
  Qed.    

  Theorem vector_FiniteCondexp_Expectation {n} (f : Ts -> vector R n) 
          {rv : RandomVariable dom (Rvector_borel_sa n) f}
          {isfe:vector_IsFiniteExpectation prts f}
    :
      vector_Expectation (vector_FiniteConditionalExpectation f) =
      vector_Expectation f.
  Proof.
    unfold vector_Expectation.
    f_equal.
    apply vector_nth_eq; intros; simpl.
    repeat rewrite vector_nth_map.
    repeat rewrite vector_nth_fun_to_vector.
    transitivity (Expectation (FiniteConditionalExpectation prts sub (vecrvnth i pf f))).
    - apply Expectation_proper; intros ?.
      now rewrite vector_FiniteConditionalExpectation_nth.
    - apply FiniteCondexp_Expectation.
  Qed.

  Global Instance vector_FiniteCondexp_isfe {n} (f : Ts -> vector R n) 
          {rv : RandomVariable dom (Rvector_borel_sa n) f}
          {isfe:vector_IsFiniteExpectation prts f}
    : vector_IsFiniteExpectation prts (vector_FiniteConditionalExpectation f).
  Proof.
    unfold vector_IsFiniteExpectation.
    apply Forall_vector; intros; simpl.
    rewrite vector_nth_fun_to_vector.
    eapply IsFiniteExpectation_proper.
    - intros ?.
      rewrite vector_FiniteConditionalExpectation_nth.
      reflexivity.
    - apply FiniteCondexp_isfe.
  Qed.

  Corollary vector_FiniteCondexp_FiniteExpectation {n} (f : Ts -> vector R n) 
          {rv : RandomVariable dom (Rvector_borel_sa n) f}
          {isfe:vector_IsFiniteExpectation prts f}
    :
      vector_FiniteExpectation prts (vector_FiniteConditionalExpectation f) =
      vector_FiniteExpectation prts f.
  Proof.
    generalize (vector_FiniteCondexp_Expectation f).
    repeat rewrite (vector_FiniteExpectation_Expectation _ _).
    intros HH.
    invcs HH.
    apply (f_equal (fun x => map real x)) in H0.
    
    repeat rewrite map_map in H0.
    repeat rewrite map_id in H0.
    now apply vector_eq.
  Qed.

  Theorem vector_FiniteCondexp_proper {n} (f1 f2 : Ts -> vector R n) 
          {rv1 : RandomVariable dom (Rvector_borel_sa n) f1}
          {rv2 : RandomVariable dom (Rvector_borel_sa n) f2}
          {isfe1:vector_IsFiniteExpectation prts f1}
          {isfe2:vector_IsFiniteExpectation prts f2} :
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (vector_FiniteConditionalExpectation f1)
             (vector_FiniteConditionalExpectation f2).
  Proof.
    intros eqq1.
    apply vector_nth_eq_almost; intros.
    generalize (FiniteCondexp_proper prts sub (vecrvnth i pf f1) (vecrvnth i pf f2))
    ; intros HH.
    cut_to HH; [| now apply vector_nth_eq_almost].
    revert HH.
    apply almost_impl; apply all_almost; intros ??.
    now repeat rewrite vector_FiniteConditionalExpectation_nth'.
  Qed.
  
  Lemma vector_FiniteCondexp_ale {n} (f1 f2 : Ts -> vector R n) 
          {rv1 : RandomVariable dom (Rvector_borel_sa n) f1}
          {rv2 : RandomVariable dom (Rvector_borel_sa n) f2}
          {isfe1:vector_IsFiniteExpectation prts f1}
          {isfe2:vector_IsFiniteExpectation prts f2} :
    almostR2 prts (vectorize_relation Rle n) f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) (vectorize_relation Rle n)
             (vector_FiniteConditionalExpectation f1)
             (vector_FiniteConditionalExpectation f2).
  Proof.
    intros eqq1.
    apply vectorize_relation_almost; intros.
    generalize (FiniteCondexp_ale prts sub (vecrvnth i pf f1) (vecrvnth i pf f2))
    ; intros HH.
    cut_to HH; [| now apply vectorize_relation_almost].
    revert HH.
    apply almost_impl; apply all_almost; intros ??.
    now repeat rewrite vector_FiniteConditionalExpectation_nth'.
  Qed.

  Lemma vector_FiniteCondexp_scale {n} c (f : Ts -> vector R n) 
        {rv : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe:vector_IsFiniteExpectation prts f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (vector_FiniteConditionalExpectation (vecrvscale c f))
             (vecrvscale c (vector_FiniteConditionalExpectation f)).
  Proof.
    apply vector_nth_eq_almost; intros.
    eapply almost_impl.
    - apply all_almost; intros ??.
      rewrite vector_FiniteConditionalExpectation_nth'.
      transitivity (FiniteConditionalExpectation prts sub (rvscale c (vecrvnth i pf f)) x).
      + apply FiniteConditionalExpectation_ext.
        intros ?.
        unfold vecrvnth, vecrvscale, rvscale, RealVectorHilbert.Rvector_scale.
        rewrite vector_nth_map.
        reflexivity.
      + unfold vecrvnth, vecrvscale, rvscale, RealVectorHilbert.Rvector_scale.
        rewrite vector_nth_map.
        rewrite vector_FiniteConditionalExpectation_nth.
        apply H.
    - apply FiniteCondexp_scale.
  Qed.

  Lemma vector_FiniteCondexp_opp {n} (f : Ts -> vector R n) 
        {rv : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe:vector_IsFiniteExpectation prts f} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (vector_FiniteConditionalExpectation (vecrvopp f))
             (vecrvopp (vector_FiniteConditionalExpectation f)).
  Proof.
    apply vector_nth_eq_almost; intros.
    eapply almost_impl.
    - apply all_almost; intros ??.
      rewrite vector_FiniteConditionalExpectation_nth'.
      transitivity (FiniteConditionalExpectation prts sub (rvopp (vecrvnth i pf f)) x).
      + apply FiniteConditionalExpectation_ext.
        intros ?.
        unfold vecrvnth, vecrvopp, vecrvscale, RealVectorHilbert.Rvector_scale.
        rewrite vector_nth_map.
        reflexivity.
      + unfold vecrvnth, vecrvopp, vecrvscale, RealVectorHilbert.Rvector_scale.
        rewrite vector_nth_map.
        rewrite vector_FiniteConditionalExpectation_nth.
        apply H.
    - apply FiniteCondexp_opp.
  Qed.

  Lemma vector_FiniteCondexp_plus {n} (f1 f2 : Ts -> vector R n) 
          {rv1 : RandomVariable dom (Rvector_borel_sa n) f1}
          {rv2 : RandomVariable dom (Rvector_borel_sa n) f2}
          {isfe1:vector_IsFiniteExpectation prts f1}
          {isfe2:vector_IsFiniteExpectation prts f2} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (vector_FiniteConditionalExpectation (vecrvplus f1 f2))
             (vecrvplus (vector_FiniteConditionalExpectation f1) (vector_FiniteConditionalExpectation f2)).
  Proof.
    apply vector_nth_eq_almost; intros.
    eapply almost_impl.
    - apply all_almost; intros ??.
      rewrite vector_FiniteConditionalExpectation_nth'.
      transitivity (FiniteConditionalExpectation prts sub (rvplus (vecrvnth i pf f1) (vecrvnth i pf f2)) x).
      + apply FiniteConditionalExpectation_ext.
        intros ?.
        unfold vecrvnth, vecrvplus.
        now rewrite RealVectorHilbert.Rvector_nth_plus.
      + unfold vecrvnth, vecrvplus.
        rewrite RealVectorHilbert.Rvector_nth_plus.
        repeat rewrite vector_FiniteConditionalExpectation_nth.
        apply H.
    - apply FiniteCondexp_plus.
  Qed.

    Lemma vector_FiniteCondexp_minus {n} (f1 f2 : Ts -> vector R n) 
          {rv1 : RandomVariable dom (Rvector_borel_sa n) f1}
          {rv2 : RandomVariable dom (Rvector_borel_sa n) f2}
          {isfe1:vector_IsFiniteExpectation prts f1}
          {isfe2:vector_IsFiniteExpectation prts f2} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (vector_FiniteConditionalExpectation (vecrvminus f1 f2))
             (vecrvminus (vector_FiniteConditionalExpectation f1) (vector_FiniteConditionalExpectation f2)).
    Proof.
      unfold vecrvminus.
      unfold Rvector_minus_rv.
      rewrite vector_FiniteCondexp_plus.
      eapply almost_impl.
      - apply all_almost; intros ??.
        unfold vecrvplus.
        f_equal.
        apply H.
      - apply vector_FiniteCondexp_opp.
  Qed.

  Theorem vector_FiniteCondexp_factor_out {n}
        (f g : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n)  f}
        {rvg : RandomVariable dom2 (Rvector_borel_sa n) g}
        {rvgf: RandomVariable dom (Rvector_borel_sa n)  (vecrvmult f g)}
        {isfef:vector_IsFiniteExpectation prts f}
        {isfefg:vector_IsFiniteExpectation prts (vecrvmult f g)} :
    almostR2 (prob_space_sa_sub prts sub) eq
             (vector_FiniteConditionalExpectation (vecrvmult f g))
             (vecrvmult g (vector_FiniteConditionalExpectation f)).
  Proof.
    apply vector_nth_eq_almost; intros.
    assert (RandomVariable dom borel_sa (rvmult (vecrvnth i pf f) (vecrvnth i pf g))).
      {
        eapply vecrvnth_rv in rvgf.
        unfold vecrvnth, vecrvmult in rvgf.
        revert rvgf.
        apply RandomVariable_proper; try reflexivity.
        intros ?.
        rewrite RealVectorHilbert.Rvector_nth_mult.
        reflexivity.
      } 

      assert (IsFiniteExpectation prts (rvmult (vecrvnth i pf f) (vecrvnth i pf g))).
      {
        eapply vector_IsFiniteExpectation_nth in isfefg.
        revert isfefg.
        apply IsFiniteExpectation_proper; intros ?.
        unfold vecrvnth, vecrvmult.
        rewrite RealVectorHilbert.Rvector_nth_mult.
        reflexivity.
      } 

    eapply almost_impl; [| apply FiniteCondexp_factor_out; typeclasses eauto].
    - apply all_almost; intros ??.
      rewrite vector_FiniteConditionalExpectation_nth'.
      transitivity (FiniteConditionalExpectation prts sub (rvmult (vecrvnth i pf f) (vecrvnth i pf g)) x).
      + apply FiniteConditionalExpectation_ext.
        intros ?.
        unfold vecrvnth, vecrvmult.
        now rewrite RealVectorHilbert.Rvector_nth_mult.
      + unfold vecrvnth, vecrvmult.
        rewrite RealVectorHilbert.Rvector_nth_mult.
        repeat rewrite vector_FiniteConditionalExpectation_nth.
        apply H1.
  Qed.

  Lemma vector_FiniteCondexp_Jensen {n} (rv_X : Ts -> vector R n) (phi : vector (R -> R) n)
        {rv : RandomVariable dom (Rvector_borel_sa n) rv_X}
        {rvphi : RandomVariable dom (Rvector_borel_sa n) (fun x => vector_apply phi (rv_X x))}
        {isfe : vector_IsFiniteExpectation prts rv_X}
        {isfephi : vector_IsFiniteExpectation prts (fun x => vector_apply phi (rv_X x))} :
    (Forall (fun f => forall c x y, convex f c x y) (proj1_sig phi)) ->
    almostR2 (prob_space_sa_sub prts sub) (vectorize_relation Rle n)
      (fun x => vector_apply phi ((vector_FiniteConditionalExpectation rv_X) x))
      (vector_FiniteConditionalExpectation (fun x => vector_apply phi (rv_X x))).
  Proof.
    intros.
    apply vectorize_relation_almost; intros.

    assert (RandomVariable dom borel_sa (fun x : Ts => vector_nth i pf phi (vecrvnth i pf rv_X x))).
    {
      eapply vecrvnth_rv in rvphi.
      revert rvphi.
      apply RandomVariable_proper; try reflexivity.
      intros ?.
      unfold vecrvnth.
      now rewrite vector_nth_apply.
    }

    assert (IsFiniteExpectation prts (fun x : Ts => vector_nth i pf phi (vecrvnth i pf rv_X x))).
    {
      eapply vector_IsFiniteExpectation_nth in isfephi.
        revert isfephi.
        apply IsFiniteExpectation_proper; intros ?.
        unfold vecrvnth.
        now rewrite vector_nth_apply.
    }

    eapply almost_impl; [| apply (FiniteCondexp_Jensen prts sub (vecrvnth i pf rv_X) (vector_nth i pf phi))].
    - apply all_almost; intros ??.
      unfold vecrvnth.
      rewrite vector_nth_apply.
      repeat rewrite vector_FiniteConditionalExpectation_nth.
      rewrite H2.
      right.
      apply FiniteConditionalExpectation_ext; intros ?.
      unfold vecrvnth.
      now rewrite vector_nth_apply.
    - now eapply vector_Forall in H.
  Qed.

  Lemma vecrvabs_unfold {n} (a:Ts -> vector R n) : rv_eq (vecrvabs a)
                                                  (fun x => vector_apply (vector_const Rabs n) (a x)).
  Proof.
    intros ?.
    unfold vecrvabs, RealVectorHilbert.Rvector_abs.
    now rewrite vector_apply_const.
  Qed.

  Lemma vector_FiniteCondexp_Jensen_abs {n} (rv_X : Ts -> vector R n)
        {rv : RandomVariable dom (Rvector_borel_sa n) rv_X}
        {isfe : vector_IsFiniteExpectation prts rv_X}
        {isfephi : vector_IsFiniteExpectation prts (vecrvabs rv_X)} :
    almostR2 (prob_space_sa_sub prts sub) (vectorize_relation Rle n)
             (vecrvabs (vector_FiniteConditionalExpectation rv_X))
             (vector_FiniteConditionalExpectation (vecrvabs rv_X)).
  Proof.

    assert (rvphi : RandomVariable dom (Rvector_borel_sa n)
                                   (fun x : Ts => vector_apply (vector_const Rabs n) (rv_X x))).
    {
      apply RandomVariable_vector.
      apply Forall_vector; intros.
      generalize (rvabs_rv _ (vecrvnth i pf rv_X)).
      apply RandomVariable_proper; try reflexivity.
      intros ?.
      simpl.
      now rewrite vector_nth_fun_to_vector, vector_nth_apply, vector_nth_const.
    }

    assert (isfephi' : vector_IsFiniteExpectation prts (fun x : Ts => vector_apply (vector_const Rabs n) (rv_X x))).
    {
      apply Forall_vector; intros.
      eapply vector_IsFiniteExpectation_nth in isfephi.
      revert isfephi.
      apply IsFiniteExpectation_proper; intros ?.
      simpl.
      rewrite vector_nth_fun_to_vector, vector_nth_apply, vector_nth_const.
      unfold vecrvnth, vecrvabs.
      unfold RealVectorHilbert.Rvector_abs.
      now rewrite vector_nth_map.
    }

    eapply almost_impl; [| apply (@vector_FiniteCondexp_Jensen _ rv_X (vector_const Rabs n) _ _ _ _)].
    - apply all_almost; intros ??.
      rewrite vecrvabs_unfold.
      rewrite H; intros ??.
      right.
      repeat rewrite vector_FiniteConditionalExpectation_nth.
      apply FiniteConditionalExpectation_ext; intros ?.
      unfold vecrvnth.
      now rewrite vecrvabs_unfold.
    - apply Forall_vector; intros ?????.
      repeat rewrite vector_nth_const.
      apply abs_convex.
  Qed.


  Lemma vector_FiniteCondexp_factor_out_zero  {n}
        (f g : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {rvgf: RandomVariable dom2 (Rvector_borel_sa n) g}
        {isfef:vector_IsFiniteExpectation prts f}
        {isfefg:vector_IsFiniteExpectation prts (vecrvmult f g)} :
    almostR2 prts eq (vector_FiniteConditionalExpectation f) (const RealVectorHilbert.Rvector_zero) ->
    vector_FiniteExpectation prts (vecrvmult f g) = RealVectorHilbert.Rvector_zero.
  Proof.
    intros.
    assert (rvfg : RandomVariable dom  (Rvector_borel_sa n) (vecrvmult f g)).
    {
      apply Rvector_mult_rv; trivial.
      now apply RandomVariable_sa_sub.
    }
    generalize (vector_FiniteCondexp_FiniteExpectation (vecrvmult f g)); intros.
    generalize (vector_FiniteCondexp_factor_out f g); intros.
    assert (almostR2 prts eq (vector_FiniteConditionalExpectation (vecrvmult f g))
                     (const RealVectorHilbert.Rvector_zero)).
    {
      apply almostR2_prob_space_sa_sub_lift in H1.
      revert H1; apply almost_impl.
      revert H; apply almost_impl.
      apply all_almost; intros ???.
      rewrite H1.
      unfold vecrvmult.
      rewrite H.
      unfold const.
      now rewrite RealVectorHilbert.Rvector_mult_zero.
    }
    erewrite vector_FiniteExpectation_proper_almostR2 in H0; try eapply H2.
    - rewrite vector_FiniteExpectation_const in H0; eauto.
      apply rvconst.
    - apply RandomVariable_sa_sub; trivial.
      typeclasses eauto.
    - apply rvconst.
  Qed.

  Lemma vector_FiniteCondexp_factor_out_inner_zero  {n}
        (f g : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {rvg: RandomVariable dom (Rvector_borel_sa n) g}
        {rvgf: RandomVariable dom2 (Rvector_borel_sa n) g}
        {isfef:vector_IsFiniteExpectation prts f} 
        {isfefg:vector_IsFiniteExpectation prts (vecrvmult f g)} :
    almostR2 prts eq (vector_FiniteConditionalExpectation f) (const RealVectorHilbert.Rvector_zero) ->
    FiniteExpectation prts (rvinner f g) = 0.
  Proof.
    intros.
    rewrite (FiniteExpectation_rvinner _) with (isfe_mult := isfefg); trivial.
    - rewrite (@vector_FiniteCondexp_factor_out_zero _ _ _ rvf _ isfef); trivial.
      now rewrite RealVectorHilbert.Rvector_sum0.
  Qed.

  Lemma vector_FiniteCondexp_factor_out_inner_zero_swapped {n}
        (f g : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {rvg: RandomVariable dom (Rvector_borel_sa n) g}
        {rvgf: RandomVariable dom2 (Rvector_borel_sa n) g}
        {isfef:vector_IsFiniteExpectation prts f}
        {isfefg:vector_IsFiniteExpectation prts (vecrvmult g f)} :
    almostR2 prts eq (vector_FiniteConditionalExpectation f) (const RealVectorHilbert.Rvector_zero) ->
    FiniteExpectation prts (rvinner g f) = 0.
  Proof.
    intros.
    assert (RandomVariable dom (Rvector_borel_sa n) (vecrvmult g f)).
    {
      apply Rvector_mult_rv; trivial.
    }
    assert (RandomVariable dom (Rvector_borel_sa n) (vecrvmult f g)).
    {
      apply Rvector_mult_rv; trivial.
    }
    assert (vector_IsFiniteExpectation prts (vecrvmult f g)).
    {
      generalize (vector_IsFiniteExpectation_proper_almostR2 _ (vecrvmult g f)); intros.
      specialize (H2 (vecrvmult f g) _ _ isfefg).
      apply H2.
      apply all_almost.
      intros.
      unfold vecrvmult.
      now rewrite RealVectorHilbert.Rvector_mult_comm.
    }
    generalize (vector_FiniteCondexp_factor_out_inner_zero f g H); intros.
    rewrite <- H3.
    apply FiniteExpectation_proper_almostR2; trivial.
    - typeclasses eauto.
    - typeclasses eauto.
    - apply all_almost.
      intros.
      unfold rvinner.
      now rewrite RealVectorHilbert.Rvector_inner_comm.
  Qed.

End vec_cond_exp.


Section vec_cond_exp_props.
  
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          {dom3 : SigmaAlgebra Ts}
          (sub2 : sa_sub dom3 dom2).

  Lemma vector_FiniteCondexp_tower' {n}
        (f: Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe: vector_IsFiniteExpectation prts f}
        {rv:RandomVariable dom (Rvector_borel_sa n) (vector_FiniteConditionalExpectation prts sub f)}
    :
      almostR2 (prob_space_sa_sub prts (transitivity sub2 sub))
               eq
               (vector_FiniteConditionalExpectation
                  prts
                  (transitivity sub2 sub)
                  (vector_FiniteConditionalExpectation prts sub f))
               (vector_FiniteConditionalExpectation prts (transitivity sub2 sub) f).
  Proof.
    apply vector_nth_eq_almost; intros.

    assert (RandomVariable dom borel_sa (vecrvnth i pf f)).
    {
      typeclasses eauto.
    } 

      assert (IsFiniteExpectation prts (vecrvnth i pf f)).
    {
      typeclasses eauto.
    }

    assert (RandomVariable dom borel_sa (FiniteConditionalExpectation prts sub (vecrvnth i pf f))).
    {
      eapply (vecrvnth_rv i pf) in rv.
      revert rv.
      apply RandomVariable_proper; try reflexivity.
      intros ?.
      rewrite vector_FiniteConditionalExpectation_nth'.
      apply FiniteConditionalExpectation_ext.
      reflexivity.
    } 
    
    eapply almost_impl; [| apply FiniteCondexp_tower'].
    apply all_almost; intros ??.
    repeat rewrite vector_FiniteConditionalExpectation_nth'.
    etransitivity
    ; [| etransitivity; [apply H2 |]].
    - apply FiniteConditionalExpectation_ext; intros ?.
      rewrite vector_FiniteConditionalExpectation_nth'.
      apply FiniteConditionalExpectation_ext; reflexivity.
    - apply FiniteConditionalExpectation_ext; reflexivity.
  Qed.

  Theorem vector_FiniteCondexp_tower {n}
        (f: Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe: vector_IsFiniteExpectation prts f}
    :
      almostR2 (prob_space_sa_sub prts (transitivity sub2 sub))
               eq
               (vector_FiniteConditionalExpectation
                  prts
                  (transitivity sub2 sub)
                  (rv:=RandomVariable_sa_sub sub _ (rv_x:=vector_FiniteCondexp_rv prts sub f))
                  (vector_FiniteConditionalExpectation prts sub f))
               (vector_FiniteConditionalExpectation prts (transitivity sub2 sub) f).
  Proof.
    apply vector_FiniteCondexp_tower'.
  Qed.

End vec_cond_exp_props.
Section condexp.
  Lemma vector_FiniteCondexp_all_proper {n : nat} {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {dom2 dom2' : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom)
          (sub' : sa_sub dom2' dom)
          (sub_equiv:sa_equiv dom2 dom2')
          (f1 f2 : Ts -> vector R n) 
          {rv1 : RandomVariable dom (Rvector_borel_sa n) f1}
          {rv2 : RandomVariable dom (Rvector_borel_sa n) f2} 
          {isfe1 : vector_IsFiniteExpectation prts f1}
          {isfe2 : vector_IsFiniteExpectation prts f2} :
    almostR2 prts eq f1 f2 ->
    almostR2 (prob_space_sa_sub prts sub) eq
             (vector_FiniteConditionalExpectation prts sub f1)
             (vector_FiniteConditionalExpectation prts sub' f2).
  Proof.
    intros eqq1.
    apply vector_nth_eq_almost; intros.
    generalize (FiniteCondexp_all_proper prts sub sub' sub_equiv (vecrvnth i pf f1) (vecrvnth i pf f2))
    ; intros HH.
    cut_to HH; [| now apply vector_nth_eq_almost].
    revert HH.
    apply almost_impl; apply all_almost; intros ??.
    now repeat rewrite vector_FiniteConditionalExpectation_nth'.
  Qed.

End condexp.

