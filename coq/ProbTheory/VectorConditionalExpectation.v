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


Section vec_util.

  Lemma almost_bounded_forall 
        {Ts:Type}
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        (P:nat->Prop)
        (dec:forall n, {P n} + {~ P n})
        {Pn:forall i (pf:P i), pre_event Ts} :
    (forall i pf1 pf2 x, Pn i pf1 x -> Pn i pf2 x) ->
    (forall n pf, almost prts (Pn n pf)) ->
    almost prts (fun x => forall n pf, Pn n pf x).
  Proof.
    intros prop a.
    assert (forall n, almost prts (
                          match dec n with
                          | left pf => (Pn n pf)
                          | right _ => fun _ => True
                          end
                        )).
    {
      intros.
      match_destr.
      now apply all_almost.
    }
    apply almost_forall in H.
    revert H.
    apply almost_impl.
    apply all_almost.
    intros ??.
    red in H.
    intros.
    specialize (H n).
    match_destr_in H; try tauto.
    eapply prop; eauto.
  Qed.

  Program Lemma vector_Forall2_almost_nth_iff
          {Ts Td:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {n}
          (P:Td->Td->Prop) (v1 v2:Ts -> vector Td n) :
    (forall (i : nat) (pf : (i < n)%nat), almostR2 prts P (vecrvnth i pf v1) (vecrvnth i pf v2)) <->
    almostR2 prts (Forall2 P) v1 v2.
  Proof.
    split; intros HH.
    - apply almost_bounded_forall in HH.
      + revert HH.
        apply almost_impl.
        apply all_almost; intros ??.
        now apply vector_Forall2_nth_iff.
      + intros.
        apply lt_dec.
      + unfold vecrvnth.
        intros.
        now repeat rewrite (vector_nth_ext _ _ pf2 pf1).
    - intros.
      revert HH.
      apply almost_impl.
      apply all_almost; intros ??.
      unfold vecrvnth.
      now apply vector_Forall2_nth_iff.
  Qed.

  Lemma vector_nth_eq_almost {Ts Td:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          {n} (v1 v2:Ts -> vector Td n) :
    (forall i pf, almostR2 prts eq (vecrvnth i pf v1) (vecrvnth i pf v2)) <->
    almostR2 prts eq v1 v2.
  Proof.
    split; intros.
    - apply vector_Forall2_almost_nth_iff in H.
      revert H.
      apply almost_impl.
      apply all_almost; intros ??.
      now apply vector_eqs.
    - apply vector_Forall2_almost_nth_iff.
      revert H.
      apply almost_impl.
      apply all_almost; intros ??.
      rewrite H.
      reflexivity.
  Qed.

  Lemma vectorize_relation_almost {Ts Td:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
          (RR:Td->Td->Prop) {n} (v1 v2:Ts -> vector Td n) :
    (forall i pf, almostR2 prts RR (vecrvnth i pf v1) (vecrvnth i pf v2)) <->
    almostR2 prts (vectorize_relation RR n) v1 v2.
  Proof.
    split; intros.
    - apply vector_Forall2_almost_nth_iff in H.
      revert H.
      apply almost_impl.
      apply all_almost; intros ??.
      intros ??.
      now apply vector_Forall2_nth_iff.
    - apply vector_Forall2_almost_nth_iff.
      revert H.
      apply almost_impl.
      apply all_almost; intros ??.
      now apply vector_Forall2_nth_iff.
  Qed.

End vec_util.

Section vec_exp.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Class vector_IsFiniteExpectation {n} (rv_X : Ts -> vector R n) 
    := is_vector_finite_expectation :
         Forall (IsFiniteExpectation prts) (proj1_sig (iso_f rv_X)).

  Global Instance vector_IsFiniteExpectation_nth {n} (f: Ts -> vector R n) i pf
             {isfe:vector_IsFiniteExpectation f} :
    IsFiniteExpectation prts (vecrvnth i pf f).
  Proof.
    generalize (vector_Forall _ isfe i pf); intros.
    simpl in H.
    rewrite vector_nth_fun_to_vector in H.
    apply H.
  Qed.

  Definition vector_IsFiniteExpectation_Finite {n} (rv_X:Ts -> vector R n)
        {isfe:vector_IsFiniteExpectation rv_X} :
    { x : vector R n | vector_Expectation rv_X = Some (vector_map Finite x)}.
  Proof.
    exists (vector_map (fun x => FiniteExpectation prts (proj1_sig x) (isfe:=proj2_sig x))
                  (vector_dep_zip _ isfe)).
    red in isfe.

    apply vectoro_to_ovector_some_eq.
    rewrite vector_map_map.
    revert isfe.
    simpl iso_f.
    generalize (fun_to_vector_to_vector_of_funs rv_X); clear
    ; intros.

    simpl.
    induction (proj1_sig v); simpl; trivial.
    generalize isfe; intros isfe'.
    invcs isfe.
    rewrite (FiniteExpectation_Expectation _ a).
    rewrite (IHl H2).
    f_equal.
    f_equal.
    - f_equal.
      now apply FiniteExpectation_ext.
    - apply list_dep_zip_ext_map; intros; simpl.
      f_equal.
      now apply FiniteExpectation_ext.
  Qed.

  Definition vector_FiniteExpectation {n} (rv_X:Ts -> vector R n)
             {isfe:vector_IsFiniteExpectation rv_X} : vector R n
    := proj1_sig (vector_IsFiniteExpectation_Finite rv_X).

  Lemma vector_FiniteExpectation_Expectation {n} (rv_X:Ts->vector R n)
        {isfe:vector_IsFiniteExpectation rv_X} : 
    vector_Expectation rv_X = Some (vector_map Finite (vector_FiniteExpectation rv_X)).
  Proof.
    unfold vector_FiniteExpectation, proj1_sig.
    match_destr.
  Qed.

  Lemma vector_Expectation_const n c
        {rv:RandomVariable dom (Rvector_borel_sa n) (const c)}
    :
      vector_Expectation (const c) = Some (vector_map Finite c).
  Proof.
    unfold vector_Expectation.
    simpl.
    assert (eqq1:vector_map Expectation (fun_to_vector_to_vector_of_funs (const c)) =
                 (vector_map Some (vector_map Finite c))).
    {
      apply vector_nth_eq; intros.
      repeat rewrite vector_nth_map.
      rewrite vector_nth_fun_to_vector.
      replace  (fun x : Ts => vector_nth i pf (const c x)) with (const (B:=Ts) (vector_nth i pf c)) by reflexivity.
      now rewrite Expectation_const.
    }
    rewrite eqq1.
    apply vectoro_to_ovector_some_eq.
    simpl.
    rewrite <- listo_to_olist_simpl_lift_map.
    now rewrite lift_map_id.
  Qed.    

  Lemma vector_FiniteExpectation_const n c
        {rv:RandomVariable dom (Rvector_borel_sa n) (const c)}
        {isfe:vector_IsFiniteExpectation (const c)}
    :
      vector_FiniteExpectation (const c) = c.
  Proof.
    generalize (vector_Expectation_const n c).
    rewrite (vector_FiniteExpectation_Expectation _).
    intros.
    invcs H.
    apply (f_equal (fun x => map real x)) in H1.
    
    repeat rewrite map_map in H1.
    repeat rewrite map_id in H1.
    now apply vector_eq.
  Qed.
        
  Lemma vector_IsFiniteExpectation_proper_almostR2 {n} rv_X1 rv_X2
        {rrv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rrv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {isfe1:vector_IsFiniteExpectation rv_X1}
    :
      almostR2 prts eq rv_X1 rv_X2 ->
      vector_IsFiniteExpectation rv_X2.
  Proof.
    intros.
    destruct (vector_nth_eq_almost prts rv_X1 rv_X2)  as [_ HH].
    specialize (HH H).
    unfold vector_IsFiniteExpectation.
    apply Forall_vector; intros.
    unfold vector_IsFiniteExpectation in isfe1.
    eapply vector_Forall in isfe1.
    specialize (HH i pf).
    eapply IsFiniteExpectation_proper_almostR2; try eapply isfe1.
    - now apply vec_rv.
    - now apply vec_rv.
    - destruct (vector_nth_eq_almost prts rv_X1 rv_X2) as [_ HH2].
      simpl.
      repeat rewrite vector_nth_fun_to_vector.
      now apply HH2.
  Qed.

    Lemma vector_Expectation_proper_almostR2 {n} rv_X1 rv_X2
        {rrv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rrv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
    :
      almostR2 prts eq rv_X1 rv_X2 ->
      vector_Expectation rv_X1 = vector_Expectation rv_X2.
  Proof.
    intros.
    unfold vector_Expectation.
    f_equal.
    apply vector_nth_eq; intros.
    repeat rewrite vector_nth_map.
    simpl.
    repeat rewrite vector_nth_fun_to_vector.
        
    destruct (vector_nth_eq_almost prts rv_X1 rv_X2) as [_ HH2].
    simpl.
    specialize (HH2 H i pf).
    apply Expectation_almostR2_proper; trivial
    ; now apply vecrvnth_rv.
  Qed.    

  Lemma vector_FiniteExpectation_proper_almostR2 {n} rv_X1 rv_X2
        {rrv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rrv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {isfe1:vector_IsFiniteExpectation rv_X1}
        {isfe2:vector_IsFiniteExpectation rv_X2}
    :
      almostR2 prts eq rv_X1 rv_X2 ->
      vector_FiniteExpectation rv_X1 = vector_FiniteExpectation rv_X2.
  Proof.
    intros.
    generalize (vector_Expectation_proper_almostR2 rv_X1 rv_X2 H).
    repeat rewrite (vector_FiniteExpectation_Expectation _).
    intros HH.
    invcs HH.
    apply (f_equal (fun x => map real x)) in H1.
    
    repeat rewrite map_map in H1.
    repeat rewrite map_id in H1.
    now apply vector_eq.
  Qed.
  
End vec_exp.

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
    
    Lemma vector_dep_zip_map1 {T : Type} {P : T -> Prop} {n} (l : vector T n) (Fp : Forall P (proj1_sig l)) :
      vector_map (proj1_sig (P:=P)) (vector_dep_zip l Fp) = l.
    Proof.
      apply vector_eq.
      unfold vector_dep_zip.
      unfold vector_map; simpl.
      now rewrite list_dep_zip_map1.
    Qed.      

    Lemma vector_dep_zip_nth_proj1 {T} {n} {P:T->Prop} (v:vector T n)
      (fl:Forall P (proj1_sig v)) :
        forall i pf,
          proj1_sig (vector_nth i pf (vector_dep_zip v fl)) =
          vector_nth i pf v.
    Proof.
      intros.
      rewrite <- (vector_nth_map (@proj1_sig _ _)).
      now rewrite vector_dep_zip_map1.
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
        (saP:sa_sigma (SigmaAlgebra := dom2) P) :
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
        (saP:sa_sigma (SigmaAlgebra := dom2) P) :
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

  Global Instance vector_IsFiniteExpectation_const {n} (c:vector R n) : vector_IsFiniteExpectation prts (const c).
  Proof.
    red.
    apply Forall_vector; intros; simpl.
    rewrite vector_nth_fun_to_vector.
    eapply IsFiniteExpectation_proper; try eapply IsFiniteExpectation_const.
    intros ?.
    unfold const.
    reflexivity.
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

  Global Instance vector_IsFiniteExpectation_scale {n} (c:R) (f:Ts -> vector R n)
         {isfe:vector_IsFiniteExpectation prts f} :
    vector_IsFiniteExpectation prts (vecrvscale c f).
  Proof.
    red.
    apply Forall_vector; intros; simpl.
    rewrite vector_nth_fun_to_vector.
    eapply IsFiniteExpectation_proper; try eapply IsFiniteExpectation_scale.
    intros ?.
    unfold vecrvscale, rvscale, RealVectorHilbert.Rvector_scale.
    rewrite vector_nth_map.
    reflexivity.
    typeclasses eauto.
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

  Global Instance vector_IsFiniteExpectation_plus {n} (f1 f2:Ts -> vector R n)
         {rv1 : RandomVariable dom (Rvector_borel_sa n) f1}
         {rv2 : RandomVariable dom (Rvector_borel_sa n) f2}
         {isfe1:vector_IsFiniteExpectation prts f1} 
         {isfe2:vector_IsFiniteExpectation prts f2} :
    vector_IsFiniteExpectation prts (vecrvplus f1 f2).
  Proof.
    red.
    apply Forall_vector; intros; simpl.
    rewrite vector_nth_fun_to_vector.
    eapply IsFiniteExpectation_proper; try eapply IsFiniteExpectation_plus.
    - intros ?.
      unfold vecrvplus.
      now rewrite RealVectorHilbert.Rvector_nth_plus.
    - typeclasses eauto. 
    - typeclasses eauto. 
    - typeclasses eauto. 
    - typeclasses eauto. 
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

  Definition vector_apply {n} {A B} (f : vector (A -> B) n)  (x : vector A n) : vector B n
    := vector_map (fun '(a,b) => a b) (vector_zip f x).

  Lemma vector_nth_apply {n} {A B} (f : vector (A -> B) n)  (x : vector A n) i pf :
    vector_nth i pf (vector_apply f x) = (vector_nth i pf f) (vector_nth i pf x).
  Proof.
    unfold vector_apply.
    now rewrite vector_nth_map, vector_nth_zip.
  Qed.

  Lemma vector_apply_const {n} {A B} (f: A->B) (a:vector A n) : vector_apply (vector_const f n) a = vector_map f a.
  Proof.
    apply vector_nth_eq; intros.
    now rewrite vector_nth_apply, vector_nth_map, vector_nth_const.
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

  Lemma FiniteExpectation_vecrvsum {n}
        (f : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {isfe: IsFiniteExpectation prts (vecrvsum f)}
        {isfev:vector_IsFiniteExpectation prts f} :
    FiniteExpectation prts (vecrvsum f) =
    RealVectorHilbert.Rvector_sum (vector_FiniteExpectation prts f).
  Proof.
  Admitted.
        
  Lemma FiniteExpectation_rvinner {n}
        (f g : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {rvgf: RandomVariable dom (Rvector_borel_sa n) g}
        {isfefg:vector_IsFiniteExpectation prts (vecrvmult f g)} 
        {isfe_inner:IsFiniteExpectation prts (rvinner f g)} :    
    FiniteExpectation prts (rvinner f g) = 
    RealVectorHilbert.Rvector_sum (vector_FiniteExpectation prts (vecrvmult f g)).
  Proof.
    generalize (rvinner_unfold f g); intros.
    rewrite (FiniteExpectation_ext prts _ _ H).
    apply FiniteExpectation_vecrvsum.
    typeclasses eauto.
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

  Instance IsFiniteExpectation_inner_vecrvmult {n}
           (f g : Ts -> vector R n)
           {isfe: vector_IsFiniteExpectation prts (vecrvmult f g)} :
    IsFiniteExpectation prts (rvinner f g).
  Proof.
    Admitted.
           
  Lemma vector_FiniteCondexp_factor_out_inner_zero  {n}
        (f g : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
        {rvgf: RandomVariable dom2 (Rvector_borel_sa n) g}
        {isfef:vector_IsFiniteExpectation prts f} 
(*       {isfe_inner:IsFiniteExpectation prts (rvinner f g)}    *)
        {isfefg:vector_IsFiniteExpectation prts (vecrvmult f g)} :
    almostR2 prts eq (vector_FiniteConditionalExpectation f) (const RealVectorHilbert.Rvector_zero) ->
    FiniteExpectation prts (rvinner f g) = 0.
  Proof.
    intros.
    rewrite  FiniteExpectation_rvinner with (isfefg0 := isfefg); trivial.
    - rewrite vector_FiniteCondexp_factor_out_zero with (rvf0 := rvf) (isfef0 := isfef); trivial.
      now rewrite RealVectorHilbert.Rvector_sum0.
    - now apply RandomVariable_sa_sub.
  Qed.

  Lemma vector_FiniteCondexp_factor_out_inner_zero_swapped {n}
        (f g : Ts -> vector R n)
        {rvf : RandomVariable dom (Rvector_borel_sa n) f}
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
      now apply RandomVariable_sa_sub.
    }
    assert (RandomVariable dom (Rvector_borel_sa n) (vecrvmult f g)).
    {
      apply Rvector_mult_rv; trivial.
      now apply RandomVariable_sa_sub.
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
