Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Import DVector.
Require Import NumberIso.
Require Import SigmaAlgebras.
Require Export FunctionsToReal ProbSpace BorelSigmaAlgebra.
Require Export RandomVariable.
Require Export Isomorphism.
Require Import FunctionalExtensionality.
Require Import RealVectorHilbert.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section VectorRandomVariables.
  
  Context {Ts:Type} {Td:Type}.


  Definition fun_to_vector_to_vector_of_funs
             {n:nat}
             (f: Ts -> vector Td n)
    : vector (Ts->Td) n
    := vector_create 0 n (fun m _ pf => fun x => vector_nth m pf (f x)).

  Definition vector_of_funs_to_fun_to_vector
             {n:nat}
             (fs:vector (Ts->Td) n)
    : Ts -> vector Td n
    := fun x => vector_create 0 n (fun m _ pf => vector_nth m pf fs x).

  Program Global Instance vector_iso n : Isomorphism (Ts -> vector Td n) (vector (Ts->Td) n)
    := {
    iso_f := fun_to_vector_to_vector_of_funs
    ; iso_b := vector_of_funs_to_fun_to_vector
      }.
  Next Obligation.
    unfold fun_to_vector_to_vector_of_funs, vector_of_funs_to_fun_to_vector.
    apply vector_nth_eq; intros.
    rewrite vector_nth_create'; simpl.
    apply functional_extensionality; intros.
    now rewrite vector_nth_create'.
  Qed.
  Next Obligation.
    unfold fun_to_vector_to_vector_of_funs, vector_of_funs_to_fun_to_vector.
    apply functional_extensionality; intros.
    erewrite vector_create_ext.
    2: {
      intros.
      rewrite vector_nth_create'.
      reflexivity.
    }
    now rewrite (vector_create_nth).
  Qed.

  Lemma vector_nth_fun_to_vector {n} (f:Ts->vector Td n) i pf : 
    vector_nth i pf (fun_to_vector_to_vector_of_funs f) = fun x:Ts => vector_nth i pf (f x).
  Proof.
    unfold fun_to_vector_to_vector_of_funs.
    now rewrite vector_nth_create'.
  Qed.

  Lemma vector_of_funs_vector_create n f :
    rv_eq (vector_of_funs_to_fun_to_vector (vector_create 0 n f))
          (fun t=> vector_create 0 n (fun m pf1 pf2 => f m pf1 pf2 t))
  .
  Proof.
    unfold vector_of_funs_to_fun_to_vector.
    intros x; simpl.
    apply vector_create_ext; intros.
    rewrite vector_nth_create.
    f_equal; apply le_uniqueness_proof.
  Qed.

End VectorRandomVariables.

Require Import Expectation.

Section vector_ops.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {prts: ProbSpace dom}.

  Definition vecrvconst (n:nat) (c : R) :=
    (fun (omega : Ts) => vector_const c n).

  Definition vecrvplus {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    (fun omega =>  Rvector_plus (rv_X1 omega) (rv_X2 omega)).

  Definition vecrvmult {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    (fun omega =>  Rvector_mult (rv_X1 omega) (rv_X2 omega)).

  Definition vecrvscale {n} (c:R) (rv_X : Ts -> vector R n) :=
    fun omega => Rvector_scale c (rv_X omega).

  Definition vecrvscalerv {n} (c: Ts -> R) (rv_X : Ts -> vector R n) :=
    fun omega => Rvector_scale (c omega) (rv_X omega).

  Definition vecrvopp {n} (rv_X : Ts -> vector R n) := 
    vecrvscale (-1) rv_X.

  Definition vecrvminus {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    vecrvplus rv_X1 (vecrvopp rv_X2).

  Definition vecrvsum {n} (rv_X : Ts -> vector R n) : Ts -> R :=
    (fun omega => Rvector_sum (rv_X omega)).

  Definition vecrvabs {n} (rv_X : Ts -> vector R n) := 
    fun omega => Rvector_abs (rv_X omega).

  Definition rvmaxabs {n} (rv_X : Ts -> vector R n) := 
    fun omega => Rvector_max_abs (rv_X omega).

  Definition rvinner {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    fun omega => Rvector_inner (rv_X1 omega) (rv_X2 omega).

  Definition vecrvnth {n} i pf (rv_X : Ts -> vector R n) :=
    (fun omega =>  vector_nth i pf (rv_X omega)).

  Global Instance vecrvplus_proper {n} : Proper (rv_eq ==> rv_eq ==> rv_eq) (@vecrvplus n).
  Proof.
    repeat red.
    unfold vecrvplus, rv_eq in *.
    congruence.
  Qed.

  Global Instance vecrvmult_proper {n} : Proper (rv_eq ==> rv_eq ==> rv_eq) (@vecrvmult n).
  Proof.
    repeat red.
    unfold vecrvmult, rv_eq.
    congruence.
  Qed.

  Global Instance vecrvscale_proper {n} : Proper (eq ==> rv_eq ==> rv_eq) (@vecrvscale n).
  Proof.
    repeat red.
    unfold vecrvscale, rv_eq.
    congruence.
  Qed.

  Global Instance vecrvopp_proper {n} : Proper (rv_eq ==> rv_eq) (@vecrvopp n).
  Proof.
    repeat red.
    unfold vecrvopp, vecrvscale, rv_eq.
    congruence.
  Qed.

  Global Instance vecrvminus_proper {n} : Proper (rv_eq ==> rv_eq ==> rv_eq) (@vecrvminus n).
  Proof.
    repeat red.
    unfold vecrvminus, vecrvplus, vecrvopp, vecrvscale, rv_eq.
    congruence.
  Qed.

  Global Instance vecrvsum_proper {n} : Proper (rv_eq ==> rv_eq) (@vecrvsum n).
  Proof.
    repeat red.
    unfold vecrvsum, rv_eq.
    congruence.
  Qed.

  Global Instance rvinner_proper {n} : Proper (rv_eq ==> rv_eq ==> rv_eq) (@rvinner n).
  Proof.
    repeat red.
    unfold rvinner, rv_eq.
    congruence.
  Qed.
  
  Lemma rvinner_unfold {n} (rv_X1 rv_X2 : Ts -> vector R n)
    : rvinner rv_X1 rv_X2 === vecrvsum (vecrvmult rv_X1 rv_X2).
  Proof.
    intros ?.
    reflexivity.
  Qed.

  
  Class RealVectorMeasurable {n} (rv_X : Ts -> vector R n) :=
    vecmeasurable : forall i pf, RealMeasurable dom (vector_nth i pf (iso_f rv_X)).

  Definition Rvector_borel_sa (n:nat) : SigmaAlgebra (vector R n)
    := vector_sa (vector_const borel_sa n).

  Lemma Rvector_borel_sa_closure (n:nat) : 
    Rvector_borel_sa n === closure_sigma_algebra
                     (pre_event_set_vector_product (vector_map (@sa_sigma _) (vector_const borel_sa n))).
  Proof.
    rewrite <- generated_sa_closure.
    reflexivity.
  Qed.

  Instance RealVectorMeasurableRandomVariable {n}
           (rv_X : Ts -> vector R n)
           {rvm:RealVectorMeasurable rv_X} :
    RandomVariable dom (Rvector_borel_sa n) rv_X.
  Proof.
    red in rvm.
    intros [e sa_e].
    assert (rvm':forall i pf, RandomVariable dom borel_sa (vector_nth i pf (iso_f rv_X))).
    {
      intros.
      apply measurable_rv.
      apply rvm.
    }
    clear rvm.
    red in rvm'.
    unfold event_preimage in *.
    simpl in sa_e.
    generalize (Rvector_borel_sa_closure n); intros HH.
    destruct (HH e) as [HH1 _].
    simpl.
    apply HH1 in sa_e.
    clear HH HH1.
    simpl in sa_e.
    clear prts.
    dependent induction sa_e; simpl.
    - apply sa_all.
    - destruct H as [v [H1 H2]].
      eapply sa_proper.
      + red; intros.
        apply H2.
      + clear e H2.
        apply sa_pre_bounded_inter; intros.
        specialize (H1 _ pf).
        rewrite vector_nth_map, vector_nth_const in H1.
        specialize (rvm' _ pf (exist _ _ H1)).
        eapply sa_proper; try eapply rvm'.
        intros x; simpl.
        rewrite vector_nth_fun_to_vector.
        reflexivity.
    - apply sa_countable_union; intros.
      eapply H0; auto.
    - apply sa_complement; auto.
  Qed.

  Instance RandomVariableRealVectorMeasurable {n}
           (rv_X : Ts -> vector R n)
           {rrv:RandomVariable dom (Rvector_borel_sa n) rv_X} :
    RealVectorMeasurable rv_X.
  Proof.
    red; intros.
    apply rv_measurable.
    red in rrv.
    intros [e sa_e].
    unfold event_preimage in *.
    simpl.
    eapply sa_proper.
    - intros ?.
      rewrite vector_nth_fun_to_vector.
      split; intros HH; eapply HH.
    - refine (rrv (exist _ (fun x => e (vector_nth i pf x)) _)).
      simpl; intros.
      apply H.
      rewrite vector_map_const.
      red.
      exists (vector_create 0 n (fun j _ pf => if Nat.eq_dec j i then e else Ω)).
      split; intros.
      + rewrite vector_nth_const.
        rewrite vector_nth_create'.
        match_destr.
        apply sa_all.
      + intros x.
        split; intros.
        * rewrite vector_nth_create'.
          match_destr.
          -- subst.
             now replace pf0 with pf by apply le_uniqueness_proof.
          -- red; trivial.
             now repeat red.
        * specialize (H0 i pf).
          rewrite vector_nth_create' in H0.
          match_destr_in H0.
          congruence.
  Qed.

  Lemma RealVectorMeasurableComponent_simplify {n} (f:Ts->vector R n) : 
    (forall (i : nat) (pf : (i < n)%nat),
        RealMeasurable dom (vector_nth i pf (fun_to_vector_to_vector_of_funs f))) ->   
    (forall (i : nat) (pf : (i < n)%nat),
        RealMeasurable dom (fun x => vector_nth i pf (f x))).
  Proof.
    intros HH i pf.
    eapply RealMeasurable_proper; try eapply HH.
    rewrite vector_nth_fun_to_vector.
    reflexivity.
  Qed.

  Instance Rvector_plus_measurable {n} (f g : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealVectorMeasurable g ->
    RealVectorMeasurable (vecrvplus f g).
  Proof.
    unfold RealVectorMeasurable, vecrvplus; simpl; intros.
    rewrite vector_nth_fun_to_vector.
    eapply RealMeasurable_proper.
    - intros ?.
      rewrite Rvector_plus_explode.
      rewrite vector_nth_create'.
      reflexivity.
    - apply plus_measurable; eauto
      ; now apply RealVectorMeasurableComponent_simplify.
  Qed.

  Instance Rvector_mult_measurable {n} (f g : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealVectorMeasurable g ->
    RealVectorMeasurable (vecrvmult f g).
  Proof.
    unfold RealVectorMeasurable, vecrvmult; simpl; intros.
    rewrite vector_nth_fun_to_vector.
    eapply RealMeasurable_proper.
    - intros ?.
      rewrite Rvector_mult_explode.
      rewrite vector_nth_create'.
      reflexivity.
    - apply mult_measurable; eauto
      ; now apply RealVectorMeasurableComponent_simplify.
  Qed.

  Lemma vecrvsum_rvsum {n} (f : Ts -> vector R n) :
    (vecrvsum f) === (rvsum (fun i x => match lt_dec i n with
                                        | left pf => vector_nth i pf (f x)
                                        | right _ => 0%R
                                        end)
                            n).
  Proof.
    intros a.
    unfold vecrvsum, Rvector_sum, rvsum; simpl.
    destruct (f a); simpl.
    subst.
    rewrite list_sum_sum_n.
    apply (@Hierarchy.sum_n_ext Hierarchy.R_AbelianGroup); intros.
    destruct (lt_dec n (length x)).
    - unfold vector_nth.
      match goal with
        [|- context [proj1_sig ?x]] => destruct x
      end; simpl in *.
      now rewrite <- e.
    - destruct (nth_error_None x n) as [_ HH].
      rewrite HH; trivial.
      lia.
  Qed.

  Instance Rvector_scale_measurable {n} c (f : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealVectorMeasurable (vecrvscale c f).
  Proof.
    unfold RealVectorMeasurable; simpl; intros.
    rewrite vector_nth_fun_to_vector.
    unfold vecrvscale, Rvector_scale.
    eapply RealMeasurable_proper.
    - intros x.
      rewrite vector_nth_map.
      reflexivity.
    - apply scale_measurable.
      specialize (H i pf).
      now rewrite vector_nth_fun_to_vector in H.
  Qed.

  Instance Rvector_scale_rv_measurable {n} (c : Ts -> R) (f : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealMeasurable dom c ->
    RealVectorMeasurable (vecrvscalerv c f).
  Proof.
    unfold RealVectorMeasurable; simpl; intros.
    rewrite vector_nth_fun_to_vector.
    unfold vecrvscalerv, Rvector_scale.
    eapply RealMeasurable_proper.
    - intros x.
      rewrite vector_nth_map.
      reflexivity.
    - apply mult_measurable; trivial.
      specialize (H i pf).
      now rewrite vector_nth_fun_to_vector in H.
  Qed.

  Instance Rvector_opp_measurable {n} (f : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealVectorMeasurable (vecrvopp f).
  Proof.
    apply Rvector_scale_measurable.
  Qed.

  Instance Rvector_abs_measurable {n} (f : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealVectorMeasurable (vecrvabs f).
  Proof.
    unfold RealVectorMeasurable; simpl; intros.
    rewrite vector_nth_fun_to_vector.
    unfold vecrvabs.
    eapply RealMeasurable_proper.
    - intros x.
      unfold Rvector_abs.
      rewrite vector_nth_map.
      reflexivity.
    - apply Rabs_measurable.
      specialize (H i pf).
      now rewrite vector_nth_fun_to_vector in H.
  Qed.

  Instance Rvector_sum_measurable {n} (f : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealMeasurable dom (vecrvsum f).
  Proof.
    unfold RealVectorMeasurable; simpl; intros.
    rewrite vecrvsum_rvsum.
    apply rvsum_measurable; intros.
    match_destr.
    - now apply RealVectorMeasurableComponent_simplify.
    - apply constant_measurable.
  Qed.

  Instance Rvector_const_measurable {n:nat} (c : R) :
    RealVectorMeasurable (vecrvconst n c ).
  Proof.
    unfold RealVectorMeasurable; intros.
    unfold iso_f; simpl.
    rewrite vector_nth_fun_to_vector.
    assert (rv_eq (fun x : Ts => vector_nth i pf (vecrvconst n c x))
                  (const c)).
    - intro x.
      unfold vecrvconst.
      unfold vector_const.
      now rewrite vector_nth_create'.
    - rewrite H.
      apply constant_measurable.
  Qed.

  Instance Rvector_max_abs_measurable {n} (f : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealMeasurable dom (rvmaxabs f).
  Proof.
    unfold RealVectorMeasurable; simpl; intros.
    unfold rvmaxabs.
    unfold RealMeasurable.
    intros.
    
    assert (pre_event_equiv
              (fun omega : Ts => Rvector_max_abs (f omega) <= r)
              (pre_event_inter (fun _ => 0 <= r)
                               (pre_list_inter
                                  (proj1_sig (vector_create 
                                                0 n 
                                                (fun m _ pf => fun omega => Rabs (vector_nth m pf 
                                                                                       (f omega)) <= r)))))).
    - intros x.
      split.
      + intros HH.
        split.
        {
          unfold Rvector_max_abs in HH.
          eapply Rle_trans; try eapply HH.
          apply fold_left_Rmax_init_le.
        } 
        intros a ain.
        apply In_vector_nth_ex in ain.
        destruct ain as [?[? inn]].
        rewrite vector_nth_create' in inn.
        subst.
        unfold Rvector_max_abs in HH.
        unfold vector_fold_left, Rvector_abs in HH.
        simpl in *.
        assert (inn:In (vector_nth x0 x1 (f x)) (proj1_sig (f x))) by apply vector_nth_In.
        eapply Rle_trans; try eapply HH.
        apply fold_left_Rmax_le.
        now apply in_map.
      + unfold list_inter.
        unfold Rvector_max_abs.
        intros [??].
        apply fold_left_lub; trivial; intros.
        apply In_vector_nth_ex in H2.
        destruct H2 as [?[? inn]].
        subst.
        apply H1.

        assert (HH:vector_nth x1 x2  
                           (vector_create 0 n
                                          (fun (m : nat) (_ : (0 <= m)%nat) (pf : (m < 0 + n)%nat) (omega : Ts) =>
                                             Rabs (vector_nth m pf (f omega)) <= r)) = (fun x0 : Ts => vector_nth x1 x2 (Rvector_abs (f x0)) <= r)).
        {
          rewrite vector_nth_create'.
          unfold Rvector_abs.
          apply functional_extensionality; intros.
          now rewrite vector_nth_map.
        }         
        rewrite <- HH.
        apply vector_nth_In.
    - rewrite H0.
      apply sa_inter.
      + apply sa_sigma_const_classic.
      + apply sa_pre_list_inter.
        intros.
        apply In_vector_nth_ex in H1.
        destruct H1 as [?[? inn]].
        rewrite vector_nth_create' in inn.
        simpl.
        subst.
        apply Rabs_measurable.
        intros rr.
        specialize (H x0 x1 rr).
        now rewrite vector_nth_fun_to_vector in H.
  Qed.

  Instance Rvector_inner_measurable {n} (f g : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealVectorMeasurable g ->
    RealMeasurable dom (rvinner f g).
  Proof.
    unfold RealVectorMeasurable; simpl; intros.
    rewrite rvinner_unfold.
    apply Rvector_sum_measurable.
    apply Rvector_mult_measurable; trivial.
  Qed.

  Global Instance Rvector_const_rv n c :
    RandomVariable dom (Rvector_borel_sa n) (vecrvconst n c).
  Proof.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_const_measurable.
  Qed.

  Global Instance Rvector_plus_rv {n} (f g : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n)  f ->
    RandomVariable dom (Rvector_borel_sa n)  g ->
    RandomVariable dom (Rvector_borel_sa n)  (vecrvplus f g).
  Proof.
    intros.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_plus_measurable
    ; now apply RandomVariableRealVectorMeasurable.
  Qed.

  Global Instance Rvector_mult_rv {n} (f g : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n)  f ->
    RandomVariable dom (Rvector_borel_sa n)  g ->
    RandomVariable dom (Rvector_borel_sa n)  (vecrvmult f g).
  Proof.
    intros.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_mult_measurable
    ; now apply RandomVariableRealVectorMeasurable.
  Qed.

  Global Instance Rvector_scale_rv {n} c (f : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom (Rvector_borel_sa n) (vecrvscale c f).
  Proof.
    intros.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_scale_measurable.
    now apply RandomVariableRealVectorMeasurable.
  Qed.
  
  Global Instance Rvector_scale_rv_rv {n} (c : Ts -> R) (f : Ts -> vector R n) :
    RandomVariable dom borel_sa c ->
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom (Rvector_borel_sa n) (vecrvscalerv c f).
  Proof.
    intros.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_scale_rv_measurable.
    - now apply RandomVariableRealVectorMeasurable.
    - now apply rv_measurable.
  Qed.

  Global Instance Rvector_opp_rv {n} (f : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom (Rvector_borel_sa n) (vecrvopp f).
  Proof.
    intros.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_opp_measurable.
    now apply RandomVariableRealVectorMeasurable.
  Qed.  

  Global Instance Rvector_abs_rv {n} (f : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom (Rvector_borel_sa n) (vecrvabs f).
  Proof.
    intros.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_abs_measurable.
    now apply RandomVariableRealVectorMeasurable.
  Qed.  

  Global Instance Rvector_minus_rv {n} (f g : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n)  f ->
    RandomVariable dom (Rvector_borel_sa n)  g ->
    RandomVariable dom (Rvector_borel_sa n)  (vecrvminus f g).
  Proof.
    intros.
    unfold vecrvminus.
    apply Rvector_plus_rv; trivial.
    now apply Rvector_opp_rv.
  Qed.

  Global Instance Rvector_sum_rv {n} (f : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom borel_sa (vecrvsum f).
  Proof.
    intros.
    apply measurable_rv.
    apply Rvector_sum_measurable
    ; now apply RandomVariableRealVectorMeasurable.
  Qed.

  Global Instance Rvector_max_abs_rv {n} (f : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom borel_sa (rvmaxabs f).
  Proof.
    intros.
    apply measurable_rv.
    apply Rvector_max_abs_measurable
    ; now apply RandomVariableRealVectorMeasurable.
  Qed.

  Global Instance Rvector_inner_rv {n} (f g : Ts -> vector R n)
         {rv1:RandomVariable dom (Rvector_borel_sa n) f}
         {rv2:RandomVariable dom (Rvector_borel_sa n) g} :
    RandomVariable dom borel_sa (rvinner f g).
  Proof.
    intros.
    apply measurable_rv.
    apply Rvector_inner_measurable
    ; now apply RandomVariableRealVectorMeasurable.
  Qed.

  Global Instance vecrvnth_rv {n} i pf (rv_X : Ts -> vector R n)
         {rv:RandomVariable dom (Rvector_borel_sa n) rv_X} :
    RandomVariable dom borel_sa (vecrvnth i pf rv_X).
  Proof.
    apply RandomVariableRealVectorMeasurable in rv.
    apply measurable_rv.
    red in rv.
    specialize (rv i pf).
    simpl in rv.
    now rewrite vector_nth_fun_to_vector in rv.
  Qed.

  Global Program Instance vecrvnth_frf {n} i pf (rv_X : Ts -> vector R n)
         {rv:FiniteRangeFunction rv_X} :
    FiniteRangeFunction (vecrvnth i pf rv_X)
    :=
      {
    frf_vals := map (fun c => vector_nth i pf c) frf_vals
      }.
  Next Obligation.
    unfold vecrvnth.
    apply in_map.
    apply frf_vals_complete.
  Qed.

  Global Instance Rvector_sum_pos {n} (f : Ts -> vector R n) :
    (forall i pf, NonnegativeFunction (fun x => vector_nth i pf (f x))) ->
    NonnegativeFunction (vecrvsum f).
  Proof.
    intros FP ?.
    apply Rvector_sum_pos.
    intros.
    apply In_vector_nth_ex in H.
    destruct H as [i [pf eqq]]; subst.
    apply FP.
  Qed.

  Global Instance Rvector_inner_pos_mult {n} (f g : Ts -> vector R n) :
    (forall i pf, NonnegativeFunction (fun x => vector_nth i pf (f x) * vector_nth i pf (g x))) ->
    NonnegativeFunction (rvinner f g).
  Proof.
    intros ?.
    apply Rvector_sum_pos; intros.
    intros ?.
    rewrite Rvector_mult_explode; rewrite vector_nth_create'.
    apply H.
  Qed.

  Global Instance Rvector_inner_self_pos {n} (f : Ts -> vector R n) :
    NonnegativeFunction (rvinner f f).
  Proof.
    intros ?.
    apply Rvector_inner_pos.
  Qed.

  Global Instance Rvector_inner_nneg_pos {n} (f g : Ts -> vector R n) :
    (forall i pf, NonnegativeFunction (fun x => vector_nth i pf (f x))) ->
    (forall i pf, NonnegativeFunction (fun x => vector_nth i pf (g x))) ->
    NonnegativeFunction (rvinner f g).
  Proof.
    unfold NonnegativeFunction.
    intros ??.
    apply Rvector_inner_pos_mult.
    intros i pf ?.
    apply Rmult_le_pos; eauto.
  Qed.

  Definition vector_Expectation {n} (rv_X : Ts -> vector R n) : option (vector Rbar n)
    := vectoro_to_ovector (vector_map Expectation (iso_f rv_X)).

  Program Instance vec_frf {n} (rv_X : Ts -> vector R n) i (pf : (i < n)%nat)
          (frf : FiniteRangeFunction rv_X) : FiniteRangeFunction
                                                (vector_nth i pf (iso_f rv_X)) 
    :=
      {
    frf_vals := map (fun c => vector_nth i pf c) frf_vals
      }.
  Next Obligation.
    rewrite vector_nth_fun_to_vector.
    destruct frf.
    now apply in_map.
  Qed.

  Instance vec_rv {n} (rv_X : Ts -> vector R n) i (pf : (i < n)%nat)
           (rv:RandomVariable dom (Rvector_borel_sa n) rv_X) :
    RandomVariable dom borel_sa (vector_nth i pf (iso_f rv_X)).
  Proof.
    apply measurable_rv.
    apply RandomVariableRealVectorMeasurable in rv.
    apply rv.
  Qed.

  Global Program Instance frf_vecrvconst n c :
    FiniteRangeFunction (vecrvconst n c)
    := { frf_vals := (vector_const c n)::nil }.
  
  Definition vector_SimpleExpectation {n} (rv_X : Ts -> vector R n)
             {rv: RandomVariable dom (Rvector_borel_sa n) rv_X}
             {frf : FiniteRangeFunction rv_X} : vector R n
    := 
      vector_create 0 n (fun m _ pf => 
                           SimpleExpectation (vector_nth m pf (iso_f rv_X))
                                             (frf := (vec_frf rv_X m pf frf))).

  Definition vector_SimpleConditionalExpectationSA {n} (rv_X : Ts -> vector R n)
             {rv: RandomVariable dom (Rvector_borel_sa n) rv_X}
             {frf : FiniteRangeFunction rv_X} 
             (l : list dec_sa_event) : Ts -> vector R n 
    := iso_b (
           vector_create 0 n (fun m _ pf => 
                                SimpleConditionalExpectationSA 
                                  (vector_nth m pf (iso_f rv_X))
                                  (frf := (vec_frf rv_X m pf frf))
                                  l)).


  Program Instance FiniteRangeFunction_nth_vector {n} {Td} (v:Ts->vector Td n)
          (frfs:forall i pf1, FiniteRangeFunction (fun a => vector_nth i pf1 (v a))) :
    FiniteRangeFunction v
    := { frf_vals :=
           if Nat.eq_dec n 0
           then [vector0]
           else 
             vector_list_product
               (vector_create 0 n
                              (fun i _ pf => (@frf_vals _ _ _ (frfs i pf)))) }.
  Next Obligation.
    match_destr.
    - simpl.
      left.
      subst.
      rewrite vector0_0.
      apply vector_eq; simpl; trivial.
    - apply vector_list_product_in_iff; trivial.
      apply vector_Forall2_nth_iff.
      intros.
      rewrite vector_nth_create'.
      destruct (frfs i pf).
      auto.
  Qed.

  (*
Lemma FiniteRangeFunction_vector {n} (f:Ts -> forall i (pf : (i < n)%nat)) :
  (forall m pf1 pf2, FiniteRangeFunction (fun a => f a m pf1 pf2)) ->
  FiniteRangeFunction (fun a => vector_reate 0 n (f a)).

   *)

  
  Instance vec_gen_condexp_rv {n}
           (rv_X : Ts -> vector R n)
           {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
           {frf : FiniteRangeFunction rv_X}
           (l : list dec_sa_event) :
    RandomVariable dom (Rvector_borel_sa n)
                   (vector_SimpleConditionalExpectationSA rv_X l).
  Proof.
    unfold vector_SimpleConditionalExpectationSA.
    simpl.
    rewrite vector_of_funs_vector_create.
    apply RealVectorMeasurableRandomVariable.
    intros ??.
    apply rv_measurable.
    simpl.
    rewrite vector_nth_fun_to_vector.
    eapply RandomVariable_proper.
    - intros ?.
      rewrite vector_nth_create'.
      reflexivity.
    - typeclasses eauto.
  Qed.

  Instance vector_SimpleConditionalExpectationSA_simpl {n}
           (rv_X : Ts -> vector R n)
           {rv: RandomVariable dom (Rvector_borel_sa n) rv_X}
           {frf : FiniteRangeFunction rv_X}
           (l : list dec_sa_event) :
    FiniteRangeFunction (vector_SimpleConditionalExpectationSA rv_X l).
  Proof.
    unfold vector_SimpleConditionalExpectationSA; simpl.
    apply FiniteRangeFunction_nth_vector; intros.
    apply FiniteRangeFunction_ext with 
        (x:= fun a =>
               (SimpleConditionalExpectationSA
                  (vector_nth i pf1 (fun_to_vector_to_vector_of_funs rv_X)) l a)).
    - intros ?.
      rewrite vector_of_funs_vector_create.
      now rewrite vector_nth_create'.
    - apply SimpleConditionalExpectationSA_simpl.
  Qed.

  
  Lemma vector_gen_conditional_tower_law {n}
        (rv_X : Ts -> vector R n)
        {rv : RandomVariable dom (Rvector_borel_sa n) rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list dec_sa_event)
        (ispart: is_partition_list (map dsa_event l)) :
    vector_SimpleExpectation rv_X =
    vector_SimpleExpectation
      (vector_SimpleConditionalExpectationSA rv_X l).
  Proof.
    apply vector_create_ext.
    intros.
    unfold vector_SimpleConditionalExpectationSA.
    transitivity (SimpleExpectation (frf:=(@SimpleConditionalExpectationSA_simpl Ts dom prts
                                                                                   (@vector_nth (Ts -> R) n i pf2 (@fun_to_vector_to_vector_of_funs Ts R n rv_X))
                                                                                   (vec_rv _ _ _ _)
                                                                                   (@vec_frf n rv_X i pf2 frf) l))
                                    (SimpleConditionalExpectationSA (vector_nth i pf2 ((fun_to_vector_to_vector_of_funs rv_X))) l)).
    - apply gen_conditional_tower_law; trivial.
    - apply SimpleExpectation_ext.
      rewrite iso_f_b.
      now rewrite vector_nth_create'.
  Qed.

  Program Instance frf_vecrvmult {n}
          (rv_X1 rv_X2 : Ts -> vector R n)
          {frf1:FiniteRangeFunction rv_X1}
          {frf2:FiniteRangeFunction rv_X2}
    : FiniteRangeFunction (vecrvmult rv_X1 rv_X2)
    := { frf_vals := map (fun ab => Rvector_mult (fst ab) (snd ab)) 
                         (list_prod (frf_vals (FiniteRangeFunction:=frf1))
                                    (frf_vals (FiniteRangeFunction:=frf2))) }.
  Next Obligation.
    destruct frf1.
    destruct frf2.
    rewrite in_map_iff.
    exists (rv_X1 x, rv_X2 x).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

  Global Program Instance frf_vecrvplus {n}
          (rv_X1 rv_X2 : Ts -> vector R n)
          {frf1:FiniteRangeFunction rv_X1}
          {frf2:FiniteRangeFunction rv_X2}
    : FiniteRangeFunction (vecrvplus rv_X1 rv_X2)
    := { frf_vals := map (fun ab => Rvector_plus (fst ab) (snd ab)) 
                         (list_prod (frf_vals (FiniteRangeFunction:=frf1))
                                    (frf_vals (FiniteRangeFunction:=frf2))) }.
  Next Obligation.
    destruct frf1.
    destruct frf2.
    rewrite in_map_iff.
    exists (rv_X1 x, rv_X2 x).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

  Global Program Instance frf_vecrvscale {n} (c:R)
          (rv_X : Ts -> vector R n)
          {frf:FiniteRangeFunction rv_X}
    : FiniteRangeFunction (vecrvscale c rv_X)
    := { frf_vals := map (fun x => Rvector_scale c x)
                         (frf_vals (FiniteRangeFunction := frf)) }.
  Next Obligation.
    destruct frf.
    rewrite in_map_iff.
    exists (rv_X x).
    now split.
  Qed.

  Global Program Instance frf_vecrvscalerv {n} (c:Ts -> R)
          (rv_X : Ts -> vector R n)
          {frfc:FiniteRangeFunction c}
          {frf:FiniteRangeFunction rv_X}
    : FiniteRangeFunction (vecrvscalerv c rv_X)
    := { frf_vals := map (fun ab => Rvector_scale (fst ab) (snd ab)) 
                         (list_prod (frf_vals (FiniteRangeFunction:=frfc))
                                    (frf_vals (FiniteRangeFunction:=frf))) }.
  Next Obligation.
    destruct frfc.
    destruct frf.
    rewrite in_map_iff.
    exists (c x, rv_X x).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

  Global Instance frf_vecropp {n}
         (rv_X : Ts -> vector R n)
         {frf:FiniteRangeFunction rv_X}
    : FiniteRangeFunction (vecrvopp rv_X)
    :=  frf_vecrvscale (-1) rv_X.    

  Global Instance frf_vecrvminus {n}
         (rv_X1 rv_X2 : Ts -> vector R n)
         {frf1 : FiniteRangeFunction rv_X1}
         {frf2 : FiniteRangeFunction rv_X2}  :
    FiniteRangeFunction (vecrvminus rv_X1 rv_X2) := 
    frf_vecrvplus rv_X1 (vecrvopp rv_X2).

  Program Instance frf_vecsum {n}
          (rv_X : Ts -> vector R n)
          {frf:FiniteRangeFunction rv_X}
    : FiniteRangeFunction (vecrvsum rv_X)
    := { frf_vals := map Rvector_sum frf_vals }.
  Next Obligation.
    destruct frf.
    rewrite in_map_iff.
    exists (rv_X x).
    easy.
  Qed.

  Global Instance frfinner {n}
         (rv_X1 rv_X2 : Ts -> vector R n)
         {frf1:FiniteRangeFunction rv_X1}
         {frf2:FiniteRangeFunction rv_X2}
    : FiniteRangeFunction (rvinner rv_X1 rv_X2).
  Proof.
    eapply FiniteRangeFunction_ext.
    - rewrite rvinner_unfold; reflexivity.
    - apply frf_vecsum.
      now apply frf_vecrvmult.
  Qed.

  Global Program Instance frfmaxabs {n}
         (rv_X : Ts -> vector R n)
         {frf:FiniteRangeFunction rv_X}
    : FiniteRangeFunction (rvmaxabs rv_X)
  := { frf_vals := map Rvector_max_abs frf_vals }.
  Next Obligation.
    unfold rvmaxabs.
    destruct frf.
    now apply in_map.
  Qed.

End vector_ops.

Lemma Rvector_borel_singleton {n} (c:vector R n) :
  sa_sigma (SigmaAlgebra:=Rvector_borel_sa n) (pre_event_singleton c).
Proof.
  apply generated_sa_sub.
  red; intros.
  exists (vector_create 0 n (fun i _ pf => (pre_event_singleton (vector_nth i pf c)))); simpl.
  split; intros.
  - rewrite vector_nth_create'.
    rewrite vector_nth_map.
    rewrite vector_nth_const.
    apply borel_singleton.
  - unfold pre_event_singleton.
    split; intros.
    + rewrite vector_nth_create'.
      congruence.
    + apply vector_nth_eq; intros.
      specialize (H i pf).
      now rewrite vector_nth_create' in H.
Qed.

Global Instance Rvector_borel_sa_has_preimages {n} : HasPreimageSingleton (Rvector_borel_sa n).
Proof.
  red; intros.
  red in rv.
  apply (rv (exist _ _ (Rvector_borel_singleton c))).
Qed.

Section vector_ops_ext.
  
  Context {Ts:Type}
          {dom: SigmaAlgebra Ts}
          {prts: ProbSpace dom}.

  Lemma partition_measurable_vecrvplus {n} (rv_X1 rv_X2 : Ts -> vector R n)
        {rv1 : RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rv2 : RandomVariable dom (Rvector_borel_sa n) rv_X2} 
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2}         
        (l : list (event dom)) :
    is_partition_list l ->
    partition_measurable (cod:=Rvector_borel_sa n) rv_X1 l ->
    partition_measurable (cod:=Rvector_borel_sa n) rv_X2 l ->     
    partition_measurable (cod:=Rvector_borel_sa n) (vecrvplus rv_X1 rv_X2) l.

  Proof.
     unfold partition_measurable. intros.
     specialize (H0 H p H3).
     specialize (H1 H p H3).
     destruct H0 as [c1 ?].
     destruct H1 as [c2 ?].     
     exists (Rvector_plus c1 c2).
     intros ?.
     simpl.
     unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
     unfold vecrvplus; simpl; intros.
     now rewrite (H0 x H4), (H1 x H4).
  Qed.
   
  Lemma partition_measurable_vecrvscale {n} (c : R) (rv_X : Ts -> vector R n)
        {rv : RandomVariable dom (Rvector_borel_sa n) rv_X}
        {frf : FiniteRangeFunction rv_X}
        (l : list (event dom)) :
    is_partition_list l ->
     partition_measurable (cod:=Rvector_borel_sa n) rv_X l ->     
     partition_measurable (cod:=Rvector_borel_sa n) (vecrvscale c rv_X) l.
   Proof.
     unfold partition_measurable. intros.
     specialize (H0 H p H2).
     destruct H0 as [c0 ?].
     unfold vecrvscale.
     exists (Rvector_scale c c0).
     intros ?.
     unfold vecrvscale; simpl; intros.
     unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
     now rewrite (H0 x).
   Qed.

  Lemma partition_measurable_vecrvscalerv {n} (rv_c : Ts -> R) 
        (rv_X : Ts -> vector R n)
        {rv : RandomVariable dom (Rvector_borel_sa n) rv_X}
        {rvc : RandomVariable dom borel_sa rv_c}        
        {frf : FiniteRangeFunction rv_X}
        {frfc : FiniteRangeFunction rv_c}        
        (l : list (event dom)) :
    is_partition_list l ->
     partition_measurable rv_c l ->     
     partition_measurable (cod:=Rvector_borel_sa n) rv_X l ->     
     partition_measurable (cod:=Rvector_borel_sa n) (vecrvscalerv rv_c rv_X) l.
   Proof.
     unfold partition_measurable. intros.
     specialize (H0 H p H3).
     specialize (H1 H p H3).
     destruct H0 as [c0 ?].
     destruct H1 as [c1 ?].     
     unfold vecrvscalerv.
     exists (Rvector_scale c0 c1).
     intros ?; simpl; intros.
     unfold pre_event_sub, pre_event_preimage, pre_event_singleton in *; simpl.
     rewrite (H0 x); trivial.
     now rewrite (H1 x).
   Qed.

   Lemma partition_measurable_vecrvminus {n} (rv_X1 rv_X2 : Ts -> vector R n) 
         {rv1 : RandomVariable dom (Rvector_borel_sa n) rv_X1}
         {rv2 : RandomVariable dom (Rvector_borel_sa n) rv_X2} 
         {frf1 : FiniteRangeFunction rv_X1}
         {frf2 : FiniteRangeFunction rv_X2}         
         (l : list (event dom)) :
    is_partition_list l ->
     partition_measurable (cod:=Rvector_borel_sa n) rv_X1 l ->
     partition_measurable (cod:=Rvector_borel_sa n) rv_X2 l ->     
     partition_measurable (cod:=Rvector_borel_sa n) (vecrvminus rv_X1 rv_X2) l.
   Proof.
     unfold vecrvminus; intros.
     eapply partition_measurable_vecrvplus; trivial.
     unfold vecrvopp.
     eapply partition_measurable_vecrvscale; trivial.     
   Qed.
   
  Instance rv_fun_simple_Rvector {n} (x:Ts -> vector R n) (f : vector R n -> vector R n)
           (rvx : RandomVariable dom (Rvector_borel_sa n) x) 
           (frfx : FiniteRangeFunction x) :
    RandomVariable dom (Rvector_borel_sa n) (fun u => f (x u)).
  Proof.
    eapply rv_fun_simple; eauto.
    intros.
    now apply Rvector_borel_sa_has_preimages.
  Qed.

   Lemma partition_measurable_comp {n} (rv_X : Ts -> vector R n) (f : vector R n -> vector R n)
         {rv : RandomVariable dom (Rvector_borel_sa n) rv_X}
         {frf : FiniteRangeFunction rv_X}
         (l : list (event dom)) :
    is_partition_list l ->
     partition_measurable (cod:=Rvector_borel_sa n) rv_X l ->
     partition_measurable (cod:=Rvector_borel_sa n) (fun v => f (rv_X v)) l.
   Proof.
     unfold partition_measurable; intros.
     specialize (H0 H p H2).
     destruct H0 as [c ?].
     exists (f c).
     destruct frf.
     unfold RandomVariable.frf_vals; simpl.
      unfold event_sub, pre_event_sub, event_preimage, preimage_singleton, pre_event_preimage, pre_event_singleton in *; simpl; intros.
      now rewrite H0.
   Qed.

   Lemma partition_measurable_const {n} (c : vector R n)
         (l : list (event dom)) :
     is_partition_list l ->
     partition_measurable (cod:=Rvector_borel_sa n) (const c) l.
   Proof.
     unfold partition_measurable; intros.
     exists c.
     unfold frf_vals; simpl.
     repeat red.
     reflexivity.
   Qed.

  Program Definition vec_induced_sigma_generators {n}
          {rv_X : Ts -> vector R n}
          {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
          (frf : FiniteRangeFunction rv_X)
    : list dec_sa_event
    :=
      map (fun (c:vector R n) => Build_dec_sa_event
                                (preimage_singleton (σd:=(Rvector_borel_sa n)) rv_X c) _)
          (nodup vector_eq_dec frf_vals).
    Next Obligation.
      unfold event_preimage, event_singleton, dec_event.
      intros.
      apply vector_eq_dec.
  Defined.

    Lemma is_partition_vec_induced_gen {n}
          {rv_X : Ts -> vector R n}
          {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
          (frf : FiniteRangeFunction rv_X) :
    is_partition_list (map dsa_event (vec_induced_sigma_generators frf)).
  Proof.
    unfold is_partition_list, vec_induced_sigma_generators.
    rewrite map_map; simpl.
    split.
    - apply event_disjoint_preimage_disj.
      apply NoDup_nodup.
    - apply frf_nodup_preimage_list_union.
  Qed.

  Lemma vec_induced_partition_measurable {n}
          {rv_X : Ts -> vector R n}
          {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
          (frf : FiniteRangeFunction rv_X) :
    partition_measurable (cod:=Rvector_borel_sa n) rv_X (map dsa_event (vec_induced_sigma_generators frf)).
  Proof.
    unfold partition_measurable, vec_induced_sigma_generators.
    intros.
    rewrite in_map_iff in H0.
    destruct H0 as [? [? ?]].
    rewrite in_map_iff in H1.
    destruct H1 as [? [? ?]].
    rewrite <- H1 in H0.
    simpl in H0.
    exists x0.
    now rewrite H0.
  Qed.

  Lemma FiniteRangeFunction_exist2_part
        (l : list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & FiniteRangeFunction rv_X})) : 
    FiniteRangeFunction
      (fold_right rvplus (const 0) (map (fun '(existT2 x _ _) => x) l)).
  Proof.
    induction l; simpl.
    - typeclasses eauto.
    - destruct a; simpl.
      typeclasses eauto.
  Defined.

  Lemma RandomVariable_exist2_part
        (l : list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & FiniteRangeFunction rv_X})) : 
    RandomVariable dom borel_sa
                   (fold_right rvplus (const 0) (map (fun '(existT2 x _ _) => x) l)).
  Proof.
    induction l; simpl.
    - typeclasses eauto.
    - destruct a; simpl.
      typeclasses eauto.
  Defined.

  Definition make_simple_vector_package {n}
             (rv_X : Ts -> vector R n)
             {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
             {frf:FiniteRangeFunction rv_X} :
    list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & FiniteRangeFunction rv_X})
    := proj1_sig (vector_create 0 n
                                (fun i _ pf => existT2 _ _ _ (vec_rv _ i pf rv) (vec_frf _ i pf frf))).
  
  Lemma SimpleExpectation_fold_rvplus'
        (l : list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & FiniteRangeFunction rv_X})) : 
    SimpleExpectation (fold_right rvplus (const 0) (map (fun '(existT2 x _ _) => x) l))
                      (rv:=RandomVariable_exist2_part l)
                      (frf:=FiniteRangeFunction_exist2_part l) =
    list_sum (map (fun '(existT2 x rx sx)  => SimpleExpectation x (rv:=rx) (frf:=sx)) l).
  Proof.
    induction l; simpl.
    - now rewrite SimpleExpectation_const.
    - destruct a; simpl.
      rewrite <- IHl.
      rewrite sumSimpleExpectation; trivial.
  Qed.

  Lemma make_simple_vector_package_proj1 {n} (rv_X:Ts -> vector R n)
        {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
        {frf:FiniteRangeFunction rv_X} :
    (map (fun '(@existT2 _ _ _ x _ _) => x) (make_simple_vector_package rv_X)) = proj1_sig (fun_to_vector_to_vector_of_funs rv_X).
  Proof.
    unfold make_simple_vector_package; simpl.
    rewrite vector_list_create_map.
    apply vector_list_create_ext; intros.
    now rewrite vector_nth_fun_to_vector.
  Qed.    
  
  Lemma SimpleExpectation_rvsum {n} (rv_X : Ts -> vector R n)
        {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
        {frf1:FiniteRangeFunction rv_X} :
    SimpleExpectation (vecrvsum rv_X)  (frf:=frf_vecsum rv_X)
    = 
    Rvector_sum (vector_SimpleExpectation rv_X).
  Proof.
    unfold vector_SimpleExpectation.
    unfold vecrvsum.
    unfold Rvector_sum; simpl.

    generalize (SimpleExpectation_fold_rvplus' (make_simple_vector_package rv_X))
    ; intros HH.
    assert (eqq1:rv_eq  (fun omega : Ts => list_sum (` (rv_X omega)))
                        (fold_right rvplus (const 0)
                                    (map (fun '(@existT2 _ _ _ x _ _) => x) (make_simple_vector_package rv_X)))).
    {
      intros ?.
      rewrite list_sum_fold_right.
      rewrite fold_right_rvplus.
      f_equal.
      rewrite make_simple_vector_package_proj1.
      simpl.
      rewrite vector_list_create_map.
      assert (eqq2:(rv_X a) =
                   vector_create 0 n
                                 (fun (x : nat) (_ : (0 <= x)%nat) (pf2 : (x < 0 + n)%nat) => vector_nth x pf2 (rv_X a)))
        by now rewrite vector_create_nth.
      now rewrite eqq2 at 1; simpl.
    }
(*    assert (frf:FiniteRangeFunction (fun omega : Ts => list_sum (` (rv_X omega)))). *)

    
    rewrite (SimpleExpectation_ext eqq1
                                   (rv2:=RandomVariable_exist2_part _)
                                   (frf2:=FiniteRangeFunction_exist2_part _)).
    rewrite HH.
    f_equal.
    clear.
    unfold make_simple_vector_package; simpl.
    now rewrite vector_list_create_map.
  Qed.
  
  Lemma SimpleExpectation_rvinner {n} (rv_X1 rv_X2 : Ts -> vector R n)
        {rv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {frf1:FiniteRangeFunction rv_X1}
        {frf2:FiniteRangeFunction rv_X2} :
    SimpleExpectation (rvinner rv_X1 rv_X2) (rv:=Rvector_inner_rv _ _) (frf:=frfinner _ _)
    = 
    Rvector_sum
      (vector_create 
         0 n 
         (fun m _ pf => 
            SimpleExpectation (frf:=frfmult _ _ (frf1:=vec_frf _ m pf _) (frf2:=vec_frf _ m pf _)) (rv:=rvmult_rv _ _ _ (rv1:=vec_rv _ m pf _) (rv2:=vec_rv _ m pf _))
                              (rvmult (vector_nth m pf (iso_f rv_X1))
                                      (vector_nth m pf (iso_f rv_X2))))).
  Proof.
    generalize (rvinner_unfold rv_X1 rv_X2); intros.
    rewrite (SimpleExpectation_ext H).
    rewrite (SimpleExpectation_pf_irrel _ (frf_vecsum _ (frf:=(frf_vecrvmult _ _ )))).
    rewrite SimpleExpectation_rvsum.
    f_equal.
    unfold vector_SimpleExpectation.
    apply vector_create_ext.
    intros.
    apply SimpleExpectation_ext.
    simpl.
    intro v.
    do 3 rewrite vector_nth_fun_to_vector.	
    unfold vecrvmult.
    rewrite Rvector_mult_explode.
    rewrite vector_nth_create'.     
    now unfold rvmult.
  Qed.
  
  Lemma simple_expection_rvinner_measurable {n}
        (rv_X1 rv_X2 : Ts -> vector R n)
        {rv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} 
        (l : list dec_sa_event) :
    is_partition_list (map dsa_event l) ->
    partition_measurable  (cod:=Rvector_borel_sa n) rv_X1 (map dsa_event l) ->
    SimpleExpectation (rvinner rv_X1 rv_X2)  (rv:=Rvector_inner_rv _ _) (frf:=frfinner _ _) =
    SimpleExpectation (rvinner rv_X1 (vector_SimpleConditionalExpectationSA rv_X2 l))
                      (frf:=frfinner _ _ (frf2:=vector_SimpleConditionalExpectationSA_simpl _ _))
                      (rv:=Rvector_inner_rv _ _ (rv2:=vec_gen_condexp_rv _ _)).
  Proof.
    intros.
    repeat rewrite SimpleExpectation_rvinner; trivial.
    f_equal.
    apply vector_create_ext.
    intros.
    erewrite gen_conditional_tower_law with (l0 := l); trivial.
    - apply SimpleExpectation_ext.
      rewrite gen_conditional_scale_measurable; trivial.
      + intro x.
        f_equal.
        unfold vector_SimpleConditionalExpectationSA.
        rewrite iso_f_b.
        now rewrite vector_nth_create'.
      + unfold partition_measurable.
        unfold partition_measurable in H0.
        intros.
        cut_to H0; trivial.
        specialize (H0 p H2).
        destruct H0 as [cvec ?].
        exists (vector_nth i pf2 cvec).
        destruct frf1.
        unfold RandomVariable.frf_vals; simpl.
        intros ?; simpl.
        rewrite vector_nth_fun_to_vector.
        unfold event_sub, pre_event_sub, event_preimage, pre_event_preimage, event_singleton, pre_event_singleton in *.
        intros.
        now rewrite H0.
  Qed.       

  Lemma simple_expectation_rvinner_measurable_zero {n}
        (rv_X1 rv_X2 : Ts -> vector R n)
        {rv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {frf1 : FiniteRangeFunction rv_X1}
        {frf2 : FiniteRangeFunction rv_X2} 
        (l : list dec_sa_event) :
    rv_eq (vector_SimpleConditionalExpectationSA rv_X2 l) (const Rvector_zero) ->
    is_partition_list (map dsa_event l) ->
    partition_measurable (cod:=Rvector_borel_sa n) rv_X1 (map dsa_event l) ->
    SimpleExpectation (rvinner rv_X1 rv_X2) (rv:=Rvector_inner_rv _ _) (frf:=frfinner _ _) = 0.
  Proof.
    intros.
    rewrite simple_expection_rvinner_measurable with (l0 := l); trivial.
    assert (rv_eq  
              (rvinner rv_X1 (vector_SimpleConditionalExpectationSA rv_X2 l))
              (const 0)).
    {
      rewrite H.
      intro v.
      apply (hilbert.inner_zero_r (rv_X1 v)).
    }
    rewrite (SimpleExpectation_ext H2).
    now rewrite SimpleExpectation_const.
  Qed.

End vector_ops_ext.
