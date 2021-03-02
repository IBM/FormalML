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


  Definition vecrvplus {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    (fun omega =>  Rvector_plus (rv_X1 omega) (rv_X2 omega)).

  Definition vecrvmult {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    (fun omega =>  Rvector_mult (rv_X1 omega) (rv_X2 omega)).

  Definition vecrvscale {n} (c:R) (rv_X : Ts -> vector R n) :=
    fun omega => Rvector_scale c (rv_X omega).

  Definition vecrvopp {n} (rv_X : Ts -> vector R n) := 
    vecrvscale (-1) rv_X.

  Definition vecrvminus {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    vecrvplus rv_X1 (vecrvopp rv_X2).

  Definition vecrvsum {n} (rv_X : Ts -> vector R n) : Ts -> R :=
    (fun omega => Rvector_sum (rv_X omega)).

  Definition rvinner {n} (rv_X1 rv_X2 : Ts -> vector R n) :=
    fun omega => Rvector_inner (rv_X1 omega) (rv_X2 omega).

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
                     (event_set_vector_product (vector_map (@sa_sigma _) (vector_const borel_sa n))).
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
    intros e sa_e.
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
        apply sa_bounded_inter; intros.
        specialize (H1 i pf).
        rewrite vector_nth_map, vector_nth_const in H1.
        specialize (rvm' i pf _ H1).
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
    intros e sa_e.
    unfold event_preimage in *.
    simpl.
    eapply sa_proper.
    - intros ?.
      rewrite vector_nth_fun_to_vector.
      split; intros HH; eapply HH.
    - apply (rrv (fun x => e (vector_nth i pf x))).
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

  Instance Rvector_opp_measurable {n} (f : Ts -> vector R n) :
    RealVectorMeasurable f ->
    RealVectorMeasurable (vecrvopp f).
  Proof.
    apply Rvector_scale_measurable.
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
  
  Global Instance Rvector_opp_rv {n} (f : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom (Rvector_borel_sa n) (vecrvopp f).
  Proof.
    intros.
    apply RealVectorMeasurableRandomVariable.
    apply Rvector_opp_measurable.
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

  Global Instance Rvector_inner_rv {n} (f g : Ts -> vector R n) :
    RandomVariable dom (Rvector_borel_sa n) f ->
    RandomVariable dom (Rvector_borel_sa n) g ->
    RandomVariable dom borel_sa (rvinner f g).
  Proof.
    intros.
    apply measurable_rv.
    apply Rvector_inner_measurable
    ; now apply RandomVariableRealVectorMeasurable.
  Qed.

  Global Instance Rvector_sum_pos {n} (f : Ts -> vector R n) :
    (forall i pf, PositiveRandomVariable (fun x => vector_nth i pf (f x))) ->
    PositiveRandomVariable (vecrvsum f).
  Proof.
    intros FP ?.
    apply Rvector_sum_pos.
    intros.
    apply In_vector_nth_ex in H.
    destruct H as [i [pf eqq]]; subst.
    apply FP.
  Qed.

  Global Instance Rvector_inner_pos_mult {n} (f g : Ts -> vector R n) :
    (forall i pf, PositiveRandomVariable (fun x => vector_nth i pf (f x) * vector_nth i pf (g x))) ->
    PositiveRandomVariable (rvinner f g).
  Proof.
    intros ?.
    apply Rvector_sum_pos; intros.
    intros ?.
    rewrite Rvector_mult_explode; rewrite vector_nth_create'.
    apply H.
  Qed.

  Global Instance Rvector_inner_self_pos {n} (f : Ts -> vector R n) :
    PositiveRandomVariable (rvinner f f).
  Proof.
    intros ?.
    apply Rvector_inner_pos.
  Qed.

  Global Instance Rvector_inner_pos {n} (f g : Ts -> vector R n) :
    (forall i pf, PositiveRandomVariable (fun x => vector_nth i pf (f x))) ->
    (forall i pf, PositiveRandomVariable (fun x => vector_nth i pf (g x))) ->
    PositiveRandomVariable (rvinner f g).
  Proof.
    unfold PositiveRandomVariable.
    intros ??.
    apply Rvector_inner_pos_mult.
    intros i pf ?.
    apply Rmult_le_pos; eauto.
  Qed.

  Definition vector_Expectation {n} (rv_X : Ts -> vector R n) : option (vector Rbar n)
    := vectoro_to_ovector (vector_map Expectation (iso_f rv_X)).

  Program Instance vec_srv {n} (rv_X : Ts -> vector R n) i (pf : (i < n)%nat)
          (srv : SimpleRandomVariable rv_X) : SimpleRandomVariable
                                                (vector_nth i pf (iso_f rv_X)) 
    :=
      {
    srv_vals := map (fun c => vector_nth i pf c) srv_vals
      }.
  Next Obligation.
    rewrite vector_nth_fun_to_vector.
    destruct srv.
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

  Definition vector_SimpleExpectation {n} (rv_X : Ts -> vector R n)
             {srv : SimpleRandomVariable rv_X} : vector R n
    := 
      vector_create 0 n (fun m _ pf => 
                           SimpleExpectation (vector_nth m pf (iso_f rv_X))
                                             (srv := (vec_srv rv_X m pf srv))).

  Definition vector_gen_SimpleConditionalExpectation {n} (rv_X : Ts -> vector R n)
             {srv : SimpleRandomVariable rv_X} 
             (l : list dec_sa_event) : Ts -> vector R n 
    := iso_b (
           vector_create 0 n (fun m _ pf => 
                                gen_SimpleConditionalExpectation 
                                  (vector_nth m pf (iso_f rv_X))
                                  (srv := (vec_srv rv_X m pf srv))
                                  l)).


  Program Instance SimpleRandomVariable_nth_vector {n} {Td} (v:Ts->vector Td n)
          (srvs:forall i pf1, SimpleRandomVariable (fun a => vector_nth i pf1 (v a))) :
    SimpleRandomVariable v
    := { srv_vals :=
           if Nat.eq_dec n 0
           then [vector0]
           else 
             vector_list_product
               (vector_create 0 n
                              (fun i _ pf => (@srv_vals _ _ _ (srvs i pf)))) }.
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
      destruct (srvs i pf).
      auto.
  Qed.

  (*
Lemma SimpleRandomVariable_vector {n} (f:Ts -> forall i (pf : (i < n)%nat)) :
  (forall m pf1 pf2, SimpleRandomVariable (fun a => f a m pf1 pf2)) ->
  SimpleRandomVariable (fun a => vector_reate 0 n (f a)).

   *)
  Instance vector_gen_SimpleConditionalExpectation_simpl {n}
           (rv_X : Ts -> vector R n)
           {srv : SimpleRandomVariable rv_X}
           (l : list dec_sa_event) :
    SimpleRandomVariable (vector_gen_SimpleConditionalExpectation rv_X l).
  Proof.
    unfold vector_gen_SimpleConditionalExpectation; simpl.
    apply SimpleRandomVariable_nth_vector; intros.
    apply SimpleRandomVariable_ext with 
        (x:= fun a =>
               (gen_SimpleConditionalExpectation
                  (vector_nth i pf1 (fun_to_vector_to_vector_of_funs rv_X)) l a)).
    - intros ?.
      rewrite vector_of_funs_vector_create.
      now rewrite vector_nth_create'.
    - apply gen_SimpleConditionalExpectation_simpl.
  Qed.
  
  Lemma vector_gen_conditional_tower_law {n}
        (rv_X : Ts -> vector R n)
        {rv : RandomVariable dom (Rvector_borel_sa n) rv_X}
        {srv : SimpleRandomVariable rv_X}
        (l : list dec_sa_event)
        (ispart: is_partition_list (map dsa_event l)) :
    vector_SimpleExpectation rv_X =
    vector_SimpleExpectation
      (vector_gen_SimpleConditionalExpectation rv_X l).
  Proof.
    apply vector_create_ext.
    intros.
    unfold vector_gen_SimpleConditionalExpectation.
    transitivity (SimpleExpectation (srv:=(@gen_SimpleConditionalExpectation_simpl Ts dom prts
                                                                                   (@vector_nth (Ts -> R) n i pf2 (@fun_to_vector_to_vector_of_funs Ts R n rv_X))
                                                                                   (@vec_srv n rv_X i pf2 srv) l))
                                    (gen_SimpleConditionalExpectation (vector_nth i pf2 ((fun_to_vector_to_vector_of_funs rv_X))) l)).
    - apply gen_conditional_tower_law; trivial.
      apply RandomVariableRealVectorMeasurable in rv.
      red in rv.
      specialize (rv i pf2).
      now apply measurable_rv.
    - apply SimpleExpectation_ext.
      rewrite iso_f_b.
      now rewrite vector_nth_create'.
  Qed.

  Program Instance srv_vecrvmult {n}
          (rv_X1 rv_X2 : Ts -> vector R n)
          {srv1:SimpleRandomVariable rv_X1}
          {srv2:SimpleRandomVariable rv_X2}
    : SimpleRandomVariable (vecrvmult rv_X1 rv_X2)
    := { srv_vals := map (fun ab => Rvector_mult (fst ab) (snd ab)) 
                         (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                    (srv_vals (SimpleRandomVariable:=srv2))) }.
  Next Obligation.
    destruct srv1.
    destruct srv2.
    rewrite in_map_iff.
    exists (rv_X1 x, rv_X2 x).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

  Program Instance srv_vecrvplus {n}
          (rv_X1 rv_X2 : Ts -> vector R n)
          {srv1:SimpleRandomVariable rv_X1}
          {srv2:SimpleRandomVariable rv_X2}
    : SimpleRandomVariable (vecrvplus rv_X1 rv_X2)
    := { srv_vals := map (fun ab => Rvector_plus (fst ab) (snd ab)) 
                         (list_prod (srv_vals (SimpleRandomVariable:=srv1))
                                    (srv_vals (SimpleRandomVariable:=srv2))) }.
  Next Obligation.
    destruct srv1.
    destruct srv2.
    rewrite in_map_iff.
    exists (rv_X1 x, rv_X2 x).
    split.
    now simpl.
    apply in_prod; trivial.
  Qed.

  Program Instance srv_vecrvscale {n} (c:R)
          (rv_X : Ts -> vector R n)
          {srv:SimpleRandomVariable rv_X}
    : SimpleRandomVariable (vecrvscale c rv_X)
    := { srv_vals := map (fun x => Rvector_scale c x)
                         (srv_vals (SimpleRandomVariable := srv)) }.
  Next Obligation.
    destruct srv.
    rewrite in_map_iff.
    exists (rv_X x).
    now split.
  Qed.

  Global Instance srv_vecropp {n}
         (rv_X : Ts -> vector R n)
         {srv:SimpleRandomVariable rv_X}
    : SimpleRandomVariable (vecrvopp rv_X)
    :=  srv_vecrvscale (-1) rv_X.    

  Global Instance srv_vecrvminus {n}
         (rv_X1 rv_X2 : Ts -> vector R n)
         {srv1 : SimpleRandomVariable rv_X1}
         {srv2 : SimpleRandomVariable rv_X2}  :
    SimpleRandomVariable (vecrvminus rv_X1 rv_X2) := 
    srv_vecrvplus rv_X1 (vecrvopp rv_X2).

  Program Instance srv_vecsum {n}
          (rv_X : Ts -> vector R n)
          {srv:SimpleRandomVariable rv_X}
    : SimpleRandomVariable (vecrvsum rv_X)
    := { srv_vals := map Rvector_sum srv_vals }.
  Next Obligation.
    destruct srv.
    rewrite in_map_iff.
    exists (rv_X x).
    easy.
  Qed.

  Global Instance srvinner {n}
         (rv_X1 rv_X2 : Ts -> vector R n)
         {srv1:SimpleRandomVariable rv_X1}
         {srv2:SimpleRandomVariable rv_X2}
    : SimpleRandomVariable (rvinner rv_X1 rv_X2).
  Proof.
    eapply SimpleRandomVariable_ext.
    - rewrite rvinner_unfold; reflexivity.
    - typeclasses eauto.
  Qed.

  (* move *)
  Lemma vector_list_create_shiftS
        {T:Type}
        (start len:nat)
        (f:(forall m, S start <= m -> m < S start + len -> T)%nat) :
    vector_list_create (S start) len f =
    vector_list_create start len (fun x pf1 pf2 => f (S x)%nat (le_n_S _ _ pf1) (lt_n_S _ _ pf2)).
  Proof.
    revert start f.
    induction len; simpl; trivial; intros.
    rewrite IHlen.
    f_equal.
    - f_equal; apply le_uniqueness_proof.
    - apply vector_list_create_ext; intros.
      f_equal; apply le_uniqueness_proof.
  Qed.
  
  Lemma vector_list_create_shift0
        {T:Type}
        (start len:nat)
        (f:(forall m, start <= m -> m < start + len -> T)%nat) :
    vector_list_create start len f =
    vector_list_create 0 len (fun x _ pf2 => f (start+x)%nat (le_plus_l start _) (plus_lt_compat_l _ _ start pf2)).
  Proof.
    induction start; simpl.
    - apply vector_list_create_ext; intros.
      f_equal; apply le_uniqueness_proof.
    - rewrite vector_list_create_shiftS.
      rewrite IHstart.
      apply vector_list_create_ext; intros.
      f_equal; apply le_uniqueness_proof.
  Qed.

  Lemma vector_list_create_map
        {T U:Type}
        (start len:nat)
        (f:(forall m, start <= m -> m < start + len -> T)%nat)
        (g:T->U) :
    map g (vector_list_create start len f) =
    vector_list_create start len (fun x pf1 pf2 => g (f x pf1 pf2)).
  Proof.
    revert start f.
    induction len; simpl; trivial; intros.
    f_equal.
    apply IHlen.
  Qed.

  Lemma fold_right_rv_inner c (l:list (Ts->R)) (a:Ts) :
    fold_right rvplus (const c) l a =
    fold_right Rplus c (map (fun x => x a) l).
  Proof.
    unfold rvplus, const.
    induction l; simpl; trivial.
    now rewrite IHl.
  Qed.


  Program Lemma Forallt_vector {A} {P:A->Type} {n:nat} (l:vector A n) :
    (forall i pf, P (vector_nth i pf l)) ->
    Forallt P l.
  Proof.
    destruct l; simpl; subst.
    induction x; simpl; intros.
    - constructor.
    - constructor.
      + apply (X 0%nat ltac:(lia)).
      + apply IHx; intros.
        specialize (X (S i) (ltac:(lia))).
        unfold vector_nth, proj1_sig in *.
        match_destr.
        match_destr_in X.
        simpl in *.
        congruence.
  Defined.

  Program Lemma Forall_vector {A} {P:A->Prop} {n:nat} (l:vector A n)
    : (forall i pf, P (vector_nth i pf l)) ->
      Forall P l.
  Proof.
    destruct l; simpl; subst.
    induction x; simpl; intros.
    - constructor.
    - constructor.
      + apply (H 0%nat ltac:(lia)).
      + apply IHx; intros.
        specialize (H (S i) (ltac:(lia))).
        unfold vector_nth, proj1_sig in *.
        match_destr.
        match_destr_in H.
        simpl in *.
        congruence.
  Defined.

  Lemma vector_nthS {A} a i (l:list A) pf1 pf2 :
    (vector_nth (S i) pf1
                (exist (fun l0 : list A => length l0 = S (length l)) (a :: l) pf2))
    = vector_nth i (lt_S_n _ _ pf1) (exist (fun l0 : list A => length l0 = length l) (l) (eq_add_S _ _ pf2)).
  Proof.
    unfold vector_nth, proj1_sig.
    repeat match_destr.
    simpl in *.
    congruence.
  Qed.

  Lemma Forallt_map_length {A B} {X:A->Type} (f:forall a : A, X a -> B) (l:list A) (ft:Forallt X l) :
    length (Forallt_map f ft) = length l.
  Proof.
    induction ft; simpl; trivial.
    now rewrite IHft.
  Qed.

  Lemma SimpleRandomVariable_exist2_part
        (l : list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & SimpleRandomVariable rv_X})) : 
    SimpleRandomVariable
      (fold_right rvplus (const 0) (map (fun '(existT2 x _ _) => x) l)).
  Proof.
    induction l; simpl.
    - typeclasses eauto.
    - destruct a; simpl.
      typeclasses eauto.
  Defined.

  Lemma RandomVariable_exist2_part
        (l : list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & SimpleRandomVariable rv_X})) : 
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
             {srv:SimpleRandomVariable rv_X} :
    list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & SimpleRandomVariable rv_X})
    := proj1_sig (vector_create 0 n
                                (fun i _ pf => existT2 _ _ _ (vec_rv _ i pf rv) (vec_srv _ i pf srv))).
  
  Lemma SimpleExpectation_fold_rvplus'
        (l : list ({rv_X:Ts -> R & RandomVariable dom borel_sa rv_X & SimpleRandomVariable rv_X})) : 
    SimpleExpectation (fold_right rvplus (const 0) (map (fun '(existT2 x _ _) => x) l)) (srv:=SimpleRandomVariable_exist2_part l) =
    list_sum (map (fun '(existT2 x _ sx)  => SimpleExpectation x (srv:=sx)) l).
  Proof.
    induction l; simpl.
    - now rewrite SimpleExpectation_const.
    - destruct a; simpl.
      rewrite <- IHl.
      rewrite sumSimpleExpectation; trivial.
      apply RandomVariable_exist2_part.
  Qed.

  Lemma make_simple_vector_package_proj1 {n} (rv_X:Ts -> vector R n)
        {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
        {srv:SimpleRandomVariable rv_X} :
    (map (fun '(@existT2 _ _ _ x _ _) => x) (make_simple_vector_package rv_X)) = proj1_sig (fun_to_vector_to_vector_of_funs rv_X).
  Proof.
    unfold make_simple_vector_package; simpl.
    rewrite vector_list_create_map.
    apply vector_list_create_ext; intros.
    now rewrite vector_nth_fun_to_vector.
  Qed.    
  
  Lemma SimpleExpectation_rvsum {n} (rv_X : Ts -> vector R n)
        {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
        {srv1:SimpleRandomVariable rv_X} :
    SimpleExpectation (vecrvsum rv_X) 
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
      rewrite fold_right_rv_inner.
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
    rewrite <- (SimpleExpectation_ext _ _ eqq1) in HH.
    rewrite HH.
    f_equal.
    clear.
    unfold make_simple_vector_package; simpl.
    now rewrite vector_list_create_map.
  Qed.
  
  Lemma SimpleExpectation_rvinner {n} (rv_X1 rv_X2 : Ts -> vector R n)
        {rv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {srv1:SimpleRandomVariable rv_X1}
        {srv2:SimpleRandomVariable rv_X2} :
    SimpleExpectation (rvinner rv_X1 rv_X2)
    = 
    Rvector_sum
      (vector_create 
         0 n 
         (fun m _ pf => 
            SimpleExpectation (rvmult (vector_nth m pf (iso_f rv_X1))
                                      (vector_nth m pf (iso_f rv_X2)))  )).
  Proof.
    generalize (rvinner_unfold rv_X1 rv_X2); intros.
    rewrite (SimpleExpectation_ext _ _ H).
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
    apply Rvector_mult_rv; trivial.
  Qed.

  Instance vec_gen_condexp_rv {n}
        (rv_X : Ts -> vector R n)
        {rv:RandomVariable dom (Rvector_borel_sa n) rv_X}
        {srv : SimpleRandomVariable rv_X}
        (l : list dec_sa_event) :
    RandomVariable dom (Rvector_borel_sa n)
                   (vector_gen_SimpleConditionalExpectation rv_X l).
  Proof.
    unfold vector_gen_SimpleConditionalExpectation.
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
    
   Lemma simple_expection_rvinner_measurable {n}
        (rv_X1 rv_X2 : Ts -> vector R n)
        {rv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} 
        (l : list dec_sa_event) :
    is_partition_list (map dsa_event l) ->
    partition_measurable rv_X1 (map dsa_event l) ->
    SimpleExpectation (rvinner rv_X1 rv_X2) =
    SimpleExpectation (rvinner rv_X1 (vector_gen_SimpleConditionalExpectation rv_X2 l)).
     Proof.
       intros.
       rewrite SimpleExpectation_rvinner; trivial.
       rewrite SimpleExpectation_rvinner; trivial.
       f_equal.
       apply vector_create_ext.
       intros.
       erewrite gen_conditional_tower_law with (l0 := l); trivial.
       - apply SimpleExpectation_ext.
         rewrite gen_conditional_scale_measurable; trivial.
         + intro x.
           f_equal.
           unfold vector_gen_SimpleConditionalExpectation.
           rewrite iso_f_b.
           now rewrite vector_nth_create'.
         + unfold partition_measurable.
           unfold partition_measurable in H0.
           intros.
           cut_to H0; trivial.
           specialize (H0 p H2).
           destruct H0 as [cvec [? ?]].
           exists (vector_nth i pf2 cvec).
           destruct srv1.
           unfold RandomVariable.srv_vals; simpl.
           split.
           * unfold RandomVariable.srv_vals in H0; simpl in H0.
             rewrite in_map_iff.
             exists cvec.
             tauto.
           * rewrite vector_nth_fun_to_vector.
             unfold event_sub, event_preimage, event_singleton in *.
             intros.
             now rewrite H3.
       - typeclasses eauto.
       - typeclasses eauto.         
    Qed.       
         
    Instance rvinner_proper {n} :
      Proper (rv_eq ==> rv_eq ==> rv_eq) (@rvinner n).
    Admitted.

   Lemma simple_expection_rvinner_measurable_zero {n}
        (rv_X1 rv_X2 : Ts -> vector R n)
        {rv1:RandomVariable dom (Rvector_borel_sa n) rv_X1}
        {rv2:RandomVariable dom (Rvector_borel_sa n) rv_X2}
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} 
        (l : list dec_sa_event) :
    rv_eq (vector_gen_SimpleConditionalExpectation rv_X2 l) (const Rvector_zero) ->
    is_partition_list (map dsa_event l) ->
    partition_measurable rv_X1 (map dsa_event l) ->
    SimpleExpectation (rvinner rv_X1 rv_X2) = 0.
   Proof.
     intros.
     rewrite simple_expection_rvinner_measurable with (l0 := l); trivial.
     assert (rv_eq  
               (rvinner rv_X1 (vector_gen_SimpleConditionalExpectation rv_X2 l))
               (const 0)).
     {
       rewrite H.
       intro v.
       now generalize (hilbert.inner_zero_r (rv_X1 v) ).
     }
     rewrite (SimpleExpectation_ext _ _ H2).
     now rewrite SimpleExpectation_const.
  Qed.

  (* if l is viewed as finite generators for a sigma algebra, this shows that
    we can factor out l-measurable random variables from conditional expectation *)
(*
  Lemma vector_gen_conditional_scale_measurable {n}
        (rv_X1 rv_X2 : Ts -> vector R n)
        {srv1 : SimpleRandomVariable rv_X1}
        {srv2 : SimpleRandomVariable rv_X2} 
        (l : list dec_sa_event) :
    is_partition_list (map dsa_event l) ->
    partition_measurable rv_X1 (map dsa_event l) ->
    rv_eq (gen_SimpleConditionalExpectation (rvinner rv_X1 rv_X2) l)
          (rvinner rv_X1 (vector_gen_SimpleConditionalExpectation rv_X2 l  )).
  Proof.
    intros.
    intro v.
    generalize (@rvinner_unfold n); intros.
    rewrite H1.
    rewrite (gen_SimpleConditionalExpectation_ext _ _ l (H1 rv_X1 rv_X2)).
    generalize (vecrvsum_rvsum (vecrvmult rv_X1 rv_X2)); intros.
*)

End vector_ops.
