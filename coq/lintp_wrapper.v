From Coq Require Import Reals.
From Coquelicot Require Import Coquelicot.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Import RealRandomVariable.
Require Import AlmostEqual.
Require Import Event.
Require Import SigmaAlgebras.
Require Import ProbSpace.
Require Import BorelSigmaAlgebra.
Require Import LInt_p.sigma_algebra.
Require Import LInt_p.measure.
Require Import LInt_p.measurable_fun.
Require Import LInt_p.LInt_p.
Require Import LInt_p.sigma_algebra_R_Rbar.
Require Import LInt_p.sum_Rbar_nonneg.
Require Import LInt_p.Rbar_compl.
Require Import Classical.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

Definition lintp_borel_sa : SigmaAlgebra R := generated_sa gen_R_uc.

Program Instance measurable_sigma_algebra {T} (F:pre_event T -> Prop) : SigmaAlgebra T
  := { sa_sigma := measurable F }.
Next Obligation.
  now apply measurable_union_countable.
Qed.
Next Obligation.
  apply measurable_compl.
  unfold pre_event_complement.
  apply measurable_ext with (A).
  intro x; tauto.
  apply H.
Qed.
Next Obligation.
  apply measurable_compl.
  unfold pre_Ω.
  apply measurable_ext with (fun _ => False).
  tauto.
  apply measurable_empty.
Qed.

Theorem measurable_sa {T} (F:pre_event T -> Prop) : 
  forall a, prob_space_closure F a <-> measurable F a.
Proof.
  split; intros.
  - induction H.
    + unfold pre_Ω.
      apply measurable_compl.
      apply measurable_ext with (fun _ => False).
      tauto.
      apply measurable_empty.
    + now apply measurable_gen.
    + now apply measurable_union_countable.
    + apply measurable_compl.
      unfold pre_event_complement.
      apply measurable_ext with (q).
      intro; tauto.
      trivial.
  - induction H.
    + now apply psc_refl. 
    + assert (@pre_event_equiv T (fun _ => False) (pre_event_complement (fun _ => True))).
      {
        intro x.
        unfold pre_event_complement.
        tauto.
      }
      rewrite H.
      apply psc_complement.
      apply psc_all.
    + assert (@pre_event_equiv T A (pre_event_complement (fun x => ~ A x))).
      {
        intro x.
        unfold pre_event_complement.
        tauto.
      }
      rewrite H0.
      now apply psc_complement.
    + now apply psc_countable.
Qed.

Definition dec_pre_event {Ts} (dom : SigmaAlgebra Ts) ( A : pre_event Ts) :
  {sa_sigma A} + {~ sa_sigma A} :=
  ClassicalDescription.excluded_middle_informative (sa_sigma A).

Program Definition ps_P_pre {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) :
  (pre_event Ts -> R) :=
  fun (A : pre_event Ts) =>
    if (dec_pre_event dom A) then ps_P A else 0.

Lemma ps_P_pre_sa_sigma {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) 
        (E : pre_event Ts) 
        (sa : sa_sigma E) :
    ps_P_pre prts E = ps_P (exist _ E sa).
  Proof.
    unfold ps_P_pre, ps_P_pre_obligation_1.
    match_destr; try easy.
    apply ps_proper.
    now intro x; simpl.
  Qed.
  
Lemma disjoint_pre_collection {T} (coll : nat -> pre_event T) :
  pre_collection_is_pairwise_disjoint coll <->
  (forall n m x, coll n x -> coll m x -> n = m).
Proof.
  unfold pre_collection_is_pairwise_disjoint.
  unfold pre_event_disjoint.
  split; intros.
  - specialize (H n m).
    assert ((n <> m) -> False).
    + intros.
      now specialize (H H2 x H0 H1).
    + tauto.
  - specialize (H n1 n2 x H1 H2).
    lia.
Qed.

Lemma measurable_pre_event {Ts} (dom : SigmaAlgebra Ts) (E : pre_event Ts) :
  measurable sa_sigma E <-> sa_sigma E.
Proof.
  split; intros.
  - induction H; trivial.
    + apply sa_none.
    + apply sa_complement in IHmeasurable.
      assert (pre_event_equiv (pre_event_complement (fun x : Ts => ~ A x))
                              A).
      * intro x.
        unfold pre_event_complement.
        tauto.
      * now rewrite H0 in IHmeasurable.
    + now apply sa_countable_union.
  - now apply measurable_gen.
 Qed.

Lemma sum_Rbar_finite (f : nat -> R) (n : nat) :
  sum_Rbar n (fun n => Finite (f n)) = Finite (sum_f_R0 f n).
Proof.
  induction n.
  - now simpl.
  - simpl.
    rewrite IHn.
    simpl.
    apply Rbar_finite_eq.
    lra.
 Qed.

(* need to create a (measure gen) from probspace. *)
Program Definition ProbSpace_measure {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) : measure sa_sigma :=
  mk_measure _ (ps_P_pre prts) _ _ _  .
Next Obligation.
  unfold ps_P_pre, ps_P_pre_obligation_1.
  match_destr.
  assert (event_equiv
            (exist sa_sigma (fun _ : Ts => False) s)
            event_none) by 
      (intro x; simpl; tauto).
  rewrite H.
  now rewrite ps_none.
Qed.
Next Obligation.
  unfold ps_P_pre.
  match_destr.
  apply ps_pos.
  lra.
Qed.
Next Obligation.
  assert (forall n, sa_sigma (A n)) by (intros; now apply measurable_pre_event).
  generalize (sa_countable_union A H1); intros.
  rewrite ps_P_pre_sa_sigma with (sa := H2).
  assert (event_equiv
            (exist sa_sigma (pre_union_of_collection A) H2) 
            (union_of_collection (fun n => exist _ (A n) (H1 n)))) by
      (intro x; now simpl).
  rewrite H3.
  generalize (ps_countable_disjoint_union (fun n => exist _ (A n) (H1 n))); intros.
  cut_to H4.
  - unfold sum_of_probs_equals in H4.
    rewrite <- infinite_sum_infinite_sum' in H4.
    rewrite <- infinite_sum_is_lim_seq in H4.
    apply lim_seq_sup_seq_incr in H4.
    + apply is_sup_seq_unique in H4.
      rewrite <- H4.
      symmetry.
      rewrite Sup_seq_ext with 
          (v :=
             (fun n => Finite (sum_f_R0 (fun m => ps_P (exist sa_sigma (A m) (H1 m))) n))).
      * apply Sup_seq_ext.
        now intros.
      * intros.
        replace (Finite (sum_f_R0 (fun m => ps_P (exist sa_sigma (A m) (H1 m))) n)) with
            (sum_Rbar n (fun m => ps_P (exist sa_sigma (A m) (H1 m)))).
        -- apply sum_Rbar_ext; intros.
           generalize (H1 i); intros.
           now rewrite ps_P_pre_sa_sigma with (sa := s).
        -- now rewrite sum_Rbar_finite.
    + intros.
      rewrite sum_f_R0_peel.
      apply Rplus_le_pos_l.
      apply ps_pos.
  - unfold collection_is_pairwise_disjoint.
    intros.
    unfold event_disjoint, pre_event_disjoint; simpl.
    intros.
    specialize (H0 n1 n2 x H6 H7).
    lia.
  Qed.
  
  Definition Rbar_Expectation_posRV {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) (f : Ts -> Rbar) := 
    LInt_p (ProbSpace_measure prts) f.

  Class Rbar_PositiveRandomVariable {Ts}
          (rv_X:Ts->Rbar) : Prop :=
    prv : forall (x:Ts), (Rbar_le 0 (rv_X x)).

  Lemma Rbar_pos_nonneg {Ts} (f : Ts -> Rbar) 
        (prv : Rbar_PositiveRandomVariable f) :
    non_neg f.
  Proof.
    easy.
  Qed.

  Lemma measurable_fun_sa_sigma {Ts} {dom : SigmaAlgebra Ts} (f : Ts -> Rbar)
        {rv : RandomVariable dom Rbar_borel_sa f} :
     measurable_fun_Rbar sa_sigma f.
  Proof.
    unfold measurable_fun_Rbar, measurable_fun.
    intros.
    unfold RandomVariable in rv.
    rewrite <- Rbar_borel_sa_preimage2 in rv.
    unfold gen_Rbar, gen_Rbar_cu in H.
    induction H.
    - destruct H.
      apply measurable_gen.
      assert (pre_event_equiv (fun x0 : Ts => A (f x0))
                              (fun x0 => Rbar_ge (f x0) x)) by (intro z; apply H).
      rewrite H0.
      now apply Rbar_sa_le_ge.
    - apply measurable_empty.
    - now apply measurable_compl.
    - now apply measurable_union_countable.
  Qed.

  Lemma Rbar_Expectation_posRV_plus {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) (f g : Ts -> Rbar) 
    {prv1 : Rbar_PositiveRandomVariable f}
    {prv2 : Rbar_PositiveRandomVariable g} 
    {rv1 : RandomVariable dom Rbar_borel_sa f}
    {rv2 : RandomVariable dom Rbar_borel_sa g}    :
    inhabited Ts ->
    Rbar_Expectation_posRV prts (fun x => Rbar_plus (f x) (g x)) = 
    Rbar_plus (Rbar_Expectation_posRV prts f) (Rbar_Expectation_posRV prts g).
  Proof.
    intros.
    unfold Rbar_Expectation_posRV.
    apply LInt_p_plus; trivial.
    now apply measurable_fun_sa_sigma.
    now apply measurable_fun_sa_sigma.    
  Qed.
    
  Lemma Rbar_Expectation_posRV_finite_ae_finite {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) (f : Ts -> Rbar)
    {prv : Rbar_PositiveRandomVariable f}
    {rv : RandomVariable dom Rbar_borel_sa f} :
    inhabited Ts ->
    is_finite (Rbar_Expectation_posRV prts f) ->
    ae (ProbSpace_measure prts) (fun x => is_finite (f x)).
  Proof.
    intros.
    apply LInt_p_ae_finite; trivial.
    now apply measurable_fun_sa_sigma.
  Qed.

  Lemma is_finite_ps_P  {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) :
    is_finite_measure (ProbSpace_measure prts).
  Proof.
    unfold is_finite_measure, ProbSpace_measure; simpl.
    generalize (sa_all); intros.
    now rewrite ps_P_pre_sa_sigma with (sa := H).
  Qed.

  Lemma sa_sigma_is_finite {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) (f : Ts -> Rbar)
    {prv : Rbar_PositiveRandomVariable f}
    {rv : RandomVariable dom Rbar_borel_sa f} :
    sa_sigma (fun x => is_finite (f x)).
  Proof.
    intros.
    assert (pre_event_equiv (fun x => is_finite (f x))
                            (fun x => Rbar_lt (f x) p_infty)).
    {
      intro x.
      case_eq (f x); intros.
      - now simpl.
      - now simpl.
      - specialize (prv x).
        rewrite H in prv.
        now simpl in prv.
    }
    rewrite H.
    apply Rbar_sa_le_lt.
    unfold RandomVariable in rv.
    now apply Rbar_borel_sa_preimage2.
  Qed.

  Lemma Rbar_Expectation_posRV_finite_ps_P_1 {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) (f : Ts -> Rbar)
    {prv : Rbar_PositiveRandomVariable f}
    {rv : RandomVariable dom Rbar_borel_sa f} :
    inhabited Ts ->
    is_finite (Rbar_Expectation_posRV prts f) ->
    ps_P (exist sa_sigma (fun x => is_finite (f x)) (sa_sigma_is_finite prts f)) = 1.
  Proof.
    intros.
    generalize (Rbar_Expectation_posRV_finite_ae_finite prts f H H0); intros.
    unfold ae in H1.
    unfold negligible in H1.
    destruct H1 as [? [? [? ?]]].
    unfold ProbSpace_measure in H3; simpl in H3.
    apply measurable_pre_event in H2.
    rewrite ps_P_pre_sa_sigma with (sa := H2) in H3.
    assert (1 - ps_P (exist sa_sigma (fun x0 => is_finite (f x0)) (sa_sigma_is_finite prts f)) = 0).
    { 
      rewrite <- ps_complement.
      generalize (ps_sub prts 
                         (event_complement (exist sa_sigma (fun x0 => is_finite (f x0)) (sa_sigma_is_finite prts f)))
                         (exist sa_sigma x H2)); intros.
      cut_to H4.
      - generalize (ps_pos (event_complement (exist sa_sigma (fun x0 => is_finite (f x0)) (sa_sigma_is_finite prts f)))); intros.
        apply Rbar_finite_eq in H3. 
        rewrite H3 in H4.
        lra.
      - intro z; simpl.
        apply H1.
    }
    lra.
  Qed.

  Lemma Rbar_Expectation_posRV_Sup_seq {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) (f : nat -> Ts -> Rbar)
    {prv : forall n, Rbar_PositiveRandomVariable (f n)}
    {rv : forall n, RandomVariable dom Rbar_borel_sa (f n)} :
    inhabited Ts ->
    (forall x n, Rbar_le (f n x) (f (S n) x)) ->
    Rbar_Expectation_posRV prts (fun x => Sup_seq (fun n => f n x)) =
    Sup_seq (fun n => Rbar_Expectation_posRV prts (f n)).
  Proof.
    intros.
    apply Beppo_Levi; trivial.
    intros.
    now apply measurable_fun_sa_sigma.
  Qed.
    
  Lemma Rbar_Expectation_posRV_monotone {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) 
        (f g : Ts -> Rbar) :
    (forall x, Rbar_le (f x) (g x)) ->
    Rbar_le (Rbar_Expectation_posRV prts f) (Rbar_Expectation_posRV prts g).
  Proof.
    apply LInt_p_monotone.
  Qed.

  Lemma measurable_fun_rv {Ts} {dom : SigmaAlgebra Ts} (f : Ts -> Rbar) :
    measurable_fun_Rbar sa_sigma f ->
    RandomVariable dom Rbar_borel_sa f.
  Proof.
    unfold measurable_fun_Rbar, RandomVariable.
    intro mfun.
    apply Rbar_borel_sa_preimage2.
    apply Rbar_sa_ge_le.
    intros.

    unfold gen_Rbar, gen_Rbar_cu in mfun.
    unfold measurable_fun in mfun.
    specialize (mfun (fun x => Rbar_ge x r)).
    induction mfun; trivial.
    - apply sa_none.
    - generalize sa_complement; intros.
      apply sa_complement in IHm.
      assert (pre_event_equiv (pre_event_complement (fun x : Ts => ~ A x)) A).
      { 
        intro x.
        unfold pre_event_complement.
        tauto.
      }
      now rewrite H0 in IHm.
    - now apply sa_countable_union.
    - apply measurable_gen.
      exists r.
      now unfold Rbar_ge.
  Qed.

  Lemma measurable_lim_seq' {Ts} (dom : SigmaAlgebra Ts)
        (f : nat -> Ts -> Rbar)
        (prv: forall n, Rbar_PositiveRandomVariable (f n))
        (rv : forall n, RandomVariable dom Rbar_borel_sa (f n)) :
    RandomVariable dom Rbar_borel_sa (fun x => Lim_seq' (fun n => f n x)).
  Proof.
    assert (forall n, measurable_fun_Rbar sa_sigma (f n)) by
        (intros; now apply measurable_fun_sa_sigma).
    apply measurable_fun_rv.
    now apply measurable_fun_Lim_seq'.
  Qed.        

  Lemma Rbar_Expectation_posRV_Lim_seq' {Ts} {dom : SigmaAlgebra Ts} (prts : ProbSpace dom) 
        (f : nat -> Ts -> Rbar)
        (prv : forall n, Rbar_PositiveRandomVariable (f n))
        (rv : forall n, RandomVariable dom Rbar_borel_sa (f n)) :
        inhabited Ts ->
        (forall x, ex_lim_seq' (fun n => f n x)) ->        
        let lim_f := fun x => Lim_seq' (fun n => f n x) in
        (forall x n, Rbar_le (f n x) (lim_f x)) ->
        Rbar_Expectation_posRV prts lim_f = Lim_seq' (fun n => Rbar_Expectation_posRV prts (f n)).
  Proof.
    intros.
    apply LInt_p_Lim_seq'; trivial.
    intros.
    now apply measurable_fun_sa_sigma.
  Qed.
        
