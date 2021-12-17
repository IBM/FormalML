Require Import LibUtils List RealAdd.
Require Import Reals Psatz Morphisms.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Program.Basics.

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Coquelicot.Rcomplements.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Markov Coquelicot.Hierarchy.
Require Import Coquelicot.Rcomplements Coquelicot.Rbar Coquelicot.Markov Coquelicot.Iter Coquelicot.Lub.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.

Require Coquelicot.Lim_seq.

Require Import Classical_Pred_Type.

Section lub.
  Definition is_ub_ERbar (E : Rbar -> Prop) (l : Rbar) :=
    forall (x : Rbar), E x -> Rbar_le x l.
  
  Definition is_lb_ERbar (E : Rbar -> Prop) (l : Rbar) :=
    forall (x : Rbar), E x -> Rbar_le l x.

  Lemma is_ub_ERbar_opp (E : Rbar -> Prop) (l : Rbar) :
    is_lb_ERbar E l <-> is_ub_ERbar (fun x => E (Rbar_opp x)) (Rbar_opp l).
  Proof.
    split ; intros Hl x Hx ; apply Rbar_opp_le.
    - now rewrite Rbar_opp_involutive ; apply Hl.
    - now apply Hl ; rewrite Rbar_opp_involutive.
  Qed.
  
  Lemma is_lb_ERbar_opp (E : Rbar -> Prop) (l : Rbar) :
    is_ub_ERbar E l <-> is_lb_ERbar (fun x => E (Rbar_opp x)) (Rbar_opp l).
  Proof.
    split ; intros Hl x Hx ; apply Rbar_opp_le.
    now rewrite Rbar_opp_involutive ; apply Hl.
    now apply Hl ; rewrite Rbar_opp_involutive.
  Qed.

  (** Decidability *)
  
  Lemma is_ub_ERbar_dec (E : Rbar -> Prop) :
    {l : R | is_ub_ERbar E l} + {(forall l : R, ~is_ub_ERbar E l)}.
  Proof.
    (* first we check p_infty *)
    destruct (is_ub_Rbar_dec (fun _ => E p_infty)).
    - destruct (is_ub_Rbar_dec (fun x => E x)).
      + left.
        destruct s as [x HH1].
        destruct s0 as [l HH2].
        unfold is_ub_Rbar in *.
        exists l; intros ??.
        destruct x0.
        * auto.
        * specialize (HH1 (x + 1) H).
          simpl in HH1; lra.
        * now simpl.
      + right; intros ? HH1.
        apply (n l); intros ? HH2.
        now apply HH1.
    - right; intros ??.
      apply (n l); intros ??.
      red in H.
      specialize (H _ H0); simpl in H; contradiction.
  Qed.

  Lemma is_lb_ERbar_dec (E : Rbar -> Prop) :
    {l : R | is_lb_ERbar E l} + {(forall l : R, ~is_lb_ERbar E l)}.
  Proof.
    destruct (is_ub_ERbar_dec (fun x => E (Rbar_opp x))) as [ [l Hl] | Hl ].
    left ; exists (Rbar_opp l).
    by apply is_ub_ERbar_opp ; rewrite (Rbar_opp_involutive l).
    right => l.
    specialize (Hl (Rbar_opp l)).
    contradict Hl.
    by apply (is_ub_ERbar_opp E l).
  Qed.

  (** Order *)

  Lemma is_ub_ERbar_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
    (forall x : Rbar, E2 x -> E1 x) -> is_ub_ERbar E1 l -> is_ub_ERbar E2 l.
  Proof.
    move => H ub1 x Hx.
    apply: ub1 ; by apply: H.
  Qed.
  
  Lemma is_lb_ERbar_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
    (forall x : Rbar, E2 x -> E1 x) -> is_lb_ERbar E1 l -> is_lb_ERbar E2 l.
  Proof.
    move => H ub1 x Hx.
    apply: ub1 ; by apply: H.
  Qed.

  Global Instance is_ub_ERbar_le_proper : Proper (pointwise_relation _ impl --> Rbar_le ==> impl) is_ub_ERbar.
  Proof.
    intros ???????.
    eapply is_ub_ERbar_subset; try eapply H.
    intros ??.
    eapply Rbar_le_trans; try apply H1; trivial.
  Qed.
  
  Global Instance is_lb_ERbar_le_proper : Proper (pointwise_relation _ impl --> Rbar_le --> impl) is_lb_ERbar.
  Proof.
    intros ???????.
    eapply is_lb_ERbar_subset; try eapply H.
    intros ??.
    eapply Rbar_le_trans; try apply H1; trivial.
  Qed.

  (** ** Least upper bound and Greatest Lower Bound *)

  Definition is_lub_ERbar (E : Rbar -> Prop) (l : Rbar) :=
    is_ub_ERbar E l /\ (forall b, is_ub_ERbar E b -> Rbar_le l b).
  Definition is_glb_ERbar (E : Rbar -> Prop) (l : Rbar) :=
    is_lb_ERbar E l /\ (forall b, is_lb_ERbar E b -> Rbar_le b l).

  Lemma is_lub_ERbar_opp (E : Rbar -> Prop) (l : Rbar) :
    is_glb_ERbar E l <-> is_lub_ERbar (fun x => E (Rbar_opp x)) (Rbar_opp l).
  Proof.
    split => [[lb glb] | [ub lub] ] ; split.
    by apply is_ub_ERbar_opp.
    intros b Hb.
    apply Rbar_opp_le ; rewrite Rbar_opp_involutive.
    apply glb, is_ub_ERbar_opp ; by rewrite Rbar_opp_involutive.
    by apply is_ub_ERbar_opp.
    intros b Hb.
    apply Rbar_opp_le.
    by apply lub, is_ub_ERbar_opp.
  Qed.
  Lemma is_glb_ERbar_opp (E : Rbar -> Prop) (l : Rbar) :
    is_lub_ERbar E l <-> is_glb_ERbar (fun x => E (Rbar_opp x)) (Rbar_opp l).
  Proof.
    split => [[lb glb] | [ub lub] ] ; split.
    by apply is_lb_ERbar_opp.
    intros b Hb.
    apply Rbar_opp_le ; rewrite Rbar_opp_involutive.
    apply glb, is_lb_ERbar_opp ; by rewrite Rbar_opp_involutive.
    by apply is_lb_ERbar_opp.
    intros b Hb.
    apply Rbar_opp_le.
    by apply lub, is_lb_ERbar_opp.
  Qed.

  (** Existence *)

  Lemma ex_lub_ERbar (E : Rbar -> Prop) : {l : Rbar | is_lub_ERbar E l}.
  Proof.
    destruct (is_ub_ERbar_dec E).
    - destruct s as [s slb].
      assert (~ E p_infty).
      {
        intros ?.
        specialize (slb _ H).
        now simpl in slb.
      } 
      destruct (ex_lub_Rbar E) as [x [xlb xglb]].
      + exists x.
        split.
        * intros ??.
          red in xlb.
          destruct x0; auto; simpl; tauto.
        * firstorder.
    - exists p_infty.
      split.
      + now intros [].
      + intros [] ?.
        * now elim (n r).
        * by simpl.
        * elim (n 0%R).
          now apply (is_ub_ERbar_le_proper _ _ (reflexivity _) m_infty); simpl.
  Qed.

  Lemma ex_glb_ERbar (E : Rbar -> Prop) : {l : Rbar | is_glb_ERbar E l}.
  Proof.
    case: (ex_lub_ERbar (fun x => E (Rbar_opp x))) => l Hl.
    exists (Rbar_opp l).
    apply is_lub_ERbar_opp ; by rewrite Rbar_opp_involutive.
  Qed.

  (** Functions *)

  Definition ERbar_lub (E : Rbar -> Prop) := proj1_sig (ex_lub_ERbar E).
  Definition ERbar_glb (E : Rbar -> Prop) := proj1_sig (ex_glb_ERbar E).

  Lemma ERbar_opp_glb_lub (E : Rbar -> Prop) :
    ERbar_glb (fun x => E (Rbar_opp x)) = Rbar_opp (ERbar_lub E).
  Proof.
    unfold ERbar_glb ; case (ex_glb_ERbar _) ; simpl ; intros g [Hg Hg'] ;
      unfold ERbar_lub ; case (ex_lub_ERbar _) ; simpl ; intros l [Hl Hl'] ;
      apply Rbar_le_antisym.
    apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hl', Rbar_lb_ub ;
      rewrite Rbar_opp_involutive ; auto.
    apply Hg', Rbar_lb_ub ; auto.
  Qed.
  Lemma ERbar_opp_lub_glb (E : Rbar -> Prop) :
    ERbar_lub (fun x => E (Rbar_opp x)) = Rbar_opp (ERbar_glb E).
  Proof.
    unfold ERbar_glb ; case (ex_glb_ERbar _) ; simpl ; intros g (Hg, Hg') ;
      unfold ERbar_lub ; case (ex_lub_ERbar _) ; simpl ; intros l [Hl Hl'] ;
      apply Rbar_le_antisym.
    apply Hl', Rbar_lb_ub ; rewrite Rbar_opp_involutive ;
      apply (Rbar_is_lb_subset _ E) ; auto ; intros x ; rewrite Rbar_opp_involutive ; auto.
    apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hg', Rbar_ub_lb ;
      rewrite Rbar_opp_involutive ; auto.
  Qed.

  Lemma is_lub_ERbar_unique (E : Rbar -> Prop) (l : Rbar) :
    is_lub_ERbar E l -> ERbar_lub E = l.
  Proof.
    move => H.
    rewrite /ERbar_lub.
    case: ex_lub_ERbar => l0 H0 /=.
    apply Rbar_le_antisym.
    apply H0, H.
    apply H, H0.
  Qed.
  Lemma ERbar_is_glb_unique (E : Rbar -> Prop) (l : Rbar) :
    is_glb_ERbar E l -> ERbar_glb E = l.
  Proof.
    move => H.
    rewrite /ERbar_glb.
    case: ex_glb_ERbar => l0 H0 /=.
    apply Rbar_le_antisym.
    apply H, H0.
    apply H0, H.
  Qed.

  (** Order *)

  Lemma ERbar_glb_le_lub (E : Rbar -> Prop) :
    (exists x, E x) -> Rbar_le (ERbar_glb E) (ERbar_lub E).
  Proof.
    case => x Hex.
    apply Rbar_le_trans with x.
    unfold ERbar_glb ; case (ex_glb_ERbar _) ; simpl ; intros g (Hg, _) ; apply Hg ; auto.
    unfold ERbar_lub ; case (ex_lub_ERbar _) ; simpl ; intros l (Hl, _) ; apply Hl ; auto.
  Qed.

  Lemma is_lub_ERbar_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
    (forall x, E1 x -> E2 x) -> (is_lub_ERbar E1 l1) -> (is_lub_ERbar E2 l2)
    -> Rbar_le l1 l2.
  Proof.
    intros Hs (_,H1) (H2, _).
    apply H1 ; intros x Hx ; apply H2, Hs, Hx.
  Qed.
  Lemma is_glb_ERbar_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
    (forall x, E2 x -> E1 x) -> (is_glb_ERbar E1 l1) -> (is_glb_ERbar E2 l2)
    -> Rbar_le l1 l2.
  Proof.
    intros Hs (H1, _) (_, H2).
    apply H2 ; intros x Hx ; apply H1, Hs, Hx.
  Qed.

  Lemma is_lub_ERbar_eq (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
    (forall x, E1 x <-> E2 x) -> (is_lub_ERbar E1 l1) -> (is_lub_ERbar E2 l2)
    -> l1 = l2.
  Proof.
    intros Hs H1 H2 ; apply Rbar_le_antisym ;
      [apply (is_lub_ERbar_subset E1 E2) | apply (is_lub_ERbar_subset E2 E1) ] ; auto ; intros x H ;
      apply Hs ; auto.
  Qed.
  Lemma is_glb_ERbar_eq (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
    (forall x, E1 x <-> E2 x) -> (is_glb_ERbar E1 l1) -> (is_glb_ERbar E2 l2)
    -> l1 = l2.
  Proof.
    intros Hs H1 H2 ; apply Rbar_le_antisym ;
      [apply (is_glb_ERbar_subset E1 E2) | apply (is_glb_ERbar_subset E2 E1) ] ; auto ; intros x H ;
      apply Hs ; auto.
  Qed.

  Lemma is_lub_ERbar_ext (E1 E2 : Rbar -> Prop) (l : Rbar) :
    (forall x, E1 x <-> E2 x) -> (is_lub_ERbar E1 l) -> (is_lub_ERbar E2 l).
  Proof.
    intros Heq (H1,H2) ; split.
    apply (Rbar_is_ub_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
    intros b Hb ; apply H2 ; apply (Rbar_is_ub_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
  Qed.
  Lemma is_glb_ERbar_ext (E1 E2 : Rbar -> Prop) (l : Rbar) :
    (forall x, E1 x <-> E2 x) -> (is_glb_ERbar E1 l) -> (is_glb_ERbar E2 l).
  Proof.
    intros Heq (H1, H2) ; split.
    apply (Rbar_is_lb_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
    intros b Hb ; apply H2 ; apply (Rbar_is_lb_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
  Qed.

  Lemma ERbar_lub_subset (E1 E2 : Rbar -> Prop) :
    (forall x, E1 x -> E2 x) -> Rbar_le (ERbar_lub E1) (ERbar_lub E2).
  Proof.
    intros Hs ; unfold ERbar_lub ; case (ex_lub_ERbar E1) ; intros l1 Hl1 ;
      case (ex_lub_ERbar E2) ; simpl ; intros l2 Hl2 ; apply (is_lub_ERbar_subset E1 E2) ; auto.
  Qed.
  Lemma ERbar_glb_subset (E1 E2 : Rbar -> Prop) :
    (forall x, E2 x -> E1 x) -> Rbar_le (ERbar_glb E1) (ERbar_glb E2).
  Proof.
    intro Hs ; unfold ERbar_glb ; case (ex_glb_ERbar E1) ; intros l1 Hl1 ;
      case (ex_glb_ERbar E2) ; simpl ; intros l2 Hl2 ; apply (is_glb_ERbar_subset E1 E2) ; auto.
  Qed.

  Lemma ERbar_lub_rw (E1 E2 : Rbar -> Prop) :
    (forall x, E1 x <-> E2 x) -> ERbar_lub E1 = ERbar_lub E2.
  Proof.
    intro Hs ; apply Rbar_le_antisym ; apply ERbar_lub_subset ; intros x H ; apply Hs ; auto.
  Qed.
  Lemma ERbar_glb_rw (E1 E2 : Rbar -> Prop) :
    (forall x, E1 x <-> E2 x) -> ERbar_glb E1 = ERbar_glb E2.
  Proof.
    intros Hs ; apply Rbar_le_antisym ; apply ERbar_glb_subset ; intros x H ; apply Hs ; auto.
  Qed.

  (** * Emptiness is decidable *)

  Definition EEmpty (E : Rbar -> Prop) :=
    ERbar_lub (fun x => x = 0 \/ E x) = ERbar_glb (fun x => x = 0 \/ E x)
    /\ ERbar_lub (fun x => x = 1 \/ E x) = ERbar_glb (fun x => x = 1 \/ E x).

  Lemma EEmpty_correct_1 (E : Rbar -> Prop) :
    EEmpty E -> forall x, ~ E x.
  Proof.
    case => E0 E1 x Ex.
    rewrite /ERbar_lub /ERbar_glb in E0 ;
      case : (ex_lub_ERbar (fun x : Rbar => x = 0 \/ E x)) E0 => /= s0 Hs0 ;
                                                        case : (ex_glb_ERbar (fun x : Rbar => x = 0 \/ E x)) => i0 Hi0 /= E0.
    have : (x = 0) ; last move => {s0 Hs0 i0 Hi0 E0}.
    apply Rbar_le_antisym.
    apply (Rbar_le_trans x s0 0).
    apply Hs0 ; by right.
    rewrite E0 ; apply Hi0 ; by left.
    apply (Rbar_le_trans 0 s0 x).
    apply Hs0 ; by left.
    rewrite E0 ; apply Hi0 ; by right.
    rewrite /ERbar_lub /ERbar_glb in E1 ;
      case : (ex_lub_ERbar (fun x : Rbar => x = 1 \/ E x)) E1 => /= s1 Hs1 ;
                                                        case : (ex_glb_ERbar (fun x : Rbar => x = 1 \/ E x)) => i1 Hi1 /= E1.
    have : (x = 1) ; last move => {s1 Hs1 i1 Hi1 E1}.
    apply Rbar_le_antisym.
    apply (Rbar_le_trans x s1 1).
    apply Hs1 ; by right.
    rewrite E1 ; apply Hi1 ; by left.
    apply (Rbar_le_trans 1 s1 x).
    apply Hs1 ; by left.
    rewrite E1 ; apply Hi1 ; by right.
    intros HH1 HH2.
    invcs HH2.
    invcs H.
    now apply R1_neq_R0.
  Qed.

  Lemma EEmpty_correct_2 (E : Rbar -> Prop) :
    (forall x, ~ E x) -> EEmpty E.
  Proof.
    move => H ; split ;
           rewrite /ERbar_glb /ERbar_lub ;
           [ case : (ex_lub_ERbar (fun x : Rbar => x = 0 \/ E x)) => s0 Hs0 ;
                                                            case : (ex_glb_ERbar (fun x : Rbar => x = 0 \/ E x)) => i0 Hi0 /=
           | case : (ex_lub_ERbar (fun x : Rbar => x = 1 \/ E x)) => s1 Hs1 ;
                                                                case : (ex_glb_ERbar (fun x : Rbar => x = 1 \/ E x)) => i1 Hi1 /=].
    - assert (s0 = Finite 0).
      {
        apply Rbar_le_antisym; [| apply Hs0; tauto].
        apply Hs0.
        red; intros ? [].
        - now subst; simpl.
        - now contradict H0.
      }
      assert (i0 = Finite 0).
      {
        apply Rbar_le_antisym; [apply Hi0; tauto |].
        apply Hi0.
        red; intros ? [].
        - now subst; simpl.
        - now contradict H1.
      }
      congruence.
    - assert (s1 = Finite 1).
      {
        apply Rbar_le_antisym; [| apply Hs1; tauto].
        apply Hs1.
        red; intros ? [].
        - now subst; simpl.
        - now contradict H0.
      }
      assert (i1 = Finite 1).
      {
        apply Rbar_le_antisym; [apply Hi1; tauto |].
        apply Hi1.
        red; intros ? [].
        - now subst; simpl.
        - now contradict H1.
      }
      congruence.
  Qed.

  Lemma EEmpty_dec (E : Rbar -> Prop) :
    {~EEmpty E}+{EEmpty E}.
  Proof.
    case: (Rbar_eq_dec (ERbar_lub (fun x => x = 0 \/ E x)) (ERbar_glb (fun x => x = 0 \/ E x))) => H0 ;
                                                                                        [ | left].
    case: (Rbar_eq_dec (ERbar_lub (fun x => x = 1 \/ E x)) (ERbar_glb (fun x => x = 1 \/ E x))) => H1 ;
                                                                                        [by right | left].
    contradict H1 ; apply H1.
    contradict H0 ; apply H0.
  Qed.
  Lemma not_EEmpty_dec (E : Rbar -> Prop) : (Decidable.decidable (exists x, E x)) ->
                                    {(exists x, E x)} + {(forall x, ~ E x)}.
  Proof.
    move => He ;
           case: (EEmpty_dec E) => Hx ;
                                 [left|right].
    case: He => // He.
    contradict Hx ;
      apply: EEmpty_correct_2 => x ; contradict He ; by exists x.
                                                        by apply: EEmpty_correct_1.
  Qed.

  Lemma Euniqueness_dec P : (exists ! x : Rbar, P x) -> {x : Rbar | P x}.
  Proof.
    move => H.
    exists (ERbar_lub P).
    case: H => x [? Hx].
    replace (ERbar_lub P) with x; trivial.
    apply sym_eq, is_lub_ERbar_unique.
    split.
    move => y Hy.
    rewrite (Hx _ Hy); apply Rbar_le_refl.
    firstorder.
  Qed.

End lub.
