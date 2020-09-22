Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad Permutation fixed_point Finite LibUtils. 
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import Streams StreamAdd. 
Require Import mdp.
Require Import Vector.
Require Import Lia.

Import ListNotations. 
Set Bullet Behavior "Strict Subproofs".


Section turtle.

  Inductive turtle_color : Set := 
    turtle_green
  | turtle_white
  | turtle_star
  | turtle_red.

  Instance turtle_color_dec : EqDec turtle_color eq.
  Proof.
    change (forall (x y:turtle_color), {x = y} + {x <> y}).
    decide equality.
  Defined.

  Definition turtle_grid max_x max_y := Matrix turtle_color max_x max_y.

  Definition turtle_state max_x max_y :=  prod ({x:nat | x < max_x}%nat) ({y:nat | y < max_y}%nat).
  
  Instance turtle_state_dec max_x max_y : EqDec (turtle_state max_x max_y) eq.
  Proof.
    intros [[x1 pfx1] [y1 pfy1]] [[x2 pfx2] [y2 pfy2]].
    destruct (x1 == x2).
    - destruct (y1 == y2).
      + left.
        destruct e; destruct e0.
        erewrite (index_pf_irrel _ _ pfx1).
        erewrite (index_pf_irrel _ _ pfy1).
        reflexivity.
      + right; congruence.
    - right; congruence.
  Defined.

  Inductive turtle_action
    := Up
     | Down
     | Left
     | Right.

  Instance turtle_action_dec : EqDec turtle_action eq.
  Proof.
    change (forall (x y:turtle_action), {x = y} + {x <> y}).
    decide equality.
  Defined.


  Instance bounded_nat_finite n : Finite {x : nat | (x < n)%nat}.
  Admitted.

  Instance turtle_state_finite max_x max_y : Finite (turtle_state max_x max_y).
  Proof.
    apply finite_prod; apply bounded_nat_finite.
  Defined.

  Instance turtle_action_finite : Finite turtle_action.
  Proof.
    exists (Up::Down::Left::Right::nil).
    destruct x; simpl; tauto.
  Qed.

  Program Instance turtle_state_nonempty max_x max_y : NonEmpty (turtle_state (S max_x) (S max_y))
    := ((0, 0))%nat.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Instance turtle_action_nonempty : NonEmpty turtle_action
    := Up.

  Definition color_reward (c:turtle_color) : R
    := match c with
         turtle_green => 2
       | turtle_white => 0
       | turtle_star => 1
       | turtle_red => -10
       end.

  Definition turtle_reward {max_x max_y} (grid:turtle_grid max_x max_y) (state:turtle_state max_x max_y): R
    := let '(x,y) := state in
       let color := grid x y in
       color_reward color.

  Definition turtle_move (s:turtle_state) : option turtle_state
    := Up
     | Down
     | Left
     | Right.
  
  Definition turtle_prob_t (s:turtle_state) (a:turtle_action) : Pmf turtle_state
    := let '(x,y) := s in
       match a with
       | Up => 
       | Down =>
       | Left
       | Right
       end.

  Definition turtle_mdp {max_x max_y} (grid:turtle_grid max_x max_y) : MDP :=
    {|
    state := turtle_state max_x max_y;
    act _ := turtle_action;
    st_eqdec := turtle_state_dec max_x max_y;
    fs := turtle_state_finite max_x max_y;
    fa _ := turtle_action_finite;
    ne := turtle_state_nonempty max_x max_y;
    na _ := turtle_action_nonempty ;
    t := turtle_prob_t ;
    reward _ _ s' := turtle_reward grid s'
    |}.
    
