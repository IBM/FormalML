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

  Program Definition turtle_move {max_x max_y} (s:turtle_state max_x max_y) (a:turtle_action) :
    option (turtle_state max_x max_y)
    := (let '(x,y) := s in
       match a with
       | Up => if y == 0 then None else Some (x, y-1)
       | Down => if lt_dec (y+1) max_y then Some (x, y+1) else None
       | Left => if x == 0 then None else Some (x-1, y)
       | Right => if lt_dec (x+1) max_x then Some (x+1, y) else None
       end)%nat.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Definition turtle_action_opp (a:turtle_action) : turtle_action
    := match a with 
       | Up => Down
       | Down => Up
       | Left => Right
       | Right => Left
       end.

  Program Definition turtle_confused_outcomes {max_x max_y} (correct_s oops_s:turtle_state max_x max_y) : Pmf (turtle_state max_x max_y)
    := {|
    outcomes := (mknonnegreal 0.75 _, correct_s)::(mknonnegreal 0.25 _, oops_s)::nil
      |}.
  Next Obligation.
    lra.
  Qed.
  Next Obligation.
    lra.
  Qed.
  Next Obligation.
    lra.
  Qed.
  
  Definition turtle_prob_t {max_x max_y} (s:turtle_state max_x max_y) (a:turtle_action) : Pmf (turtle_state max_x max_y)
    := let '(x,y) := s in
       match turtle_move s a, turtle_move s (turtle_action_opp a) with
       | Some correct_s, Some oops_s => turtle_confused_outcomes correct_s oops_s
       | Some next_s, None => Pmf_pure next_s
       | None, Some next_s => Pmf_pure next_s
       (* This grid is one or zero dimensional, so just stay still *)
       | None, None => Pmf_pure s
       end.

  Definition turtle_mdp {max_x max_y} (grid:turtle_grid (S max_x) (S max_y)) : MDP :=
    {|
    state := turtle_state (S max_x) (S max_y);
    act _ := turtle_action;
    st_eqdec := turtle_state_dec (S max_x) (S max_y);
    fs := turtle_state_finite (S max_x) (S max_y);
    fa _ := turtle_action_finite;
    ne := turtle_state_nonempty max_x max_y;
    na _ := turtle_action_nonempty ;
    t := turtle_prob_t ;
    reward _ _ s' := turtle_reward grid s'
    |}.

  
End turtle.
