Require Import String.
Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad Permutation fixed_point Finite LibUtils. 
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import Streams RealAdd.
Require Import mdp.
Require Import Vector.
Require Import Lia.
Require Import ListAdd.

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

  (* Convenience method for creating a state with known in-bounds constant co-ordinates *)
  Definition make_turtle_state max_x max_y x y : if lt_dec x max_x
                                                 then if lt_dec y max_y
                                                      then turtle_state max_x max_y
                                                      else True
                                                 else True.
  Proof.
    destruct (lt_dec x max_x).
    - destruct (lt_dec y max_y).
      + apply pair.
        * exists x; trivial.
        * exists y; trivial.
      + trivial.
    - trivial.
  Defined.
  
  Instance turtle_state_finite max_x max_y : Finite (turtle_state max_x max_y).
  Proof.
    apply finite_prod; apply bounded_nat_finite.
  Defined.

  Program Definition turtle_start_state {max_x max_y} : turtle_state (S max_x) (S max_y)
    := ((0, 0))%nat.
  Next Obligation.
    lia.
  Qed.
  Next Obligation.
    lia.
  Qed.

  Program Instance turtle_state_nonempty max_x max_y : NonEmpty (turtle_state (S max_x) (S max_y))
    := turtle_start_state.

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

  Instance turtle_action_finite : Finite turtle_action.
  Proof.
    exists (Up::Down::Left::Right::nil).
    destruct x; simpl; tauto.
  Qed.

  Instance turtle_action_nonempty : NonEmpty turtle_action
    := Up.

  Definition turtle_action_opp (a:turtle_action) : turtle_action
    := match a with 
       | Up => Down
       | Down => Up
       | Left => Right
       | Right => Left
       end.
  
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
  
Section optimal_path.

  Context (γ : R).
  Context {max_x max_y : nat}.
  Context (grid : turtle_grid (S max_x) (S max_y)).
  
  Definition turtle_Rfct :=
    @Rfct_CompleteNormedModule (state (turtle_mdp grid)) (fs (turtle_mdp grid)).

  Definition turtle_init : turtle_Rfct := fun _ => 0.  

  Definition turtle_bellman_iter (n : nat) :=
    (@fixed_point.iter (CompleteNormedModule.UniformSpace R_AbsRing _)
 (@bellman_max_op (turtle_mdp grid) γ) n turtle_init).


  (* Recovering the greedy policy for each iteration n. *)
  Definition turtle_approx_dec_rule (n : nat) : dec_rule (turtle_mdp grid) :=
    fun s => argmax (act_list_not_nil s)
                 (fun a => expt_value (turtle_prob_t s a)
                                   (fun s' => reward (turtle_mdp grid) s a s' + γ*(turtle_bellman_iter n s'))).
    
End optimal_path.

  Section move.

    Definition sum_self_to_bool {A} (a:A+A) : A*bool
      := match a with
         | inl a' => (a',true)
         | inr a' => (a',false)
         end.

    Definition turtle_path max_x max_y : Set := (list (turtle_state max_x max_y)*bool)%type.
    
    Definition turtle_path_from_actions {max_x max_y}
               (grid:turtle_grid max_x max_y)
               (start:turtle_state max_x max_y)
               (actions:list turtle_action)
      : turtle_path max_x max_y
      := sum_self_to_bool
           (fold_left_partial_with_history (@turtle_move max_x max_y) actions start).

    Definition turtle_path_from_dec_rules
               {max_x max_y}
               (grid:turtle_grid max_x max_y)
               (start:turtle_state max_x max_y)
               (dec_rules:list (turtle_state max_x max_y->turtle_action))
      : turtle_path max_x max_y
      := sum_self_to_bool
           (fold_left_partial_with_history
              (fun s rule => turtle_move s (rule s))
              dec_rules start
           ).

    Definition turtle_path_from_stationary_dec_rule
               {max_x max_y}
               (grid:turtle_grid max_x max_y)
               (start:turtle_state max_x max_y)
               (dec_rule:turtle_state max_x max_y->turtle_action)
               (steps:nat)
      : turtle_path max_x max_y
      := turtle_path_from_dec_rules grid start (repeat dec_rule steps).
    
    Definition turtle_path_optimal
               {max_x max_y}
               (γ : R)
               (grid:turtle_grid (S max_x) (S max_y))
               (start:turtle_state (S max_x) (S max_y))
               (approx_iters:nat)
               (steps:nat)
      : turtle_path (S max_x) (S max_y)
      := let opt_dec_rule := turtle_approx_dec_rule γ grid approx_iters in
         turtle_path_from_stationary_dec_rule grid start opt_dec_rule steps.

  End move.
  
  Section to_string.
    Section utils.

      Definition newline := String (Ascii.ascii_of_N 10) EmptyString.

      Definition string_bracket (sstart send:string) (smiddle:string)
        := String.append sstart (String.append smiddle send).
      
      Definition vector_join {A} (delim:string) (f:A->string) {n} (v:Vector A n) : string
        := String.concat delim (List.map f (vector_to_list v)).
      
      Definition vector_enum_join {A} (delim:string) (f:nat*A->string) {n} (v:Vector A n) : string
        := String.concat delim (List.map f (List.combine (seq 0 n) (vector_to_list v))).

    End utils.

    Instance turtle_color_tostring : ToString turtle_color
      := {|
      toString c := match c with
                      turtle_green => "+"%string
                    | turtle_white => " "%string
                    | turtle_star => "*"%string
                    | turtle_red  => "X"%string
                    end
        |}.
    
    Definition turtle_gridline_tostring {n} (v:Vector turtle_color n) : string
      := string_bracket "| "%string " |"%string (vector_join " | "%string toString v).

    Definition turtle_grid_vline max_x
      := string_bracket "--"%string "--"%string (String.concat "---"%string (repeat "-"%string max_x)).

    Global Instance turtle_grid_tostring {max_x max_y} : ToString (turtle_grid max_x max_y)
      := {|
      toString m :=
        string_bracket (String.append (turtle_grid_vline max_x) newline)
                       (String.append newline (turtle_grid_vline max_x))
                       (vector_join (string_bracket newline newline (turtle_grid_vline max_x))
                                    (fun line => turtle_gridline_tostring line)
                                    (transpose m))
        |}.

    Definition stately_turtle_grid_vline max_x
      := String.append "--"%string (turtle_grid_vline max_x).

    Definition stately_turtle_gridline_tostring {n} (has_turtle:bool) (x: {n':nat | n' < n}%nat) (v:Vector turtle_color n) : string
      := string_bracket "| "%string " |"%string
                        (vector_enum_join " | "%string
                                          (fun '(cur_x,c) =>
                                             if cur_x == proj1_sig x
                                             then string_bracket
                                                    (if has_turtle then "T"%string else " "%string)
                                                    (if has_turtle then "T"%string else " "%string)
                                                    (toString c)
                                             else toString c)
                                          v).

    Definition stately_turtle_grid_turtleline {n} (x: {n':nat | n' < n}%nat) : string
      :=
        string_bracket "| "%string " |"%string
                       (String.concat " | "
                                      (List.map
                                         (fun cur_x => if cur_x == proj1_sig x
                                                    then "TTT"%string
                                                    else " "%string)
                                         (List.seq 0 n))).

    Global Instance turtle_grid_state_tostring {max_x max_y} : ToString (turtle_grid max_x max_y * turtle_state max_x max_y)
      := {|
      toString '(m, (x,y)) :=
        string_bracket (String.append (stately_turtle_grid_vline max_x) newline)
                       (String.append newline (stately_turtle_grid_vline max_x))
                       (vector_enum_join (string_bracket newline newline (stately_turtle_grid_vline max_x))
                                         (fun '(cur_y,line) =>
                                            if cur_y == proj1_sig y
                                            then
                                              String.concat
                                                newline
                                                [
                                                  stately_turtle_grid_turtleline x ;
                                                stately_turtle_gridline_tostring true x line ;
                                                stately_turtle_grid_turtleline x 
                                                ]
                                            else
                                              stately_turtle_gridline_tostring false x line)
                                         (transpose m))
        |}.


    Definition turtle_path_to_string {max_x max_y}
               (grid:turtle_grid max_x max_y)
               (path:turtle_path max_x max_y)
      := (let '(states, success) := path in
          let boards := String.concat (String.append newline (String.append "====>" newline)) (List.map (fun s => toString (grid,s)) states) in
          let end_message := if success
                             then "and then he took a nap."
                             else "and then he crashed...  Hey, watch where you are going!" in
          String.append boards (String.append newline (String.append newline end_message)))%string.

  End to_string.

End turtle.


Section certl.

  Definition CeRtL_grid : turtle_grid 5%nat 5%nat
    := transpose (
           list_to_vector [
               list_to_vector [turtle_white; turtle_white; turtle_white; turtle_white; turtle_white] ;
             list_to_vector [turtle_red; turtle_red; turtle_red; turtle_star; turtle_white] ;
             list_to_vector [turtle_white; turtle_white; turtle_star; turtle_red; turtle_white] ;
             list_to_vector [turtle_green; turtle_red; turtle_white; turtle_white; turtle_white] ;
             list_to_vector [turtle_white; turtle_white; turtle_white; turtle_red; turtle_white]
         ]).

  Lemma CeRtl_grid_correct : toString CeRtL_grid =
                             String.concat newline [
                                             "---------------------";
                                           "|   |   |   |   |   |";
                                           "---------------------";
                                           "| X | X | X | * |   |";
                                           "---------------------";
                                           "|   |   | * | X |   |";
                                           "---------------------";
                                           "| + | X |   |   |   |";
                                           "---------------------";
                                           "|   |   |   | X |   |";
                                           "---------------------"]%string.
  Proof.
    reflexivity.
  Qed.

  Definition CeRtL_mdp : MDP := turtle_mdp CeRtL_grid.

  Definition make_CeRtL_state := make_turtle_state 5 5.

  Definition CeRtL_run_actions (actions:list turtle_action) : string
    := turtle_path_to_string CeRtL_grid (turtle_path_from_actions CeRtL_grid turtle_start_state actions).

  Definition CeRtL_run_dec_rules dec_rules : string
    := turtle_path_to_string CeRtL_grid (turtle_path_from_dec_rules CeRtL_grid turtle_start_state dec_rules).

  
  Definition CeRtL_run_optimal (γ : R) (approx_iters:nat) (steps:nat) : string
    := turtle_path_to_string CeRtL_grid (turtle_path_optimal γ CeRtL_grid turtle_start_state approx_iters steps).
  
(*
  Eval vm_compute in
      String.append newline (toString (CeRtL_grid, turtle_start_state)).

  Eval vm_compute in
      String.append newline (toString (CeRtL_grid,  make_CeRtL_state 1 3)).
*)

(*
  Eval vm_compute in
      String.append newline
                    (CeRtL_run_actions
                       [Right; Right; Right; Down; Left; Down; Right; Up; Left]).

    Eval vm_compute in
      String.append newline
                    (CeRtL_run_actions
                       [Right; Right; Right; Down; Left; Right; Right; Down; Right; Up; Left]).
 *)

End certl.

 
