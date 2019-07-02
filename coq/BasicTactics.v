Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
      set (x := name); move_to_top x
    | assert_eq x name; move_to_top x
    | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* Some generic tactics from Avi *)

(* Fails when a specific hypothesis is present *)
Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ => idtac
  end.

Ltac extend P :=
  let t := type of P in
  notHyp t; generalize P; intro.

Ltac match_destr
  := match goal with [|- context [match ?x with _ => _ end]] => destruct x end; trivial; try discriminate.

Ltac match_destr_in H
  := match type of H with context [match ?x with _ => _ end] => destruct x end; trivial; try discriminate.

Ltac match_case
  := match goal with [|- context [match ?x with _ => _ end]] => case_eq x end; trivial; try discriminate.

Ltac match_case_in H
  := match type of H with context [match ?x with _ => _ end] => case_eq x end; trivial; try discriminate.

Ltac match_option
  := let eqq := fresh "eqq" in
     match goal with
       [|- context [match ?x with | Some _ => _ | None => _ end]] =>
       case_eq x end; [ intros ? eqq | intros eqq]; try rewrite eqq;
     trivial; try discriminate.

Ltac match_option_in H
  := let eqq := fresh "eqq" in
     match type of H with
       context [match ?x with | Some _ => _ | None => _ end] =>
       case_eq x end; [ intros ? eqq | intros eqq]; rewrite eqq in H;
     trivial; try discriminate.


Ltac cut_to H :=
  match type of H with
  | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> _ -> ?b => cut (b); [clear H; intros H|apply H]
  | _ -> ?b => cut (b); [clear H; intros H|apply H]
  end.

Ltac invcs H := inversion H; clear H; try subst.
