Require Import String.
Require Import RelationClasses.
Require Import List.
Require Import Rbase Rtrigo Rpower Rbasic_fun.
Require Import Lra.

Require Import ListAdd Assoc.

Module DefinedFunctions.

  Section Definitions.
    
    Definition var := string.

    (* A subset of defined functions *)

    Inductive DefinedFunction : Set :=
    | Number (x : R)
    | Var (name : var)
    | Plus (l r : DefinedFunction)
    | Minus (l r : DefinedFunction)
    | Times (l r : DefinedFunction)
    | Divide (l r : DefinedFunction)
    | Exp (e : DefinedFunction)
    | Log (e : DefinedFunction)
    | Abs (e : DefinedFunction)
    | Max (l r : DefinedFunction).

  End Definitions.

  Section eval.

    Definition df_env := list (string * R).

    Fixpoint df_eval (σ:df_env) (df:DefinedFunction) : option R
      := match df with
         | Number r => Some r
         | Var x => lookup string_dec σ x
         | Plus l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' + r')%R
           | _, _ => None
           end
         | Minus l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' - r')%R
           | _, _ => None
           end
         | Times l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' * r')%R
           | _, _ => None
           end
         | Divide l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' / r')%R
           | _, _ => None
           end
         | Exp e =>
           match df_eval σ e with
           | Some v => Some (exp v)
           | _ => None
           end
         | Log e => 
           match df_eval σ e with
           | Some v => Some (ln v)
           | _ => None
           end
         | Abs e =>
           match df_eval σ e with
           | Some v => Some (Rabs v)
           | _ => None
           end
         | Max l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (Rmax l' r')
           | _, _ => None
           end
         end.

  End eval.

  Section max_derived.
    Definition MaxDerived (a b : DefinedFunction) :=
      Divide (Plus (Plus (Abs (Minus b a)) b) a) (Number 2).
    
    Lemma MaxDerivedMax_eq (a b : DefinedFunction) :
      forall σ, df_eval σ (Max a b) = df_eval σ (MaxDerived a b).
    Proof.
      simpl; intros σ.
      destruct (df_eval σ a); destruct (df_eval σ b); trivial.
      f_equal.
      destruct (Rle_dec r r0).
      - rewrite Rmax_right by trivial.
        rewrite Rabs_pos_eq by lra.
        lra.
      - rewrite Rmax_left by lra.
        rewrite Rabs_minus_sym.
        rewrite Rabs_pos_eq by lra.
        lra.
    Qed.

  End max_derived.

  Section fv.

    Fixpoint df_free_variables (f : DefinedFunction) : list var
      := match f with
         | Number x => nil
         | Var name => name::nil
         | Plus l r => (df_free_variables l) ++ (df_free_variables r)
         | Minus l r => (df_free_variables l) ++ (df_free_variables r)
         | Times l r => (df_free_variables l) ++ (df_free_variables r)
         | Divide l r => (df_free_variables l) ++ (df_free_variables r)
         | Max l r => (df_free_variables l) ++ (df_free_variables r)
         | Abs e => df_free_variables e
         | Log e => df_free_variables e
         | Exp e => df_free_variables e
         end.

    Definition df_closed (f: DefinedFunction) : Prop
      := match df_free_variables f with
         | nil => True
         | _ => False
         end.

    Lemma df_closed_nil (f: DefinedFunction) : df_closed f -> df_free_variables f = nil.
    Proof.
      unfold df_closed.
      destruct (df_free_variables f); tauto.
    Qed.

    Lemma df_eval_complete' (σ:df_env) (f:DefinedFunction) :
      incl (df_free_variables f) (domain σ) -> {v | df_eval σ f = Some v}.
    Proof.
      induction f; simpl; intros inc
      ;  try solve [rewrite incl_app_iff in inc
                    ; intuition
                    ; destruct H1 as [v1 ev1]
                    ; destruct H2 as [v2 ev2]
                    ; rewrite ev1; rewrite ev2
                    ; eauto
                   | intuition
                     ; destruct H as [v1 ev1]
                     ; rewrite ev1
                     ; eauto].
      - eauto.
      - apply in_dom_lookup.
        specialize (inc name); simpl in *.
        intuition.
    Qed.

    (* This version has better computational properties *)
    Lemma df_eval_complete (σ:df_env) (f:DefinedFunction) :
      incl (df_free_variables f) (domain σ) -> {v | df_eval σ f = Some v}.
    Proof.
      case_eq (df_eval σ f); simpl.
      - intros r ?? ; exists r; eauto.
      - intros ? inc.
        destruct (df_eval_complete' _ _ inc); congruence.
    Defined.

    Lemma df_eval_none  (σ:df_env) (f:DefinedFunction) :
      df_eval σ f = None ->
      {v | In v (df_free_variables f) /\ ~ In v (domain σ)}.
    Proof.
      intros.
      destruct (incl_dec string_dec (df_free_variables f) (domain σ)).
      - destruct (df_eval_complete _ _ i); congruence.
      - apply (nincl_exists string_dec) in n; trivial.
    Qed.

    (* Either we can evaluate df or we are missing a variable definition.
       Note that this theorem may fail to hold if we change the definition of 
       division to make it partial.
     *)
    Lemma df_eval_compute (σ:df_env) (f:DefinedFunction) :
      {v | df_eval σ f = Some v} + {x | In x (df_free_variables f) /\ ~ In x (domain σ)}.
    Proof.
      case_eq (df_eval σ f); simpl.
      - eauto.
      - intros H; apply df_eval_none in H; eauto.
    Defined.

    Lemma df_eval_closed (f:DefinedFunction) :
      df_closed f -> {v | df_eval nil f = Some v}.
    Proof.
      intros c.
      apply (df_eval_complete nil f).
      rewrite df_closed_nil by trivial.
      simpl; reflexivity.
    Defined.        

    Lemma df_eval_lookup_on (σ₁ σ₂:df_env) (f:DefinedFunction) :
      lookup_equiv_on string_dec (df_free_variables f) σ₁ σ₂ ->
      df_eval σ₁ f = df_eval σ₂ f.
    Proof.
      intros lookeq.
      induction f; simpl in *; trivial
      ;  try solve [apply lookup_equiv_on_dom_app in lookeq; intuition
                    ; rewrite H1, H2; trivial
                   | rewrite IHf; trivial].
      - apply lookeq; simpl; tauto.
    Qed.

  End fv.

  Section subst.
    Fixpoint df_subst (e: DefinedFunction) (args: string -> DefinedFunction) :=
      match e with
      | Number x => Number x
      | Var name => args name
      | Plus l r => Plus (df_subst l args) (df_subst r args)
      | Times l r => Times (df_subst l args) (df_subst r args)
      | Minus l r => Minus (df_subst l args) (df_subst r args)
      | Divide l r => Divide (df_subst l args) (df_subst r args)
      | Exp e => Exp (df_subst e args)
      | Log e => Log (df_subst e args)
      | Abs e => Abs (df_subst e args)
      | Max l r => Max (df_subst l args) (df_subst r args)
      end.
  End subst.


  Section FreeVariablesExample.
    (* We need ot open the string scope in order to use "a" as a string. *)
    Open Scope string_scope.
    Theorem ex1 : (df_free_variables (Plus (Var "a") (Var "b"))) = "a"::"b"::nil.
    Proof.
      (* Reflexivity doesn't need syntactically identical things on either side of =. 
       * It suffices that the left-hand side beta-reduced to the right-hand side. *)
      reflexivity.
    Qed.
    
    Close Scope string_scope.
    
  End FreeVariablesExample.
    
End DefinedFunctions.

