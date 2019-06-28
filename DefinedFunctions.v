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
    | Sign (e : DefinedFunction)
    | Max (l r : DefinedFunction).

  End Definitions.

  Section deriv.
    Fixpoint df_deriv (df:DefinedFunction) (v:var) : DefinedFunction
      := (match df with
         | Number _ => Number 0
         | Var x => if string_dec x v
                    then Number 1
                    else Number 0
         | Plus l r => Plus (df_deriv l v) (df_deriv r v)
         | Minus l r => Minus (df_deriv l v) (df_deriv r v)
         | Times l r => Plus (Times l (df_deriv r v))
                             (Times (df_deriv l v) r)
         | Divide l r => Divide 
                           (Minus
                              (Times (df_deriv l v) r)
                              (Times l (df_deriv r v)))
                           (Times r r)
         | Exp e => Times (df_deriv e v) (Exp e)
         | Log e => Divide (df_deriv e v) e
         | Abs e => Times (df_deriv e v) (Sign e) 
         | Sign e => Number 0
         | Max l r => Divide (Plus (Times (Minus (df_deriv l v) (df_deriv r v)) (Sign (Minus l r)))
                                   (Plus (df_deriv l v) (df_deriv r v)))
                             (Number 2)
          end)%R.

    Definition df_gradient (df:DefinedFunction) (lv:list var) : list DefinedFunction
      := map (df_deriv df) lv.
    
  End deriv.
  
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
         | Sign e =>
           match df_eval σ e with
           | Some v => Some (0)%R
           | _ => None
           end
         | Max l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (Rmax l' r')
           | _, _ => None
           end
         end.

    Definition df_eval_symbolic_gradient (σ:df_env) (df:DefinedFunction) (lv:list var) : option (list R)
      := listo_to_olist (map (df_eval σ) (df_gradient df lv)).
    
  End eval.

  Section deriv2.

    Definition neg_sign (e:R)
      := (if Rle_dec e 0 then -1 else 1)%R.

    Fixpoint df_eval_deriv (σ:df_env) (df:DefinedFunction) (v:var) : option R
      := (match df with
         | Number _ => Some 0
         | Var x => if string_dec x v
                    then Some 1
                    else Some 0
         | Plus l r => 
           match df_eval σ l, df_eval σ r with
           | Some le, Some lr => Some (le + lr)
           | _, _ => None
           end
         | Minus l r =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some lr => Some (le - lr)
           | _, _ => None
           end
         | Times l r =>
           match df_eval σ l, df_eval_deriv σ r v, df_eval σ r, df_eval_deriv σ l v with
           | Some le, Some ld, Some re, Some rd =>
             Some (le * rd + 
                   (ld * re))
           | _, _, _, _ => None
           end
         | Divide l r =>
           match df_eval σ l, df_eval_deriv σ r v, df_eval σ r, df_eval_deriv σ l v with
           | Some le, Some ld, Some re, Some rd =>
             Some (((ld * re) - (le * rd)) / (re * re))
           | _, _, _, _ => None
           end
         | Exp e =>
           match df_eval σ e, df_eval_deriv σ e v with
           | Some ee, Some ed => Some (ed * exp ee)
           | _, _  => None
           end
         | Log e =>
           match df_eval σ e, df_eval_deriv σ e v with
           | Some ee, Some ed => Some (ed / ee)
           | _, _ => None
           end
         | Abs e =>
           match df_eval σ e, df_eval_deriv σ e v with
           | Some ee, Some ed => Some (ed * (neg_sign ee))
           | _, _ => None
           end
         | Sign e => Some 0
         | Max l r =>
           match df_eval σ l, df_eval_deriv σ r v, df_eval σ r, df_eval_deriv σ l v with
           | Some le, Some ld, Some re, Some rd =>
             Some (((ld - rd) * (neg_sign (le - re)) + (ld + rd)) / 2)
           | _, _, _, _ => None
           end
          end)%R.

    Definition df_eval_gradient σ (df:DefinedFunction) (lv:list var) : option (list R)
      := listo_to_olist (map (df_eval_deriv σ df) lv).
    
    End deriv2.

    
  Section max_derived.
    Definition MaxDerived (a b : DefinedFunction) :=
      Divide (Plus (Plus (Abs (Minus b a)) b) a) (Number 2).

    Delimit Scope df_scope with df.
    
    Notation "x + y" := (Plus x y) (only printing) : df_scope.
    Notation "x - y" := (Minus x y) (only printing) : df_scope.
    Notation "x / y" := (Divide x y) (only printing) : df_scope.
    Notation "x * y" := (Times x y) (only printing) : df_scope.
    Notation "x" := (Number x) (only printing, at level 0) : df_scope.
    Notation "x" := (Var x) (only printing, at level 0) : df_scope.
    Notation "'|' x '|'" := (Abs x) (only printing, at level 0) : df_scope.
    
(*    Eval vm_compute in (df_deriv (MaxDerived (Var ("hi"%string)) (Var ("hello"%string))) "hi"%string)%df. *)
    
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
         | Sign e => df_free_variables e
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

  Section apply.
    
    Fixpoint df_apply (e: DefinedFunction) (args: string -> DefinedFunction) :=
      match e with
      | Number x => Number x
      | Var name => args name
      | Plus l r => Plus (df_apply l args) (df_apply r args)
      | Times l r => Times (df_apply l args) (df_apply r args)
      | Minus l r => Minus (df_apply l args) (df_apply r args)
      | Divide l r => Divide (df_apply l args) (df_apply r args)
      | Exp e => Exp (df_apply e args)
      | Log e => Log (df_apply e args)
      | Abs e => Abs (df_apply e args)
      | Sign e => Sign (df_apply e args)
      | Max l r => Max (df_apply l args) (df_apply r args)
      end.
    
 End apply.

    
  Section subst.
    Fixpoint df_subst (e: DefinedFunction) (v:var) (e':DefinedFunction) :=
      match e with
      | Number x => Number x
      | Var name =>
        if string_dec name v
        then e'
        else Var name
      | Plus l r => Plus (df_subst l v e') (df_subst r v e')
      | Times l r => Times (df_subst l v e') (df_subst r v e')
      | Minus l r => Minus (df_subst l v e') (df_subst r v e')
      | Divide l r => Divide (df_subst l v e') (df_subst r v e')
      | Exp e => Exp (df_subst e v e')
      | Log e => Log (df_subst e v e')
      | Abs e => Abs (df_subst e v e')
      | Sign e => Sign (df_subst e v e')
      | Max l r => Max (df_subst l v e') (df_subst r v e')
      end.


    Lemma df_subst_nfree (e: DefinedFunction) (v:var) (e':DefinedFunction) :
      ~ In v (df_free_variables e) ->
      df_subst e v e' = e.
    Proof.
      induction e; simpl; trivial; intros nin
      ; try solve [try rewrite in_app_iff in nin
                   ; intuition congruence].
      - destruct (string_dec name v); intuition.
    Qed.

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

