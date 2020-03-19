Require Import String.
Require Import EquivDec.
Require Import RelationClasses.
Require Import List.
Require Import NPeano.
Require Import Lra Omega.
Require Reals.
Require Import Eqdep_dec.

Require Import Floatish.
Require Import Utils.
Require Import derivlemmas.
Require Import DefinedFunctions.
Set Bullet Behavior "Strict Subproofs".

Section DefinedFunctions.

  Context {floatish_impl:floatish}.
  Local Open Scope float.


Section real_pfs.

  Local Existing Instance floatish_R.
  Import Reals.
  Import List.


  (* following returns None if not-differentiable *)
    Fixpoint df_eval_deriv_exact {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v:var_type) : option (definition_function_types_interp T)
      := (match df with
         | Number _ _ => Some 0
         | Constant t _ x => Some
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
         | DVector n _ dfs => vectoro_to_ovector (fun i => df_eval_deriv_exact σ (dfs i) v)
         | DMatrix n m _ df => matrixo_to_omatrix (fun i j => df_eval_deriv_exact σ (df i j) v)
         | Var x _ => Some (let t:=snd x in 
               match t return definition_function_types_interp t with
               | DTfloat => if x == v then 1 else 0
               | DTVector n => ConstVector n (if x == v then 1 else 0)
               | DTMatrix m n => ConstMatrix m n (if x == v then 1 else 0)
               end)
         | Plus _ l r => 
           match df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with
           | Some le, Some lr => Some (le + lr)
           | _, _ => None
           end
         | Minus _ l r =>
           match df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with
           | Some le, Some lr => Some (le - lr)
           | _, _ => None
           end
         | Times _ l r =>
           match df_eval σ l, df_eval_deriv_exact σ l v, df_eval σ r, df_eval_deriv_exact σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (le * rd + 
                   (ld * re))
           | _, _, _, _ => None
           end
         | Divide _ l r =>
           match df_eval σ l, df_eval_deriv_exact σ l v, df_eval σ r, df_eval_deriv_exact σ r v with
           | Some le, Some ld, Some re, Some rd =>
             if Feq re 0 then None else 
               Some ((ld / re) - ((le * rd) / (re * re)))
           | _, _, _, _ => None
           end
         | Square _ e =>
           match df_eval σ e, df_eval_deriv_exact σ e v with
           | Some ee, Some ed => Some (2 * ee * ed)
           | _, _  => None
           end
         | Exp _ e =>
           match df_eval σ e, df_eval_deriv_exact σ e v with
           | Some ee, Some ed => Some (ed * Fexp ee)
           | _, _  => None
           end
         | Log _ e =>
           match df_eval σ e, df_eval_deriv_exact σ e v with
           | Some ee, Some ed => 
             if ee > 0 then Some (ed / ee) else None
           | _, _ => None
           end
         | Abs _ e =>
           match df_eval σ e, df_eval_deriv_exact σ e v with
           | Some ee, Some ed => 
             if Feq ee 0 then None else Some (ed * (sign ee))
           | _, _ => None
           end
         | Sign _ e =>
           match df_eval σ e, df_eval_deriv_exact σ e v with
           | Some ee, Some ed => 
             if Feq ee 0 then None else Some 0
           | _, _ => None
           end
         | PSign _ e =>
           match df_eval σ e, df_eval_deriv_exact σ e v with
           | Some ee, Some ed => 
             if Feq ee 0 then None else Some 0
           | _, _ => None
           end
         | Max _ l r =>
           match df_eval σ l, df_eval σ r, df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with
           | Some le, Some re, Some ld, Some rd =>
             if Feq le re then None else
               if le < re then Some rd else Some ld
           | _, _, _, _=> None
           end
         | VectorElem n _ l i => 
           match (df_eval_deriv_exact σ l v)  with
           | Some l' => Some (l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_deriv_exact σ l v)  with
           | Some l' => Some (l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval σ l, df_eval_deriv_exact σ l v, df_eval σ r, df_eval_deriv_exact σ r v with
           | Some le, Some ld, Some re, Some rd => 
               Some (vsum (fun j => (le j) * (rd j) + (ld j) * (re j)))
           | _, _, _, _ => None
           end
         | VectorSum n _ l =>
           match df_eval_deriv_exact σ l v with
           | Some ld =>
               Some (vsum ld)
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_eval_deriv_exact σ l v with
           | Some ld =>
               Some (msum ld)
           | _ => None
           end
         | VectorScalMult n _ x r =>
           match df_eval σ x, df_eval_deriv_exact σ x v, df_eval σ r, df_eval_deriv_exact σ r v with
           | Some xe, Some xd, Some re, Some rd => Some (fun j => xe * (rd j) + xd * (re j))
           | _, _, _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval σ x, df_eval_deriv_exact σ x v, df_eval σ r, df_eval_deriv_exact σ r v with
           | Some xe, Some xd, Some re, Some rd => Some (fun i j => xe * (rd i j) + xd * (re i j))
           | _, _, _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           match df_eval σ l, df_eval_deriv_exact σ l v, df_eval σ r, df_eval_deriv_exact σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i => vsum (fun j => (le i j)*(rd j) + (ld i j)*(re j)))
           | _, _, _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with
           | Some le, Some re =>
             Some (fun i j => (le i j) + (re i))
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           match df_eval σ l, df_eval_deriv_exact σ l v, df_eval σ r, df_eval_deriv_exact σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i k => vsum (fun j => (le i j)*(rd j k) + (ld i j)*(re j k)))
           | _, _, _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with           
           | Some l', Some r' => Some (fun i => (l' i) + (r' i))
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with           
           | Some l', Some r' => Some (fun i => (l' i) - (r' i))
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with           
           | Some l', Some r' => Some (fun i j => (l' i j) + (r' i j))
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_deriv_exact σ l v, df_eval_deriv_exact σ r v with           
           | Some l', Some r' => Some (fun i j => (l' i j) - (r' i j))
           | _, _ => None
           end
         | VectorApply n _ x s r =>
           match df_eval σ r, df_eval_deriv_exact σ r v with                      
           | Some re, Some rd => 
             vectoro_to_ovector 
               (fun i => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv_exact (cons (mk_env_entry xv (re i)) σ) s v with
                         | Some sd => Some ((rd i) * sd)
                         | _ => None
                         end)
           | _, _ => None                                                    
           end
         | MatrixApply n m _ x s r =>
           match df_eval σ r, df_eval_deriv_exact σ r v with                      
           | Some re, Some rd => 
             matrixo_to_omatrix
               (fun i j => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv_exact (cons (mk_env_entry xv (re i j)) σ) s v with
                         | Some sd => Some ((rd i j) * sd)
                         | _ => None
                         end)
           | _, _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_eval σ l, df_eval_deriv_exact σ l v with                      
           | Some le, Some ld => 
             match (vectoro_to_ovector 
                      (fun i => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv_exact (cons (mk_env_entry xv1 (le i)) 
                                                   (cons (mk_env_entry xv2 (r i)) σ)) s v with
                         | Some sd => Some ((ld i) * sd)
                         | _ => None
                         end)) with
             | Some vv => Some (vsum vv)
             | _ => None
             end
           | _, _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           match df_eval σ l, df_eval_deriv_exact σ l v with                      
           | Some le, Some ld => 
             match (matrixo_to_omatrix
                      (fun i j => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv_exact (cons (mk_env_entry xv1 (le i j)) 
                                                   (cons (mk_env_entry xv2 (r i j)) σ)) s v with
                         | Some sd => Some ((ld i j) * sd)
                         | _ => None
                         end)) with
             | Some vv => Some ((msum vv)/(FfromZ (Z.of_nat m)))
             | _ => None
             end
           | _, _ => None
           end
          end).


   Definition addBinding σ v x := (mk_env_entry (v,DTfloat) x)::σ.

   Definition df_eval_at_point {Ann T} σ (df:DefinedFunction Ann T) v x
     := df_eval (addBinding σ v x) df.
   
   Definition df_R {Ann} (σ:df_env) (df:DefinedFunction Ann DTfloat) v : R -> R
     := fun x => match df_eval_at_point σ df v x with
        | Some y => y
        | None => 0%R
        end.

   Require Import Coquelicot.Coquelicot.
                        
    Definition ex_deriv_df {Ann} σ (df:DefinedFunction Ann DTfloat) v (x:R)
     :=  fully_closed_over df ((v,DTfloat)::map (@projT1 _ _) σ) /\
         ex_derive (df_R σ df v) x.

   Definition is_deriv_df {Ann} σ (df:DefinedFunction Ann DTfloat) v (x y:R)
     :=  fully_closed_over df ((v,DTfloat)::map (@projT1 _ _) σ) /\
         is_derive (df_R σ df v) x y.


   Lemma eval_at_point_fully_closed_total {T} (σ:df_env) (df:DefinedFunction UnitAnn T) v x :
      let vl := (v,DTfloat)::map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> 
      {d:definition_function_types_interp T | df_eval_at_point σ df v x = Some d}.
   Proof.
     intros.
     unfold df_eval_at_point.
     destruct (eval_fully_closed_total (addBinding σ v x) df) as [dd pfd]
     ; simpl; eauto.
   Defined.

   Lemma eval_at_point_diferentiable_total {σ} {df:DefinedFunction UnitAnn DTfloat} {v x y} :
     is_deriv_df σ df v x y ->
     {xve | df_eval_at_point σ df v x = Some xve}.
   Proof.
     intros [closed _ ].
     destruct (eval_at_point_fully_closed_total σ df v x); eauto.
   Defined.

   Definition eval_differentiable_at_point {σ} {df:DefinedFunction UnitAnn DTfloat} {v x y}
              (pf_deriv:is_deriv_df σ df v x y) :=
     proj1_sig (eval_at_point_diferentiable_total pf_deriv).

   Lemma is_derive_df_exp
         (df:DefinedFunction UnitAnn DTfloat) (σ:df_env) v x y
         (pf_deriv:is_deriv_df σ df v x y) :
     forall a,
     is_deriv_df σ (Exp a df) v x (y * exp (eval_differentiable_at_point pf_deriv)).
   Proof.
     unfold eval_differentiable_at_point.
     destruct (eval_at_point_diferentiable_total pf_deriv) as [xve eqqx]; simpl.
     unfold is_deriv_df; simpl; destruct pf_deriv as [base_closed base_deriv].
     split; trivial.
     generalize (is_derive_comp exp (df_R σ df v) x (exp xve) y)
     ; intros isd.
     unfold df_R, df_eval_at_point in *.
     eapply is_derive_ext; [ | eapply isd]; trivial.
     - intros; simpl.
       match_option; simpl.
       eelim eval_fully_closed_not_none; [ | eapply eqq].
       simpl; trivial.
     - rewrite eqqx.
       apply is_derive_exp.
   Qed.

   Lemma is_derive_df_mult
         (df1 df2:DefinedFunction UnitAnn DTfloat) (σ:df_env) v x y1 y2 
         (pf_deriv1:is_deriv_df σ df1 v x y1) 
         (pf_deriv2:is_deriv_df σ df2 v x y2) :
     forall a,
     is_deriv_df σ (Times a df1 df2) v x ((y1 * eval_differentiable_at_point pf_deriv2 + eval_differentiable_at_point pf_deriv1 * y2)).
   Proof.
     unfold eval_differentiable_at_point.
     intros.
     destruct (eval_at_point_diferentiable_total pf_deriv1) as [xve1 eqqx1]; simpl.
     destruct (eval_at_point_diferentiable_total pf_deriv2) as [xve2 eqqx2]; simpl.
     unfold is_deriv_df; simpl
     ; destruct pf_deriv1 as [base_closed1 base_deriv1]
     ; destruct pf_deriv2 as [base_closed2 base_deriv2].
     split; [tauto | ].
     generalize (is_derive_mult (df_R σ df1 v) (df_R σ df2 v) x y1 y2 base_deriv1 base_deriv2)
     ; intros HH.
     unfold df_R in *.
     rewrite eqqx1, eqqx2 in HH.
     eapply is_derive_ext; [ | eapply HH]; trivial.
     - intros; simpl.
       unfold df_eval_at_point; simpl.
       repeat match_option; unfold mult; simpl; lra.
       (*
       + eelim eval_fully_closed_not_none; [ | eapply eqq0].
         simpl; eauto.
       + eelim eval_fully_closed_not_none; [ | eapply eqq].
         simpl; eauto.
       + eelim eval_fully_closed_not_none; [ | eapply eqq0].
         simpl; eauto.
        *)
     - simpl; intros.
       unfold mult; simpl.
       lra.
   Qed.

Tactic Notation "DefinedFunction_scalar_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Number"%string
  | Case_aux c "Constant"%string                 
  | Case_aux c "Var"%string
  | Case_aux c "Plus"%string
  | Case_aux c "Minus"%string
  | Case_aux c "Times"%string
  | Case_aux c "Divide"%string
  | Case_aux c "Square"%string
  | Case_aux c "Exp"%string
  | Case_aux c "Log"%string
  | Case_aux c "Abs"%string
  | Case_aux c "Sign"%string
  | Case_aux c "PSign"%string
  | Case_aux c "Max"%string].


   Require FunctionalExtensionality.

    Ltac refl_simpler := 
      repeat
        match goal with
        | [H: @eq var_type _ _ |- _ ] => try (inversion H; subst); rewrite (var_type_UIP_refl H)
        | [H: @equiv var_type _ _ _ _ |- _ ] => try (inversion H; subst); rewrite (var_type_UIP_refl H)
        | [H: @eq definition_function_types _ _ |- _ ] => try (inversion H; subst); rewrite (definition_function_types_UIP_refl H)
        | [H: @equiv definition_function_types _ _ _ _ |- _ ] => try (inversion H; subst); rewrite (definition_function_types_UIP_refl H)
        end.


    Lemma df_R_total_plus σ a (l r:DefinedFunction UnitAnn DTfloat) v x :
      fully_closed_over l ((v,DTfloat)::map (@projT1 _ _) σ) ->
      fully_closed_over r ((v,DTfloat)::map (@projT1 _ _) σ) ->
      df_R σ (Plus a l r) v x = df_R σ l v x + df_R σ r v x.
    Proof.
      simpl.
      intros.
      destruct (eval_fully_closed_total (addBinding σ v x) l); simpl; trivial.
      destruct (eval_fully_closed_total (addBinding σ v x) r); simpl; trivial.
      unfold df_R, df_eval_at_point; simpl.
      now rewrite e, e0.
    Qed.

    Lemma df_R_total_minus σ a (l r:DefinedFunction UnitAnn DTfloat) v x :
      fully_closed_over l ((v,DTfloat)::map (@projT1 _ _) σ) ->
      fully_closed_over r ((v,DTfloat)::map (@projT1 _ _) σ) ->
      df_R σ (Minus a l r) v x = df_R σ l v x - df_R σ r v x.
    Proof.
      simpl.
      intros.
      destruct (eval_fully_closed_total (addBinding σ v x) l); simpl; trivial.
      destruct (eval_fully_closed_total (addBinding σ v x) r); simpl; trivial.
      unfold df_R, df_eval_at_point; simpl.
      now rewrite e, e0.
    Qed.

    Lemma df_R_total_times σ a (l r:DefinedFunction UnitAnn DTfloat) v x :
      fully_closed_over l ((v,DTfloat)::map (@projT1 _ _) σ) ->
      fully_closed_over r ((v,DTfloat)::map (@projT1 _ _) σ) ->
      df_R σ (Times a l r) v x = df_R σ l v x * df_R σ r v x.
    Proof.
      simpl.
      intros.
      destruct (eval_fully_closed_total (addBinding σ v x) l); simpl; trivial.
      destruct (eval_fully_closed_total (addBinding σ v x) r); simpl; trivial.
      unfold df_R, df_eval_at_point; simpl.
      now rewrite e, e0.
    Qed.

    Lemma df_R_total_divide σ a (l r:DefinedFunction UnitAnn DTfloat) v x :
      fully_closed_over l ((v,DTfloat)::map (@projT1 _ _) σ) ->
      fully_closed_over r ((v,DTfloat)::map (@projT1 _ _) σ) ->
      df_R σ (Divide a l r) v x = df_R σ l v x / df_R σ r v x.
    Proof.
      simpl.
      intros.
      destruct (eval_fully_closed_total (addBinding σ v x) l); simpl; trivial.
      destruct (eval_fully_closed_total (addBinding σ v x) r); simpl; trivial.
      unfold df_R, df_eval_at_point; simpl.
      now rewrite e, e0.
    Qed.

    Lemma ex_deriv_div (f g :R ->R) (x:R) :
      ex_derive (fun t => (f t)/(g t)) x -> (g x) <> 0.
      Admitted.

    Lemma ex_deriv_log (f : R -> R) (x:R) :
      ex_derive (fun t => ln (f t)) x -> (f x) > 0.
      Admitted.

    Lemma ex_deriv_abs (f : R -> R) (x:R) :
      ex_derive f x -> ex_derive (fun t => Rabs (f t)) x ->
      f x <> 0 \/ is_derive f x 0.
      Admitted.

    Lemma ex_deriv_sign (f : R -> R) (x:R) :
      ex_derive f x -> ex_derive (fun t => sign (f t)) x ->
      f x <> 0 \/ locally x (fun t => f t = 0).
      Admitted.

    Lemma ex_deriv_psign (f : R -> R) (x:R) :
      ex_derive f x -> ex_derive (fun t => psign (f t)) x ->
      f x <> 0 \/ locally x (fun t => f t >= 0).
      Admitted.
     
    Lemma ex_deriv_max (f g : R -> R) (x: R) :
      ex_derive f x -> ex_derive g x -> ex_derive (fun t => Rmax (f t) (g t)) x ->
      (f x) <> (g x) \/ is_derive (fun t => (f t) - (g t)) x 0.
    Admitted.
    
    Lemma floatish_sign :
      forall (x:R), sign x = FloatishOps.sign x.
    Proof.
      intros.
      unfold sign, FloatishOps.sign; simpl.
      case_eq (Rlt_dec x 0); intros.
      - match_case; intros.
        destruct s; lra.
      - match_case; intros.
        + destruct s; case_eq (Rgt_dec x 0); simpl; intros; lra.
        + lra.
    Qed.
    
    Lemma pos_sign_psign:
      forall (x:R), psign x = pos_sign x.      
    Proof.
      unfold psign, pos_sign.
      intros.
      simpl.
      now destruct (Rge_dec x 0).
    Qed.

    Lemma Rmax_Fmax :
      forall (x y:R), Rmax x y = Fmax x y.
      unfold Rmax, Fmax; simpl; intros.
      match_case; intros.
      - case_eq (Rlt_dec x y); intros; trivial.
        lra.
      - case_eq (Rlt_dec x y); intros; trivial.
        lra.
    Qed.
  
    Theorem df_eval_deriv_exact_correct σ (df:DefinedFunction UnitAnn DTfloat) v (x:R) y
     : is_scalar_function df ->
       fully_closed_over df ((v,DTfloat)::map (@projT1 _ _) σ) ->
       df_eval_deriv_exact (addBinding σ v x) df (v,DTfloat) = Some y ->
       is_derive (df_R σ df v) x y.
   Proof.
     simpl.
     intros is_scalar.
     generalize is_scalar.
     revert y.
     pattern df.
     revert df is_scalar.
     DefinedFunction_scalar_cases (apply is_scalar_function_ind) Case; simpl; intros.
     - Case "Number"%string.
       unfold df_R, df_eval_at_point; simpl.
       inversion H0; subst.
       now apply (@is_derive_const R_AbsRing).
     - Case "Constant"%string.
       unfold df_R, df_eval_at_point; simpl.
       inversion H0; subst.
       now apply (@is_derive_const R_AbsRing).
     - Case "Var"%string.
       unfold df_R, df_eval_at_point; simpl.
       inversion H0; subst.
       simpl.
       unfold equiv_dec, vart_eqdec.
       destruct (vart_dec (sv, DTfloat) (v, DTfloat)).
       + refl_simpler; simpl.
         now apply (@is_derive_id R_AbsRing).
       + now apply (@is_derive_const R_AbsRing).
     - Case "Plus"%string.
       destruct H1.
       do 2 match_option_in H2.
       invcs H2.
       destruct is_scalar as [isc1 isc2].
       specialize (H _ isc1 H1 eqq).
       specialize (H0 _ isc2 H3 eqq0).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_plus.
       + generalize (@is_derive_plus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "Minus"%string.
       destruct H1.
       do 2 match_option_in H2.
       invcs H2.
       destruct is_scalar as [isc1 isc2].
       specialize (H _ isc1 H1 eqq).
       specialize (H0 _ isc2 H3 eqq0).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_minus.
       + generalize (@is_derive_minus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "Times"%string.
       destruct H1.
       do 4 match_option_in H2.
       invcs H2.
       destruct is_scalar as [isc1 isc2].
       specialize (H _ isc1 H1 eqq0).
       specialize (H0 _ isc2 H3 eqq2).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_times.
       + generalize Derive.is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d * d2 + d0 * d1) with
                 (d0 * (df_R σ r v x) + (df_R σ l v x) * d2).
         * apply HH; trivial.
         * unfold df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "Divide"%string.
       destruct H1.
       do 4 match_option_in H2.
       invcs H2.
       destruct is_scalar as [isc1 isc2].
       specialize (H _ isc1 H1 eqq0).
       specialize (H0 _ isc2 H3 eqq2).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_divide.
       + generalize is_derive_div; simpl; intros HH.
         replace (d0 / d1 - d * d2 / (d1 * d1)) with
             ((d0 * (df_R σ r v x) - (df_R σ l v x) * d2) / ((df_R σ r v x)*((df_R σ r v x)*1))).
         * destruct (Req_EM_T d1 0); [congruence |].
           inversion H5.
           specialize (HH (df_R σ l v) (df_R σ r v) x d0 d2).
           replace (d0 / d1 - d * d2 / (d1 * d1)) with
             ((d0 * df_R σ r v x - df_R σ l v x * d2) / (df_R σ r v x * (df_R σ r v x * 1))).
           apply HH; trivial.
           unfold df_R, df_eval_at_point; simpl.
           now rewrite eqq1.
           unfold df_R, df_eval_at_point; simpl.           
           rewrite eqq; rewrite eqq1.
           now field.
         * unfold df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           destruct (Req_EM_T d1 0); [congruence |].           
           now field; trivial.
     - Case "Square"%string.
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (Rsqr (df_R σ e v t) = df_R σ (Square a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; unfold Rsqr; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * replace (2 * d * d0) with (d0 * (2 * d)) by lra.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           --  apply is_derive_sqr.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Exp"%string.
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (exp (df_R σ e v t) = df_R σ (Exp a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           --  apply is_derive_exp.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Log"%string.               
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (ln (df_R σ e v t) = df_R σ (Log a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * destruct (Rgt_dec d 0); [|congruence].
           inversion H3.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           --  apply is_derive_ln.
               unfold df_R, df_eval_at_point; simpl.
               rewrite eqq.
               lra.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Abs"%string.         
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (Rabs (df_R σ e v t) = df_R σ (Abs a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * destruct ( Req_EM_T d 0 ); [congruence |].
           inversion H3.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           -- replace (@FloatishOps.sign floatish_R (df_R σ e v x)) with (sign (df_R σ e v x)).
              ++ apply is_derive_abs.
                 unfold df_R, df_eval_at_point; simpl.
                 rewrite eqq.
                 lra.
              ++ apply floatish_sign.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Sign"%string.         
       match_option_in H1.
       match_option_in H1.
       destruct (Req_EM_T d 0); [congruence|].
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (sign (df_R σ e v t) = df_R σ (Sign a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
         apply floatish_sign.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * replace (0) with (d0 * 0) by lra.
           apply (@is_derive_comp R_AbsRing); trivial.           
           apply is_derive_sign.
           unfold df_R, df_eval_at_point; simpl.           
           rewrite eqq; lra.
     - Case "PSign"%string.         
       match_option_in H1.
       match_option_in H1.
       destruct (Req_EM_T d 0); [congruence|].
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (psign (df_R σ e v t) = df_R σ (PSign a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
         apply pos_sign_psign.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * replace (0) with (d0 * 0) by lra.
           apply (@is_derive_comp R_AbsRing); trivial.           
           apply is_derive_psign.
           unfold df_R, df_eval_at_point; simpl.           
           rewrite eqq; lra.
     - Case "Max"%string.
       do 2 match_option_in H2.
       destruct H1.
       destruct is_scalar as [isc1  isc2].
       assert (forall t, (Rmax (df_R σ l v t) (df_R σ r v t)) = df_R σ (Max a l r) v t).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) l); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v t) r); simpl; trivial. 
         rewrite e, e0; trivial.
         apply Rmax_Fmax.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H4.
         * match_option_in H2.
           match_option_in H2.           
           destruct (Req_EM_T d d0); [congruence |].
           destruct (Rlt_dec d d0).
           -- invcs H2.
              specialize (H _ isc1 H1 eqq1).
              specialize (H0 _ isc2 H3 eqq2).
              replace (y) with ((d1 + y + (d1-y)*sign(df_R σ l v x - df_R σ r v x))/2).
              ++ apply is_derive_max; trivial.
                 unfold df_R, df_eval_at_point; simpl.           
                 now rewrite eqq, eqq0.
              ++ unfold df_R, df_eval_at_point; simpl.           
                 rewrite eqq, eqq0.
                 unfold sign; simpl.
                 destruct (total_order_T 0 (d - d0)).
                 ** destruct s; lra.
                 ** lra.
           -- invcs H2.
              specialize (H _ isc1 H1 eqq1).
              specialize (H0 _ isc2 H3 eqq2).
              replace (y) with ((y + d2 + (y - d2)*sign(df_R σ l v x - df_R σ r v x))/2).
              ++ apply is_derive_max; trivial.
                 unfold df_R, df_eval_at_point; simpl.           
                 now rewrite eqq, eqq0.
              ++ unfold df_R, df_eval_at_point; simpl.           
                 rewrite eqq, eqq0.
                 unfold sign; simpl.
                 destruct (total_order_T 0 (d - d0)).
                 ** destruct s; lra.
                 ** lra.
   Qed.
   
   Definition df_R_vec {Ann} {n} (σ:df_env) (df:DefinedFunction Ann (DTVector n)) v : 
     R -> Vector R n
     := fun x => match df_eval_at_point σ df v x with
        | Some y => y
        | None => ConstVector n 0
        end.

   Definition df_R_mat {Ann} {n m} (σ:df_env) (df:DefinedFunction Ann (DTMatrix n m)) v : 
     R -> Matrix R n m
     := fun x => match df_eval_at_point σ df v x with
        | Some y => y
        | None => ConstMatrix n m 0
        end.

   Definition df_R_gen Ann T σ :
     (DefinedFunction Ann T) -> SubVar -> R -> (definition_function_types_interp T) :=
     match T with
     | DTfloat => fun df v => df_R σ df v
     | DTVector n => fun df v => df_R_vec σ df v 
     | DTMatrix n m => fun df v => df_R_mat σ df v                      
     end.

    Definition is_derive_vec {n} (f : R -> Vector R n) (x:R) (df : Vector R n) :=
      forall i, is_derive (fun x0 => f x0 i) x (df i).

    Definition is_derive_mat {n m} (f : R -> Matrix R n m) (x:R) (df : Matrix R n m) :=
      forall i j, is_derive (fun x0 => f x0 i j) x (df i j).

    Definition is_derive_gen {T} (f: R->definition_function_types_interp T) (x:R)
               (df : definition_function_types_interp T)
        :=
          (match T return (R -> definition_function_types_interp T) ->
                     definition_function_types_interp T -> Prop
           with
           | DTfloat => fun f df =>  is_derive f x df
           | DTVector n => fun f df => is_derive_vec f x df
           | DTMatrix n m => fun f df => is_derive_mat f x df
           end) f df.

    Theorem df_eval_deriv_exact_gen_correct {T} σ (df:DefinedFunction UnitAnn T) v (x:R) y
     : fully_closed_over df ((v,DTfloat)::map (@projT1 _ _) σ) ->
       df_eval_deriv_exact (addBinding σ v x) df (v,DTfloat) = Some y ->
       is_derive_gen (df_R_gen UnitAnn T σ df v) x y.
   Proof.
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case; simpl; intros.
     - Case "Number"%string.
       unfold df_R, df_eval_at_point; simpl.
       inversion H0; subst.
       now apply (@is_derive_const R_AbsRing).
     - Case "Constant"%string.
       unfold df_R_gen, is_derive_gen; simpl.
       destruct t.
       + unfold df_R; simpl; invcs H0.
         now apply (@is_derive_const R_AbsRing).
       + unfold df_R_vec; simpl; invcs H0.
         unfold is_derive_vec, ConstVector; intro.
         now apply (@is_derive_const R_AbsRing).         
       + unfold df_R_mat; simpl; invcs H0.
         unfold is_derive_mat, ConstMatrix; intros.
         now apply (@is_derive_const R_AbsRing).                  
     - Case "DVector"%string.
       unfold is_derive_vec; intros.
       specialize (vectoro_to_ovector_forall_some_f H1); intros.
       specialize (H2 i); simpl in H2.
       rewrite vforall_forall in H0.
       assert (H0c := H0).
       specialize (H0 i).
       specialize (H i (y i) H0 H2); simpl in *.
       apply (is_derive_ext (df_R σ (x0 i) v) ); trivial; intros.
       unfold df_R_vec, df_R, df_eval_at_point; simpl.
       match_option.
       + match_option.
         * specialize (vectoro_to_ovector_forall_some_f eqq0); intros.       
           specialize (H3 i); simpl in H3.
           now rewrite eqq in H3; invcs H3.
         * unfold ConstVector.
           apply vectoro_to_ovector_exists_None in eqq0; destruct eqq0.
           specialize (H0c x1).
           apply (eval_fully_closed_not_none (addBinding σ v t) (x0 x1)) in H0c; tauto.
       + match_option.
         specialize (vectoro_to_ovector_forall_some_f eqq0); intros.
         specialize (H3 i); simpl in H3; congruence.
     - Case "DMatrix"%string.
       unfold is_derive_mat; intros.
       unfold matrixo_to_omatrix in H1.
       specialize (vectoro_to_ovector_forall_some_f H1); intros.
       specialize (H2 i); simpl in H2.
       specialize (vectoro_to_ovector_forall_some_f H2); intros.       
       specialize (H3 j); simpl in H3.
       rewrite vforall_forall in H0.
       assert (H0c := H0).
       specialize (H0 i).
       rewrite vforall_forall in H0.
       specialize (H0 j).
       specialize (H i j (y i j) H0 H3); simpl in H.
       apply (is_derive_ext (df_R σ (x0 i j) v)); trivial; intros.
       unfold df_R_mat, df_R, df_eval_at_point; simpl.
       match_option.
       + match_option.
         * unfold matrixo_to_omatrix in eqq0.
           specialize (vectoro_to_ovector_forall_some_f eqq0); intros.       
           specialize (H4 i); simpl in H4.
           specialize (vectoro_to_ovector_forall_some_f H4); intros.                  
           specialize (H5 j); simpl in H5.
           now rewrite eqq in H5; invcs H5.
         * unfold ConstMatrix.
           unfold matrixo_to_omatrix in eqq0.
           apply vectoro_to_ovector_exists_None in eqq0; destruct eqq0.
           apply vectoro_to_ovector_exists_None in e; destruct e.
           specialize (H0c x1).
           rewrite vforall_forall in H0c.
           specialize (H0c x2).
           apply (eval_fully_closed_not_none (addBinding σ v t) (x0 x1 x2)) in H0c; tauto.
       + match_option.
         unfold matrixo_to_omatrix in eqq0.
         specialize (vectoro_to_ovector_forall_some_f eqq0); intros.
         specialize (H4 i); simpl in H4.
         specialize (vectoro_to_ovector_forall_some_f H4); intros.
         specialize (H5 j); simpl in H5; congruence.
     - Case "Var"%string.
       unfold is_derive_gen.
       destruct v0; unfold snd in *.
       destruct d.
       + unfold df_R_gen; simpl.
         invcs H0.
         destruct (vart_dec (s, DTfloat) (v, DTfloat)).
         * unfold equiv_dec, vart_eqdec.
           inversion e.
           destruct (vart_dec (v, DTfloat) (v, DTfloat)); [|congruence].
           apply (is_derive_ext id); [|apply (@is_derive_id R_AbsRing)].
           intro.
           unfold id, df_R, df_eval_at_point.
           simpl.
           unfold equiv_dec, vart_eqdec.
           destruct (vart_dec (v, DTfloat) (v, DTfloat)); [|congruence].
           now refl_simpler.
         * unfold equiv_dec, vart_eqdec.
           destruct (vart_dec (s, DTfloat) (v, DTfloat)); [congruence|].
           invcs H; [congruence | ].
           unfold df_R, df_eval_at_point.
           simpl.
           unfold equiv_dec, vart_eqdec.
           destruct (vart_dec (s, DTfloat) (v, DTfloat)); [congruence|].
           apply (@is_derive_const R_AbsRing).
       + simpl.
         invcs H0.
         unfold is_derive_vec; simpl; intros.
         unfold ConstVector.
         unfold df_R_vec, df_eval_at_point; simpl.
         unfold equiv_dec, vart_eqdec.
         destruct (vart_dec (s, DTVector n) (v, DTfloat)); [congruence |].
         apply (@is_derive_const R_AbsRing).
       + simpl.
         invcs H0.
         unfold is_derive_mat; simpl; intros.
         unfold ConstMatrix.
         unfold df_R_mat, df_eval_at_point; simpl.
         unfold equiv_dec, vart_eqdec.
         destruct (vart_dec (s, DTMatrix m n) (v, DTfloat)); [congruence |].
         apply (@is_derive_const R_AbsRing).
     - Case "Plus"%string.
       destruct H.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _ H eqq).
       specialize (IHdf2 _ H1 eqq0).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_plus.
       + generalize (@is_derive_plus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "Minus"%string.
       destruct H.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _ H eqq).
       specialize (IHdf2 _ H1 eqq0).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_minus.
       + generalize (@is_derive_minus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "Times"%string.
       destruct H.
       do 4 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _ H eqq0).
       specialize (IHdf2 _ H1 eqq2).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_times.
       + generalize Derive.is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d * d2 + d0 * d1) with
                 (d0 * (df_R σ df2 v x) + (df_R σ df1 v x) * d2).
         * apply HH; trivial.
         * unfold df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "Divide"%string.
       destruct H.
       do 4 match_option_in H0.
       invcs H0.
       destruct is_scalar as [isc1 isc2].
       specialize (H _ isc1 H1 eqq0).
       specialize (H0 _ isc2 H3 eqq2).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_divide.
       + generalize is_derive_div; simpl; intros HH.
         replace (d0 / d1 - d * d2 / (d1 * d1)) with
             ((d0 * (df_R σ r v x) - (df_R σ l v x) * d2) / ((df_R σ r v x)*((df_R σ r v x)*1))).
         * destruct (Req_EM_T d1 0); [congruence |].
           inversion H5.
           specialize (HH (df_R σ l v) (df_R σ r v) x d0 d2).
           replace (d0 / d1 - d * d2 / (d1 * d1)) with
             ((d0 * df_R σ r v x - df_R σ l v x * d2) / (df_R σ r v x * (df_R σ r v x * 1))).
           apply HH; trivial.
           unfold df_R, df_eval_at_point; simpl.
           now rewrite eqq1.
           unfold df_R, df_eval_at_point; simpl.           
           rewrite eqq; rewrite eqq1.
           now field.
         * unfold df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           destruct (Req_EM_T d1 0); [congruence |].           
           now field; trivial.
     - Case "Square"%string.
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (Rsqr (df_R σ e v t) = df_R σ (Square a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; unfold Rsqr; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * replace (2 * d * d0) with (d0 * (2 * d)) by lra.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           --  apply is_derive_sqr.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Exp"%string.
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (exp (df_R σ e v t) = df_R σ (Exp a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           --  apply is_derive_exp.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Log"%string.               
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (ln (df_R σ e v t) = df_R σ (Log a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * destruct (Rgt_dec d 0); [|congruence].
           inversion H3.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           --  apply is_derive_ln.
               unfold df_R, df_eval_at_point; simpl.
               rewrite eqq.
               lra.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Abs"%string.         
       do 2 match_option_in H1.
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (Rabs (df_R σ e v t) = df_R σ (Abs a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * destruct ( Req_EM_T d 0 ); [congruence |].
           inversion H3.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ e v x).
           -- replace (@FloatishOps.sign floatish_R (df_R σ e v x)) with (sign (df_R σ e v x)).
              ++ apply is_derive_abs.
                 unfold df_R, df_eval_at_point; simpl.
                 rewrite eqq.
                 lra.
              ++ apply floatish_sign.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Sign"%string.         
       match_option_in H1.
       match_option_in H1.
       destruct (Req_EM_T d 0); [congruence|].
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (sign (df_R σ e v t) = df_R σ (Sign a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
         apply floatish_sign.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * replace (0) with (d0 * 0) by lra.
           apply (@is_derive_comp R_AbsRing); trivial.           
           apply is_derive_sign.
           unfold df_R, df_eval_at_point; simpl.           
           rewrite eqq; lra.
     - Case "PSign"%string.         
       match_option_in H1.
       match_option_in H1.
       destruct (Req_EM_T d 0); [congruence|].
       invcs H1.
       specialize (H _ is_scalar H0 eqq0).
       assert (forall t, (psign (df_R σ e v t) = df_R σ (PSign a e) v t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) e); simpl; trivial.
         rewrite e0; trivial.
         apply pos_sign_psign.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H1.
         * replace (0) with (d0 * 0) by lra.
           apply (@is_derive_comp R_AbsRing); trivial.           
           apply is_derive_psign.
           unfold df_R, df_eval_at_point; simpl.           
           rewrite eqq; lra.
     - Case "Max"%string.
       do 2 match_option_in H2.
       destruct H1.
       destruct is_scalar as [isc1  isc2].
       assert (forall t, (Rmax (df_R σ l v t) (df_R σ r v t)) = df_R σ (Max a l r) v t).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v t) l); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v t) r); simpl; trivial. 
         rewrite e, e0; trivial.
         apply Rmax_Fmax.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H4.
         * match_option_in H2.
           match_option_in H2.           
           destruct (Req_EM_T d d0); [congruence |].
           destruct (Rlt_dec d d0).
           -- invcs H2.
              specialize (H _ isc1 H1 eqq1).
              specialize (H0 _ isc2 H3 eqq2).
              replace (y) with ((d1 + y + (d1-y)*sign(df_R σ l v x - df_R σ r v x))/2).
              ++ apply is_derive_max; trivial.
                 unfold df_R, df_eval_at_point; simpl.           
                 now rewrite eqq, eqq0.
              ++ unfold df_R, df_eval_at_point; simpl.           
                 rewrite eqq, eqq0.
                 unfold sign; simpl.
                 destruct (total_order_T 0 (d - d0)).
                 ** destruct s; lra.
                 ** lra.
           -- invcs H2.
              specialize (H _ isc1 H1 eqq1).
              specialize (H0 _ isc2 H3 eqq2).
              replace (y) with ((y + d2 + (y - d2)*sign(df_R σ l v x - df_R σ r v x))/2).
              ++ apply is_derive_max; trivial.
                 unfold df_R, df_eval_at_point; simpl.           
                 now rewrite eqq, eqq0.
              ++ unfold df_R, df_eval_at_point; simpl.           
                 rewrite eqq, eqq0.
                 unfold sign; simpl.
                 destruct (total_order_T 0 (d - d0)).
                 ** destruct s; lra.
                 ** lra.
   Qed.
   


(*
   Theorem df_eval_deriv_complete σ (df:DefinedFunction UnitAnn DTfloat) v (x:R)
     : is_scalar_function df -> 
       ex_deriv_df σ df v x  ->
       df_eval_deriv_exact (addBinding σ v x) df (v,DTfloat) = Some (Derive (df_R σ df v) x).
   Proof.
     simpl.
     intros is_scalar.
     generalize is_scalar.
     pattern df.
     revert df is_scalar.
     DefinedFunction_scalar_cases (apply is_scalar_function_ind) Case; simpl; intros.
     - Case "Number"%string.
       unfold df_R; simpl.
       now rewrite Derive_const.
     - Case "Constant"%string.
       unfold df_R; simpl.
       now rewrite Derive_const.
     - Case "Var"%string.
       f_equal.
       unfold df_R.
       unfold ex_deriv_df in H.
       destruct H.
       match_case; intros.
       + unfold df_eval_at_point; simpl.
         rewrite H1; simpl.
         refl_simpler; simpl.
         now rewrite Derive_id.
       + unfold df_eval_at_point; simpl.
         rewrite H1; simpl.
         match_option.
         * now rewrite Derive_const.
         * now rewrite Derive_const.
     - Case "Plus"%string.
       unfold ex_deriv_df in H1.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       cut_to H7; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       rewrite eqq in H.
       rewrite eqq0 in H0.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       replace (df_R σ (Plus a l r) v) with (fun x0 => ((df_R σ l v)x0) + ((df_R σ r v)x0)).
       + rewrite Derive_plus; trivial.
         inversion H; inversion H0.
         now subst.
       + unfold df_R.
         apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H11; [|apply H1].
         cut_to H12; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Minus"%string.
       unfold ex_deriv_df in H1.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       cut_to H7; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       rewrite eqq in H.
       rewrite eqq0 in H0.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       replace (df_R σ (Minus a l r) v) with (fun x0 => ((df_R σ l v)x0) - ((df_R σ r v)x0)).
       + rewrite Derive_minus; trivial.
         inversion H; inversion H0.
         now subst.
       + unfold df_R.
         apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H11; [|apply H1].
         cut_to H12; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Times"%string.
       unfold ex_deriv_df in H1.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_fully_closed_not_none (addBinding σ v x) l); simpl; intros.
       generalize (eval_fully_closed_not_none (addBinding σ v x) r); simpl; intros.
       cut_to H7; [|apply H1].
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       cut_to H9; [|apply H1].
       match_option; [|tauto].
       match_option; [|tauto].       
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       cut_to H10; [|apply H1].
       match_option; [|tauto].       
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       replace (df_R σ (Times a l r) v) with (fun x0 => ((df_R σ l v)x0) * ((df_R σ r v)x0)).
       + rewrite Derive_mult; trivial.
         rewrite eqq0 in H.
         rewrite eqq2 in H0.
         inversion H; inversion H0.
         rewrite <- H14.
         rewrite <- H15.
         unfold df_R.
         unfold df_eval_at_point.
         rewrite eqq, eqq1.
         f_equal; lra.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H13; [|apply H1].
         cut_to H14; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Divide"%string.
       unfold ex_deriv_df in H1.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_fully_closed_not_none (addBinding σ v x) l); simpl; intros.
       generalize (eval_fully_closed_not_none (addBinding σ v x) r); simpl; intros.
       cut_to H7; [|apply H1].
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       cut_to H9; [|apply H1].
       match_option; [|tauto].
       match_option; [|tauto].       
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       cut_to H10; [|apply H1].
       match_option; [|tauto].       
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       assert (d1 <> 0).
       admit.
       replace (df_R σ (Divide a l r) v) with (fun x0 => ((df_R σ l v)x0) / ((df_R σ r v)x0)).
       + rewrite Derive_div; trivial.
         rewrite eqq0 in H.
         rewrite eqq2 in H0.
         inversion H; inversion H0.
         rewrite <- H15.
         rewrite <- H16.
         unfold df_R.
         unfold df_eval_at_point.
         rewrite eqq, eqq1.
         f_equal; field; trivial.
         unfold df_R.
         unfold df_eval_at_point.
         now rewrite eqq1.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H14; [|apply H1].
         cut_to H15; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Square"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e); simpl; intros.       
       assert (H1c := H1).
       unfold ex_deriv_df in H1.
       destruct H1.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       replace (df_R σ (Square a e) v) with (fun x0 => Rsqr ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_sqr.
           rewrite eqq0 in H.
           cut_to H; trivial; inversion H.
           rewrite <- H7.
           unfold df_R, df_eval_at_point.
           rewrite eqq; f_equal.
           now lra.
         * unfold ex_derive; eexists; eapply is_derive_sqr.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         match_option.
         unfold Rsqr.
         lra.
     - Case "Exp"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e); simpl; intros.       
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       replace (df_R σ (Exp a e) v) with (fun x0 => exp ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_exp.
           cut_to H; trivial.
           rewrite eqq0 in H.
           inversion H.
           rewrite <- H7.
           unfold df_R, df_eval_at_point.
           now rewrite eqq.
         * unfold ex_derive; eexists; eapply is_derive_exp.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros.       
         match_option; tauto.
     - Case "Log"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e); simpl; intros.       
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 < df_R σ e v x).
       admit.
       replace (df_R σ (Log a e) v) with (fun x0 => ln ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_ln; trivial.
           cut_to H; trivial.
           rewrite eqq0 in H.
           inversion H.
           rewrite <- H8.
           unfold df_R, df_eval_at_point.
           now rewrite eqq.
         * unfold ex_derive; eexists; eapply is_derive_ln; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros.       
         match_option; tauto.
     - Case "Abs"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e ); simpl; intros.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 <> df_R σ e v x).
       admit.
       replace (df_R σ (Abs a e) v) with (fun x0 => abs ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_abs; trivial.
           cut_to H; trivial.
           rewrite eqq0 in H.
           inversion H.
           rewrite <- H8; f_equal.
           unfold df_R, df_eval_at_point.
           rewrite eqq.
           unfold sign, FloatishOps.sign.
           destruct (total_order_T 0 d).
           -- destruct s; simpl.
              ++ destruct (Rlt_dec d 0); [lra|].
                 destruct (Rgt_dec d 0); lra.
              ++ destruct (Rlt_dec d 0); [lra|].
                 destruct (Rgt_dec d 0); lra.
           -- simpl; destruct (Rlt_dec d 0); lra.
         * unfold ex_derive; eexists; eapply is_derive_abs; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros. 
         match_option.
         unfold abs; simpl.
         unfold Rabs.
         match_case; intros; lra.
     - Case "Sign"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 <> df_R σ e v x).
       admit.
       replace (df_R σ (Sign a e) v) with (fun x0 => sign ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_sign; trivial.
           cut_to H; trivial.
           rewrite eqq in H.
           inversion H.
           rewrite <- H7; f_equal; lra.
         * unfold ex_derive; eexists; eapply is_derive_sign; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros. 
         match_option; [|tauto].
         unfold sign.
         unfold FloatishOps.sign.
         match_case; intros; simpl.
         * destruct s; simpl.
           -- destruct (Rlt_dec d0 0); [lra|].
              now destruct (Rgt_dec d0 0); [|lra].
           -- destruct (Rlt_dec d0 0); [lra|].
              now destruct (Rgt_dec d0 0); [lra|].
         * destruct (Rlt_dec d0 0); [lra|].
           now destruct (Rgt_dec d0 0); [|lra].
     - Case "PSign"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 <> df_R σ e v x).
       admit.
       replace (df_R σ (PSign a e) v) with (fun x0 => psign ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_psign; trivial.
           cut_to H; trivial.
           rewrite eqq in H.
           inversion H.
           rewrite <- H7; f_equal; lra.
         * unfold ex_derive; eexists; eapply is_derive_psign; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros. 
         match_option; [|tauto].
         unfold psign, pos_sign.
         match_case; intros; simpl.
         * destruct (Rge_dec d0 0); lra.
         * destruct (Rge_dec d0 0); lra.
     - Case "Max"%string.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_fully_closed_not_none (addBinding σ v x) l); simpl; intros.
       generalize (eval_fully_closed_not_none (addBinding σ v x) r); simpl; intros.
       cut_to H7; [|apply H1].
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       match_option; [|tauto].
       assert (df_R σ l v x <> df_R σ r v x).
       admit.
       cut_to H; trivial.
       cut_to H0; trivial.

       replace (df_R σ (Max a l r) v) with (fun x0 => Rmax ((df_R σ l v)x0) ((df_R σ r v)x0)).       
       + unfold ex_deriv_df in H5; destruct H5.
         unfold ex_deriv_df in H6; destruct H6.
         case_eq (df_eval_deriv_exact (addBinding σ v x) l (v, DTfloat)); intros; [|tauto].
         case_eq (df_eval_deriv_exact (addBinding σ v x) r (v, DTfloat)); intros; [|tauto].
         rewrite Derive_max; trivial.
         rewrite H14 in H.
         rewrite H15 in H0.
         inversion H; inversion H0.
         rewrite <- H17.
         rewrite <- H18.
         unfold df_R, df_eval_at_point.
         rewrite eqq0; rewrite eqq.
         unfold df_R,df_eval_at_point in H11.
         rewrite eqq in H11; rewrite eqq0 in H11.
         case_eq (Rle_dec d d0); intros.
         * f_equal; unfold sign.
           match_case; intros.
           -- destruct s; lra.
           -- lra.
         * f_equal; unfold sign.
           match_case; intros.
           -- destruct s; lra.
           -- lra.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H13; [|apply H1].
         cut_to H12; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
         intros.
         unfold Rmax, Fmax.
         case_eq (Rle_dec d1 d2); intros; simpl.
         case_eq (Rlt_dec d1 d2); intros; simpl; trivial; lra.
         case_eq (Rlt_dec d1 d2); intros; simpl; lra.
   Admitted.
*)
   
    Definition ex_deriv_df_vec {Ann} {n} σ (df:DefinedFunction Ann (DTVector n)) v (x:R)
     :=  fully_closed_over df ((v,DTfloat)::map (@projT1 _ _) σ) /\
         forall i,  ex_derive (fun x0 => (df_R_vec σ df v) x0 i) x.

    Definition ex_deriv_df_mat {Ann} {n m} σ (df:DefinedFunction Ann (DTMatrix n m)) v (x:R)
     :=  fully_closed_over df ((v,DTfloat)::map (@projT1 _ _) σ) /\
         forall i j,  ex_derive (fun x0 => (df_R_mat σ df v) x0 i j) x.

    Definition ex_deriv_df_gen (T:definition_function_types) (σ:df_env) :  
       DefinedFunction UnitAnn T -> SubVar -> R -> Prop :=
      match T with
     | DTfloat => fun df v x => ex_deriv_df σ df v x
     | DTVector n => fun df v x => ex_deriv_df_vec σ df v x
     | DTMatrix n m => fun df v x => ex_deriv_df_mat σ df v x
     end.
   
    Definition Derive_vec {n} (f : R -> Vector R n) (x:R) : Vector R n :=
      fun i => Derive (fun x0 => f x0 i) x.

    Definition Derive_mat {n m} (f : R -> Matrix R n m) (x:R) : Matrix R n m :=
      fun i j => Derive (fun x0 => f x0 i j) x.

    Definition Derive_gen {T} (f: R->definition_function_types_interp T) (x:R)
        :=
          (match T return (R -> definition_function_types_interp T) ->
                     definition_function_types_interp T
           with
           | DTfloat => fun f =>  Derive f x
           | DTVector n => fun f => Derive_vec f x
           | DTMatrix n m => fun f => Derive_mat f x
           end) f.
    
   Theorem df_eval_deriv_exact_correct_gen {T} (σ:df_env) (df:DefinedFunction UnitAnn T) v (x:R) :
       ex_deriv_df_gen T σ df v x  ->
       df_eval_deriv_exact (addBinding σ v x) df (v,DTfloat) =
       Some (Derive_gen (df_R_gen UnitAnn T σ df v) x).
   Proof.
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case; simpl; intros.
     - Case "Number"%string.
       unfold df_R; simpl.
       now rewrite Derive_const.
     - Case "Constant"%string.
       unfold df_R_gen, Derive_gen; simpl.
       destruct t.
       + unfold df_R; simpl.
         now rewrite Derive_const.
       + unfold df_R_vec; simpl.
         unfold Derive_vec; f_equal.
         unfold ConstVector.
         apply FunctionalExtensionality.functional_extensionality; intros.
         now rewrite Derive_const.
       + unfold df_R_mat; simpl.
         unfold Derive_mat; f_equal.
         unfold ConstMatrix.
         apply FunctionalExtensionality.functional_extensionality; intros.
         apply FunctionalExtensionality.functional_extensionality; intros.         
         now rewrite Derive_const.
     - Case "DVector"%string; admit.
     - Case "DMatrix"%string; admit.
     - Case "Var"%string.
       f_equal.
       unfold Derive_gen.
       unfold var_type in v0.
       destruct v0.
       simpl.
       destruct d; simpl; unfold var_type.
       + destruct (equiv_dec (s, DTfloat) (v, DTfloat)); simpl.
         * admit.
         * admit.
       + admit.
       + admit.
     - Case "Plus"%string.
       unfold ex_deriv_df in H.
       destruct H.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) df1 (v,DTfloat)); simpl; intros.
       cut_to H1; [|apply H].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) df2 (v,DTfloat)); simpl; intros.       
       cut_to H2; [|apply H].
       match_option; [|tauto].
       rewrite eqq in H.
       rewrite eqq0 in H0.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       replace (df_R σ (Plus a l r) v) with (fun x0 => ((df_R σ l v)x0) + ((df_R σ r v)x0)).
       + rewrite Derive_plus; trivial.
         inversion H; inversion H0.
         now subst.
       + unfold df_R.
         apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H11; [|apply H1].
         cut_to H12; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Minus"%string.
       unfold ex_deriv_df in H1.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       cut_to H7; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       rewrite eqq in H.
       rewrite eqq0 in H0.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       replace (df_R σ (Minus a l r) v) with (fun x0 => ((df_R σ l v)x0) - ((df_R σ r v)x0)).
       + rewrite Derive_minus; trivial.
         inversion H; inversion H0.
         now subst.
       + unfold df_R.
         apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H11; [|apply H1].
         cut_to H12; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Times"%string.
       unfold ex_deriv_df in H1.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_fully_closed_not_none (addBinding σ v x) l); simpl; intros.
       generalize (eval_fully_closed_not_none (addBinding σ v x) r); simpl; intros.
       cut_to H7; [|apply H1].
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       cut_to H9; [|apply H1].
       match_option; [|tauto].
       match_option; [|tauto].       
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       cut_to H10; [|apply H1].
       match_option; [|tauto].       
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       replace (df_R σ (Times a l r) v) with (fun x0 => ((df_R σ l v)x0) * ((df_R σ r v)x0)).
       + rewrite Derive_mult; trivial.
         rewrite eqq0 in H.
         rewrite eqq2 in H0.
         inversion H; inversion H0.
         rewrite <- H14.
         rewrite <- H15.
         unfold df_R.
         unfold df_eval_at_point.
         rewrite eqq, eqq1.
         f_equal; lra.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H13; [|apply H1].
         cut_to H14; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Divide"%string.
       unfold ex_deriv_df in H1.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_fully_closed_not_none (addBinding σ v x) l); simpl; intros.
       generalize (eval_fully_closed_not_none (addBinding σ v x) r); simpl; intros.
       cut_to H7; [|apply H1].
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       cut_to H9; [|apply H1].
       match_option; [|tauto].
       match_option; [|tauto].       
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       cut_to H10; [|apply H1].
       match_option; [|tauto].       
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold ex_deriv_df in H5; destruct H5.
       unfold ex_deriv_df in H6; destruct H6.
       assert (d1 <> 0).
       admit.
       replace (df_R σ (Divide a l r) v) with (fun x0 => ((df_R σ l v)x0) / ((df_R σ r v)x0)).
       + rewrite Derive_div; trivial.
         rewrite eqq0 in H.
         rewrite eqq2 in H0.
         inversion H; inversion H0.
         rewrite <- H15.
         rewrite <- H16.
         unfold df_R.
         unfold df_eval_at_point.
         rewrite eqq, eqq1.
         f_equal; field; trivial.
         unfold df_R.
         unfold df_eval_at_point.
         now rewrite eqq1.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H14; [|apply H1].
         cut_to H15; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
     - Case "Square"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e); simpl; intros.       
       assert (H1c := H1).
       unfold ex_deriv_df in H1.
       destruct H1.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       replace (df_R σ (Square a e) v) with (fun x0 => Rsqr ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_sqr.
           rewrite eqq0 in H.
           cut_to H; trivial; inversion H.
           rewrite <- H7.
           unfold df_R, df_eval_at_point.
           rewrite eqq; f_equal.
           now lra.
         * unfold ex_derive; eexists; eapply is_derive_sqr.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         match_option.
         unfold Rsqr.
         lra.
     - Case "Exp"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e); simpl; intros.       
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       replace (df_R σ (Exp a e) v) with (fun x0 => exp ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_exp.
           cut_to H; trivial.
           rewrite eqq0 in H.
           inversion H.
           rewrite <- H7.
           unfold df_R, df_eval_at_point.
           now rewrite eqq.
         * unfold ex_derive; eexists; eapply is_derive_exp.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros.       
         match_option; tauto.
     - Case "Log"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e); simpl; intros.       
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 < df_R σ e v x).
       admit.
       replace (df_R σ (Log a e) v) with (fun x0 => ln ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_ln; trivial.
           cut_to H; trivial.
           rewrite eqq0 in H.
           inversion H.
           rewrite <- H8.
           unfold df_R, df_eval_at_point.
           now rewrite eqq.
         * unfold ex_derive; eexists; eapply is_derive_ln; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros.       
         match_option; tauto.
     - Case "Abs"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       generalize (eval_fully_closed_not_none (addBinding σ v x) e ); simpl; intros.
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 <> df_R σ e v x).
       admit.
       replace (df_R σ (Abs a e) v) with (fun x0 => abs ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_abs; trivial.
           cut_to H; trivial.
           rewrite eqq0 in H.
           inversion H.
           rewrite <- H8; f_equal.
           unfold df_R, df_eval_at_point.
           rewrite eqq.
           unfold sign, FloatishOps.sign.
           destruct (total_order_T 0 d).
           -- destruct s; simpl.
              ++ destruct (Rlt_dec d 0); [lra|].
                 destruct (Rgt_dec d 0); lra.
              ++ destruct (Rlt_dec d 0); [lra|].
                 destruct (Rgt_dec d 0); lra.
           -- simpl; destruct (Rlt_dec d 0); lra.
         * unfold ex_derive; eexists; eapply is_derive_abs; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros. 
         match_option.
         unfold abs; simpl.
         unfold Rabs.
         match_case; intros; lra.
     - Case "Sign"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 <> df_R σ e v x).
       admit.
       replace (df_R σ (Sign a e) v) with (fun x0 => sign ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_sign; trivial.
           cut_to H; trivial.
           rewrite eqq in H.
           inversion H.
           rewrite <- H7; f_equal; lra.
         * unfold ex_derive; eexists; eapply is_derive_sign; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros. 
         match_option; [|tauto].
         unfold sign.
         unfold FloatishOps.sign.
         match_case; intros; simpl.
         * destruct s; simpl.
           -- destruct (Rlt_dec d0 0); [lra|].
              now destruct (Rgt_dec d0 0); [|lra].
           -- destruct (Rlt_dec d0 0); [lra|].
              now destruct (Rgt_dec d0 0); [lra|].
         * destruct (Rlt_dec d0 0); [lra|].
           now destruct (Rgt_dec d0 0); [|lra].
     - Case "PSign"%string.
       assert (ex_deriv_df σ e v x).
       admit.
       assert (H1c := H1).
       unfold ex_deriv_df in H1; destruct H1.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) e (v,DTfloat)); simpl; intros.
       match_option; [|tauto].
       unfold ex_deriv_df in H0.
       destruct H0.
       assert (0 <> df_R σ e v x).
       admit.
       replace (df_R σ (PSign a e) v) with (fun x0 => psign ((df_R σ e v) x0)).
       + rewrite Derive_comp; trivial.
         * rewrite Derive_psign; trivial.
           cut_to H; trivial.
           rewrite eqq in H.
           inversion H.
           rewrite <- H7; f_equal; lra.
         * unfold ex_derive; eexists; eapply is_derive_psign; trivial.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R, df_eval_at_point; simpl.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) e); simpl; intros. 
         match_option; [|tauto].
         unfold psign, pos_sign.
         match_case; intros; simpl.
         * destruct (Rge_dec d0 0); lra.
         * destruct (Rge_dec d0 0); lra.
     - Case "Max"%string.
       destruct H1.
       destruct is_scalar.
       assert ((ex_deriv_df σ l v x) /\  (ex_deriv_df σ r v x)).
       admit.
       destruct H5.
       generalize (eval_fully_closed_not_none (addBinding σ v x) l); simpl; intros.
       generalize (eval_fully_closed_not_none (addBinding σ v x) r); simpl; intros.
       cut_to H7; [|apply H1].
       cut_to H8; [|apply H1].
       match_option; [|tauto].
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) l (v,DTfloat)); simpl; intros.
       generalize (eval_deriv_fully_closed_not_none (addBinding σ v x) r (v,DTfloat)); simpl; intros.       
       match_option; [|tauto].
       assert (df_R σ l v x <> df_R σ r v x).
       admit.
       cut_to H; trivial.
       cut_to H0; trivial.

       replace (df_R σ (Max a l r) v) with (fun x0 => Rmax ((df_R σ l v)x0) ((df_R σ r v)x0)).       
       + unfold ex_deriv_df in H5; destruct H5.
         unfold ex_deriv_df in H6; destruct H6.
         case_eq (df_eval_deriv (addBinding σ v x) l (v, DTfloat)); intros; [|tauto].
         case_eq (df_eval_deriv (addBinding σ v x) r (v, DTfloat)); intros; [|tauto].
         rewrite Derive_max; trivial.
         rewrite H14 in H.
         rewrite H15 in H0.
         inversion H; inversion H0.
         rewrite <- H17.
         rewrite <- H18.
         unfold df_R, df_eval_at_point.
         rewrite eqq0; rewrite eqq.
         unfold df_R,df_eval_at_point in H11.
         rewrite eqq in H11; rewrite eqq0 in H11.
         case_eq (Rle_dec d d0); intros.
         * f_equal; unfold sign.
           match_case; intros.
           -- destruct s; lra.
           -- lra.
         * f_equal; unfold sign.
           match_case; intros.
           -- destruct s; lra.
           -- lra.
       + apply FunctionalExtensionality.functional_extensionality; intros.
         unfold df_R.
         unfold df_eval_at_point.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) l); simpl; intros.
         generalize (eval_fully_closed_not_none (addBinding σ v x0) r); simpl; intros.
         cut_to H13; [|apply H1].
         cut_to H12; [|apply H1].
         match_option; [|tauto].
         case_eq (df_eval (addBinding σ v x0) r); [|tauto]; trivial.
         intros.
         unfold Rmax, Fmax.
         case_eq (Rle_dec d1 d2); intros; simpl.
         case_eq (Rlt_dec d1 d2); intros; simpl; trivial; lra.
         case_eq (Rlt_dec d1 d2); intros; simpl; lra.
   Admitted.

