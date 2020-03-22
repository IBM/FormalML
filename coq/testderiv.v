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
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Rcomplements.
Require Import DefinedFunctions.
Require FunctionalExtensionality.

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
                  match df_eval_deriv_exact (cons (mk_env_entry xv (re i)) nil) s xv with
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
                  match df_eval_deriv_exact (cons (mk_env_entry xv (re i j)) σ) s xv with
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
                                                   (cons (mk_env_entry xv2 (r i)) σ)) s xv1 with
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
                                                   (cons (mk_env_entry xv2 (r i j)) σ)) s xv1 with
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

(*
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
*)    
    Lemma floatish_sign :
      forall (x:R), sign x = FloatishOps.sign x.
    Proof.
      intros.
      unfold sign, FloatishOps.sign; simpl.
      case_eq (Rlt_dec x 0); intros; trivial.
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
         replace (d * d2 + d0 * d1)%R with
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
           replace (d0 / d1 - d * d2 / (d1 * d1))%R with
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
         * replace (2 * d * d0)%R with (d0 * (2 * d))%R by lra.
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
           replace (d) with (df_R σ e v x)
           ; unfold df_R, df_eval_at_point; simpl; rewrite eqq; trivial.
           apply is_derive_abs; lra.
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
         * replace (0)%R with (d0 * 0)%R by lra.
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
         * replace (0)%R with (d0 * 0)%R by lra.
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

    Definition vec_to_nat_fun {n:nat} (v:Vector R n) (i:nat) : R :=
        match lt_dec i n with
        | left pf => v (exist _ i pf)
        | right _ => 0
        end.

    Lemma vec_to_nat_fun_vcons_end {n} (v : Vector R n) b : 
      vec_to_nat_fun (vcons b v) n = b.
    Proof.
      unfold vec_to_nat_fun; simpl.
      destruct (lt_dec n (S n)); [ | omega].
      destruct (Nat.eq_dec n n); [ | omega].
      trivial.
    Qed.

    Lemma vec_to_nat_fun_vcons_nend {n} (v : Vector R n) b m (pf:(m<n)%nat) : 
      vec_to_nat_fun (vcons b v) m = vec_to_nat_fun v m.
    Proof.
      unfold vec_to_nat_fun; simpl.
      destruct (lt_dec m (S n)); [ | omega].
      destruct (Nat.eq_dec m n); [omega | ].
      destruct (lt_dec m n); [| omega].
      erewrite index_pf_irrel; eauto.
    Qed.

    Lemma sum_n_vsum {n:nat} (v:Vector R n) :
      sum_n (vec_to_nat_fun v) (n-1) = vsum v.
    Proof.
      unfold vsum, vector_fold_right1.
      apply (vector_fold_right1_dep_gen_ind (P:=fun n v r => sum_n (vec_to_nat_fun v) (n-1) = r)).
      - unfold vec_to_nat_fun, sum_n, sum_n_m, Iter.iter, Iter.iter_nat, plus, zero.
        simpl.
        lra.
      - unfold vec_to_nat_fun, sum_n, sum_n_m, Iter.iter, Iter.iter_nat, plus, zero, Datatypes.id.
        simpl; intros.
        lra.
      - intros.
        simpl.
        rewrite <- H.
        destruct n0.
        + unfold vec_to_nat_fun, sum_n, sum_n_m, Iter.iter, Iter.iter_nat, plus, zero, Datatypes.id.
          simpl.
          lra.
        + simpl.
          rewrite Nat.sub_0_r.
          rewrite sum_Sn.
          unfold plus; simpl.
          rewrite vec_to_nat_fun_vcons_end.
          rewrite Rplus_comm.
          f_equal; simpl.
          erewrite sum_n_ext_loc; [ reflexivity | ]; intros.
          apply vec_to_nat_fun_vcons_nend.
          omega.
    Qed.

    Lemma is_derive_vsum {n} (vf : R -> Vector R n) (x:R) (df : Vector R n) :
      is_derive_vec vf x df ->
      is_derive (fun x0 => vsum (vf x0)) x (vsum df).
    Proof.
      unfold is_derive_vec; intro.
      apply (is_derive_ext (fun x0 => sum_n (vec_to_nat_fun (vf x0)) (n-1)%nat))
      ; [intros; apply sum_n_vsum |].
      replace  (@vsum floatish_R n df) with (sum_n (vec_to_nat_fun df) (n-1)%nat)
      ; [|intros; apply sum_n_vsum ].
      apply (@is_derive_sum_n R_AbsRing); intros.
      unfold vec_to_nat_fun.
      destruct (lt_dec k n).
      - apply H.
      - apply (@is_derive_const R_AbsRing).
    Qed.

    Lemma is_derive_msum {n m} (mf : R -> Matrix R n m) (x:R) (df : Matrix R n m) :
      is_derive_mat mf x df ->
      is_derive (fun x0 => msum (mf x0)) x (msum df).
    Proof.
      simpl.
      unfold is_derive_mat; intro.
      unfold msum.
      apply is_derive_vsum.
      unfold is_derive_vec; simpl; intro.
      rewrite vmap_nth.
      apply (is_derive_ext (fun x0 => (@vsum floatish_R m) (mf x0 i))).
      - intro; now rewrite vmap_nth.
      - apply is_derive_vsum.
        now unfold is_derive_vec.
    Qed.

    Lemma apply_vector_correct (v v0 : SubVar) (x:R) :
      let vec : Vector (DefinedFunction UnitAnn DTfloat) 2 :=
          fun _ => Var (v, DTfloat) tt in
      let dfvec := DVector tt vec in
      let env := addBinding nil v 1 in
      df_eval_deriv_exact env (VectorSum tt dfvec) (v,DTfloat) =
      df_eval_deriv_exact env (VectorSum tt (VectorApply tt v0 (Var (v0, DTfloat) tt) dfvec)) 
                          (v,DTfloat).
   Proof.
      intros.
      simpl.
      match_option.
      - match_option_in eqq.
        f_equal; f_equal.
        unfold vectoro_to_ovector in eqq.
        unfold vector_fold_right_dep in eqq.
        unfold vector_fold_right_bounded_dep in eqq.        
        simpl in eqq.
        unfold equiv_dec, vart_eqdec in *.
        destruct (vart_dec (v, DTfloat) (v,DTfloat)).
        destruct (vart_dec (v0, DTfloat) (v0, DTfloat)).
        replace (1*1)%R with 1 in eqq.
        inversion eqq; trivial.
        simpl; lra.
        tauto.
        congruence.
      - match_option_in eqq.
        apply vectoro_to_ovector_exists_None in eqq0.
        destruct eqq0.
        unfold equiv_dec, vart_eqdec in *.
        destruct (vart_dec (v, DTfloat) (v,DTfloat)).
        congruence.
        tauto.
   Qed.
   
    Lemma apply_vector_correct2 (v v0 : SubVar) (x:R) :
      let vec : Vector (DefinedFunction UnitAnn DTfloat) 2 :=
          fun _ => Var (v, DTfloat) tt in
      let dfvec := DVector tt vec in
      let env := addBinding nil v 1 in
      df_eval_deriv_exact env (VectorSum tt (VectorApply tt v0 (Var (v0, DTfloat) tt) dfvec)) 
                          (v,DTfloat) = Some (1 + 1)%R.
   Proof.
      intros.
      simpl.
      match_option.
      - match_option_in eqq.
        f_equal; f_equal.
        unfold vectoro_to_ovector in eqq.
        unfold vector_fold_right_dep in eqq.
        unfold vector_fold_right_bounded_dep in eqq.        
        simpl in eqq.
        unfold equiv_dec, vart_eqdec in *.
        destruct (vart_dec (v, DTfloat) (v,DTfloat)); [|congruence].
        destruct (vart_dec (v0, DTfloat) (v0, DTfloat)); [|congruence].
        replace (1*1)%R with 1 in eqq.
        + inversion eqq; trivial.
        + simpl; lra.
      - match_option_in eqq.
        apply vectoro_to_ovector_exists_None in eqq0.
        destruct eqq0.
        unfold equiv_dec, vart_eqdec in e.
        destruct (vart_dec (v, DTfloat) (v,DTfloat)); congruence.
   Qed.



    Theorem df_eval_deriv_exact_gen_correct {T} σ (df:DefinedFunction UnitAnn T) v (x:R) y
     : fully_closed_over df ((v,DTfloat)::map (@projT1 _ _) σ) ->
       df_eval_deriv_exact (addBinding σ v x) df (v,DTfloat) = Some y ->
       is_derive_gen (df_R_gen UnitAnn T σ df v) x y.
   Proof.
     revert  σ v x.
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case; simpl; intros σ v0 xx; intros.
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
       specialize (H i (y i) σ v0 xx H0 H2); simpl in *.
       apply (is_derive_ext (df_R σ (x i) v0) ); trivial; intros.
       unfold df_R_vec, df_R, df_eval_at_point; simpl.
       match_option.
       + match_option.
         * specialize (vectoro_to_ovector_forall_some_f eqq0); intros.       
           specialize (H3 i); simpl in H3.
           now rewrite eqq in H3; invcs H3.
         * unfold ConstVector.
           apply vectoro_to_ovector_exists_None in eqq0; destruct eqq0.
           specialize (H0c x0).
           apply (eval_fully_closed_not_none (addBinding σ v0 t) (x x0)) in H0c; tauto.
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
       specialize (H i j (y i j)  σ v0 xx H0 H3); simpl in H.
       apply (is_derive_ext (df_R σ (x i j) v0)); trivial; intros.
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
           specialize (H0c x0).
           rewrite vforall_forall in H0c.
           specialize (H0c x1).
           apply (eval_fully_closed_not_none (addBinding σ v0 t) (x x0 x1)) in H0c; tauto.
       + match_option.
         unfold matrixo_to_omatrix in eqq0.
         specialize (vectoro_to_ovector_forall_some_f eqq0); intros.
         specialize (H4 i); simpl in H4.
         specialize (vectoro_to_ovector_forall_some_f H4); intros.
         specialize (H5 j); simpl in H5; congruence.
     - Case "Var"%string.
       unfold is_derive_gen.
       destruct v; unfold snd in *.
       destruct d.
       + unfold df_R_gen; simpl.
         invcs H0.
         destruct (vart_dec (s, DTfloat) (v0, DTfloat)).
         * unfold equiv_dec, vart_eqdec.
           inversion e.
           destruct (vart_dec (v0, DTfloat) (v0, DTfloat)); [|congruence].
           apply (is_derive_ext id); [|apply (@is_derive_id R_AbsRing)].
           intro.
           unfold id, df_R, df_eval_at_point.
           simpl.
           unfold equiv_dec, vart_eqdec.
           destruct (vart_dec (v0, DTfloat) (v0, DTfloat)); [|congruence].
           now refl_simpler.
         * unfold equiv_dec, vart_eqdec.
           destruct (vart_dec (s, DTfloat) (v0, DTfloat)); [congruence|].
           invcs H; [congruence | ].
           unfold df_R, df_eval_at_point.
           simpl.
           unfold equiv_dec, vart_eqdec.
           destruct (vart_dec (s, DTfloat) (v0, DTfloat)); [congruence|].
           apply (@is_derive_const R_AbsRing).
       + simpl.
         invcs H0.
         unfold is_derive_vec; simpl; intros.
         unfold ConstVector.
         unfold df_R_vec, df_eval_at_point; simpl.
         unfold equiv_dec, vart_eqdec.
         destruct (vart_dec (s, DTVector n) (v0, DTfloat)); [congruence |].
         apply (@is_derive_const R_AbsRing).
       + simpl.
         invcs H0.
         unfold is_derive_mat; simpl; intros.
         unfold ConstMatrix.
         unfold df_R_mat, df_eval_at_point; simpl.
         unfold equiv_dec, vart_eqdec.
         destruct (vart_dec (s, DTMatrix m n) (v0, DTfloat)); [congruence |].
         apply (@is_derive_const R_AbsRing).
     - Case "Plus"%string.
       destruct H.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _  σ v0 xx H eqq).
       specialize (IHdf2 _  σ v0 xx H1 eqq0).
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
       specialize (IHdf1 _  σ v0 xx H eqq).
       specialize (IHdf2 _  σ v0 xx H1 eqq0).
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
       specialize (IHdf1 _  σ v0 xx H eqq0).
       specialize (IHdf2 _  σ v0 xx H1 eqq2).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_times.
       + generalize Derive.is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d * d2 + d0 * d1)%R with
                 (d0 * (df_R σ df2 v0 xx) + (df_R σ df1 v0 xx) * d2).
         * apply HH; trivial.
         * unfold df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "Divide"%string.
       destruct H.
       do 4 match_option_in H0.
       destruct (Req_EM_T d1 0); [congruence |].
       invcs H0.
       specialize (IHdf1 _  σ v0 xx H eqq0).
       specialize (IHdf2 _  σ v0 xx H1 eqq2).
       eapply is_derive_ext.
       + intros.
         symmetry.
         now apply df_R_total_divide.
       + generalize is_derive_div; simpl; intros HH.
         replace (d0 / d1 - d * d2 / (d1 * d1))%R with
             ((d0 * (df_R σ df2 v0 xx) - (df_R σ df1 v0 xx) * d2) / ((df_R σ df2 v0 xx)*((df_R σ df2 v0 xx)*1))).
         * specialize (HH (df_R σ df1 v0) (df_R σ df2 v0) xx d0 d2).
           apply HH; trivial.
           unfold df_R, df_eval_at_point; simpl.
           now rewrite eqq1.
         * unfold df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           destruct (Req_EM_T d1 0); [congruence |].           
           now field; trivial.
     - Case "Square"%string.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf _  σ v0 xx H eqq0).
       assert (forall t, (Rsqr (df_R σ df v0 t) = df_R σ (Square ann df) v0 t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; unfold Rsqr; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H0.
         * replace (2 * d * d0)%R with (d0 * (2 * d))%R by lra.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ df v0 xx).
           --  apply is_derive_sqr.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Exp"%string.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf _   σ v0 xx H eqq0).
       assert (forall t, (exp (df_R σ df v0 t) = df_R σ (Exp ann df) v0 t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H0.
         * apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ df v0 xx).
           --  apply is_derive_exp.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Log"%string.               
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf _   σ v0 xx H eqq0).
       assert (forall t, (ln (df_R σ df v0 t) = df_R σ (Log ann df) v0 t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H0.
         * destruct (Rgt_dec d 0); [|congruence].
           inversion H2.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ df v0 xx).
           --  apply is_derive_ln.
               unfold df_R, df_eval_at_point; simpl.
               rewrite eqq.
               lra.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Abs"%string.         
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf _  σ v0 xx H eqq0).
       assert (forall t, (Rabs (df_R σ df v0 t) = df_R σ (Abs ann df) v0 t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; trivial.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H0.
         * destruct ( Req_EM_T d 0 ); [congruence |].
           inversion H2.
           apply (@is_derive_comp R_AbsRing); trivial.
           replace (d) with (df_R σ df v0 xx).
           -- replace (@FloatishOps.sign floatish_R (df_R σ df v0 xx)) with (sign (df_R σ df v0 xx)).
              ++ apply is_derive_abs.
                 unfold df_R, df_eval_at_point; simpl.
                 rewrite eqq.
                 lra.
              ++ apply floatish_sign.
           --  unfold df_R, df_eval_at_point; simpl.
               now rewrite eqq.
     - Case "Sign"%string.         
       do 2 match_option_in H0.
       destruct (Req_EM_T d 0); [congruence|].
       invcs H0.
       specialize (IHdf _  σ v0 xx H eqq0).
       assert (forall t, (sign (df_R σ df v0 t) = df_R σ (Sign ann df) v0 t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; trivial.
         apply floatish_sign.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H0.
         * replace (0)%R with (d0 * 0)%R by lra.
           apply (@is_derive_comp R_AbsRing); trivial.
           apply is_derive_sign.
           unfold df_R, df_eval_at_point; simpl.
           rewrite eqq; lra.
     - Case "PSign"%string.         
       do 2 match_option_in H0.
       destruct (Req_EM_T d 0); [congruence|].
       invcs H0.
       specialize (IHdf _  σ v0 xx H eqq0).
       assert (forall t, (psign (df_R σ df v0 t) = df_R σ (PSign ann df) v0 t)).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; trivial.
         apply pos_sign_psign.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H0.
         * replace (0)%R with (d0 * 0)%R by lra.
           apply (@is_derive_comp R_AbsRing); trivial.
           apply is_derive_psign.
           unfold df_R, df_eval_at_point; simpl.           
           rewrite eqq; lra.
     - Case "Max"%string.
       do 4 match_option_in H0.
       destruct H.
       assert (forall t, (Rmax (df_R σ df1 v0 t) (df_R σ df2 v0 t)) = df_R σ (Max ann df1 df2) v0 t).
       + intros; simpl.
         unfold df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial. 
         rewrite e, e0; trivial.
         apply Rmax_Fmax.
       + eapply is_derive_ext.
         * intros; simpl.
           now rewrite H2.
         * destruct (Req_EM_T d d0); [congruence |].
           destruct (Rlt_dec d d0).
           -- invcs H0.
              specialize (IHdf1 _  σ v0 xx H eqq1).
              specialize (IHdf2 _  σ v0 xx H1 eqq2).
              replace (y) with ((d1 + y + (d1-y)*sign(df_R σ df1 v0 xx - df_R σ df2 v0 xx))/2).
              ++ apply is_derive_max; trivial.
                 unfold df_R, df_eval_at_point; simpl.           
                 now rewrite eqq, eqq0.
              ++ unfold df_R, df_eval_at_point; simpl.           
                 rewrite eqq, eqq0.
                 unfold sign; simpl.
                 destruct (total_order_T 0 (d - d0)).
                 ** destruct s; lra.
                 ** lra.
           -- invcs H0.
              specialize (IHdf1 _  σ v0 xx H eqq1).
              specialize (IHdf2 _  σ v0 xx H1 eqq2).
              replace (y) with ((y + d2 + (y - d2)*sign(df_R σ df1 v0 xx - df_R σ df2 v0 xx))/2).
              ++ apply is_derive_max; trivial.
                 unfold df_R, df_eval_at_point; simpl.           
                 now rewrite eqq, eqq0.
              ++ unfold df_R, df_eval_at_point; simpl.           
                 rewrite eqq, eqq0.
                 unfold sign; simpl.
                 destruct (total_order_T 0 (d - d0)).
                 ** destruct s; lra.
                 ** lra.
     - Case "VectorDot"%string.
       do 4 match_option_in H0.
       invcs H0.
       destruct H.
       specialize (IHdf1 _  σ v0 xx H eqq0).
       specialize (IHdf2 _  σ v0 xx H0 eqq2).
       apply (is_derive_ext (fun x0 => (@vsum floatish_R n)
                                         (fun i => ((df_R_vec σ df1 v0 x0 i) *
                                                   (df_R_vec σ df2 v0 x0 i))%R ))).
       + intros.
         unfold df_R_vec, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + apply is_derive_vsum.
         unfold df_R_vec, df_R, df_eval_at_point; simpl.
         unfold is_derive_vec; intros.
         generalize is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d i * d2 i + d0 i * d1 i)%R with
             (d0 i * (df_R_vec σ df2 v0 xx i) + (df_R_vec σ df1 v0 xx i) * d2 i).       
         * apply HH; trivial.
         * unfold df_R_vec, df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "VectorSum"%string.
       match_option_in H0.
       invcs H0.
       specialize (IHdf _  σ v0 xx H eqq).
       assert (forall t, (vsum (df_R_vec σ df v0 t)) = df_R σ (VectorSum ann df) v0 t).
       + intros; simpl.
         unfold df_R_vec, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; unfold Rsqr; trivial.
       + apply (is_derive_ext (fun x0 => (@vsum floatish_R n) (df_R_vec σ df v0 x0))).
         * intros; simpl.
           now rewrite H0.
         * apply is_derive_vsum.
           now simpl in IHdf.
     - Case "MatrixSum"%string.
       match_option_in H0.
       invcs H0.
       specialize (IHdf _  σ v0 xx H eqq).
       assert (forall t, (msum (df_R_mat σ df v0 t)) = df_R σ (MatrixSum ann df) v0 t).
       + intros; simpl.
         unfold df_R_mat, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         rewrite e; unfold Rsqr; trivial.
       + apply (is_derive_ext (fun x0 => (@msum floatish_R m n) (df_R_mat σ df v0 x0))).
         * intros; simpl.
           now rewrite H0.
         * apply is_derive_msum.
           now simpl in IHdf.
     - Case "VectorElem"%string.
       match_option_in H0.
       specialize (IHdf d σ v0 xx H eqq); simpl in IHdf.
       invcs H0.
       apply (is_derive_ext (fun x0 => (df_R_vec σ df v0) x0 i)); intros.
       + unfold df_R_vec, df_R, df_eval_at_point. simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         now rewrite e.
       + unfold is_derive_vec in IHdf.
         apply IHdf.
     - Case "MatrixElem"%string.
       match_option_in H0.
       specialize (IHdf d σ v0 xx H eqq); simpl in IHdf.
       invcs H0.
       apply (is_derive_ext (fun x0 => (df_R_mat σ df v0) x0 i j)); intros.
       + unfold df_R_mat, df_R, df_eval_at_point. simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df); simpl; trivial.
         now rewrite e.
       + unfold is_derive_mat in IHdf.
         apply IHdf.
     - Case "MatrixVectorMult"%string.
       do 4 match_option_in H0.
       invcs H0.
       destruct H.
       specialize (IHdf1 _  σ v0 xx H eqq0).
       specialize (IHdf2 _  σ v0 xx H0 eqq2).
       unfold is_derive_vec; intros.
       apply (is_derive_ext
                (fun x0 => ((@matrix_vector_mult floatish_R m n)
                                (df_R_mat σ df1 v0 x0)
                                (df_R_vec σ df2 v0 x0)) i)).
       + intros.
         unfold df_R_vec, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         rewrite e, e0.
         unfold df_R_mat, df_R, df_eval_at_point; simpl.
         now rewrite e.
       + unfold matrix_vector_mult.
         apply is_derive_vsum.
         unfold is_derive_vec; intros.
         simpl.
         unfold df_R_vec, df_R, df_eval_at_point; simpl.
         unfold is_derive_mat; intros.
         generalize Derive.is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d i i0 * d2 i0 + d0 i i0 * d1 i0)%R with
             (d0 i i0 * (df_R_vec σ df2 v0 xx i0) + (df_R_mat σ df1 v0 xx i i0) * d2 i0)%R.
         * apply HH; trivial.
           simpl in IHdf1.
           unfold is_derive_mat in IHdf1.
           apply IHdf1.
         * unfold df_R_mat, df_R_vec, df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "MatrixVectorAdd"%string.
       do 2 match_option_in H0.
       invcs H0.
       destruct H.
       specialize (IHdf1 _  σ v0 xx H eqq).
       specialize (IHdf2 _  σ v0 xx H0 eqq0).
       unfold is_derive_mat; intros.
       apply (is_derive_ext
                (fun x0 => ((@matrix_vector_add floatish_R m n)
                              (df_R_mat σ df1 v0 x0)
                              (df_R_vec σ df2 v0 x0)) i j)).
       + intros.
         unfold df_R_mat, df_R_vec, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         rewrite e, e0.
         now unfold matrix_vector_add.
       + unfold matrix_vector_add; simpl.
         simpl in *.
         apply (@is_derive_plus R_AbsRing); simpl.
         apply IHdf1.
         apply IHdf2.
     - Case "MatrixMult"%string.
       do 4 match_option_in H0.
       invcs H0.
       destruct H.
       specialize (IHdf1 _  σ v0 xx H eqq0).
       specialize (IHdf2 _  σ v0 xx H0 eqq2).
       unfold is_derive_mat; intros.
       apply (is_derive_ext
                (fun x0 => ((@matrix_mult floatish_R m p n)
                                (df_R_mat σ df1 v0 x0)
                                (df_R_mat σ df2 v0 x0)) i j)).
       + intros.
         unfold df_R_mat, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + unfold matrix_mult.
         apply is_derive_vsum.
         unfold is_derive_vec; intros.
         simpl.
         unfold df_R_mat, df_R, df_eval_at_point; simpl.
         generalize Derive.is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d i i0 * d2 i0 j + d0 i i0 * d1 i0 j)%R with
             (d0 i i0 * (df_R_mat σ df2 v0 xx i0 j) + (df_R_mat σ df1 v0 xx i i0) * d2 i0 j)%R.
         * apply HH; trivial.
         * unfold df_R_mat, df_R_vec, df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "VectorPlus"%string.
       destruct H.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _  σ v0 xx H eqq).
       specialize (IHdf2 _  σ v0 xx H1 eqq0).
       unfold is_derive_vec; intro.
       simpl in *.
       unfold is_derive_vec in IHdf1.
       unfold is_derive_vec in IHdf2.
       specialize (IHdf1 i); specialize (IHdf2 i).
       apply (is_derive_ext (fun x0 => ((df_R_vec σ df1 v0 x0 i) + (df_R_vec σ df2 v0 x0 i))%R)).
       + intros.
         symmetry.
         unfold df_R_vec, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + generalize (@is_derive_plus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "VectorMinus"%string.
       destruct H.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _ σ v0 xx H eqq).
       specialize (IHdf2 _ σ v0 xx H1 eqq0).
       unfold is_derive_vec; intro.
       simpl in *.
       unfold is_derive_vec in IHdf1.
       unfold is_derive_vec in IHdf2.
       specialize (IHdf1 i); specialize (IHdf2 i).
       apply (is_derive_ext (fun x0 => ((df_R_vec σ df1 v0 x0 i) - (df_R_vec σ df2 v0 x0 i))%R)).
       + intros.
         symmetry.
         unfold df_R_vec, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + generalize (@is_derive_minus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "MatrixPlus"%string.
       destruct H.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _ σ v0 xx H eqq).
       specialize (IHdf2 _ σ v0 xx H1 eqq0).
       unfold is_derive_mat; intros.
       simpl in *.
       unfold is_derive_mat in IHdf1.
       unfold is_derive_mat in IHdf2.
       specialize (IHdf1 i j); specialize (IHdf2 i j).
       apply (is_derive_ext (fun x0 => ((df_R_mat σ df1 v0 x0 i j) + (df_R_mat σ df2 v0 x0 i j))%R)).
       + intros.
         symmetry.
         unfold df_R_mat, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + generalize (@is_derive_plus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "MatrixMinus"%string.
       destruct H.
       do 2 match_option_in H0.
       invcs H0.
       specialize (IHdf1 _ σ v0 xx H eqq).
       specialize (IHdf2 _ σ v0 xx H1 eqq0).
       unfold is_derive_mat; intros.
       simpl in *.
       unfold is_derive_mat in IHdf1.
       unfold is_derive_mat in IHdf2.
       specialize (IHdf1 i j); specialize (IHdf2 i j).
       apply (is_derive_ext (fun x0 => ((df_R_mat σ df1 v0 x0 i j) - (df_R_mat σ df2 v0 x0 i j))%R)).
       + intros.
         symmetry.
         unfold df_R_mat, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + generalize (@is_derive_minus R_AbsRing); simpl
         ; intros HH; now apply HH.
     - Case "VectorScalMult"%string.
       do 4 match_option_in H0.
       invcs H0.
       destruct H.
       specialize (IHdf1 _ σ v0 xx H eqq0).
       specialize (IHdf2 _ σ v0 xx H0 eqq2).
       unfold is_derive_vec; intros.
       apply (is_derive_ext (fun x0 => ((df_R σ df1 v0 x0) * (df_R_vec σ df2 v0 x0 i))%R)).
       + intro.
         unfold df_R_vec, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + generalize Derive.is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d * d2 i + d0 * d1 i)%R with
             (d0 * (df_R_vec σ df2 v0 xx i) + (df_R σ df1 v0 xx) * (d2 i))%R.       
         * apply HH; trivial.
           simpl in IHdf1; simpl in IHdf2.
           unfold is_derive_vec in IHdf2.
           apply IHdf2.
         * unfold df_R_vec, df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "MatrixScalMult"%string.
       do 4 match_option_in H0.
       invcs H0.
       destruct H.
       specialize (IHdf1 _ σ v0 xx H eqq0).
       specialize (IHdf2 _ σ v0 xx H0 eqq2).
       unfold is_derive_mat; intros.
       apply (is_derive_ext (fun x0 => ((df_R σ df1 v0 x0) * (df_R_mat σ df2 v0 x0 i j))%R)).
       + intro.
         unfold df_R_mat, df_R, df_eval_at_point; simpl.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df1); simpl; trivial.
         destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         now rewrite e, e0.
       + generalize Derive.is_derive_mult
         ; unfold plus, mult; simpl; intros HH.
         replace (d * d2 i j + d0 * d1 i j)%R with
             (d0 * (df_R_mat σ df2 v0 xx i j) + (df_R σ df1 v0 xx) * (d2 i j))%R. 
         * apply HH; trivial.
           simpl in IHdf1; simpl in IHdf2.
           unfold is_derive_mat in IHdf2.
           apply IHdf2.
         * unfold df_R_mat, df_R, df_eval_at_point; simpl.         
           rewrite eqq; rewrite eqq1.
           lra.
     - Case "VectorApply"%string.
       destruct H.
       do 2 match_option_in H0.
       specialize (vectoro_to_ovector_forall_some_f H0); intros.
       specialize (IHdf2 d0 σ v0 xx H1 eqq0).
       unfold is_derive_vec; intro.
       specialize (H2 i); simpl in H2.
       match_option_in H2; invcs H2.
       simpl in IHdf2; simpl in IHdf1.
       specialize (IHdf1 d1).
       unfold df_R_vec, df_eval_at_point; simpl.
       unfold is_derive_vec in IHdf2; specialize (IHdf2 i).
       generalize 
         (@is_derive_comp R_AbsRing R_NormedModule
                          (fun r' => match df_eval 
                                             (mk_env_entry (v, DTfloat) r' :: nil) df1 with
                                     | Some y => y
                                     | None => 0
                                     end)
                                   
                          (fun x0 => match df_eval (addBinding σ v0 x0) df2 with
                                     | Some y => y i
                                     | None => 0
                                     end) )
       ; simpl; intros.
       specialize (H2 xx d1 (d0 i)).
       apply (is_derive_ext  (fun x : R =>
          match
            df_eval
              (mk_env_entry (v, DTfloat)
                 match df_eval (addBinding σ v0 x) df2 with
                 | Some y => y i
                 | None => 0
                 end :: Datatypes.nil) df1
          with
          | Some y => y
          | None => 0%R
          end)); intros.
       + destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         rewrite e.
         destruct (eval_fully_closed_total (mk_env_entry (v, DTfloat) (x i) :: nil) df1); simpl; trivial.
         rewrite e0.
         match_option.
         * specialize (vectoro_to_ovector_forall_some_f eqq2); intros.
           specialize (H3 i).
           simpl in H3.
           congruence.
         * apply vectoro_to_ovector_exists_None in eqq2.
           destruct eqq2.
           destruct (eval_fully_closed_total (mk_env_entry (v, DTfloat) (x x1) :: nil) df1); simpl; trivial.
           congruence.
       + apply H2.
         * rewrite eqq.
           unfold df_R, df_eval_at_point in IHdf1.
           specialize (IHdf1 nil v (d i)).
           apply IHdf1; trivial.
         * unfold df_R_vec, df_R, df_eval_at_point in IHdf2; simpl in IHdf2.

           apply (is_derive_ext (fun x0 : R =>
                                   match df_eval (addBinding σ v0 x0) df2 with
                                   | Some y => y
                                   | None => ConstVector n 0
                                   end i)); intros.
           -- match_option.
           -- apply IHdf2.
     - Case "MatrixApply"%string.
       destruct H.
       do 2 match_option_in H0.
       specialize (vectoro_to_ovector_forall_some_f H0); intros.
       specialize (IHdf2 d0 σ v0 xx H1 eqq0).
       unfold is_derive_mat; intros.
       specialize (H2 i); simpl in H2.
       unfold matrixo_to_omatrix in H0.
       specialize (vectoro_to_ovector_forall_some_f H2); intros.       
       specialize (H3 j); simpl in H3.
       match_option_in H3; invcs H3.
       simpl in IHdf2; simpl in IHdf1.
       specialize (IHdf1 d1).
       unfold is_derive_mat in IHdf2; specialize (IHdf2 i j).
       generalize 
         (@is_derive_comp R_AbsRing R_NormedModule 
                          (df_R nil df1 v)
                          (fun x0 => (df_R_mat σ df2 v0 x0 i j)))
       ; simpl; intros.
       specialize (H3 xx d1 (d0 i j)).
       apply (is_derive_ext  (fun x : R => df_R Datatypes.nil df1 v (df_R_mat σ df2 v0 x i j))); intros.
       + destruct (eval_fully_closed_total (addBinding σ v0 t) df2); simpl; trivial.
         unfold df_R_mat, df_eval_at_point; simpl.
         rewrite e.
         unfold matrixo_to_omatrix.
         destruct (eval_fully_closed_total (mk_env_entry (v, DTfloat) (x i j) :: nil) df1); simpl; trivial.
         unfold df_R, df_eval_at_point, addBinding; simpl.
         rewrite e0.
         match_option.
         * specialize (vectoro_to_ovector_forall_some_f eqq2); intros.
           specialize (H4 i); simpl in H4.
           specialize (vectoro_to_ovector_forall_some_f H4); intros.           
           specialize (H6 j); simpl in H6.
           congruence.
         * apply vectoro_to_ovector_exists_None in eqq2.
           destruct eqq2.
           apply vectoro_to_ovector_exists_None in e1.
           destruct e1.
           destruct (eval_fully_closed_total (mk_env_entry (v, DTfloat) (x x1 x2) :: nil) df1); simpl; trivial.
           congruence.
       + apply H3.
         * unfold df_R_mat, df_R, df_eval_at_point; simpl.
           rewrite eqq.
           specialize (IHdf1 nil v (d i j)).
           unfold df_R, df_eval_at_point in IHdf1; simpl in IHdf1.
           apply IHdf1; trivial.
           destruct (eval_fully_closed_total (mk_env_entry (v, DTfloat) (d i j) :: nil) df1); simpl; trivial.           
           admit.
         * apply IHdf2.
     - Case "VLossfun"%string.
       admit.
     - Case "MLossfun"%string.
       admit.
Admitted.       
