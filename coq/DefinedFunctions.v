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

Set Bullet Behavior "Strict Subproofs".

Section DefinedFunctions.

  Context {floatish_impl:floatish}.
  Local Open Scope float.

(* Declare Scope df_scope. *)

(* in pytorch relu(f)' if f <=0 then 0 else f' *)
(* in pytorch abs(f)' = f'*sign(f) *)
(* max(a,b)' = if a<=b then b' else a' *)
(* min(a,b)' = if a>=b then b' else a' *)
(* x = Variable(torch.tensor(0.0), requires_grad=True) *)
(* z = torch.min(x*x, x); z.backward(); print(x.grad) = 1 *)
(* x.grad.data.zero_() between tests *)
(* relu behaves like max(x, 0), not max(0,x), i.e. relu(x)' at 0 = 0 *)


  Section Definitions.
    
    Definition var := string.
    
    Inductive SubVar : Set :=
    | Name (s : string)
    | Sub (v : SubVar) (i : nat).


    Definition var_dec : forall v1 v2 : SubVar, {v1 = v2} + {v1 <> v2}.
    Proof.
      decide equality.
      apply string_dec.
      apply Nat.eq_dec.
    Defined.
    
    Global Instance var_eqdec : EqDec SubVar eq.
    Proof.
      intros x y.
      apply var_dec.
    Defined.
    
    (* A subset of defined functions *)


    Inductive definition_function_types
     := DTfloat
      | DTVector (n:nat)
      | DTMatrix (m n:nat).
   
    Definition definition_function_types_interp (dft:definition_function_types) : Type
     := match dft with
        | DTfloat => float
        | DTVector n => Vector float n
        | DTMatrix m n => Matrix float m n
        end.

    Inductive data_type : definition_function_types -> Type
     := DataFloat : data_type DTfloat
     | DataVector n (v:Vector float n) : data_type (DTVector n)
     | DataMatrix m n (mat:Matrix float m n) : data_type (DTMatrix m n).

    Definition var_type := (SubVar * definition_function_types)%type.
    
    Definition vart_dec : forall v1 v2 : var_type, {v1 = v2} + {v1 <> v2}.
    Proof.
      decide equality.
      decide equality.
      apply Nat.eq_dec.
      apply Nat.eq_dec.
      apply Nat.eq_dec.            
      apply var_dec.
    Defined.

    Global Instance vart_eqdec : EqDec var_type eq. 
    Proof.
      intros ??.
      apply vart_dec.
    Defined.

    Definition env_entry_type := {v:var_type & definition_function_types_interp (snd v)}.
    Definition df_env := list env_entry_type.

    Definition mk_env_entry v e : env_entry_type
    := let P := fun xv => definition_function_types_interp (snd xv) in
       existT P v e.

    Definition UnitAnn: definition_function_types->Type := fun _ => unit.
    Definition EvalAnn: definition_function_types->Type := definition_function_types_interp.

    Inductive DefinedFunction {Ann:definition_function_types->Type} : definition_function_types -> Type :=
    | Number (ann:Ann DTfloat) (x : float) : DefinedFunction DTfloat
    | Constant {t:definition_function_types} (ann:Ann t) (x : definition_function_types_interp t) : DefinedFunction t
    | DVector {n} (ann:Ann (DTVector n)) (x : Vector (DefinedFunction DTfloat) n) : DefinedFunction (DTVector n)
    | DMatrix {n m} (ann:Ann (DTMatrix n m)) (x : Matrix (DefinedFunction DTfloat) n m) : DefinedFunction (DTMatrix n m)
    | Var (v : var_type) (ann: Ann (snd v)) : DefinedFunction (snd v)
    | Plus (ann:Ann DTfloat) (l r : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Minus (ann:Ann DTfloat) (l r : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Times (ann:Ann DTfloat) (l r : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Divide (ann:Ann DTfloat) (l r : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Square (ann:Ann DTfloat) (e : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Exp (ann:Ann DTfloat) (e : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Log (ann:Ann DTfloat) (e : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Abs (ann:Ann DTfloat) (e : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Sign (ann:Ann DTfloat) (e : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | PSign (ann:Ann DTfloat) (e : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | Max (ann:Ann DTfloat) (l r : DefinedFunction DTfloat) : DefinedFunction DTfloat
    | VectorDot {n} (ann:Ann DTfloat) (l r: DefinedFunction (DTVector n)) : DefinedFunction DTfloat
    | VectorSum {n} (ann:Ann DTfloat) (v: DefinedFunction (DTVector n)) : DefinedFunction DTfloat
    | MatrixSum {m n} (ann:Ann DTfloat) (v: DefinedFunction (DTMatrix m n)) : DefinedFunction DTfloat
    | VectorElem {n} (ann:Ann DTfloat) (l:DefinedFunction (DTVector n)) (i:{x:nat|x<n}%nat) : DefinedFunction DTfloat
    | MatrixElem {m n} (ann:Ann DTfloat) (l:DefinedFunction (DTMatrix m n)) (i:{x:nat|x<m}%nat) (j:{x:nat|x<n}%nat) :
        DefinedFunction DTfloat
    | MatrixVectorMult {m n} (ann:Ann (DTVector m)) (l : DefinedFunction (DTMatrix m n)) (r : DefinedFunction (DTVector n)) :
        DefinedFunction (DTVector m)
    | MatrixVectorAdd {m n} (ann:Ann (DTMatrix m n)) (l : DefinedFunction (DTMatrix m n)) (r : DefinedFunction (DTVector m)) :
        DefinedFunction (DTMatrix m n)                        
    | MatrixMult {m p n} (ann:Ann (DTMatrix m n)) (l : DefinedFunction (DTMatrix m p)) (r : DefinedFunction (DTMatrix p n)) :
        DefinedFunction (DTMatrix m n)
    | VectorPlus {n} (ann:Ann (DTVector n)) (l r: DefinedFunction (DTVector n)) : DefinedFunction (DTVector n)
    | VectorMinus {n} (ann:Ann (DTVector n)) (l r: DefinedFunction (DTVector n)) : DefinedFunction (DTVector n)
    | MatrixPlus {n m} (ann:Ann (DTMatrix n m)) (l r : DefinedFunction (DTMatrix n m)) : DefinedFunction (DTMatrix n m)
    | MatrixMinus {n m} (ann:Ann (DTMatrix n m)) (l r : DefinedFunction (DTMatrix n m)) : DefinedFunction (DTMatrix n m)
    | VectorScalMult {n} (ann:Ann (DTVector n)) (x:DefinedFunction DTfloat) (l : DefinedFunction (DTVector n)) :
        DefinedFunction (DTVector n)
    | MatrixScalMult {n m} (ann:Ann (DTMatrix n m)) (x:DefinedFunction DTfloat) (l : DefinedFunction (DTMatrix n m)) :
        DefinedFunction (DTMatrix n m)
    | VectorApply {n} (ann:Ann (DTVector n)) (v:SubVar) (s:@DefinedFunction UnitAnn DTfloat) (l: DefinedFunction (DTVector n)) :
        DefinedFunction (DTVector n)
    | MatrixApply {m n} (ann:Ann (DTMatrix m n)) (v:SubVar) (s:@DefinedFunction UnitAnn DTfloat) (l: DefinedFunction (DTMatrix m n)) :
        DefinedFunction (DTMatrix m n)

    | VLossfun {n} (ann:Ann DTfloat) (v1 v2:SubVar) (s:@DefinedFunction UnitAnn DTfloat) (l: DefinedFunction (DTVector n)) (r:Vector float n) : DefinedFunction DTfloat
    | MLossfun {m n} (ann:Ann DTfloat) (v1 v2:SubVar) (s:@DefinedFunction UnitAnn DTfloat) (l: DefinedFunction (DTMatrix m n)) (r:Matrix float m n) : DefinedFunction DTfloat
    .

    Global Arguments DefinedFunction : clear implicits.

    Definition get_annotation {Ann T} (df:DefinedFunction Ann T) : Ann T
      := match df with
         | Number ann _ => ann
         | Constant _ ann _ => ann
         | DVector _ ann _ => ann
         | DMatrix _ _ ann _ => ann
         | Var _ ann => ann                                  
         | Plus ann _ _ => ann
         | Minus ann _ _ => ann
         | Times ann _ _ => ann
         | Divide ann _ _ => ann
         | Square ann _ => ann
         | Exp ann _ => ann
         | Log ann _ => ann
         | Abs ann _ => ann
         | Sign ann _ => ann
         | PSign ann _ => ann
         | Max ann _ _ => ann                            
         | VectorDot _ ann _ _ => ann
         | VectorSum _ ann _ => ann
         | MatrixSum _ _ ann _ => ann                                  
         | VectorElem _ ann _ _ => ann
         | MatrixElem _ _ ann _ _ _ => ann                                     
         | MatrixVectorMult _ _ ann _ _ => ann
         | MatrixVectorAdd _ _ ann _ _ => ann                                             
         | MatrixMult _ _ _ ann _ _ => ann
         | VectorPlus _ ann _ _ => ann
         | VectorMinus _ ann _ _ => ann                                     
         | MatrixPlus _ _ ann _ _ => ann
         | MatrixMinus _ _ ann _ _ => ann                                       
         | VectorScalMult _ ann _ _ => ann
         | MatrixScalMult _ _ ann _ _ => ann                                          
         | VectorApply _ ann _ _ _ => ann
         | MatrixApply _ _ ann _ _ _ => ann                                        
         | VLossfun _ ann _ _ _ _ _ => ann
         | MLossfun _ _ ann _ _ _ _ _ => ann                                         
     end.

    Definition dft_eq_dec :
            forall (t1 t2 : definition_function_types), {t1 = t2} + {t1 <> t2}.
    Proof.
      decide equality.
      decide equality.
      apply Nat.eq_dec.
      apply Nat.eq_dec.
    Defined.

    Global Instance dft_eqdec : EqDec definition_function_types eq. 
    Proof.
      intros ??.
      apply dft_eq_dec.
    Defined.

(*
    Definition df_eq_dec {t: definition_function_types} : 
      forall (v1 v2 : DefinedFunction t), {v1 = v2} + {v1 <> v2}.
    Proof.
      destruct t.
      destruct v1.
    Admitted.

    Global Instance df_eqdec {t:definition_function_types} : EqDec (DefinedFunction t) eq. 
    Proof.
      intros ??.
      apply df_eq_dec.
    Defined.
*)
  End Definitions.

    Tactic Notation "DefinedFunction_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "Number"%string
      | Case_aux c "Constant"%string                 
      | Case_aux c "DVector"%string
      | Case_aux c "DMatrix"%string
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
      | Case_aux c "Max"%string
      | Case_aux c "VectorDot"%string
      | Case_aux c "VectorSum"%string
      | Case_aux c "MatrixSum"%string                 
      | Case_aux c "VectorElem"%string
      | Case_aux c "MatrixElem"%string
      | Case_aux c "MatrixVectorMult"%string
      | Case_aux c "MatrixVectorAdd"%string                 
      | Case_aux c "MatrixMult"%string
      | Case_aux c "VectorPlus"%string
      | Case_aux c "VectorMinus"%string
      | Case_aux c "MatrixPlus"%string
      | Case_aux c "MatrixMinus"%string
      | Case_aux c "VectorScalMult"%string
      | Case_aux c "MatrixScalMult"%string
      | Case_aux c "VectorApply"%string
      | Case_aux c "MatrixApply"%string                 
      | Case_aux c "VLossfun"%string
      | Case_aux c "MLossfun"%string].        



  Definition df_plus  (df1 df2 : DefinedFunction UnitAnn DTfloat) : DefinedFunction UnitAnn DTfloat :=
    Plus tt df1 df2.

  Definition df_times (df1 df2 : DefinedFunction UnitAnn DTfloat) : DefinedFunction UnitAnn DTfloat :=
    Times tt df1 df2.

  Definition defined_sum {m} (v:Vector (DefinedFunction UnitAnn DTfloat) m) : DefinedFunction UnitAnn DTfloat
    := vector_fold_right1 (fun a b => Plus tt a b) (Number tt 0) id v.

  Definition vsum {m:nat} (v:Vector float m) : float
      := vector_fold_right1 Fplus 0 id v.

  Definition msum {m n:nat} (v:Matrix float m n) : float :=
    vsum (vmap vsum v).


  Definition transpose {A} {n m:nat} (mat:Matrix A n m) :=
      fun i j => mat j i.

  Definition matrix_vector_mult {n m} (l : Matrix float n m)(r : Vector float m) : Vector float n :=
      fun i => vsum (fun j => (l i j) * (r j)).

  Definition matrix_vector_add {n m} (l : Matrix float n m) (r : Vector float n) : Matrix float n m := fun i j => (l i j) + (r i).

  Definition matrix_mult {m n p} (l : Matrix float n m)(r : Matrix float m p) : Matrix float n p :=
      fun i k => vsum (fun j => (l i j) * (r j k)).


 Section deriv.
    

  Section subst.

    Program Definition substvar {Ann} (v vv:var_type) (e':DefinedFunction Ann (snd v)) (e:DefinedFunction Ann (snd vv)) : (DefinedFunction Ann (snd vv)) :=
      
      match v == vv with
      | left pf => eq_rect _ (fun t => DefinedFunction Ann t) e' _ _
      | right pf => e
      end.
  
 Fixpoint df_subst {T Ann} (df: DefinedFunction Ann T) (v:var_type) (e':DefinedFunction UnitAnn (snd v)) :=
      match df with
      | Number _ x => Number tt x
      | Constant t _ x => Constant tt x
      | DVector n _ df => DVector tt (fun x => df_subst (df x) v e')
      | DMatrix n m _ df => DMatrix tt (fun i j => df_subst (df i j) v e')
      | Var vvar _ => substvar v vvar e' (Var vvar tt)
      | Plus _ l r => Plus tt (df_subst l v e') (df_subst r v e')
      | Times _ l r => Times tt (df_subst l v e') (df_subst r v e')
      | Minus _ l r => Minus tt (df_subst l v e') (df_subst r v e')
      | Divide _ l r => Divide tt (df_subst l v e') (df_subst r v e')
      | Square _ e => Square tt (df_subst e v e')
      | Exp _ e => Exp tt (df_subst e v e')                     
      | Log _ e => Log tt (df_subst e v e')
      | Abs _ e => Abs tt (df_subst e v e')
      | Sign _ e => Sign tt (df_subst e v e')
      | PSign _ e => PSign tt (df_subst e v e')
      | Max _ l r => Max tt (df_subst l v e') (df_subst r v e')
      | VectorElem n _ l i => VectorElem tt (df_subst l v e') i
      | MatrixElem m n _ l i j => MatrixElem tt (df_subst l v e') i j
      | VectorDot n _ l r =>
        VectorDot tt (df_subst l v e') (df_subst r v e')
      | VectorSum n _ e =>
        VectorSum tt (df_subst e v e')
      | MatrixSum n m _ e =>
        MatrixSum tt (df_subst e v e')
      | VectorScalMult n _ x r =>
        VectorScalMult tt (df_subst x v e') (df_subst r v e')
      | MatrixScalMult n m _ x r =>
        MatrixScalMult tt (df_subst x v e') (df_subst r v e')
      | MatrixVectorMult n m _ l r =>
        MatrixVectorMult tt (df_subst l v e') (df_subst r v e')
      | MatrixVectorAdd n m _ l r =>
        MatrixVectorAdd tt (df_subst l v e') (df_subst r v e')
      | MatrixMult n m p _ l r =>
        MatrixMult tt (df_subst l v e') (df_subst r v e')
      | VectorPlus n _ l r =>
        VectorPlus tt (df_subst l v e') (df_subst r v e')
      | VectorMinus n _ l r =>
        VectorMinus tt (df_subst l v e') (df_subst r v e')
      | MatrixPlus n m _ l r =>
        MatrixPlus tt (df_subst l v e') (df_subst r v e')
      | MatrixMinus n m _ l r =>
        MatrixMinus tt (df_subst l v e') (df_subst r v e')
      | VectorApply n _ x s l => 
        VectorApply tt x (df_subst s v e') (df_subst l v e')
      | MatrixApply n m _ x s l => 
        MatrixApply tt x (df_subst s v e') (df_subst l v e')
      | VLossfun n _ v1 v2 s l r =>
        VLossfun tt v1 v2 (df_subst s v e') (df_subst l v e') r
      | MLossfun n m _ v1 v2 s l r =>
        MLossfun tt v1 v2 (df_subst s v e') (df_subst l v e') r
      end.

    Definition df_substp {T Ann} := 
      fun e (ve':{v:var_type & DefinedFunction UnitAnn (snd v)}) => 
        @df_subst T Ann e (projT1 ve') (projT2 ve').

    Definition df_subst_list {T} (e:DefinedFunction UnitAnn T)
               (l:list {v:var_type & DefinedFunction UnitAnn (snd v)}) : DefinedFunction UnitAnn T
      := fold_left (@df_substp T UnitAnn) l e.

  End subst.


(* restrict to scalar v? *)
    Fixpoint df_deriv {T} (df:DefinedFunction UnitAnn T) (v:var_type) {struct df} : DefinedFunction UnitAnn T
      := (match df with
          | Number _ _ => Number tt 0
          | Constant t _ x => Constant tt
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
          | DVector n _ df => DVector tt (fun x => df_deriv (df x) v)
          | DMatrix n m _ df => DMatrix tt (fun i j => df_deriv (df i j) v)
          | Var x _ => Constant tt 
               match snd x as y return definition_function_types_interp y with
               | DTfloat => if x == v then 1 else 0
               | DTVector n => ConstVector n (if x == v then 1 else 0)
               | DTMatrix m n => ConstMatrix m n (if x == v then 1 else 0)
               end
          | Plus _ l r => Plus tt (df_deriv l v) (df_deriv r v)
          | Minus _ l r => Minus tt (df_deriv l v) (df_deriv r v)
          | Times _ l r => Plus tt (Times tt l (df_deriv r v))
                              (Times tt (df_deriv l v) r)
          | Divide _ l r => Divide tt 
                            (Minus tt 
                               (Times tt (df_deriv l v) r)
                               (Times tt l (df_deriv r v)))
                            (Times tt r r)
          | Square _ e => Times tt 
                                (Times tt (Number tt 2) e) (df_deriv e v)
          | Exp _ e => Times tt (df_deriv e v) (Exp tt e)
          | Log _ e => Divide tt (df_deriv e v) e
          | Abs _ e => Times tt (df_deriv e v) (Sign tt e) 
          | Sign _ e => Number tt 0
          | PSign _ e => Number tt 0
          | Max _ l r => Divide tt 
                                (Plus tt 
                                      (Times tt (Minus tt 
                                                               (df_deriv r v) 
                                                               (df_deriv l v)) 
                                             (PSign tt (Minus tt r l)))
                                      (Plus tt (df_deriv r v) (df_deriv l v)))
                              (Number tt 2)
          | VectorElem n _ l i => VectorElem tt (df_deriv l v) i
          | MatrixElem m n _ l i j => MatrixElem tt (df_deriv l v) i j
          | VectorDot n _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            Plus tt (VectorDot tt ll r) (VectorDot tt l rr)
          | VectorSum n _ l =>
            let ll := df_deriv l v in 
            VectorSum tt ll
          | MatrixSum m n _ l =>
            let ll := df_deriv l v in 
            MatrixSum tt ll
          | VectorScalMult n _ x r => 
            let xx := df_deriv x v in 
            let rr := df_deriv r v in
            VectorPlus tt 
                       (VectorScalMult tt xx r) 
                       (VectorScalMult tt x rr)
          | MatrixScalMult n m _ x r => 
            let xx := df_deriv x v in 
            let rr := df_deriv r v in
            MatrixPlus tt 
                       (MatrixScalMult tt xx r) (MatrixScalMult tt x rr)
          | MatrixVectorMult n m _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            VectorPlus tt (MatrixVectorMult tt ll r) 
                       (MatrixVectorMult tt l rr)
          | MatrixVectorAdd n m _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            MatrixVectorAdd tt ll rr
          | MatrixMult n m p _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            MatrixPlus tt (MatrixMult tt ll r) (MatrixMult tt l rr)
          | VectorPlus n _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            VectorPlus tt ll rr
          | VectorMinus n _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            VectorMinus tt ll rr
          | MatrixPlus n m _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            MatrixPlus tt ll rr
          | MatrixMinus n m _ l r =>
            let ll := df_deriv l v in
            let rr := df_deriv r v in
            MatrixMinus tt ll rr
          | VectorApply n _ x s r => 
            let rr := df_deriv r v in
            let ss := df_deriv s (x, DTfloat) in
            DVector tt (fun i => Times tt (VectorElem tt rr i) (df_subst ss (x, DTfloat) (VectorElem tt r i)))
          | MatrixApply n m _ x s r => 
            let rr := df_deriv r v in
            let ss := df_deriv s (x, DTfloat) in
            DMatrix tt (fun i j => Times tt (MatrixElem tt rr i j) (df_subst ss (x, DTfloat) (MatrixElem tt r i j)))
          | VLossfun n _ v1 v2 s l r =>
            let ll := df_deriv l v in
            let ss := df_deriv s (v1, DTfloat) in
            VectorDot tt ll 
                      (DVector tt (fun i => 
                                     df_subst (df_subst ss (v1, DTfloat) (VectorElem tt l i))
                                              (v2, DTfloat) (Number tt (r i))))
          | MLossfun n m _ v1 v2 s l r =>
            let ll := df_deriv l v in
            let ss := df_deriv s (v1, DTfloat) in
            MatrixSum tt
               (DMatrix tt 
                  (fun i j => 
                     (Divide tt 
                          (Times tt (MatrixElem tt ll i j)
                                 (df_subst (df_subst ss (v1, DTfloat) (MatrixElem tt l i j))
                                           (v2, DTfloat) (Number tt (r i j))))
                     (Number tt (FfromZ (Z.of_nat m))))))
          end).

    Definition df_gradient {T} (df:DefinedFunction UnitAnn T) (lv:list var_type) : list (DefinedFunction UnitAnn T)
      := map (df_deriv df) lv.

  End deriv.
  
  Section eval.
    
    Program
      Fixpoint vartlookup (l:df_env) (a:var_type) : 
      option (definition_function_types_interp (snd a))
      := match l with
         | nil => None
         | fv::os => if a == (projT1 fv) then 
                       Some (eq_rect _ definition_function_types_interp (projT2 fv) _ _) 
                     else vartlookup os a
         end.

    Fixpoint vart_update (l:df_env) (a:var_type) (n:definition_function_types_interp (snd a)) : df_env
      := match l with 
         | nil =>  (mk_env_entry a n)::nil
         | fv::os => if a == (projT1 fv) then 
                       (mk_env_entry a n)::os else fv::(vart_update os a n)
         end.

    Fixpoint df_eval {T Ann} (σ:df_env) (df:DefinedFunction Ann T) : option (definition_function_types_interp T)
      := match df with
         | Number _ r => Some r
         | Constant t _ x => Some x
         | DVector n _ dfs => vectoro_to_ovector (fun i => df_eval σ (dfs i))
         | DMatrix n m _ df => matrixo_to_omatrix (fun i j => df_eval σ (df i j))
         | Var x _ => vartlookup  σ x
         | Plus _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' + r')
           | _, _ => None
           end
         | Minus _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' - r')
           | _, _ => None
           end
         | Times _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' * r')
           | _, _ => None
           end
         | Divide _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (l' / r')
           | _, _ => None
           end
         | Square _ e => 
           match df_eval σ e with
           | Some v => Some (v * v)
           | _ => None
           end
         | Exp _ e => 
           match df_eval σ e with
           | Some v => Some (Fexp v)
           | _ => None
           end
         | Log _ e => 
           match df_eval σ e with
           | Some v => Some (Fln v) 
           | _ => None
           end
         | Abs _ e =>
           match df_eval σ e with
           | Some v => Some (Fabs v) 
           | _ => None
           end
         | Sign _ e =>
           match df_eval σ e with
           | Some v => Some (sign v)
           | _ => None
           end
         | PSign _ e =>
           match df_eval σ e with
           | Some v => Some (pos_sign v)
           | _ => None
           end
         | Max _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (Fmax l' r')
           | _, _ => None
           end
         | VectorElem n _ l i => 
           match (df_eval σ l)  with
           | Some l' => Some (l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval σ l)  with
           | Some l' => Some (l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (vsum (fun i => (l' i) * (r' i)))
           | _, _ => None
           end
         | VectorSum n _ l =>
           match df_eval σ l with
           | Some l' => Some (vsum l')
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_eval σ l with
           | Some l' => Some (msum l')
           | _ => None
           end
         | VectorScalMult n _ x r =>
           match df_eval σ x, df_eval σ r with
           | Some x', Some r' => Some (fun j => x' * (r' j))
           | _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval σ x, df_eval σ r with
           | Some x', Some r' => Some (fun i j => x' * (r' i j))
           | _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (matrix_vector_mult l' r')
           | _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (matrix_vector_add l' r')
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (matrix_mult l' r')
           | _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval σ l, df_eval σ r with           
           | Some l', Some r' => Some (fun i => (l' i) + (r' i))
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval σ l, df_eval σ r with           
           | Some l', Some r' => Some (fun i => (l' i) - (r' i))
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval σ l, df_eval σ r with           
           | Some l', Some r' => Some (fun i j => (l' i j) + (r' i j))
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval σ l, df_eval σ r with           
           | Some l', Some r' => Some (fun i j => (l' i j) - (r' i j))
           | _, _ => None
           end
         | VectorApply n _ x s r => 
           match df_eval σ r with           
           | Some r' => vectoro_to_ovector 
                          (fun i => 
                             let xv := (x, DTfloat):var_type in
                             df_eval (cons (mk_env_entry xv (r' i)) σ) s)
           | _ => None
           end
         | MatrixApply n m _ x s r => 
           match df_eval σ r with           
           | Some r' => matrixo_to_omatrix
                          (fun i j => 
                             let xv := (x, DTfloat):var_type in
                             df_eval (cons (mk_env_entry xv (r' i j)) σ) s)
           | _ => None
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_eval σ l with
           | Some l' => 
             match (vectoro_to_ovector 
                      (fun i => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (l' i)) 
                                       (cons (mk_env_entry xv2 (r i)) σ)) s)) with
             | Some vv => Some (vsum vv)
             | _ => None
             end
           | _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           match df_eval σ l with
           | Some l' => 
             match (matrixo_to_omatrix
                      (fun i j => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (l' i j)) 
                                       (cons (mk_env_entry xv2 (r i j)) σ)) s)) with
             | Some vv => Some ((msum vv) / (FfromZ (Z.of_nat m)))
             | _ => None
             end
           | _ => None
           end

         end.

    Fixpoint df_eval_tree {T Ann} (σ:df_env) (df:DefinedFunction Ann T) : option (DefinedFunction EvalAnn T)
      := match df with
         | Number _ r => Some (Number r r)
         | Constant t _ x => Some (Constant x x)
         | DVector n _ dfs => 
           match vectoro_to_ovector (fun i => df_eval_tree σ (dfs i)) with
           | Some val => Some (DVector (vmap get_annotation val) val)
           | _ => None
           end
         | DMatrix n m _ df => 
           match matrixo_to_omatrix (fun i j => df_eval_tree σ (df i j)) with
           | Some val => Some (DMatrix 
                                       (vmap (fun x => vmap get_annotation x) val) val)
           | _ => None
           end 
         | Var x _ => match vartlookup  σ x with
                      | Some val => Some (Var x val)
                      | _ => None
                      end                 
         | Plus _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => Some (Plus ((get_annotation l') + (get_annotation r'))
                                            l' r')
           | _, _ => None
           end
         | Minus _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => Some (Minus ((get_annotation l') - (get_annotation r'))
                                             l' r')
           | _, _ => None
           end
         | Times _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => Some (Times ((get_annotation l') * (get_annotation r'))
                                             l' r')
           | _, _ => None
           end
         | Divide _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => Some (Divide ((get_annotation l') / (get_annotation r'))
                                             l' r')
           | _, _ => None
           end
         | Square _ e => 
           match df_eval_tree σ e with
           | Some vv => let v := get_annotation vv in Some (Square (v * v) vv)
           | _ => None
           end
         | Exp _ e => 
           match df_eval_tree σ e with
           | Some vv => Some (Exp (Fexp (get_annotation vv)) vv)
           | _ => None
           end
         | Log _ e => 
           match df_eval_tree σ e with
           | Some vv => Some (Log (Fln (get_annotation vv)) vv)
           | _ => None
           end
         | Abs _ e =>
           match df_eval_tree σ e with
           | Some vv => Some (Abs (Fabs (get_annotation vv)) vv)
           | _ => None
           end
         | Sign _ e =>
           match df_eval_tree σ e with
           | Some vv => Some (Sign (sign (get_annotation vv)) vv)
           | _ => None
           end
         | PSign _ e =>
           match df_eval_tree σ e with
           | Some vv => Some (PSign (pos_sign (get_annotation vv)) vv)
           | _ => None
           end
         | Max _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => Some (Max (Fmax (get_annotation l') (get_annotation r'))
                                           l' r')
           | _, _ => None
           end
         | VectorElem n _ l i => 
           match (df_eval_tree σ l)  with
           | Some l' => let vl' := get_annotation l' in
                        Some (VectorElem (vl' i) l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_tree σ l)  with
           | Some l' => let vl' := get_annotation l' in
                        Some (MatrixElem (vl' i j) l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in 
                                 Some (VectorDot (vsum (fun i => (vl' i) * (vr' i))) l' r')
           | _, _ => None
           end
         | VectorSum n _ l =>
           match df_eval_tree σ l with
           | Some l' => let vl' := get_annotation l' in
                        Some (VectorSum (vsum vl') l')
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_eval_tree σ l with
           | Some l' => let vl' := get_annotation l' in
                        Some (MatrixSum (msum vl') l')
           | _ => None
           end
         | VectorScalMult n _ x r =>
           match df_eval_tree σ x, df_eval_tree σ r with
           | Some x', Some r' => let vx' := get_annotation x' in
                                 let vr' := get_annotation r' in
                                 let vec : Vector float n := (fun j => vx' * (vr' j)) in
                                 Some (VectorScalMult vec x' r')
           | _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval_tree σ x, df_eval_tree σ r with
           | Some x', Some r' => let vx' := get_annotation x' in
                                 let vr' := get_annotation r' in
                                 let mat : Matrix float n m := fun i j => vx' * (vr' i j) in
                                 Some (MatrixScalMult mat x' r')
           | _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 Some (MatrixVectorMult (matrix_vector_mult vl' vr') l' r')
           | _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 Some (MatrixVectorAdd (matrix_vector_add vl' vr') l' r')
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 Some (MatrixMult (matrix_mult vl' vr') l' r')
           | _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with           
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 let vec : Vector float n := 
                                     fun i => (vl' i) + (vr' i) in
                                 Some (VectorPlus vec l' r')
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with           
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 let vec : Vector float n := 
                                     fun i => (vl' i) - (vr' i) in
                                 Some (VectorMinus vec l' r')
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with           
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 let mat : Matrix float n m := 
                                     fun i j => (vl' i j) + (vr' i j) in
                                 Some (MatrixPlus mat l' r')
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with           
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 let mat : Matrix float n m := 
                                     fun i j => (vl' i j) - (vr' i j) in
                                 Some (MatrixMinus mat l' r')
           | _, _ => None
           end

         | VectorApply n _ x s r => 
           match df_eval_tree σ r with           
           | Some r' => 
             let vr' := get_annotation r' in
             match vectoro_to_ovector 
                     (fun i => 
                        let xv := (x, DTfloat):var_type in
                        df_eval (cons (mk_env_entry xv (vr' i)) σ) s) with
             | Some val => Some (VectorApply val x s r')
             | _ => None
             end
           | _ => None
           end
         | MatrixApply n m _ x s r => 
           match df_eval_tree σ r with           
           | Some r' => 
             let vr' := get_annotation r' in
             match matrixo_to_omatrix
                     (fun i j => 
                        let xv := (x, DTfloat):var_type in
                        df_eval (cons (mk_env_entry xv (vr' i j)) σ) s) with
             | Some val => Some (MatrixApply val x s r')
             | _ => None
             end
           | _ => None
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_eval_tree σ l with
           | Some l' => 
             let vl' := get_annotation l' in
             match (vectoro_to_ovector 
                      (fun i => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (vl' i)) 
                                       (cons (mk_env_entry xv2 (r i)) σ)) s)) with
             | Some vv => Some (VLossfun (vsum vv) v1 v2 s l' r)
             | _ => None
             end
           | _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           match df_eval_tree σ l with
           | Some l' => 
             let vl' := get_annotation l' in
             match (matrixo_to_omatrix
                      (fun i j => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (vl' i j)) 
                                       (cons (mk_env_entry xv2 (r i j)) σ)) s)) with
             | Some vv => Some (MLossfun ((msum vv)/(FfromZ (Z.of_nat m))) v1 v2 s l' r)
             | _ => None
             end
           | _ => None
           end
         end.

    Definition eval_env_entry_type := {T:definition_function_types & (DefinedFunction UnitAnn T) & definition_function_types_interp T}.
    Definition df_eval_env := list eval_env_entry_type.
    
    Definition mk_eval_env_entry {T} df val : eval_env_entry_type
      := let P := fun t => DefinedFunction UnitAnn t in
         let Q := fun t => definition_function_types_interp t in
       existT2 P Q T df val.

    Definition pair_update_evals {T} (df:DefinedFunction UnitAnn T) (val:definition_function_types_interp T) (dfevals : df_eval_env) : (definition_function_types_interp T * df_eval_env) :=
      (val, (mk_eval_env_entry df val)::dfevals).

    Fixpoint df_evals_list {T} (σ:df_env) (df:DefinedFunction UnitAnn T) (dfevals : df_eval_env) : option (definition_function_types_interp T * df_eval_env)
      := match df with
         | Number _ r => Some (pair_update_evals (Number tt r) r dfevals)
         | Constant t _ x => Some (pair_update_evals (Constant tt x) x dfevals)
         | DVector n _ dfs => None (*vectoro_to_ovector (fun i => df_eval σ (dfs i))*)
         | DMatrix n m _ df => None (*matrixo_to_omatrix (fun i j => df_eval σ (df i j))*)
         | Var x _ => 
           match vartlookup σ x with
           | Some val => Some (pair_update_evals (Var x tt) val dfevals)
           | _ => None
           end                    
         | Plus _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => Some (pair_update_evals (Plus tt l r) (l'+r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | Minus _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => Some (pair_update_evals (Minus tt l r) (l'-r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | Times _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => Some (pair_update_evals (Times tt l r) (l'*r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | Divide _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => Some (pair_update_evals (Divide tt l r) (l'/r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | Square _ e => 
           match df_evals_list σ e dfevals with
           | Some (v, dfevals') => Some (pair_update_evals (Square tt e) (v * v) dfevals')
           | _ => None
           end
         | Exp _ e => 
           match df_evals_list σ e dfevals with
           | Some (v, dfevals') => Some (pair_update_evals (Exp tt e) (Fexp v) dfevals')
           | _ => None
           end
         | Log _ e => 
           match df_evals_list σ e dfevals with
           | Some (v, dfevals') => Some (pair_update_evals (Log tt e) (Fln v) dfevals')
           | _ => None
           end
         | Abs _ e =>
           match df_evals_list σ e dfevals with
           | Some (v, dfevals') => Some (pair_update_evals (Abs tt e) (Fabs v) dfevals')
           | _ => None
           end
         | Sign _ e =>
           match df_evals_list σ e dfevals with
           | Some (v, dfevals') => Some (pair_update_evals (Sign tt e) (sign v) dfevals')
           | _ => None
           end
         | PSign _ e =>
           match df_evals_list σ e dfevals with
           | Some (v, dfevals') => Some (pair_update_evals (PSign tt e) (pos_sign v) dfevals')
           | _ => None
           end
         | Max _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => Some (pair_update_evals (Max tt l r) (Fmax l' r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | VectorElem n _ l i => 
           match (df_evals_list σ l dfevals)  with
           | Some (l', dfevals') => Some (pair_update_evals (VectorElem tt l i) (l' i) dfevals')
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_evals_list σ l dfevals)  with
           | Some (l', dfevals') => Some (pair_update_evals (MatrixElem tt l i j) (l' i j) dfevals')
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (VectorDot tt l r) 
                                          (vsum (fun i => (l' i) * (r' i))) dfevals'')
             | _ => None
             end
           | _ => None
           end
         | VectorSum n _ l =>
           match df_evals_list σ l dfevals with
           | Some (l',dfevals') => Some (pair_update_evals (VectorSum tt l) (vsum l') dfevals')
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_evals_list σ l dfevals with
           | Some (l',dfevals') => Some (pair_update_evals (MatrixSum tt l) (msum l') dfevals')
           | _ => None
           end
         | VectorScalMult n _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (VectorScalMult tt l r) (fun j => l' * (r' j)) dfevals'')
             | _ => None
             end
           | _ => None
           end
         | MatrixScalMult n m _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (MatrixScalMult tt l r) (fun i j => l' * (r' i j)) dfevals'')
             | _ => None
             end
           | _ => None
           end
         | MatrixVectorMult n m _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (MatrixVectorMult tt l r) 
                                          (matrix_vector_mult l' r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (MatrixVectorAdd tt l r) 
                                          (matrix_vector_add l' r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | MatrixMult n m p _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (MatrixMult tt l r) (matrix_mult l' r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | VectorPlus n _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (VectorPlus tt l r) 
                                          (fun i => (l' i) + (r' i)) dfevals'')
             | _ => None
             end
           | _ => None
           end
         | VectorMinus n _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (VectorMinus tt l r) 
                                          (fun i => (l' i) - (r' i)) dfevals'')
             | _ => None
             end
           | _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (MatrixPlus tt l r) 
                                          (fun i j => (l' i j) + (r' i j)) dfevals'')
             | _ => None
             end
           | _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (MatrixMinus tt l r) 
                                          (fun i j => (l' i j) - (r' i j)) dfevals'')
             | _ => None
             end
           | _ => None
           end
         | VectorApply n _ x s r => 
           match df_evals_list σ r dfevals with           
(*           | Some r' => vectoro_to_ovector 
                          (fun i => 
                             let xv := (x, DTfloat):var_type in
                             df_eval (cons (mk_env_entry xv (r' i)) σ) s) *)
           | _ => None
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_evals_list σ l dfevals with
(*           | Some l' => 
             match (vectoro_to_ovector 
                      (fun i => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (l' i)) 
                                       (cons (mk_env_entry xv2 (r i)) σ)) s)) with
             | Some vv => Some (vsum vv)
             | _ => None
             end *)
           | _ => None
           end
           | _ => None
         end.

(*
    Program
      Fixpoint evalslookup {T} (l:df_eval_env) (df:DefinedFunction UnitAnn T) : 
      option (definition_function_types_interp T)
      := match l with
         | nil => None
         | fv::os => if T == (projT1 (sigT_of_sigT2 fv)) then
                       if df == (projT2 (sigT_of_sigT2 fv)) then 
                         Some (eq_rect _ definition_function_types_interp (projT3 fv) _ _) 
                       else evalslookup os df
                     else evalslookup os df
         end.
*)
    Definition df_eval_symbolic_gradient {T} (σ:df_env) (df:DefinedFunction UnitAnn T) (lv:list var_type) : option (list (definition_function_types_interp T))
      := listo_to_olist (map (df_eval σ) (df_gradient df lv)).
    
  End eval.

  Section isderiv.
    
  Context (σ:df_env).
  Context (v:SubVar).
(*
  Inductive is_deriv : DefinedFunction -> float -> Prop
    := 
    | is_deriv_Number (x : float) : is_deriv (Number x) 0
    | is_deriv_Var_eq : is_deriv (Var v) 1
    | is_deriv_Var_neq (sv : SubVar) : sv <> v -> is_deriv (Var sv) 0
    | is_deriv_Plus l l' r r' :
        is_deriv l l' ->
        is_deriv r r' ->
        is_deriv (Plus l r) (l' + r')
    | is_deriv_Minus l l' r r' :
        is_deriv l l' ->
        is_deriv r r' ->
        is_deriv (Minus l r) (l' - r')
    | is_deriv_Times l le l' r re r' :
        df_eval σ l = Some le ->
        is_deriv l l' ->
        df_eval σ r = Some re ->
        is_deriv r r' ->
        is_deriv (Times l r) ((le * r') + (l' * re))
    | is_deriv_Divide l le l' r re r' :
        df_eval σ l = Some le ->
        is_deriv l l' ->
        df_eval σ r = Some re ->
        is_deriv r r' ->
        is_deriv (Times l r)
                 (((l' * re ) - (le  * r'))
                    / (re * re))
    | is_deriv_Exp e ee e' :
        df_eval σ e = Some ee ->
        is_deriv e e' ->
        is_deriv (Exp e) (e' * (Fexp ee))
    | is_deriv_Log e ee e' :
        df_eval σ e = Some ee ->
        is_deriv e e' ->
        is_deriv (Exp e) (e' / ee)
    | is_deriv_Abs e ee e' :
        df_eval σ e = Some ee ->
        is_deriv e e' -> is_deriv (Abs e) (e' * (sign ee))
    | is_deriv_Sign (e : DefinedFunction) :
        is_deriv (Sign e) 0
    | is_deriv_PSign (e : DefinedFunction) :
        is_deriv (PSign e) 0
    | is_deriv_Max_l l le l' re r :
        df_eval σ l = Some le ->
        df_eval σ r = Some re ->
        (le > re) = true ->
        is_deriv l l' ->
        is_deriv (Max l r) l'
    | is_deriv_Max_r l le r re r' :
        df_eval σ l = Some le ->
        df_eval σ r = Some re ->
        (re >= le) = true ->
        is_deriv r r' ->
        is_deriv (Max l r) r'.
   (*
    | is_deriv_Max_eq l l' ee r r' :
        df_eval σ l = Some ee ->
        df_eval σ r = Some ee ->
        is_deriv l l' ->
        is_deriv r r' ->
        is_deriv (Max l r) ((l' + r')/2) *)

*)
  End isderiv.
  
  Section deriv2.

    Fixpoint df_eval_deriv {T} (σ:df_env) (df:DefinedFunction UnitAnn T) (v:var_type) : option (definition_function_types_interp T)
      := (match df with
         | Number _ _ => Some 0
         | Constant t _ x => Some
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
         | DVector n _ dfs => vectoro_to_ovector (fun i => df_eval_deriv σ (dfs i) v)
         | DMatrix n m _ df => matrixo_to_omatrix (fun i j => df_eval_deriv σ (df i j) v)
         | Var x _ => Some (let t:=snd x in 
               match t return definition_function_types_interp t with
               | DTfloat => if x == v then 1 else 0
               | DTVector n => ConstVector n (if x == v then 1 else 0)
               | DTMatrix m n => ConstMatrix m n (if x == v then 1 else 0)
               end)
         | Plus _ l r => 
           match df_eval_deriv σ l v, df_eval_deriv σ r v with
           | Some le, Some lr => Some (le + lr)
           | _, _ => None
           end
         | Minus _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with
           | Some le, Some lr => Some (le - lr)
           | _, _ => None
           end
         | Times _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (le * rd + 
                   (ld * re))
           | _, _, _, _ => None
           end
         | Divide _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some ((ld / re) - ((le * rd) / (re * re)))
           | _, _, _, _ => None
           end
         | Square _ e =>
           match df_eval σ e, df_eval_deriv σ e v with
           | Some ee, Some ed => Some (2 * ee * ed)
           | _, _  => None
           end
         | Exp _ e =>
           match df_eval σ e, df_eval_deriv σ e v with
           | Some ee, Some ed => Some (ed * Fexp ee)
           | _, _  => None
           end
         | Log _ e =>
           match df_eval σ e, df_eval_deriv σ e v with
           | Some ee, Some ed => Some (ed / ee)
           | _, _ => None
           end
         | Abs _ e =>
           match df_eval σ e, df_eval_deriv σ e v with
           | Some ee, Some ed => Some (ed * (sign ee))
           | _, _ => None
           end
         | Sign _ e =>
           match df_eval_deriv σ e v with
           | Some _ => Some 0
           | None => None
           end
         | PSign _ e =>
           match df_eval_deriv σ e v with
           | Some _ => Some 0
           | None => None
           end
         | Max _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some re =>
             if le <= re then df_eval_deriv σ r v else df_eval_deriv σ l v
           | _, _ => None
           end
         | VectorElem n _ l i => 
           match (df_eval_deriv σ l v)  with
           | Some l' => Some (l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_deriv σ l v)  with
           | Some l' => Some (l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd => 
               Some (vsum (fun j => (le j) * (rd j) + (ld j) * (re j)))
           | _, _, _, _ => None
           end
         | VectorSum n _ l =>
           match df_eval_deriv σ l v with
           | Some ld =>
               Some (vsum ld)
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_eval_deriv σ l v with
           | Some ld =>
               Some (msum ld)
           | _ => None
           end
         | VectorScalMult n _ x r =>
           match df_eval σ x, df_eval_deriv σ x v, df_eval σ r, df_eval_deriv σ r v with
           | Some xe, Some xd, Some re, Some rd => Some (fun j => xe * (rd j) + xd * (re j))
           | _, _, _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval σ x, df_eval_deriv σ x v, df_eval σ r, df_eval_deriv σ r v with
           | Some xe, Some xd, Some re, Some rd => Some (fun i j => xe * (rd i j) + xd * (re i j))
           | _, _, _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i => vsum (fun j => (le i j)*(rd j) + (ld i j)*(re j)))
           | _, _, _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with
           | Some le, Some re =>
             Some (fun i j => (le i j) + (re i))
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i k => vsum (fun j => (le i j)*(rd j k) + (ld i j)*(re j k)))
           | _, _, _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (fun i => (l' i) + (r' i))
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (fun i => (l' i) - (r' i))
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (fun i j => (l' i j) + (r' i j))
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (fun i j => (l' i j) - (r' i j))
           | _, _ => None
           end
         | VectorApply n _ x s r =>
           match df_eval σ r, df_eval_deriv σ r v with                      
           | Some re, Some rd => 
             vectoro_to_ovector 
               (fun i => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (re i)) σ) s v with
                         | Some sd => Some ((rd i) * sd)
                         | _ => None
                         end)
           | _, _ => None                                                    
           end
         | MatrixApply n m _ x s r =>
           match df_eval σ r, df_eval_deriv σ r v with                      
           | Some re, Some rd => 
             matrixo_to_omatrix
               (fun i j => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (re i j)) σ) s v with
                         | Some sd => Some ((rd i j) * sd)
                         | _ => None
                         end)
           | _, _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_eval σ l, df_eval_deriv σ l v with                      
           | Some le, Some ld => 
             match (vectoro_to_ovector 
                      (fun i => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (le i)) 
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
           match df_eval σ l, df_eval_deriv σ l v with                      
           | Some le, Some ld => 
             match (matrixo_to_omatrix
                      (fun i j => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (le i j)) 
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

    Fixpoint df_eval_tree_deriv {T} (σ:df_env) (df:DefinedFunction EvalAnn T) (v:var_type) : option (definition_function_types_interp T)
      := (match df with
         | Number _ _ => Some 0
         | Constant t _ x => Some
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
         | DVector n _ dfs => vectoro_to_ovector (fun i => df_eval_tree_deriv σ (dfs i) v)
         | DMatrix n m _ df => matrixo_to_omatrix (fun i j => df_eval_tree_deriv σ (df i j) v)
         | Var x _ => Some (let t:=snd x in 
               match t return definition_function_types_interp t with
               | DTfloat => if x == v then 1 else 0
               | DTVector n => ConstVector n (if x == v then 1 else 0)
               | DTMatrix m n => ConstMatrix m n (if x == v then 1 else 0)
               end)
         | Plus _ l r => 
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some le, Some lr => Some (le + lr)
           | _, _ => None
           end
         | Minus _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some le, Some lr => Some (le - lr)
           | _, _ => None
           end
         | Times _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some (le * rd + 
                   (ld * re))
           | _, _ => None
           end
         | Divide _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in            
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some ((ld / re) - ((le * rd) / (re * re)))
           | _, _ => None
           end
         | Square _ e =>
           let ee := get_annotation e in
           match df_eval_tree_deriv σ e v with
           | Some ed => Some (2 * ee * ed)
           | _  => None
           end
         | Exp _ e =>
           let ee := get_annotation e in           
           match df_eval_tree_deriv σ e v with
           | Some ed => Some (ed * Fexp ee)
           | _  => None
           end
         | Log _ e =>
           let ee := get_annotation e in                      
           match df_eval_tree_deriv σ e v with
           | Some ed => Some (ed / ee)
           | _ => None
           end
         | Abs _ e =>
           let ee := get_annotation e in                                 
           match df_eval_tree_deriv σ e v with
           | Some ed => Some (ed * (sign ee))
           | _ => None
           end
         | Sign _ e => 
           match df_eval_tree_deriv σ e v with
           | Some _ => Some 0
           | None => None
           end
         | PSign _ e => 
           match df_eval_tree_deriv σ e v with
           | Some _ => Some 0
           | None => None
           end
         | Max _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in                       
           if le <= re then df_eval_tree_deriv σ r v else df_eval_tree_deriv σ l v
         | VectorElem n _ l i => 
           match (df_eval_tree_deriv σ l v)  with
           | Some l' => Some (l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_tree_deriv σ l v)  with
           | Some l' => Some (l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd => 
               Some (vsum (fun j => (le j) * (rd j) + (ld j) * (re j)))
           | _, _ => None
           end
         | VectorSum n _ l =>
           match df_eval_tree_deriv σ l v with
           | Some ld =>
               Some (vsum ld)
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_eval_tree_deriv σ l v with
           | Some ld =>
               Some (msum ld)
           | _ => None
           end
         | VectorScalMult n _ x r =>
           let '(xe,re) := (get_annotation x, get_annotation r) in
           match df_eval_tree_deriv σ x v, df_eval_tree_deriv σ r v with
           | Some xd, Some rd => Some (fun j => xe * (rd j) + xd * (re j))
           | _, _ => None
           end
         | MatrixScalMult n m _ x r =>
           let '(xe,re) := (get_annotation x, get_annotation r) in           
           match df_eval_tree_deriv σ x v, df_eval_tree_deriv σ r v with
           | Some xd, Some rd => Some (fun i j => xe * (rd i j) + xd * (re i j))
           | _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in           
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some (fun i => vsum (fun j => (le i j)*(rd j) + (ld i j)*(re j)))
           | _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some (fun i j => (ld i j) + (rd i))
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in                      
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some (fun i k => vsum (fun j => (le i j)*(rd j k) + (ld i j)*(re j k)))
           | _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (fun i => (l' i) + (r' i))
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (fun i => (l' i) - (r' i))
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (fun i j => (l' i j) + (r' i j))
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (fun i j => (l' i j) - (r' i j))
           | _, _ => None
           end
         | VectorApply n _ x s r =>
           let re := get_annotation r in 
           match df_eval_tree_deriv σ r v with                      
           | Some rd => 
             vectoro_to_ovector 
               (fun i => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (re i)) (* σ *) nil) s v with
                         | Some sd => Some ((rd i) * sd)
                         | _ => None
                         end)
           | _ => None                                                    
           end
         | MatrixApply n m _ x s r =>
           let re := get_annotation r in 
           match df_eval_tree_deriv σ r v with                      
           | Some rd => 
             matrixo_to_omatrix
               (fun i j => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (re i j)) (* σ *) nil) s v with
                         | Some sd => Some ((rd i j) * sd)
                         | _ => None
                         end)
           | _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l r => 
           let le := get_annotation l in 
           match df_eval_tree_deriv σ l v with                      
           | Some ld => 
             match (vectoro_to_ovector 
                      (fun i => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (le i)) 
                                                   (cons (mk_env_entry xv2 (r i)) (* σ *) nil)) s v with
                         | Some sd => Some ((ld i) * sd)
                         | _ => None
                         end)) with
             | Some vv => Some (vsum vv)
             | _ => None
             end
           | _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           let le := get_annotation l in 
           match df_eval_tree_deriv σ l v with                      
           | Some ld => 
             match (matrixo_to_omatrix
                      (fun i j => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (le i j)) 
                                                   (cons (mk_env_entry xv2 (r i j)) (* σ *) nil)) s v with
                         | Some sd => Some ((ld i j) * sd)
                         | _ => None
                         end)) with
             | Some vv => Some ((msum vv) / (FfromZ (Z.of_nat m)))
             | _ => None
             end
           | _ => None
           end
          end).
    
    Definition vector_env_iter {n} {A} (f: A -> df_env -> option df_env)
             (env: df_env) (v : Vector A n) : option df_env :=
      vector_fold_right (fun a oenv => match oenv with
                                      | Some env => f a env
                                      | _ => None
                                      end)
                        (Some env) v.
    
    Fixpoint list_env_iter {A} (f: A -> df_env -> option df_env)
             (oenv:option df_env) (l: list A) : option df_env :=
      match oenv, l with
      | Some env, x :: l' => list_env_iter f (f x env) l'
      | _, _ => oenv
      end.         

   Lemma list_env_iter_none {A} (f: A -> df_env -> option df_env) (l: list A) : 
     list_env_iter f None l = None.
   Proof.
     induction l.
     now simpl.
     now simpl.
   Qed.

    Definition two_vector_env_iter {n} {A B} (f: A -> B -> df_env -> option df_env)
               (env: df_env) (v: Vector A n) (w: Vector B n) : option df_env :=
      vector_env_iter (fun '(a,b) env => f a b env) env 
                      (vector_zip v w).


    Definition two_vector_env_iter_alt {n} {A B} (f: A -> B -> df_env -> option df_env)
               (env: df_env) (v: Vector A n) (w: Vector B n) : option df_env :=
      list_env_iter (fun i env => f (v i) (w i) env) (Some env) (bounded_seq0 n).

    Definition matrix_env_iter {m n} {A} (f: A -> df_env -> option df_env)
               (env: option df_env) (mat : Matrix A m n) : option df_env :=
      vector_fold_right
        (fun vec oenv =>
           vector_fold_right (fun a oenv => match oenv with
                                      | Some env => f a env
                                      | _ => None
                                      end) oenv vec
        ) env mat.
    
    Definition two_matrix_env_iter {n m} {A B} (f: A -> B -> df_env -> option df_env)
               (env: option df_env) (v: Matrix A n m) (w: Matrix B n m) : option df_env :=
      let vw := matrix_zip v w in
      matrix_env_iter (fun '(a,b) e => f a b e) env vw.
          
    Definition two_matrix_env_iter_alt {n m} {A B} (f: A -> B -> df_env -> option df_env)
               (env: df_env) (v: Matrix A n m) (w: Matrix B n m) : option df_env :=
      list_env_iter (fun i env => list_env_iter (fun j env => f (v i j) (w i j) env)
                                                (Some env) (bounded_seq0 m))
                    (Some env) (bounded_seq0 n).


    Program Definition addvar (x : var_type) (grad_env:df_env) :=
      (match snd x as y return snd x = y ->
                               definition_function_types_interp y -> 
                               definition_function_types_interp y with
       | DTfloat =>  fun pf grad => match vartlookup grad_env x with
                     | Some val => grad + ((coerce _ val):float)
                     | _ => grad
                     end
       | DTVector n => fun pf grad => match vartlookup grad_env x with
                       | Some val => fun i => (grad i) + (((coerce _ val):Vector float n) i)
                       | _ =>  grad
                       end
       | DTMatrix m n => fun pf grad => match vartlookup grad_env x with
                         | Some val => fun i j => (((coerce _ val):Matrix float m n) i j) + (grad i j)
                         | _ => grad
                         end
       end) (eq_refl _).
    Next Obligation.
      rewrite pf; reflexivity.
    Defined.
    Next Obligation.
      rewrite pf; reflexivity.
    Defined.
    Next Obligation.
      rewrite pf; reflexivity.
    Defined.

    Definition gradenv_init1 (v : var_type) : env_entry_type :=
      mk_env_entry v 
      (match snd v as y return definition_function_types_interp y with
       | DTfloat =>  0
       | DTVector n => ConstVector n 0
       | DTMatrix n m => ConstMatrix n m 0
       end).

    Definition gradenv_init (dvars : list var_type) : df_env :=
         map gradenv_init1 dvars.

    Fixpoint df_eval_backprop_deriv {T Ann} (σ:df_env) (df:DefinedFunction Ann T) (grad_env:df_env) {struct df} : definition_function_types_interp T -> option df_env
      := match df with
         | Number _ _ => fun grad => Some grad_env
         | Constant _ _ _ => fun grad => Some grad_env
         | DVector n _ dfs => fun grad => 
             two_vector_env_iter_alt (fun x g genv => df_eval_backprop_deriv σ x genv g) 
                                     grad_env dfs grad 
         | DMatrix n m _ dfs => fun grad => 
             two_matrix_env_iter_alt (fun x g genv => df_eval_backprop_deriv σ x genv  g) 
                                     grad_env dfs grad
         | Var x _ => fun grad => 
                        if vartlookup grad_env x then 
                          Some (vart_update grad_env x (addvar x grad_env grad))
                        else Some grad_env
         | Plus _ l r => fun grad => 
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | Minus _ l r => fun grad => 
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  (-grad)
           | _ => None
           end
         | Times _ l r => fun grad => 
           match df_eval σ l, df_eval σ r with
               | Some le, Some re =>
                 match df_eval_backprop_deriv σ l grad_env  (re * grad) with                 
                 | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  (le * grad)
                 | _ => None
                 end
           | _, _ => None
           end
         | Divide _ l r => fun grad => 
           match df_eval σ l, df_eval σ r with
               | Some le, Some re =>
                 match df_eval_backprop_deriv σ l grad_env (grad / re) with
                 | Some grad_env' => df_eval_backprop_deriv σ r grad_env' (- le / (re * re) * grad)
                 | _ => None
                 end
           | _, _ => None
           end
         | Square _ e => fun grad => 
           match df_eval σ e with
           | Some ee => df_eval_backprop_deriv σ e grad_env  (2 * ee * grad)
           | _  => None
           end
         | Exp _ e => fun grad => 
           match df_eval σ e with
           | Some ee => df_eval_backprop_deriv σ e grad_env  (grad * Fexp ee)
           | _  => None
           end
         | Log _ e => fun grad => 
           match df_eval σ e with
           | Some ee => df_eval_backprop_deriv σ e grad_env  (grad / ee)
           | _  => None
           end
         | Abs _ e => fun grad => 
           match df_eval σ e with
           | Some ee => df_eval_backprop_deriv σ e grad_env  (grad * (sign ee))
           | _  => None
           end
         | Sign _ e => fun grad => df_eval_backprop_deriv σ e grad_env  0
         | PSign _ e => fun grad => df_eval_backprop_deriv σ e grad_env  0
         | Max _ l r => fun grad => 
                          match df_eval σ l,
                                df_eval σ r with
           | Some le, Some re =>
             if le <= re then 
               (df_eval_backprop_deriv σ r grad_env grad) else
               (df_eval_backprop_deriv σ l grad_env grad)
           | _, _ => None
           end
         | VectorElem n _ l i => fun grad => 
           let grad' := fun k => if proj1_sig k == proj1_sig i then grad else 0 in
           df_eval_backprop_deriv σ l grad_env  grad'
         | MatrixElem m n _ l i j => fun grad => 
           let grad' := fun k1 k2 => 
                          if (proj1_sig k1 == proj1_sig i) then
                            if (proj1_sig k2 == proj1_sig j) then grad else 0
                            else 0 in
           df_eval_backprop_deriv σ l grad_env  grad'
         | VectorDot n _ l r => fun grad =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some re =>
             match df_eval_backprop_deriv σ l grad_env  (vmap (fun rv => rv*grad) re) with
             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env'  (vmap (fun lv => lv*grad) le)
             | _ => None
             end
           | _, _ => None
           end
         | VectorSum n _ l => fun grad =>
           df_eval_backprop_deriv σ l grad_env  (ConstVector n grad)
         | MatrixSum n m _ l => fun grad =>
           df_eval_backprop_deriv σ l grad_env  (ConstMatrix n m grad)
         | VectorScalMult n _ x r => fun grad =>
           match df_eval σ x, df_eval σ r with
           | Some xe, Some re => 
             match df_eval_backprop_deriv σ x grad_env  (vsum (fun j => (re j) * (grad j))) with
             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env'  (fun j => xe * (grad j))
             | _ => None
             end
           | _, _ => None
           end
         | MatrixScalMult n m _ x r => fun grad =>
           match df_eval σ x, df_eval σ r with
           | Some xe, Some re => 
             match df_eval_backprop_deriv σ x grad_env  (msum (fun i j => (re i j) * (grad i j))) with
             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env'  (fun i j => (grad i j) * xe)
             | _ => None
             end
           | _, _ => None
           end
         | MatrixVectorMult n m _ l r => fun grad =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some re => 
             match df_eval_backprop_deriv σ l grad_env  (fun i j => (grad i) * (re j)) with


             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env'  (matrix_vector_mult (fun i j => le j i) grad)
             | _ => None
             end
           | _, _ => None
           end
         | MatrixVectorAdd n m _ l r => fun grad =>
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => 
             match list_env_iter 
                     (fun i env => df_eval_backprop_deriv σ r env  ((transpose grad) i))
                     (Some grad_env') (bounded_seq0 m) with
               | Some grad_env'' => Some grad_env''
               | _ => None
               end
           | _ => None
           end
         | MatrixMult n m p _ l r => fun grad =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some re => 
             match df_eval_backprop_deriv σ l grad_env  (matrix_mult grad (fun i j => (re j i))) with


             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env'  (matrix_mult (fun i j => le j i) grad)
             | _ => None
             end
           | _, _ => None
           end
         | VectorPlus n _ l r => fun grad =>
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | VectorMinus n _ l r => fun grad => 
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  (fun i => - (grad i))
           | _ => None
           end
         | MatrixPlus n m _ l r => fun grad =>
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | MatrixMinus n m _ l r => fun grad =>
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  (fun i j => - (grad i j))
           | _ => None
           end
         | VectorApply n _ x s r => fun grad =>
           match df_eval σ r with
           | Some re => 
             let xv := (x, DTfloat):var_type in
             let s' := df_deriv s xv in
             let ograd := 
                 vmap (fun '(rei, g) => 
                         match df_eval (cons (mk_env_entry xv rei) σ) s' with
                         | Some se => Some (g * se)
                         | _ => None
                         end)
                      (vector_zip re grad) in
             match vectoro_to_ovector ograd with 
             | Some grad' => df_eval_backprop_deriv σ r grad_env  grad'
             | _ => None
             end
           | _ => None                                                    
           end
         | MatrixApply n m _ x s r => fun grad =>
           match df_eval σ r with
           | Some re => 
             let xv := (x, DTfloat):var_type in
             let s' := df_deriv s xv in
             let ograd := 
                 mmap (fun '(rei, g) => 
                         match df_eval (cons (mk_env_entry xv rei) σ) s' with
                         | Some se => Some (g * se)
                         | _ => None
                         end)
                      (matrix_zip re grad) in
             match matrixo_to_omatrix ograd with 
             | Some grad' => df_eval_backprop_deriv σ r grad_env  grad'
             | _ => None
             end
           | _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l re => fun grad =>
           match df_eval σ l with
           | Some le => 
             let xv1 := (v1, DTfloat):var_type in
             let xv2 := (v2, DTfloat):var_type in                         
             let s' := df_deriv s xv1 in
             let ograd := 
                 vmap (fun '(lei, rei) => 
                         let senv := cons (mk_env_entry xv1 lei) 
                                          (cons (mk_env_entry xv2 rei) σ) in
                         match df_eval senv s' with
                         | Some se => Some (grad * se)
                         | _ => None
                         end)
                      (vector_zip le re) in
             match vectoro_to_ovector ograd with 
             | Some grad' => df_eval_backprop_deriv σ l grad_env  grad'
             | _ => None
             end
           | _ => None                                                    
           end
         | MLossfun n m _ v1 v2 s l re => fun grad =>
           match df_eval σ l with
           | Some le => 
             let xv1 := (v1, DTfloat):var_type in
             let xv2 := (v2, DTfloat):var_type in                         
             let s' := df_deriv s xv1 in
             let ograd := 
                 mmap (fun '(lei, rei) => 
                         let senv := cons (mk_env_entry xv1 lei) 
                                          (cons (mk_env_entry xv2 rei) σ) in
                         match df_eval senv s' with
                         | Some se => Some ((grad * se)/(FfromZ (Z.of_nat m)))
                         | _ => None
                         end)
                      (matrix_zip le re) in
             match matrixo_to_omatrix ograd with 
             | Some grad' => df_eval_backprop_deriv σ l grad_env  grad'
             | _ => None
             end
           | _ => None                                                    
           end
          end.


    Fixpoint df_eval_tree_backprop_deriv {T} (σ:df_env) (df:DefinedFunction EvalAnn T) (grad_env:df_env)  {struct df} : definition_function_types_interp T -> option df_env
      := match df with
         | Number _ _ => fun grad => Some grad_env
         | Constant _ _ _ => fun grad => Some grad_env
         | DVector n _ dfs => fun grad => 
             two_vector_env_iter_alt (fun x g genv => df_eval_tree_backprop_deriv σ x genv  g) 
                                     grad_env dfs grad 
         | DMatrix n m _ dfs => fun grad => 
             two_matrix_env_iter_alt (fun x g genv => df_eval_tree_backprop_deriv σ x genv  g) 
                                     grad_env dfs grad
         | Var x _ => fun grad => 
                        if vartlookup grad_env x then 
                          Some (vart_update grad_env x (addvar x grad_env grad))
                        else Some grad_env
         | Plus _ l r => fun grad => 
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | Minus _ l r => fun grad => 
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  (-grad)
           | _ => None
           end
         | Times _ l r => fun grad => 
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ l grad_env  (re * grad) with                 
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  (le * grad)
           | _ => None
           end
         | Divide _ l r => fun grad =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ l grad_env  (grad / re) with                 
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env' (- le / (re * re) * grad)
           | _ => None
           end
         | Square _ e => fun grad => 
           let ee := get_annotation e in
           df_eval_tree_backprop_deriv σ e grad_env  (2 * ee * grad)
         | Exp _ e => fun grad => 
           let ee := get_annotation e in
           df_eval_tree_backprop_deriv σ e grad_env  (grad * Fexp ee)
         | Log _ e => fun grad => 
           let ee := get_annotation e in
           df_eval_tree_backprop_deriv σ e grad_env  (grad / ee)
         | Abs _ e => fun grad => 
           let ee := get_annotation e in
           df_eval_tree_backprop_deriv σ e grad_env  (grad * (sign ee))
         | Sign _ e => fun grad => df_eval_tree_backprop_deriv σ e grad_env  0
         | PSign _ e => fun grad => df_eval_tree_backprop_deriv σ e grad_env  0
         | Max _ l r => fun grad => 
           let '(le,re) := (get_annotation l, get_annotation r) in 
           if le <= re then 
             (df_eval_tree_backprop_deriv σ r grad_env  grad) else
             (df_eval_tree_backprop_deriv σ l grad_env  grad)
         | VectorElem n _ l i => fun grad => 
           let grad' := fun k => if proj1_sig k == proj1_sig i then grad else 0 in
           df_eval_tree_backprop_deriv σ l grad_env  grad'
         | MatrixElem m n _ l i j => fun grad => 
           let grad' := fun k1 k2 => 
                          if (proj1_sig k1 == proj1_sig i) then
                            if (proj1_sig k2 == proj1_sig j) then grad else 0
                            else 0 in
           df_eval_tree_backprop_deriv σ l grad_env  grad'
         | VectorDot n _ l r => fun grad =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ l grad_env  (vmap (fun rv => rv*grad) re) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (vmap (fun lv => lv*grad) le)
           | _ => None
           end
         | VectorSum n _ l => fun grad =>
           df_eval_tree_backprop_deriv σ l grad_env  (ConstVector n grad)
         | MatrixSum n m _ l => fun grad =>
           df_eval_tree_backprop_deriv σ l grad_env  (ConstMatrix n m grad)
         | VectorScalMult n _ x r => fun grad =>
           let '(xe,re) := (get_annotation x, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ x grad_env  (vsum (fun j => (re j) * (grad j))) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (fun j => xe * (grad j))
           | _ => None
           end
         | MatrixScalMult n m _ x r => fun grad =>
           let '(xe,re) := (get_annotation x, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ x grad_env  (msum (fun i j => (re i j) * (grad i j))) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (fun i j => (grad i j) * xe)
           | _ => None
           end
         | MatrixVectorMult n m _ l r => fun grad =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ l grad_env  (fun i j => (grad i) * (re j)) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (matrix_vector_mult (fun i j => le j i) grad)
           | _ => None
           end
         | MatrixVectorAdd n m _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => 
             match list_env_iter 
                     (fun i env => df_eval_tree_backprop_deriv σ r env  ((transpose grad) i))
                     (Some grad_env') (bounded_seq0 m) with
               | Some grad_env'' => Some grad_env''
               | _ => None
               end
           | _ => None
           end
         | MatrixMult n m p _ l r => fun grad =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ l grad_env  (matrix_mult grad (fun i j => (re j i))) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (matrix_mult (fun i j => le j i) grad)
           | _ => None
           end
         | VectorPlus n _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | VectorMinus n _ l r => fun grad => 
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  (fun i => - (grad i))
           | _ => None
           end
         | MatrixPlus n m _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | MatrixMinus n m _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  (fun i j => - (grad i j))
           | _ => None
           end
         | VectorApply n _ x s r => fun grad =>
           let re := get_annotation r in 
           let xv := (x, DTfloat):var_type in
           let s' := df_deriv s xv in
           let ograd := 
               vmap (fun '(rei, g) => 
                       match df_eval (cons (mk_env_entry xv rei) σ) s' with
                       | Some se => Some (g * se)
                       | _ => None
                       end)
                    (vector_zip re grad) in
           match vectoro_to_ovector ograd with 
           | Some grad' => df_eval_tree_backprop_deriv σ r grad_env  grad'
           | _ => None
           end
         | MatrixApply n m _ x s r => fun grad =>
           let re := get_annotation r in 
           let xv := (x, DTfloat):var_type in
           let s' := df_deriv s xv in
           let ograd := 
               mmap (fun '(rei, g) => 
                       match df_eval (cons (mk_env_entry xv rei) σ) s' with
                       | Some se => Some (g * se)
                       | _ => None
                       end)
                    (matrix_zip re grad) in
           match matrixo_to_omatrix ograd with 
           | Some grad' => df_eval_tree_backprop_deriv σ r grad_env  grad'
           | _ => None
           end
         | VLossfun n _ v1 v2 s l re => fun grad =>
           let le := get_annotation l in
           let xv1 := (v1, DTfloat):var_type in
           let xv2 := (v2, DTfloat):var_type in                         
           let s' := df_deriv s xv1 in
           let ograd := 
               vmap (fun '(lei, rei) => 
                       let senv := cons (mk_env_entry xv1 lei) 
                                        (cons (mk_env_entry xv2 rei) σ) in
                       match df_eval senv s' with
                       | Some se => Some (grad * se)
                       | _ => None
                       end)
                    (vector_zip le re) in
           match vectoro_to_ovector ograd with 
           | Some grad' => df_eval_tree_backprop_deriv σ l grad_env  grad'
           | _ => None
           end
         | MLossfun n m _ v1 v2 s l re => fun grad =>
           let le := get_annotation l in
           let xv1 := (v1, DTfloat):var_type in
           let xv2 := (v2, DTfloat):var_type in                         
           let s' := df_deriv s xv1 in
           let ograd := 
               mmap (fun '(lei, rei) => 
                       let senv := cons (mk_env_entry xv1 lei) 
                                        (cons (mk_env_entry xv2 rei) σ) in
                       match df_eval senv s' with
                       | Some se => Some ((grad * se) / (FfromZ (Z.of_nat m)))
                       | _ => None
                       end)
                    (matrix_zip le re) in
           match matrixo_to_omatrix ograd with 
           | Some grad' => df_eval_tree_backprop_deriv σ l grad_env  grad'
           | _ => None
           end
          end.

    Definition o_df_env_to_df_env (oenv : option df_env) : df_env :=
      match oenv with
      | Some env => env
      | _ => nil
      end.

    Lemma var_type_UIP_refl {x:var_type} (e:x=x) : e = eq_refl x.
    Proof.
      apply (UIP_dec vart_dec).
    Qed.
    
    Definition backprop_lookup (oenv:option df_env) (a:var_type) : 
      option (definition_function_types_interp (snd a)) :=
      match oenv with
      | Some env =>        
        match vartlookup env a with
        | Some val => Some val
        | _ => None
        end
      | _ => None
     end.          

   Definition is_scalar_df_type (dft:definition_function_types) : Prop
     := match dft with
        | DTfloat => True
        | _ => False
        end.

   Fixpoint is_scalar_function {Ann} {T} (df:DefinedFunction Ann T) : Prop
     := match df with
        | Number _ _ => True
        | Constant t _ _ => is_scalar_df_type t
        | Var v _ => is_scalar_df_type (snd v)
        | Plus _ l r => is_scalar_function l /\ is_scalar_function r
        | Minus _ l r => is_scalar_function l /\ is_scalar_function r
        | Times _ l r => is_scalar_function l /\ is_scalar_function r
        | Divide _ l r => is_scalar_function l /\ is_scalar_function r
        | Square _ e => is_scalar_function e
        | Exp _ e => is_scalar_function e
        | Log _ e => is_scalar_function e
        | Abs _ e => is_scalar_function e
        | Sign _ e => is_scalar_function e
        | PSign _ e => is_scalar_function e
        | Max _ l r => is_scalar_function l /\ is_scalar_function r
        | _ => False
        end.

   Fixpoint is_df_rec_prop {Ann} {T} 
            (prop : forall TT:definition_function_types, 
                (DefinedFunction Ann TT) -> Prop)
            (df:DefinedFunction Ann T) {struct df}: Prop
     := prop T df /\
        match df with
         | Number _ _ => True
         | Constant _ _ _ => True
         | DVector n _ vec => 
           vector_fold_right (fun x p => (is_df_rec_prop prop x) /\ p) True vec
         | DMatrix n m _ mat => 
           vector_fold_right 
             (fun vec p => (vector_fold_right (fun x p => (is_df_rec_prop prop x) /\ p) True vec) /\ p) True mat
         | Var _ _ => True
         | Plus _ l r => (is_df_rec_prop prop l) /\ (is_df_rec_prop prop r)
         | Minus _ l r => (is_df_rec_prop prop l) /\ (is_df_rec_prop prop r)
         | Times _ l r => (is_df_rec_prop prop l) /\ (is_df_rec_prop prop r)
         | Divide _ l r => (is_df_rec_prop prop l) /\ (is_df_rec_prop prop r)
         | Square _ l => is_df_rec_prop prop l
         | Exp _ l => is_df_rec_prop prop l
         | Log _ l => is_df_rec_prop prop l
         | Abs _ l => is_df_rec_prop prop l
         | Sign _ l => is_df_rec_prop prop l
         | PSign _ l => is_df_rec_prop prop l
         | Max _ l r => (is_df_rec_prop prop l) /\ (is_df_rec_prop prop r)
         | VectorDot n _ l r => (is_df_rec_prop prop l) /\ 
                                (is_df_rec_prop prop r)
         | VectorSum _ _ l => is_df_rec_prop prop l
         | MatrixSum _ _ _ l => is_df_rec_prop prop l
         | VectorElem _ _ vec i => is_df_rec_prop prop vec
         | MatrixElem _ _ _ mat i j => is_df_rec_prop prop mat
         | MatrixVectorMult _ _ _ l r => (is_df_rec_prop prop l) /\ 
                                         (is_df_rec_prop prop r)
         | MatrixVectorAdd _ _ _ l r =>  (is_df_rec_prop prop l) /\ 
                                         (is_df_rec_prop prop r)
         | MatrixMult _ _ _ _ l r => (is_df_rec_prop prop l) /\ 
                                     (is_df_rec_prop prop r)
         | VectorPlus _ _ l r =>  (is_df_rec_prop prop l) /\ 
                                  (is_df_rec_prop prop r)
         | VectorMinus _ _ l r =>  (is_df_rec_prop prop l) /\ 
                                   (is_df_rec_prop prop r)
         | MatrixPlus _ _ _ l r => (is_df_rec_prop prop l) /\ 
                                   (is_df_rec_prop prop r)
         | MatrixMinus _ _ _ l r => (is_df_rec_prop prop l) /\ 
                                    (is_df_rec_prop prop r)
         | VectorScalMult _ _ l r => (is_df_rec_prop prop l) /\ 
                                    (is_df_rec_prop prop r)
         | MatrixScalMult _ _ _ l r => (is_df_rec_prop prop l) /\ 
                                       (is_df_rec_prop prop r)
         | VectorApply _ _ _ _ l => is_df_rec_prop prop l
         | MatrixApply _ _ _ _ _ l => is_df_rec_prop prop l
         | VLossfun _ _ _ _ _ l _ => is_df_rec_prop prop l
         | MLossfun _ _ _ _ _ _ l _ => is_df_rec_prop prop l
         end.


   Definition is_df_evalann_correct_top (σ:df_env) {T} (df:DefinedFunction EvalAnn T)
     := df_eval σ df = Some (get_annotation df). 

   Definition is_df_evalann_correct (σ:df_env) {T} (df:DefinedFunction EvalAnn T)
     := is_df_rec_prop (@is_df_evalann_correct_top σ) df.

   Lemma is_df_rec_prop_top {Ann} {T} 
            {prop : forall TT:definition_function_types, 
                (DefinedFunction Ann TT) -> Prop}
            {df:DefinedFunction Ann T} :
     is_df_rec_prop prop df ->
     prop _ df.
   Proof.
     destruct df; simpl; tauto.
   Qed.
     
   Lemma df_eval_tree_correct {T Ann} (σ:df_env) (df:DefinedFunction Ann T) (dfann:DefinedFunction EvalAnn T):
     df_eval_tree σ df = Some dfann ->
     is_df_evalann_correct σ dfann.
   Proof.
     unfold is_df_evalann_correct, is_df_evalann_correct_top.
     revert dfann.
     DefinedFunction_cases (induction df) Case; simpl; intros dfann eqq
     ; try solve[case_eq (df_eval_tree σ df1)
       ; [intros adf1 a1eqq | intros a1eqq]
       ; rewrite a1eqq in eqq
       ; [| congruence]
       ; (case_eq (df_eval_tree σ df2)
       ; [intros adf2 a2eqq | intros a2eqq]
       ; rewrite a2eqq in eqq
       ; [| congruence]
       ; inversion eqq; simpl
       ; specialize (IHdf1 _ a1eqq)
       ; specialize (IHdf2 _ a2eqq)
       ; split; [| tauto]
       ; apply is_df_rec_prop_top in IHdf1
       ; apply is_df_rec_prop_top in IHdf2
       ; simpl in IHdf1, IHdf2
       ; rewrite IHdf1, IHdf2
       ; trivial)

                |
        case_eq (df_eval_tree σ df)
       ; [intros adf aeqq | intros aeqq]
       ; rewrite aeqq in eqq
       ; [| congruence]
       ; inversion eqq; simpl
       ; specialize (IHdf _ aeqq)
       ; split; [| tauto]
       ; apply is_df_rec_prop_top in IHdf
       ; simpl in IHdf
       ; rewrite IHdf
       ; trivial].
     - Case "Number"%string.
       inversion eqq; subst.
       simpl; tauto.
     - Case "Constant"%string.
       inversion eqq; subst. 
       simpl; tauto.
     - Case "DVector"%string.
       revert eqq.
       case_eq (vectoro_to_ovector (fun i : {n' : nat | (n' < n)%nat} => df_eval_tree σ (x i)))
       ; [| congruence].
       intros.
       inversion eqq; subst.
       simpl.
       split.
       revert H0.
       admit.
       admit.
     - Case "DMatrix"%string.
       admit.
     - Case "Var"%string.
       revert eqq.
       case_eq (vartlookup σ v) ; [| congruence].
       intros.
       inversion eqq; subst; simpl.
       rewrite H; tauto.
     - Case "VectorApply"%string.
       case_eq (df_eval_tree σ df2)
       ; [intros adf2 a2eqq | intros a2eqq]
       ; rewrite a2eqq in eqq 
       ; [| congruence].
       specialize (IHdf2 _ a2eqq).

       revert eqq.
       case_eq ( @vectoro_to_ovector (@float floatish_impl) n
              (fun i : @sig nat (fun n' : nat => lt n' n) =>
               @df_eval DTfloat UnitAnn
                 (@cons env_entry_type
                    (mk_env_entry (@pair SubVar definition_function_types v DTfloat)
                                  (@get_annotation EvalAnn (DTVector n) adf2 i)) σ) df1))
              ; [| congruence].
       intros.
       inversion eqq; subst.
       simpl.
       apply is_df_rec_prop_top in IHdf2.
       rewrite  IHdf2.
       split.
       
       admit.
       
       admit.

     - Case "MatrixApply"%string.
       admit.
     - Case "VLossfun"%string.
       admit.
     - Case "MLossfun"%string.
       admit.
   Admitted.
   
   (*
      Definition annotations_correct
     := is_df_rec_prop ()
              
    is_df_rec_prop {Ann} {T} 
            (prop : forall TT:definition_function_types, 
                (DefinedFunction Ann TT) -> Prop)
            (df:DefinedFunction Ann T) {struct df}: Prop
*)
   Lemma is_scalar_function_scalar {Ann} {T} (df:DefinedFunction Ann T) :
     is_scalar_function df -> is_scalar_df_type T.
   Proof.
     induction df; simpl; trivial.
   Qed.
   


   Definition definition_function_types_map_base (f:Type->Type) (dft:definition_function_types): Type
     := match dft with
        | DTfloat => f float
        | DTVector n => Vector (f float) n
        | DTMatrix m n => Matrix (f float) m n
        end.

   Definition definition_function_types_subgradient (dft:definition_function_types)
     := definition_function_types_map_base (fun t => list (list t)) dft.


    Definition df_eval_gradient {T} σ (df:DefinedFunction UnitAnn T) (lv:list var_type) : option (list (definition_function_types_interp T))
      := listo_to_olist (map (df_eval_deriv σ df) lv).
    
    Definition combine_prod (l1 l2 : list (list float)) : list (list (float * float))
     := let l12 := list_prod l1 l2
        in map (fun '(x,y) => combine x y) l12.
(*
   Fixpoint df_eval_subgradient {dft:definition_function_types} (σ:df_env) (df:DefinedFunction dft) (lv:list SubVar) : option (definition_function_types_subgradient dft)
    := (match df with
        | Number _ => Some ((map (fun _ => 0) lv) :: nil)
        | DVector n v => vectoro_to_ovector (vmap (fun x => df_eval_subgradient σ x lv) v)
        | DMatrix n m df => matrixo_to_omatrix (vmap (fun x => vmap (fun y => df_eval_subgradient σ y lv) x) df)
         | Var x => Some ((map (fun v => if x == v then 1 else 0) lv) :: nil)
         | Plus l r => 
           match df_eval_subgradient σ l lv, df_eval_subgradient σ r lv with
           | Some ld, Some rd => Some (map (map (fun '(x, y) => x+y)) (combine_prod ld rd))
           | _, _ => None
           end
         | Minus l r =>
           match df_eval_subgradient σ l lv, df_eval_subgradient σ r lv with
           | Some ld, Some rd => Some (map (map (fun '(x, y) => x-y)) (combine_prod ld rd))
           | _, _ => None
           end
         | Times l r =>
           match df_eval σ l, df_eval_subgradient σ l lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (map (map (fun '(lp,rp) => lp*re + le*rp)) (combine_prod ld rd))
           | _, _, _, _ => None
           end
         | Divide l r =>
           match df_eval σ l, df_eval_subgradient σ l lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (map (map (fun '(lp,rp) => (lp*re - le*rp)/(re * re))) (combine_prod ld rd))
           | _, _, _, _ => None
           end
         | Square e =>
           match df_eval σ e, df_eval_subgradient σ e lv with
           | Some ee, Some ed => Some (map (map (fun pd => 2 * ee * pd)) ed)
           | _, _  => None
           end
         | Exp e =>
           match df_eval σ e, df_eval_subgradient σ e lv with
           | Some ee, Some ed => Some (map (map (fun pd => pd * Fexp ee)) ed)
           | _, _  => None
           end
         | Log e =>
           match df_eval σ e, df_eval_subgradient σ e lv with
           | Some ee, Some ed => Some (map (map (fun pd => (pd / ee))) ed)
           | _, _ => None
           end
         | Abs e =>
           match df_eval σ e, df_eval_subgradient σ e lv with
           | Some ee, Some ed => 
              if Feq ee 0 then Some (ed ++ (map (map (fun ep => -ep)) ed))
              else Some (map (map (fun ed => (ed * (sign ee)))) ed)
           | _, _ => None
           end
         | Sign e =>
           match df_eval σ e with
           | Some ee => Some ((map (fun _ => 0) lv) :: nil )
           | _ => None
           end
         | PSign e =>
           match df_eval σ e with
           | Some ee => Some ((map (fun _ => 0) lv) :: nil )
           | _ => None
           end
         | Max l r =>
           match df_eval σ l, df_eval_subgradient σ l lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             if Feq le re then Some (ld ++ rd)
             else if le > re then Some ld
                  else Some rd
           | _, _, _, _ => None
           end
         | VectorElem n l i => 
           match (df_eval_subgradient σ l lv)  with
           | Some l' => Some (l' i)
           | _ => None
           end
         | MatrixElem m n l i j =>
           match (df_eval_subgradient σ l lv)  with
           | Some l' => Some (l' i j)
           | _ => None
           end
         | VectorSum n l => 
           match df_eval_subgradient σ l lv with
           | Some l' =>
             Some (vector_fold_right (fun a b => map (map (fun '(xp,rp) => xp + rp)) 
                                                     (combine_prod a b)) 
                                     ((map (fun _ => 0) lv)::nil) l')
           | _ => None
           end 
         | VectorDot n l r => 
           match df_eval σ l, df_eval_subgradient σ l lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (vector_fold_right (fun a b => map (map (fun '(xp,rp) => xp + rp)) 
                                                     (combine_prod a b)) 
                                     ((map (fun _ => 0) lv)::nil) 
                                     (fun i => map (map (fun '(lp,rp) => lp*(re i) + (le i)*rp)) 
                                                   (combine_prod (ld i) (rd i))))
           | _, _, _, _ => None
           end
         | VectorScalMult n x r =>
           match df_eval σ x, df_eval_subgradient σ x lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some xe, Some xd, Some re, Some rd => 
             Some (fun j => map (map (fun '(xp,rp) => xe * rp + xp * (re j))) (combine_prod xd (rd j)))
           | _, _, _, _ => None
           end
         | MatrixScalMult n m x r =>
           match df_eval σ x, df_eval_subgradient σ x lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some xe, Some xd, Some re, Some rd => 
             Some (fun i j => map (map (fun '(xp,rp) => xe * rp + xp * (re i j))) (combine_prod xd (rd i j)))

           | _, _, _, _ => None
           end
         | MatrixVectorMult n m l r => 
           match df_eval σ l, df_eval_subgradient σ l lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i => 
                     (vector_fold_right (fun a b => map (map (fun '(xp,rp) => xp + rp)) 
                                                        (combine_prod a b)) 
                                        ((map (fun _ => 0) lv)::nil) 
                                        (fun j => map (map (fun '(lp,rp) => lp*(re j) + (le i j)*rp)) 
                                                      (combine_prod (ld i j) (rd j)))))
           | _, _, _, _ => None
           end
         | MatrixMult n m p l r =>
           match df_eval σ l, df_eval_subgradient σ l lv, df_eval σ r, df_eval_subgradient σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i k => 
                     (vector_fold_right (fun a b => map (map (fun '(xp,rp) => xp + rp)) 
                                                        (combine_prod a b)) 
                                        ((map (fun _ => 0) lv)::nil) 
                                        (fun j => map (map (fun '(lp,rp) => lp*(re j k) + (le i j)*rp)) 
                                                      (combine_prod (ld i j) (rd j k)))))
           | _, _, _, _ => None
           end
         | VectorPlus n l r =>
           match df_eval_subgradient σ l lv, df_eval_subgradient σ r lv with           
           | Some ld, Some rd => Some (fun i => (map (map (fun '(x, y) => x+y)) (combine_prod (ld i) (rd i))))
           | _, _ => None
           end
         | VectorMinus n l r =>
           match df_eval_subgradient σ l lv, df_eval_subgradient σ r lv with           
           | Some ld, Some rd => Some (fun i => (map (map (fun '(x, y) => x-y)) (combine_prod (ld i) (rd i))))
           | _, _ => None
           end
         | MatrixPlus n m l r =>
           match df_eval_subgradient σ l lv, df_eval_subgradient σ r lv with           
           | Some ld, Some rd => Some (fun i j => (map (map (fun '(x, y) => x+y)) (combine_prod (ld i j) (rd i j))))
           | _, _ => None
           end
         | MatrixMinus n m l r =>
           match df_eval_subgradient σ l lv, df_eval_subgradient σ r lv with           
           | Some ld, Some rd => Some (fun i j => (map (map (fun '(x, y) => x-y)) (combine_prod (ld i j) (rd i j))))
           | _, _ => None
           end
         | VectorApply n x s r => 
           match df_eval σ r, df_eval_subgradient σ r lv with                      
           | Some re, Some rd => 
             vectoro_to_ovector 
               (fun i => match df_eval_subgradient (cons (x, re i) σ) s lv with
                         | Some sd => 
                           Some (map (map (fun '(x, y) => x*y)) (combine_prod (rd i) sd))
                         | _ => None
                         end)
           | _, _ => None                                                    
           end
         | Lossfun n v1 v2 s l r => 
           match df_eval σ l, df_eval_subgradient σ l lv with                      
           | Some le, Some ld => 
             match (vectoro_to_ovector 
                      (fun i => match df_eval_subgradient (cons (v1, (le i)) (cons (v2, r i) σ)) s lv with
                         | Some sd => Some (map (map (fun '(x, y) => x*y)) (combine_prod (ld i) sd))
                         | _ => None
                         end)) with
             | Some vv => Some (vector_fold_right (fun a b => map (map (fun '(xp,rp) => xp + rp)) 
                                                     (combine_prod a b)) 
                                     ((map (fun _ => 0) lv)::nil) vv)
             | _ => None
             end
           | _, _ => None
           end
          end).
*)
   End deriv2.
   
   Definition dft_one (dft:definition_function_types) : definition_function_types_interp dft
     := match dft with
        | DTfloat => 1
        | DTVector n => fun _ => 1
        | DTMatrix m n => fun _ _ => 1
        end.

   Section scalar_ind.
     
   Fixpoint is_scalar_function_ind_gen {Ann}
             {P:forall {T}, DefinedFunction Ann T->Prop}
             (fnumber:forall ann x, P (Number ann x))
             (fconstant:forall (ann:Ann DTfloat) x, P (@Constant _ DTfloat ann x))
             (fvar:forall sv ann, P (@Var _ (sv,DTfloat) ann))
             (fplus:forall a l r, P l -> P r -> P (Plus a l r))
             (fminus:forall a l r, P l -> P r -> P (Minus a l r))
             (ftimes:forall a l r, P l -> P r -> P (Times a l r))
             (fdivide:forall a l r, P l -> P r -> P (Divide a l r))
             (fsquare:forall a e, P e -> P (Square a e))
             (fexp:forall a e, P e -> P (Exp a e))
             (flog:forall a e, P e -> P (Log a e))
             (fabs:forall a e, P e -> P (Abs a e))
             (fsign:forall a e, P e -> P (Sign a e))
             (fpsign:forall a e, P e -> P (PSign a e))
             (fmax:forall a l r, P l -> P r -> P (Max a l r))
             {T}
            (df:DefinedFunction Ann T) {struct df} : is_scalar_function df -> P df.
   Proof.
     induction df; simpl; intros isc; try tauto.
     - apply fnumber.
     - destruct t; simpl in isc; try tauto.
       apply fconstant.
     - destruct v.
       destruct d; simpl in isc; try tauto.
       apply fvar.
     - apply fplus.
       + apply IHdf1; tauto.
       + apply IHdf2; tauto.
     - apply fminus.
       + apply IHdf1; tauto.
       + apply IHdf2; tauto.
     - apply ftimes.
       + apply IHdf1; tauto.
       + apply IHdf2; tauto.
     - apply fdivide.
       + apply IHdf1; tauto.
       + apply IHdf2; tauto.
     - apply fsquare.
       + apply IHdf; tauto.
     - apply fexp.
       + apply IHdf; tauto.
     - apply flog.
       + apply IHdf; tauto.
     - apply fabs.
       + apply IHdf; tauto.
     - apply fsign.
       + apply IHdf; tauto.
     - apply fpsign.
       + apply IHdf; tauto.
     - apply fmax.
       + apply IHdf1; tauto.
       + apply IHdf2; tauto.
   Qed.

   Definition is_scalar_function_ind {Ann}
             {P:DefinedFunction Ann DTfloat->Prop}
             (fnumber:forall ann x, P (Number ann x))
             (fconstant:forall (ann:Ann DTfloat) x, P (@Constant _ DTfloat ann x))
             (fvar:forall sv ann, P (@Var _ (sv,DTfloat) ann))
             (fplus:forall a l r, P l -> P r -> P (Plus a l r))
             (fminus:forall a l r, P l -> P r -> P (Minus a l r))
             (ftimes:forall a l r, P l -> P r -> P (Times a l r))
             (fdivide:forall a l r, P l -> P r -> P (Divide a l r))
             (fsquare:forall a e, P e -> P (Square a e))
             (fexp:forall a e, P e -> P (Exp a e))
             (flog:forall a e, P e -> P (Log a e))
             (fabs:forall a e, P e -> P (Abs a e))
             (fsign:forall a e, P e -> P (Sign a e))
             (fpsign:forall a e, P e -> P (PSign a e))
             (fmax:forall a l r, P l -> P r -> P (Max a l r))
             (df:DefinedFunction Ann DTfloat) : is_scalar_function df -> P df.
   Proof.
     apply (@is_scalar_function_ind_gen _ (fun t => match t with
                                                        | DTfloat => fun df => P df
                                                        | _ => fun _ => False
                                                    end)); trivial.
   Qed.

   Definition vartlookup_eq (l1 l2:df_env) : Prop := forall a, vartlookup l1 a = vartlookup l2 a.

   Global Instance vartlookup_eq_equiv : Equivalence vartlookup_eq.
   Proof.
     unfold vartlookup_eq.
     constructor; red.
     - intros; reflexivity.
     - intros; eauto.
     - intro; etransitivity; eauto.
   Qed.

   End scalar_ind.
   (*
   Lemma vart_update_lookup_ext (l1 l2:df_env) (a:var_type) (n:definition_function_types_interp (snd a)) : vartlookup_eq l1 l2 -> vart_update l1 a n = vart_update l2 a n.
   Proof.
   Admitted.
    *)

   Lemma lookup_update (xv : var_type) (gradenv : df_env) 
         (val : definition_function_types_interp (snd xv)) :
     vartlookup (vart_update gradenv xv val) xv = Some val.
   Proof.
     induction gradenv; simpl.
     - destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
       rewrite (var_type_UIP_refl e); simpl.
       reflexivity.
     - destruct a; simpl.
       case_eq (@equiv_dec var_type _ _ _ xv x); simpl; intros.
       + destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
         rewrite (var_type_UIP_refl e0); simpl.
         reflexivity.
       + rewrite H; trivial.
   Qed.

   Lemma lookup_update_neq (xv1 xv2 : var_type) (gradenv : df_env) 
         (val : definition_function_types_interp (snd xv1)) : xv1 <> xv2 ->
     vartlookup (vart_update gradenv xv1 val) xv2 = vartlookup gradenv xv2.
   Proof.
     intros neq.
     induction gradenv; simpl.
     - destruct (@equiv_dec var_type _ _ _ xv2 xv1); congruence.
     - destruct a; simpl.
       case_eq (@equiv_dec var_type _ _ _ xv1 x); simpl; intros.
       + destruct (@equiv_dec var_type _ _ _ xv2 xv1); [congruence | ].
         destruct (@equiv_dec var_type _ _ _ xv2 x); congruence.
       + destruct (@equiv_dec var_type _ _ _ xv2 x); congruence.
   Qed.

   Lemma lookup_update2 (xv : var_type) (gradenv : df_env) 
         (val : definition_function_types_interp (snd xv)) :
     vartlookup ((mk_env_entry xv val) :: gradenv) xv = Some val.
   Proof.
     induction gradenv; simpl.
     - destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
       rewrite (var_type_UIP_refl e); simpl.
       reflexivity.
     - destruct a; simpl.
       case_eq (@equiv_dec var_type _ _ _ xv x); simpl; intros.
       + destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
         rewrite (var_type_UIP_refl e0); simpl.
         reflexivity.
       + destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
         now rewrite (var_type_UIP_refl e); simpl.         
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

   Lemma scalar_df_eval_backprop_deriv_preserves_lookup_not_none {Ann} {env} {df:DefinedFunction Ann DTfloat} {gradenv grad d}:
     is_scalar_function df ->
     df_eval_backprop_deriv env df gradenv grad = Some d ->
     forall xv,
     vartlookup gradenv xv <> None ->
     vartlookup d xv <> None.
   Proof.
     simpl.
     intros is_scalar.
     revert grad gradenv d.
     pattern df.
     revert df is_scalar.
     DefinedFunction_scalar_cases (apply is_scalar_function_ind) Case; simpl.
     - Case "Number"%string; intros.
       inversion H; subst; trivial.
     - Case "Constant"%string; intros.
       inversion H; subst; trivial.
     - Case "Var"%string; intros.
       destruct (vartlookup gradenv (sv, DTfloat)).
       intros.
       inversion H.
       assert (((sv, DTfloat) = xv) \/ ((sv, DTfloat) <> xv)).
       apply Classical_Prop.classic.
       destruct H1; subst.
       rewrite lookup_update.
       discriminate.
       rewrite lookup_update_neq; trivial.
       inversion H; subst; trivial.
     - Case "Plus"%string.
       intros an l r Hl Hr grad gradenv d.
       case_eq (df_eval_backprop_deriv env l gradenv grad) ; [|congruence].
       intros d0.
       specialize (Hl grad gradenv d0).
       specialize (Hr grad d0 d).
       intros.
       apply Hr; trivial.
       apply Hl; trivial.
     - Case "Minus"%string.
       intros an l r Hl Hr grad gradenv d.
       case_eq (df_eval_backprop_deriv env l gradenv grad) ; [|congruence].
       intros d0.
       specialize (Hl grad gradenv d0).
       specialize (Hr (-grad) d0 d).       
       intros.
       apply Hr; trivial.
       apply Hl; trivial.
     - Case "Times"%string.
       intros an l r Hl Hr grad gradenv d.
       destruct (df_eval env l); [|congruence].
       destruct (df_eval env r); [|congruence].              
       case_eq (df_eval_backprop_deriv env l gradenv (d1 * grad)) ; [|congruence].       
       intros d2.
       specialize (Hl (d1 * grad) gradenv d2).
       specialize (Hr (d0 * grad) d2 d).       
       intros.
       apply Hr; trivial.
       apply Hl; trivial.
     - Case "Divide"%string.
       intros an l r Hl Hr grad gradenv d.       
       destruct (df_eval env l); [|congruence].
       destruct (df_eval env r); [|congruence].              
       case_eq (df_eval_backprop_deriv env l gradenv (grad / d1)) ; [|congruence].
       intros d2.
       specialize (Hl (grad / d1) gradenv d2).
       specialize (Hr ( - d0 / (d1 * d1) * grad) d2 d).       
       intros.
       apply Hr; trivial.
       apply Hl; trivial.
     - Case "Square"%string; intros.
       destruct (df_eval env e); [|congruence].
       specialize (H (2 * d0 * grad) gradenv).
       now apply H.
     - Case "Exp"%string; intros.  
       destruct (df_eval env e); [|congruence].
       specialize (H (grad * Fexp d0) gradenv).
       now apply H.
     - Case "Log"%string; intros.
       destruct (df_eval env e); [|congruence].
       specialize (H (grad / d0) gradenv).
       now apply H.
     - Case "Abs"%string; intros.
       destruct (df_eval env e); [|congruence].
       specialize (H (grad * sign d0) gradenv).
       now apply H.
     - Case "Sign"%string; intros.
       specialize (H 0 gradenv).
       now apply H.
     - Case "PSign"%string; intros.
       specialize (H 0 gradenv).
       now apply H.
     - Case "Max"%string.
       intros an l r Hl Hr grad gradenv d.              
       destruct (df_eval env l); [|congruence].
       destruct (df_eval env r); [|congruence].              
       destruct (d0 <= d1).
       specialize (Hr grad gradenv d).
       apply Hr.
       specialize (Hl grad gradenv d).
       apply Hl.
Qed.


   Lemma df_eval_backprop_deriv_preserves_lookup_not_none {Ann T} {env} {grad gradenv d} {df:DefinedFunction Ann T} :
     df_eval_backprop_deriv env df gradenv grad = Some d ->
     forall xv,
     vartlookup gradenv xv <> None ->
     vartlookup d xv <> None.
   Proof.
     simpl.
     revert grad gradenv d.
     DefinedFunction_cases (induction df) Case; simpl.
     - Case "Number"%string; intros; inversion H; subst; easy.
     - Case "Constant"%string; intros; inversion H; subst; easy.
     - Case "DVector"%string.
       intros grad.
       unfold two_vector_env_iter_alt.
       induction (bounded_seq0 n).
       simpl.
       intros.
       inversion H0; subst; trivial.
       simpl.
       intros gradenv d.
       case_eq (df_eval_backprop_deriv env (x a) gradenv (grad a)).
       intros.
       specialize (H a (grad a) gradenv d0).
       specialize (IHl d0 d).
       apply IHl; trivial.
       apply H; trivial.
       intros.
       assert (list_env_iter
         (fun (i : {n' : nat | (n' < n)%nat}) (env0 : df_env) =>
          df_eval_backprop_deriv env (x i) env0 (grad i)) None l = None) 
         by apply list_env_iter_none.
       intros; rewrite H1 in H3; discriminate.
     - Case "DMatrix"%string.
       intros grad.
       unfold two_matrix_env_iter_alt.
       induction (bounded_seq0 n).
       simpl.
       intros.
       inversion H0; subst; trivial.
       simpl.
       intro gradenv.

       admit.
     - Case "Var"%string.
       intros.
       destruct (vartlookup gradenv v)  ; [|congruence].
       intros.
       inversion H.
       assert ((v = xv) \/ (v <> xv)).
       apply Classical_Prop.classic.
       destruct H1; subst.
       rewrite lookup_update.
       discriminate.
       rewrite lookup_update_neq; trivial.
     - Case "Plus"%string.
       intros grad gradenv.
       case_eq (df_eval_backprop_deriv env df1 gradenv grad) ; [|congruence].
       intros.
       specialize (IHdf1 grad gradenv d).
       specialize (IHdf2 grad d d0).
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "Minus"%string.
       intros grad gradenv.
       case_eq (df_eval_backprop_deriv env df1 gradenv grad) ; [|congruence].
       intros.
       specialize (IHdf1 grad gradenv d).
       specialize (IHdf2 (-grad) d d0).
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "Times"%string.
       intros grad gradenv d.
       destruct (df_eval env df1)  ; [|congruence].
       destruct (df_eval env df2)  ; [|congruence].
       case_eq (df_eval_backprop_deriv env df1 gradenv (d1 * grad)) ; [|congruence].
       intros d2.
       specialize (IHdf1 (d1 * grad) gradenv d2).
       specialize (IHdf2 (d0 * grad) d2 d).       
       intros.
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "Divide"%string.
       intros grad gradenv d.
       destruct (df_eval env df1)  ; [|congruence].
       destruct (df_eval env df2)  ; [|congruence].
       case_eq (df_eval_backprop_deriv env df1 gradenv (grad / d1)) ; [|congruence].
       intros d2.
       specialize (IHdf1 (grad / d1) gradenv d2).
       specialize (IHdf2 (- d0 / (d1 * d1) * grad) d2 d).       
       intros.
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "Square"%string; intros.
       destruct (df_eval env df) ; [|congruence]. 
       specialize (IHdf (2 * d0 * grad) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "Exp"%string; intros.
       destruct (df_eval env df) ; [|congruence]. 
       specialize (IHdf (grad * Fexp d0) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "Log"%string; intros.
       destruct (df_eval env df) ; [|congruence]. 
       specialize (IHdf (grad / d0) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "Abs"%string; intros.
       destruct (df_eval env df) ; [|congruence]. 
       specialize (IHdf (grad * sign d0) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "Sign"%string; intros.
       specialize (IHdf 0 gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "PSign"%string; intros.
       specialize (IHdf 0 gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "Max"%string; intros.
       destruct (df_eval env df1) ; [|congruence]. 
       destruct (df_eval env df2) ; [|congruence]. 
       destruct (d0 <= d1).
       specialize (IHdf2 grad gradenv d).
       apply IHdf2.
       apply H.
       trivial.
       specialize (IHdf1 grad gradenv d).
       apply IHdf1.
       apply H.
       trivial.
     - Case "VectorDot"%string.
       intros grad gradenv d.
       destruct (df_eval env df1) ; [|congruence]. 
       destruct (df_eval env df2)  ; [|congruence]. 
       case_eq (df_eval_backprop_deriv env df1 gradenv 
                     (vmap (fun rv : float => rv * grad) d1));  [|congruence]. 
       intros.
       specialize (IHdf1 (vmap (fun rv : float => rv * grad) d1) gradenv d2).
       specialize (IHdf2 (vmap (fun lv : float => lv * grad) d0) d2 d).
       apply IHdf2.
       apply H0.
       apply IHdf1.
       apply H.
       apply H1.
     - Case "VectorSum"%string.
       intros.
       specialize (IHdf (ConstVector n grad) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "MatrixSum"%string.
       intros.
       specialize (IHdf (ConstMatrix m n grad) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "VectorElem"%string.
       intros.
       specialize (IHdf (fun k : {n' : nat | (n' < n)%nat} =>
                           if equiv_dec (proj1_sig k) (proj1_sig i) 
                           then grad else 0) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "MatrixElem"%string.
       intros.
       specialize (IHdf (fun (k1 : {n' : nat | (n' < m)%nat}) 
                             (k2 : {m' : nat | (m' < n)%nat}) =>
                           if equiv_dec (proj1_sig k1) (proj1_sig i)
                           then if equiv_dec (proj1_sig k2) (proj1_sig j) then grad else 0
                           else 0) gradenv d).
       apply IHdf.
       apply H.
       apply H0.
     - Case "MatrixVectorMult"%string.
       intros grad gradenv d.
       destruct (df_eval env df1)  ; [|congruence].
       destruct (df_eval env df2)  ; [|congruence].
       case_eq (df_eval_backprop_deriv env df1 gradenv 
                    (fun (i : {n' : nat | (n' < m)%nat}) 
                         (j : {m' : nat | (m' < n)%nat}) => grad i * d1 j)) ; [|congruence].
       intros d2.
       specialize (IHdf1 (fun (i : {n' : nat | (n' < m)%nat}) 
                              (j : {m' : nat | (m' < n)%nat}) => grad i * d1 j) gradenv d2).
       specialize (IHdf2 (matrix_vector_mult
                            (fun (i : {n' : nat | (n' < n)%nat}) 
                                 (j : {m' : nat | (m' < m)%nat}) => d0 j i) grad) d2 d).
       intros.
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "MatrixVectorAdd"%string.
       intros grad gradenv d.
       case_eq (df_eval_backprop_deriv env df1 gradenv grad); [|congruence].
       intros d0 casedf1.
       specialize (IHdf1 _ _ _ casedf1).
       clear casedf1.
       revert gradenv d d0 IHdf1.
       induction (bounded_seq0 n).
       + simpl.
         intros.
         inversion H; subst.
         eauto.
       + intros gradenv d d0 d0eqq.
         simpl.
         case_eq (df_eval_backprop_deriv env df2 d0 (transpose grad a)); simpl
         ; [intros ? eqq1 | intros eqq1].
         * intros.
           { apply (IHl d0 _ d1); trivial.
             - eapply IHdf2; eauto.
             - eauto.
           } 
         * destruct l; simpl; discriminate.
     - Case "MatrixMult"%string.
       intros grad gradenv d.
       destruct (df_eval env df1)  ; [|congruence].
       destruct (df_eval env df2)  ; [|congruence].
       case_eq (df_eval_backprop_deriv env df1 gradenv 
                    (matrix_mult grad
                                 (fun (i : {n' : nat | (n' < n)%nat}) 
                                      (j : {m' : nat | (m' < p)%nat}) => d1 j i)))
                ; [|congruence].
       intros d2.
       specialize (IHdf1 (matrix_mult grad
                                      (fun (i : {n' : nat | (n' < n)%nat}) 
                                           (j : {m' : nat | (m' < p)%nat}) => d1 j i))
                         gradenv d2).
       specialize (IHdf2 (matrix_mult
                            (fun (i : {n' : nat | (n' < p)%nat}) 
                                 (j : {m' : nat | (m' < m)%nat}) => d0 j i) grad) d2 d).
       intros.
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "VectorPlus"%string.
       intros grad gradenv d.
       case_eq (df_eval_backprop_deriv env df1 gradenv grad) ; [|congruence].
       intros.
       specialize (IHdf1 grad gradenv d0).
       specialize (IHdf2 grad d0 d).
       apply IHdf2.
       apply H0.
       apply IHdf1.
       apply H.
       apply H1.
     - Case "VectorMinus"%string.
       intros grad gradenv d.
       case_eq (df_eval_backprop_deriv env df1 gradenv grad) ; [|congruence].
       intros.
       specialize (IHdf1 grad gradenv d0).
       specialize (IHdf2 (fun i : {n' : nat | (n' < n)%nat} => - grad i) d0 d).
       apply IHdf2.
       apply H0.
       apply IHdf1.
       apply H.
       apply H1.
     - Case "MatrixPlus"%string.
       intros grad gradenv d.
       case_eq (df_eval_backprop_deriv env df1 gradenv grad) ; [|congruence].
       intros.
       specialize (IHdf1 grad gradenv d0).
       specialize (IHdf2 grad d0 d).
       apply IHdf2.
       apply H0.
       apply IHdf1.
       apply H.
       apply H1.
     - Case "MatrixMinus"%string.
       intros grad gradenv d.
       case_eq (df_eval_backprop_deriv env df1 gradenv grad) ; [|congruence].
       intros.
       specialize (IHdf1 grad gradenv d0).
       specialize (IHdf2 (fun (i : {n' : nat | (n' < n)%nat}) 
                              (j : {m' : nat | (m' < m)%nat}) => - grad i j)
                         d0 d).
       apply IHdf2.
       apply H0.
       apply IHdf1.
       apply H.
       apply H1.
     - Case "VectorScalMult"%string.
       intros grad gradenv d.
       destruct (df_eval env df1)  ; [|congruence].
       destruct (df_eval env df2)  ; [|congruence].
       case_eq (df_eval_backprop_deriv env df1 gradenv
                          (vsum (fun j : {n' : nat | (n' < n)%nat} => d1 j * grad j)))
                ; [|congruence].
       intros d2.
       specialize (IHdf1 (vsum (fun j : {n' : nat | (n' < n)%nat} => d1 j * grad j))
                         gradenv d2).
       specialize (IHdf2 (fun j : {n' : nat | (n' < n)%nat} => d0 * grad j)
                         d2 d).
       intros.
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "MatrixScalMult"%string.
       intros grad gradenv d.
       destruct (df_eval env df1)  ; [|congruence].
       destruct (df_eval env df2)  ; [|congruence].
       case_eq (df_eval_backprop_deriv env df1 gradenv
                   (msum
                      (fun (i : {n' : nat | (n' < n)%nat}) 
                           (j : {m' : nat | (m' < m)%nat}) =>
                         d1 i j * grad i j)))
                ; [|congruence].
       intros d2.
       specialize (IHdf1 (msum
                            (fun (i : {n' : nat | (n' < n)%nat}) 
                                 (j : {m' : nat | (m' < m)%nat}) =>
                               d1 i j * grad i j))
                  gradenv d2).
       specialize (IHdf2 (fun (i : {n' : nat | (n' < n)%nat}) 
                              (j : {m' : nat | (m' < m)%nat}) => grad i j * d0)
                         d2 d).
       intros.
       apply IHdf2; trivial.
       apply IHdf1; trivial.
     - Case "VectorApply"%string.
       intros grad gradenv d.
       destruct (df_eval env df2)  ; [|congruence].
       admit.
     - Case "MatrixApply"%string.
       intros grad gradenv d.
       destruct (df_eval env df2)  ; [|congruence].
       admit.
     - Case "VLossfun"%string.
       intros grad gradenv d.
       destruct (df_eval env df2)  ; [|congruence].
       admit.
     - Case "MLossfun"%string.
       intros grad gradenv d.
       destruct (df_eval env df2)  ; [|congruence].
       admit.

   Admitted.

   Lemma df_eval_tree_backprop_deriv_preserves_lookup_not_none {T} {env} {df:DefinedFunction EvalAnn T} {gradenv grad d} :
     df_eval_tree_backprop_deriv env df gradenv grad = Some d ->
     forall xv,
     vartlookup gradenv xv <> None ->
     vartlookup d xv <> None.
   Proof.

   Admitted.

    Section deriv_deriv.

(*
      Theorem df_eval_deriv_same (σ:df_env) (df:DefinedFunction) (v:SubVar) :
        df_eval_deriv σ df v = df_eval σ (df_deriv df v).
      Proof.
        DefinedFunction_cases (induction df) Case; simpl; trivial
        ; try rewrite <- IHdf1, <- IHdf2; trivial
        ; try rewrite <- IHdf; trivial 
        ; try solve [ destruct (df_eval σ df1); trivial
                      ; destruct (df_eval_deriv σ df1 v); trivial
                      ; destruct (df_eval_deriv σ df2 v); trivial
                      ; destruct (df_eval σ df2); trivial
                    |  destruct (df_eval σ df); trivial
                       ; destruct (df_eval_deriv σ df v); trivial].
        - Case "Var"%string.
          destruct (equiv_dec v0 v); simpl; trivial.
        - case_eq (df_eval σ df1); trivial
          ; case_eq (df_eval_deriv σ df1 v); trivial
          ; case_eq (df_eval_deriv σ df2 v); trivial
          ; case_eq (df_eval σ df2); trivial.
          intros.
          destruct (Rle_dec r2 r); simpl.
          + f_equal.
            unfold sign.
            destruct (Rlt_dec (r2-r) 0); try lra.
            destruct (Rgt_dec (r2-r) 0); try lra.
            unfold pos_sign.
            destruct (Rge_dec (r-r2) 0); try lra.
            unfold pos_sign.
            destruct (Rge_dec (r-r2) 0); try lra.

          + unfold pos_sign.
            destruct (Rge_dec (r- r2) 0); try lra.
            destruct (Rgt_dec (r2-r) 0); try lra.
            f_equal.
            lra.
      Qed.
*)
      End deriv_deriv.
        
  Section max_derived.
    Definition MaxDerived (a b : DefinedFunction UnitAnn  DTfloat) :=
      Divide tt (Plus tt (Plus tt (Abs tt (Minus tt b a)) b) a) (Number tt 2).

    Delimit Scope df_scope with df.
    
    Notation "x + y" := (Plus x y) (only printing) : df_scope.
    Notation "x - y" := (Minus x y) (only printing) : df_scope.
    Notation "x / y" := (Divide x y) (only printing) : df_scope.
    Notation "x * y" := (Times x y) (only printing) : df_scope.
    Notation "x" := (Number x) (only printing, at level 0) : df_scope.
    Notation "x" := (Var x) (only printing, at level 0) : df_scope.
    Notation "'|' x '|'" := (Abs x) (only printing, at level 0) : df_scope.
    
  End max_derived.

  Section fv.

    Fixpoint df_free_variables {Ann} {T} (f : DefinedFunction Ann T) : list SubVar
      := match f with
         | Number _ x => nil
         | DVector n _ x => vlconcat_map df_free_variables x
         | Constant t _ x => nil
         | DMatrix n m _ x => vlconcat_map (fun a => vlconcat_map df_free_variables a) x
         | Var v _ => (fst v)::nil
         | Plus _ l r => (df_free_variables l) ++ (df_free_variables r)
         | Minus _ l r => (df_free_variables l) ++ (df_free_variables r)
         | Times _ l r => (df_free_variables l) ++ (df_free_variables r)
         | Divide _ l r => (df_free_variables l) ++ (df_free_variables r)
         | Max _ l r => (df_free_variables l) ++ (df_free_variables r)
         | Abs _ e => df_free_variables e
         | Sign _ e => df_free_variables e
         | PSign _ e => df_free_variables e
         | Log _ e => df_free_variables e
         | Square _ e => df_free_variables e
         | Exp _ e => df_free_variables e
         | VectorElem n _ l i => df_free_variables l
         | MatrixElem m n _ l i j => df_free_variables l
         | VectorDot n _ l r => (df_free_variables l) ++ (df_free_variables r)
         | VectorSum n _ l => df_free_variables l
         | MatrixSum n m _ l => df_free_variables l
         | VectorScalMult n _ x r => (df_free_variables x) ++ (df_free_variables r)
         | MatrixScalMult n m _ x r => (df_free_variables x) ++ (df_free_variables r)
         | MatrixVectorMult n m _ l r => (df_free_variables l) ++ (df_free_variables r)
         | MatrixVectorAdd n m _ l r => (df_free_variables l) ++ (df_free_variables r)
         | MatrixMult n m p _ l r => (df_free_variables l) ++ (df_free_variables r)
         | VectorPlus n _ l r => (df_free_variables l) ++ (df_free_variables r)
         | VectorMinus n _ l r => (df_free_variables l) ++ (df_free_variables r)
         | MatrixPlus n m _ l r => (df_free_variables l) ++ (df_free_variables r)
         | MatrixMinus n m _ l r => (df_free_variables l) ++ (df_free_variables r)
         | VectorApply n _ x s l => (df_free_variables s) ++ (df_free_variables l)
         | MatrixApply n m _ x s l => (df_free_variables s) ++ (df_free_variables l)
         | VLossfun n _ v1 v2 s l r => (df_free_variables s) ++ (df_free_variables l)
         | MLossfun n m _ v1 v2 s l r => (df_free_variables s) ++ (df_free_variables l)
         end.

    Definition df_closed {Ann} {T} (f: DefinedFunction Ann T) : Prop
      := match df_free_variables f with
         | nil => True
         | _ => False
         end.

    Lemma df_closed_nil {T} (f: DefinedFunction UnitAnn T) : df_closed f -> df_free_variables f = nil.
    Proof.
      unfold df_closed.
      destruct (df_free_variables f); tauto.
    Qed.

(*
    Require Import FunctionalExtensionality.
*)
(*
    Lemma df_subst_nfree {T} (e: DefinedFunction T) (v:SubVar) (e':DefinedFunction DTfloat) :
      ~ In v (df_free_variables e) ->
      df_subst e v e' = e.
    Proof.
      DefinedFunction_cases (induction e) Case; simpl; trivial; intros nin
      ; try solve [try rewrite in_app_iff in nin
                   ; intuition congruence].
      - Case "DVector"%string.
        f_equal.
        apply functional_extensionality.
        intros x0.
        apply H.
        intros inn.
        apply nin.
        unfold vlconcat_map, vlconcat.
        apply concat_In.
        exists ((df_free_variables (x x0))).
        split; trivial.
        apply vector_to_list_In.
        
      - Case "DMatrix"%string.

      - Case "Var"%string.
        destruct (var_dec v0 v); intuition.
    Qed.

    Lemma df_eval_complete' {T} (σ:df_env) (f:DefinedFunction T) :
      incl (df_free_variables f) (domain σ) -> {v | df_eval σ f = Some v}.
    Proof.
      induction f; simpl; intros inc
      ;  try solve [rewrite <- incl_app_iff in inc
                    ; intuition
                    ; destruct X as [v1 ev1]
                    ; destruct X0 as [v2 ev2]
                    ; rewrite ev1; rewrite ev2
                    ; eauto
                   | intuition
                     ; destruct X as [v1 ev1]
                     ; rewrite ev1
                     ; eauto].
      - eauto.
      - apply in_dom_lookup_strong.
        specialize (inc v); simpl in *.
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
      destruct (incl_dec (df_free_variables f) (domain σ)).
      - destruct (df_eval_complete _ _ i); congruence.
      - apply (nincl_exists) in n; trivial.
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
      lookup_equiv_on (df_free_variables f) σ₁ σ₂ ->
      df_eval σ₁ f = df_eval σ₂ f.
    Proof.
      intros lookeq.
      induction f; simpl in *; trivial
      ;  try solve [apply lookup_equiv_on_dom_app in lookeq; intuition
                    ; rewrite H1, H2; trivial
                   | rewrite IHf; trivial].
      - apply lookeq; simpl; tauto.
    Qed.
*)
  End fv.

  Section apply.

    Fixpoint df_apply {T} (e: DefinedFunction UnitAnn T) 
             (args: forall (v:var_type),  DefinedFunction UnitAnn (snd v)) : DefinedFunction UnitAnn T :=
      match e with
      | Number _ x => Number tt x
      | Constant t _ x => Constant tt x 
      | DVector n _ df => DVector tt (fun x => df_apply (df x) args)
      | DMatrix n m _ df => DMatrix tt (fun i j => df_apply (df i j) args)
      | Var v _ => args v
      | Plus _ l r => Plus tt (df_apply l args) (df_apply r args)
      | Times _ l r => Times tt (df_apply l args) (df_apply r args)
      | Minus _ l r => Minus tt (df_apply l args) (df_apply r args)
      | Divide _ l r => Divide tt (df_apply l args) (df_apply r args)
      | Square _ e => Square tt (df_apply e args)
      | Exp _ e => Exp tt (df_apply e args)
      | Log _ e => Log tt (df_apply e args)
      | Abs _ e => Abs tt (df_apply e args)
      | Sign _ e => Sign tt (df_apply e args)
      | PSign _ e => PSign tt (df_apply e args)
      | Max _ l r => Max tt (df_apply l args) (df_apply r args)
      | VectorElem n _ l i => VectorElem tt (df_apply l args) i
      | MatrixElem m n _ l i j => MatrixElem tt (df_apply l args) i j
      | VectorDot n _ l r => VectorDot tt (df_apply l args) (df_apply r args)
      | VectorSum n _ l => VectorSum tt (df_apply l args)
      | MatrixSum n m _ l => MatrixSum tt (df_apply l args)                                     
      | VectorScalMult n _ x r => VectorScalMult tt (df_apply x args) (df_apply r args)
      | MatrixScalMult n m _ x r => MatrixScalMult tt (df_apply x args) (df_apply r args)
      | MatrixVectorMult n m _ l r => MatrixVectorMult tt (df_apply l args) (df_apply r args)
      | MatrixVectorAdd n m _ l r => MatrixVectorAdd tt (df_apply l args) (df_apply r args)
      | MatrixMult n m p _ l r => MatrixMult tt (df_apply l args) (df_apply r args)
      | VectorPlus n _ l r => VectorPlus tt (df_apply l args) (df_apply r args)
      | VectorMinus n _ l r => VectorMinus tt (df_apply l args) (df_apply r args)
      | MatrixPlus n m _ l r => MatrixPlus tt (df_apply l args) (df_apply r args)
      | MatrixMinus n m _ l r => MatrixMinus tt (df_apply l args) (df_apply r args)
      | VectorApply n _ x s l => VectorApply tt x (df_apply s args) (df_apply l args)
      | MatrixApply n m _ x s l => MatrixApply tt x (df_apply s args) (df_apply l args)
      | VLossfun n _ v1 v2 s l r => VLossfun tt v1 v2 (df_apply s args) (df_apply l args) r
      | MLossfun n m _ v1 v2 s l r => MLossfun tt v1 v2 (df_apply s args) (df_apply l args) r
      end.

 End apply.

End DefinedFunctions.

Section real_pfs.

  Local Existing Instance floatish_R.
  Import Reals.
  Import List.
  
  Lemma MaxDerivedMax_eq (a b : DefinedFunction UnitAnn DTfloat) :
    forall σ, df_eval σ (Max tt a b) = df_eval σ (MaxDerived a b).
  Proof.
    simpl; intros σ.
    destruct (df_eval σ a); destruct (df_eval σ b); trivial.
    f_equal.
    autorewrite with Rarith in *.
    destruct (Rle_dec d d0).
    - rewrite Rmax_right by trivial.
      rewrite Rabs_pos_eq by lra.
      lra.
    - rewrite Rmax_left by lra.
      rewrite Rabs_minus_sym.
      rewrite Rabs_pos_eq by lra.
      lra.
  Qed.

(*  Lemma coerce_dec_id {A} (dec:forall x y:A, {x=y}+{x<>y}) (x:A) (pf:x=x) : coerce pf x = x.
  Proof.
    unfold coerce.
    replace pf with (eq_refl A); trivial.
    apply UIP_dec.
    apply dec.
    generalize (@UIP_dec A dec pf).
        Lemma var_type_UIP_refl {x:var_type} (e:x=x) : e = eq_refl x.
        Proof.
      apply (UIP_dec vart_dec x x pf).
    Qed.

    unfold coerce.
    destruct pf.
      destruct pf.
      exact a.
    Defined.
*)

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


   Lemma backpropeq_gen (x : SubVar) (env gradenv : df_env) (dfexpr : DefinedFunction UnitAnn DTfloat) (grad : float) :
      let xvar := (x, DTfloat) in 
      is_scalar_function dfexpr -> 
      vartlookup gradenv (x,DTfloat) <> None ->
      match df_eval_deriv env dfexpr xvar, 
            backprop_lookup (Some gradenv) xvar,
            backprop_lookup (df_eval_backprop_deriv env dfexpr gradenv grad) xvar
      with
      | Some dval, Some bval0, Some bval1 => (dval*grad + bval0)%R = bval1
      | None, _, None => True
      | _, _, _ => False
      end.
   Proof.
     simpl.
     intros is_scalar.
     generalize is_scalar.
     revert grad gradenv.
     pattern dfexpr.
     revert dfexpr is_scalar.
     DefinedFunction_scalar_cases (apply is_scalar_function_ind) Case; simpl.
     - Case "Number"%string.
       intros _ _ grad gradenv _ xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - Case "Constant"%string.
       intros _ _ grad gradenv _ xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - Case "Var"%string.
       intros sv _ grad gradenv _ xinn.
       case_eq (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto].
       destruct (var_dec x sv); simpl.
       + subst.
         rewrite H; simpl.
         rewrite lookup_update.
         destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (sv, DTfloat)); [| congruence].
         unfold addvar; simpl.
         rewrite H.
         lra.
       + destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (x, DTfloat)); [congruence | ].
         case_eq (vartlookup gradenv (sv, DTfloat)); simpl; intros.
         * rewrite lookup_update_neq by congruence.
           rewrite H.
           lra.
         * rewrite H.
           lra.
     - Case "Plus"%string.
       intros _ l r IHl IHr grad gradenv [isc1 isc2] xinn. 
       case_eq (df_eval_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl grad gradenv isc1 xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_backprop_deriv env l gradenv grad)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr grad ge' isc2).
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_backprop_deriv env r ge' grad) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_backprop_deriv env l gradenv grad ); simpl; trivial; intros.
           apply IHr; trivial.
           apply (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv isc1 xinn).
         case_eq (df_eval_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn); intros.
         destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Minus"%string.
       intros _ l r IHl IHr grad gradenv [isc1 isc2] xinn.
       case_eq (df_eval_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl grad gradenv isc1 xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_backprop_deriv env l gradenv grad)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (- grad)%R ge' isc2).
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_backprop_deriv env r ge' (- grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_backprop_deriv env l gradenv grad ); simpl; trivial; intros.
           apply IHr; trivial.
           apply (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv isc1 xinn).
         case_eq (df_eval_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn); intros.
         destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Times"%string.
       intros _ l r IHl IHr grad gradenv [isc1 isc2] xinn. 
       case_eq (df_eval env l);
       [ intros le eqle | intros eqle]; simpl; trivial.
       case_eq (df_eval_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval env r);
           [ intros re eqre | intros eqre]
           ; simpl; trivial.
         case_eq (df_eval_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl (re * grad)%R gradenv isc1 xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_backprop_deriv env l gradenv (re * grad)%R)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (le * grad)%R ge' isc2).
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_backprop_deriv env r ge' (le * grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_backprop_deriv env l gradenv (re * grad)%R ); simpl; trivial; intros.
           apply IHr; trivial.
           apply (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn).
       + case_eq (df_eval env r);
           [ intros re eqre | intros eqre]
           ; simpl; trivial.
           specialize (IHl (re * grad)%R gradenv isc1 xinn).
           case_eq (df_eval_backprop_deriv env l gradenv (re * grad)%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn); intros.
           destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Divide"%string.
       intros _ l r IHl IHr grad gradenv [isc1 isc2] xinn. 
       case_eq (df_eval env l);
       [ intros le eqle | intros eqle]; simpl; trivial.
       case_eq (df_eval_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval env r);
           [ intros re eqre | intros eqre]
           ; simpl; trivial.
         case_eq (df_eval_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl (grad / re)%R gradenv isc1 xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_backprop_deriv env l gradenv (grad / re)%R)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (- le / (re * re) * grad)%R ge' isc2).
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_backprop_deriv env r ge' (- le  / (re * re) * grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_backprop_deriv env l gradenv (grad / re)%R ); simpl; trivial; intros.
           apply IHr; trivial.
           apply (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn).
       + case_eq (df_eval env r);
           [ intros re eqre | intros eqre]
           ; simpl; trivial.
           specialize (IHl (grad / re)%R gradenv isc1 xinn).
           case_eq (df_eval_backprop_deriv env l gradenv (grad / re)%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (scalar_df_eval_backprop_deriv_preserves_lookup_not_none isc1 H (x, DTfloat) xinn); intros.
           destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Square"%string.
       intros _ e IHe grad gradenv isc xinn. 
       case_eq (df_eval env e);
         [ intros le eqee | intros eqee]; simpl; trivial.
       
       specialize (IHe (2 * le * grad)%R gradenv isc xinn).
       case_eq (df_eval_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.

       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_backprop_deriv env e gradenv (2 * le * grad)%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Exp"%string.
       intros _ e IHe grad gradenv isc xinn. 
       case_eq (df_eval env e);
         [ intros le eqee | intros eqee]; simpl; trivial.
       
       specialize (IHe (grad * exp le)%R gradenv isc xinn).
       case_eq (df_eval_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.

       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_backprop_deriv env e gradenv (grad * exp le)%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Log"%string.
       intros _ e IHe grad gradenv isc xinn. 
       case_eq (df_eval env e);
         [ intros le eqee | intros eqee]; simpl; trivial.
       
       specialize (IHe (grad / le)%R gradenv isc xinn).
       case_eq (df_eval_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.

       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_backprop_deriv env e gradenv (grad / le)%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Abs"%string.
       intros _ e IHe grad gradenv isc xinn. 
       case_eq (df_eval env e);
         [ intros le eqee | intros eqee]; simpl; trivial.
       
       specialize (IHe (grad * (sign le))%R gradenv isc xinn).
       case_eq (df_eval_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.

       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_backprop_deriv env e gradenv (grad * (sign  le))%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Sign"%string.
       intros _ e IHe grad gradenv isc xinn. 
       specialize (IHe 0%R gradenv isc xinn).
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (df_eval_backprop_deriv env e gradenv 0%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       simpl.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       lra.
     - Case "PSign"%string.
       intros _ e IHe grad gradenv isc xinn. 
       specialize (IHe 0%R gradenv isc xinn).
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (df_eval_backprop_deriv env e gradenv 0%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       simpl.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       lra.
     - Case "Max"%string.
       intros _ l r IHl IHr grad gradenv [isc1 isc2] xinn.
       specialize (IHl grad gradenv isc1 xinn).
       specialize (IHr grad gradenv isc2 xinn).
       
       case_eq (df_eval env l); simpl; trivial
       ; intros eld eqeld.
       case_eq (df_eval env r ); simpl; intros; trivial.
       destruct (Rle_dec eld d); simpl.
       + destruct (df_eval_deriv env r (x, DTfloat)); simpl; trivial.
       + destruct (df_eval_deriv env l (x, DTfloat)); simpl; trivial.
 Qed.
  

 Lemma tree_backpropeq_gen (x : SubVar) (env gradenv : df_env) 
       (dfexpr : DefinedFunction EvalAnn DTfloat) (grad : float) :
   let xvar := (x, DTfloat) in 
   is_scalar_function dfexpr ->
   vartlookup gradenv (x,DTfloat) <> None ->
   match df_eval_tree_deriv env dfexpr xvar, 
         backprop_lookup (Some gradenv) xvar,
         backprop_lookup (df_eval_tree_backprop_deriv env dfexpr gradenv grad) xvar
      with
      | Some dval, Some bval0, Some bval1 => (dval*grad + bval0)%R = bval1
      | None, _, None => True
      | _, _, _ => False
      end.
   Proof.
     simpl.
     intros is_scalar.
     revert grad gradenv.
     pattern dfexpr.
     revert dfexpr is_scalar.
     DefinedFunction_scalar_cases (apply is_scalar_function_ind) Case; simpl.

     - Case "Number"%string.
       intros _ _ grad gradenv xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - Case "Constant"%string.
       intros _ _ grad gradenv xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - Case "Var"%string.
       intros sv _ grad gradenv xinn.
       case_eq (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto].
       destruct (var_dec x sv); simpl.
       + subst.
         rewrite H; simpl.
         rewrite lookup_update.
         destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (sv, DTfloat)); [| congruence].
         unfold addvar; simpl.
         rewrite H.
         lra.
       + destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (x, DTfloat)); [congruence | ].
         case_eq (vartlookup gradenv (sv, DTfloat)); simpl; intros.
         * rewrite lookup_update_neq by congruence.
           rewrite H.
           lra.
         * rewrite H.
           lra.
     - Case "Plus"%string.
       intros _ l r IHl IHr grad gradenv xinn.
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl grad gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv grad)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr grad ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' grad) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv grad ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv xinn).
         case_eq (df_eval_tree_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
         destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Minus"%string.
       intros _ l r IHl IHr grad gradenv xinn.
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl grad gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv grad)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (- grad)%R ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' (- grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv grad ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv xinn).
         case_eq (df_eval_tree_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
         destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Times"%string.
       intros _ l r IHl IHr grad gradenv xinn. 
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl (get_annotation r * grad)%R gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv (get_annotation r * grad)%R)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (get_annotation l * grad)%R ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' (get_annotation l * grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv (get_annotation r * grad)%R ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       +   specialize (IHl (get_annotation r * grad)%R gradenv xinn).
           case_eq (df_eval_tree_backprop_deriv env l gradenv (get_annotation r * grad)%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
           destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Divide"%string.
       intros _ l r IHl IHr grad gradenv xinn. 
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl (grad / get_annotation r)%R gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv (grad / get_annotation r)%R)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (- get_annotation l / ((get_annotation r) * (get_annotation r)) * grad)%R ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' (- get_annotation l  / ((get_annotation r) * (get_annotation r)) * grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv (grad / get_annotation r)%R ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       +   specialize (IHl (grad / get_annotation r)%R gradenv xinn).
           case_eq (df_eval_tree_backprop_deriv env l gradenv (grad / get_annotation r )%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
           destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Square"%string.
       intros _ e IHe grad gradenv xinn. 
       
       specialize (IHe (2 * (get_annotation e) * grad)%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.

       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (2 * (get_annotation e) * grad)%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Exp"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe (grad * exp (get_annotation e))%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (grad * exp (get_annotation e))%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.

     - Case "Log"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe (grad / get_annotation e)%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (grad / get_annotation e)%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.

     - Case "Abs"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe (grad * (sign (get_annotation e)))%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (grad * (sign (get_annotation e)))%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Sign"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe 0%R gradenv xinn).
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (df_eval_tree_backprop_deriv env e gradenv 0%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       simpl.
       replace (de * 0)%R with (0)%R in IHe by lra.
       replace (0 * grad)%R with (0)%R by lra.
       apply IHe.
     - Case "PSign"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe 0%R gradenv xinn).
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (df_eval_tree_backprop_deriv env e gradenv 0%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       simpl.
       replace (de * 0)%R with (0)%R in IHe by lra.
       replace (0 * grad)%R with (0)%R by lra.
       apply IHe.
     - Case "Max"%string.
       intros _ l r IHl IHr grad gradenv xinn.
       specialize (IHl grad gradenv xinn).
       specialize (IHr grad gradenv xinn).
       destruct (Rle_dec (get_annotation l) (get_annotation r)); simpl.
       destruct (df_eval_tree_deriv env r (x, DTfloat)); simpl; trivial.
       destruct (df_eval_tree_deriv env l (x, DTfloat)); simpl; trivial.
 Qed.

(*
Tactic Notation "DefinedFunction_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Number"%string
  | Case_aux c "Constant"%string                 
  | Case_aux c "DVector"%string
  | Case_aux c "DMatrix"%string
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
  | Case_aux c "Max"%string
  | Case_aux c "VectorDot"%string
  | Case_aux c "VectorSum"%string
  | Case_aux c "MatrixSum"%string             
  | Case_aux c "VectorElem"%string
  | Case_aux c "MatrixElem"%string
  | Case_aux c "MatrixVectorMult"%string
  | Case_aux c "MatrixVectorAdd"%string             
  | Case_aux c "MatrixMult"%string
  | Case_aux c "VectorPlus"%string
  | Case_aux c "VectorMinus"%string
  | Case_aux c "MatrixPlus"%string
  | Case_aux c "MatrixMinus"%string
  | Case_aux c "VectorScalMult"%string
  | Case_aux c "MatrixScalMult"%string
  | Case_aux c "VectorApply"%string
  | Case_aux c "MatrixApply"%string             
  | Case_aux c "VLossfun"%string
  | Case_aux c "MLossfun"%string].

 Lemma tree_backpropeq_complte_gen (x : SubVar) (env gradenv : df_env) 
       (dfexpr : DefinedFunction EvalAnn DTfloat) (grad : float) :
   let xvar := (x, DTfloat) in 
   vartlookup gradenv (x,DTfloat) <> None ->
   match df_eval_tree_deriv env dfexpr xvar, 
         backprop_lookup (Some gradenv) xvar,
         backprop_lookup (df_eval_tree_backprop_deriv env dfexpr gradenv grad) xvar
      with
      | Some dval, Some bval0, Some bval1 => (dval*grad + bval0)%R = bval1
      | None, _, None => True
      | _, _, _ => False
      end.
   Proof.
     simpl.
     DefinedFunction_cases (induction dfexpr) Case; simpl.

     - Case "Number"%string.
       intros _ _ grad gradenv xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - Case "Constant"%string.
       intros _ _ grad gradenv xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - Case "Var"%string.
       intros sv _ grad gradenv xinn.
       case_eq (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto].
       destruct (var_dec x sv); simpl.
       + subst.
         rewrite H; simpl.
         rewrite lookup_update.
         destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (sv, DTfloat)); [| congruence].
         unfold addvar; simpl.
         rewrite H.
         lra.
       + destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (x, DTfloat)); [congruence | ].
         case_eq (vartlookup gradenv (sv, DTfloat)); simpl; intros.
         * rewrite lookup_update_neq by congruence.
           rewrite H.
           lra.
         * rewrite H.
           lra.
     - Case "Plus"%string.
       intros _ l r IHl IHr grad gradenv xinn.
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl grad gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv grad)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr grad ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' grad) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv grad ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv xinn).
         case_eq (df_eval_tree_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
         destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Minus"%string.
       intros _ l r IHl IHr grad gradenv xinn.
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl grad gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv grad)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (- grad)%R ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' (- grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv grad ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv xinn).
         case_eq (df_eval_tree_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
         destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Times"%string.
       intros _ l r IHl IHr grad gradenv xinn. 
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl (get_annotation r * grad)%R gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv (get_annotation r * grad)%R)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (get_annotation l * grad)%R ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' (get_annotation l * grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv (get_annotation r * grad)%R ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       +   specialize (IHl (get_annotation r * grad)%R gradenv xinn).
           case_eq (df_eval_tree_backprop_deriv env l gradenv (get_annotation r * grad)%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
           destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Divide"%string.
       intros _ l r IHl IHr grad gradenv xinn. 
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl (grad / get_annotation r)%R gradenv xinn).
           case_eq (vartlookup gradenv (x, DTfloat))
           ; [intros xv xveqq | intros xveqq]
           ; rewrite xveqq in IHl
           ; [ | tauto].
           case_eq (df_eval_tree_backprop_deriv env l gradenv (grad / get_annotation r)%R)
           ; [intros ge' ge'eq | intros ge'eq]
           ; rewrite ge'eq in IHl
           ; [ | tauto].
           simpl in IHl.
           case_eq (vartlookup ge' (x, DTfloat))
           ; [intros xv' xv'eqq | intros xv'eqq]
           ; rewrite xv'eqq in IHl
           ; [ | tauto].
           specialize (IHr (- get_annotation l / ((get_annotation r) * (get_annotation r)) * grad)%R ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_tree_backprop_deriv env r ge' (- get_annotation l  / ((get_annotation r) * (get_annotation r)) * grad)%R) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_tree_backprop_deriv env l gradenv (grad / get_annotation r)%R ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       +   specialize (IHl (grad / get_annotation r)%R gradenv xinn).
           case_eq (df_eval_tree_backprop_deriv env l gradenv (grad / get_annotation r )%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (df_eval_tree_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
           destruct (vartlookup d (x, DTfloat)); tauto.
     - Case "Square"%string.
       intros _ e IHe grad gradenv xinn. 
       
       specialize (IHe (2 * (get_annotation e) * grad)%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.

       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (2 * (get_annotation e) * grad)%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Exp"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe (grad * exp (get_annotation e))%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (grad * exp (get_annotation e))%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.

     - Case "Log"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe (grad / get_annotation e)%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (grad / get_annotation e)%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.

     - Case "Abs"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe (grad * (sign (get_annotation e)))%R gradenv xinn).
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_backprop_deriv env e gradenv (grad * (sign (get_annotation e)))%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       case_eq (vartlookup ge' (x, DTfloat))
       ; [intros xv' xv'eqq | intros xv'eqq]
       ; rewrite xv'eqq in IHe
       ; [ | tauto].
       simpl.
       rewrite xv'eqq.
       lra.
     - Case "Sign"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe 0%R gradenv xinn).
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (df_eval_tree_backprop_deriv env e gradenv 0%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       simpl.
       replace (de * 0)%R with (0)%R in IHe by lra.
       replace (0 * grad)%R with (0)%R by lra.
       apply IHe.
     - Case "PSign"%string.
       intros _ e IHe grad gradenv xinn. 
       specialize (IHe 0%R gradenv xinn).
       case_eq (vartlookup gradenv (x, DTfloat))
       ; [intros xv xveqq | intros xveqq]
       ; rewrite xveqq in IHe
       ; [ | tauto].
       case_eq (df_eval_tree_deriv env e (x, DTfloat))
       ; [intros de eqde | intros eqde]
       ; rewrite eqde in IHe
       ; trivial.
       case_eq (df_eval_tree_backprop_deriv env e gradenv 0%R)
       ; [intros ge' ge'eq | intros ge'eq]
       ; rewrite ge'eq in IHe
       ; [ | tauto].
       simpl in IHe.
       simpl.
       replace (de * 0)%R with (0)%R in IHe by lra.
       replace (0 * grad)%R with (0)%R by lra.
       apply IHe.
     - Case "Max"%string.
       intros _ l r IHl IHr grad gradenv xinn.
       specialize (IHl grad gradenv xinn).
       specialize (IHr grad gradenv xinn).
       destruct (Rle_dec (get_annotation l) (get_annotation r)); simpl.
       destruct (df_eval_tree_deriv env r (x, DTfloat)); simpl; trivial.
       destruct (df_eval_tree_deriv env l (x, DTfloat)); simpl; trivial.
 Qed.
*)
End real_pfs.

(*
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
*)            

Tactic Notation "DefinedFunction_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Number"%string
  | Case_aux c "Constant"%string                 
  | Case_aux c "DVector"%string
  | Case_aux c "DMatrix"%string
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
  | Case_aux c "Max"%string
  | Case_aux c "VectorDot"%string
  | Case_aux c "VectorSum"%string
  | Case_aux c "MatrixSum"%string             
  | Case_aux c "VectorElem"%string
  | Case_aux c "MatrixElem"%string
  | Case_aux c "MatrixVectorMult"%string
  | Case_aux c "MatrixVectorAdd"%string             
  | Case_aux c "MatrixMult"%string
  | Case_aux c "VectorPlus"%string
  | Case_aux c "VectorMinus"%string
  | Case_aux c "MatrixPlus"%string
  | Case_aux c "MatrixMinus"%string
  | Case_aux c "VectorScalMult"%string
  | Case_aux c "MatrixScalMult"%string
  | Case_aux c "VectorApply"%string
  | Case_aux c "MatrixApply"%string             
  | Case_aux c "VLossfun"%string
  | Case_aux c "MLossfun"%string].
