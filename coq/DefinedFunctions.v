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

    Definition Vector (T:Type) (n : nat) := {n':nat | n' < n}%nat -> T.
    Definition Matrix (T:Type) (n m : nat) := 
      {n':nat | n' < n}%nat -> {m':nat | m' < m}%nat -> T.

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
    | MatrixSum {m n} (ann:Ann DTfloat) (v: DefinedFunction (DTMatrix m n)) : DefinedFunction DTfloat                                                                                       | VectorElem {n} (ann:Ann DTfloat) (l:DefinedFunction (DTVector n)) (i:{x:nat|x<n}%nat) : DefinedFunction DTfloat
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


    Fixpoint get_annotation {Ann T} (df:DefinedFunction T) : Ann T
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



  Definition df_plus  (df1 df2 : DefinedFunction DTfloat) : @DefinedFunction UnitAnn DTfloat :=
    Plus tt df1 df2.

  Definition df_times (df1 df2 : DefinedFunction DTfloat) : @DefinedFunction UnitAnn DTfloat :=
    Times tt df1 df2.

  Section deriv.

    Definition vector_fold_right1_bounded_dep {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} (v:Vector B m) (n:nat) (pf:(n<=m)%nat)
    : A n.
    Proof.
      induction n.
      - exact init.
      - destruct n.
        + assert (pf2:(0 < m)%nat) by omega.
          exact (singleton (v (exist _ 0 pf2)%nat)).
        + assert (pf2:(S n <= m)%nat) by omega.
          assert (pf3:(S n < m)%nat) by omega.
          apply f.
          * exact (v (exist _ (S n) pf3)).
          * exact (IHn pf2).
    Defined.

    Definition vector_fold_right_bounded_dep {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B m) (n:nat) (pf:(n<=m)%nat)
    : A n.
    Proof.
      induction n.
      - exact init.
      - apply f.
        + assert (pf2:(n < m)%nat) by omega.
          exact (v (exist _ n pf2)).
        + apply IHn.
          omega.
    Defined.

    Definition vnil {T} : Vector T 0.
    Proof.
      intros [i pf].
      omega.
    Defined.

    Definition vcons {T} {n} (x:T) (v:Vector T n) : (Vector T (S n)).
    Proof.
      intros [i pf].
      destruct (Nat.eq_dec i n).
      + exact x.
      + apply v.
        exists i.
        omega.
    Defined.

    
    Definition vhd {T} {n} (v:Vector T (S n)) : T := v (exist _ (0%nat) (Nat.lt_0_succ n)).
    Definition vlast {T} {n} (v:Vector T (S n)) : T := v (exist _ (n%nat) (Nat.lt_succ_diag_r n)).

    Definition vdrop_last {T} {n} (v:Vector T (S n)) : Vector T n.
    Proof.
      intros [i pf]; apply v.
      exists i.
      apply NPeano.Nat.lt_lt_succ_r; trivial.
    Defined.


    Definition vector_fold_right1_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} (v:Vector B m) : A m
      := vector_fold_right1_bounded_dep f init singleton v m (le_refl _).

    Definition vector_fold_right_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B m) : A m
      := vector_fold_right_bounded_dep f init v m (le_refl _).

    Definition vector_fold_right1 {A B:Type} (f:B->A->A) (init:A) (singleton:B->A) {m:nat} (v:Vector B m)
      := vector_fold_right1_dep (A:=fun _ => A) (fun _ => f) init singleton v.

    Definition vector_fold_right {A B:Type} (f:B->A->A) (init:A) {m:nat} (v:Vector B m)
      := vector_fold_right_dep (fun _ => f) init v.

    Definition defined_sum {m} (v:Vector (DefinedFunction DTfloat) m) : @DefinedFunction UnitAnn DTfloat
      := vector_fold_right1 (fun a b => Plus tt a b) (Number tt 0) id v.

    Definition vsum {m:nat} (v:Vector float m) : float
      := vector_fold_right1 Fplus 0 id v.

    Definition vectoro_to_ovector {T} {n} (v:Vector (option T) n) : option (Vector T n)
      := vector_fold_right_dep (fun n => lift2 (@vcons _ n)) (Some vnil) v.

    Definition matrixo_to_omatrix {T} {m n} (v:Matrix (option T) m n) : option (Matrix T m n)
      := vectoro_to_ovector (fun i => vectoro_to_ovector (v i)).

    Definition vmap {A B} {n} (f:A->B) (v:Vector A n) : Vector B n
      := vector_fold_right_dep (fun n x y => vcons (n:=n) (f x) y) vnil v.

    Definition msum {m n:nat} (v:Matrix float m n) : float :=
      vsum (vmap vsum v).

    Definition mmap {A B} {m n} (f:A->B) (mat:Matrix A m n) : Matrix B m n
      := vmap (fun mrow => vmap f mrow) mat.

    Definition list_fold_right1_bounded_dep {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) (l:list B) (n:nat) (pf:(n<=length l)%nat)
    : A n.
    Proof.
      induction n.
      - exact init.
      - destruct n.
        + assert (pf2:(0 < length l)%nat) by omega.
          destruct l.
          * simpl in pf; omega.
          * exact (singleton b).
        + assert (pf2:(S n <= length l)%nat) by omega.
          apply f.
          * destruct l; simpl in *; try omega.
            apply b.
          * apply IHn.
            apply pf2.
    Defined.

    Definition list_fold_right1_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) (l:list B) : A (length l)
      := list_fold_right1_bounded_dep f init singleton l (length l) (le_refl _).

    Definition list_fold_right_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) (l:list B) : A (length l)
      := list_fold_right1_dep f init (fun a => f _ a init) l.

    Definition list_to_vector {A} (l:list A) : Vector A (length l)
      := list_fold_right_dep (@vcons _) vnil l.

    Definition vector_to_list {A} {n} (v:Vector A n) : list A
      := vector_fold_right cons nil v.
    
    Definition vseq start len : Vector nat len
      := eq_rect _ _ (list_to_vector (seq start len)) _ (seq_length _ _).

    Definition vector_zip {A B} {m:nat} (v1:Vector A m) (v2:Vector B m) : Vector (A*B) m
      := fun i => (v1 i, v2 i).

    Definition matrix_zip {A B} {m n:nat} (mat1:Matrix A m n) (mat2:Matrix B m n) : Matrix (A*B) m n
      := let mat12:Vector (Vector A n*Vector B n) m := vector_zip mat1 mat2 in
         vmap (fun '(a,b) => vector_zip a b) mat12.
                                 
    Definition vector_split {A B} {m:nat} (v:Vector (A*B) m) : Vector A m * Vector B m
      := (fun i => fst (v i), fun i => snd (v i)).

    Program Definition vtake {A} {m:nat} (v:Vector (A) m) (n:nat) (pf:(n<=m)%nat) : Vector A n
      := fun i => v i.
    Next Obligation.
      omega.
    Defined.

    Definition vec_eq {A} {m:nat} (x y:Vector A m) := forall i, x i = y i.
    Notation "x =v= y" := (vec_eq x y) (at level 70).
    
    (* If we are willing to assume an axiom *)
    (*
    Lemma vec_eq_eq {A} {m:nat} (x y:Vector A m) : vec_eq x y -> x = y.
    Proof.
      Require Import FunctionalExtensionality.
      intros.
      apply functional_extensionality.
      apply H.
    Qed.
     *)

    Lemma index_pf_irrel n m pf1 pf2 : 
      exist (fun n' : nat => (n' < n)%nat) m pf1 =
      exist (fun n' : nat => (n' < n)%nat) m pf2.
      f_equal.
      apply digit_pf_irrel.
    Qed.
    
    Lemma vector_Sn_split {T} {n} (v:Vector T (S n)) :
      v =v= vcons (vlast v) (vdrop_last v).
    Proof.
      intros [i pf].
      unfold vcons, vlast, vdrop_last.
      destruct (Nat.eq_dec i n)
      ; subst
      ; f_equal
      ; apply index_pf_irrel.
    Qed.

    Lemma vector_split_zip {A B} {m:nat} (v:Vector (A*B) m) :
      let '(va,vb):=vector_split v in vector_zip va vb =v= v.
    Proof.
      simpl.
      intros i.
      vm_compute.
      now destruct (v i).
    Qed.

    Lemma split_vector_zip {A B} {m:nat} (va:Vector A m) (vb:Vector B m) :
      vector_split (vector_zip va vb) = (va,vb).
    Proof.
      vm_compute.
      f_equal.
    Qed.
    
  Section subst.

    Program Definition substvar {Ann} (v vv:var_type) (e':@DefinedFunction Ann (snd v)) (e:@DefinedFunction Ann (snd vv)) : (@DefinedFunction Ann (snd vv)) :=
      
      match v == vv with
      | left pf => eq_rect _ (fun t => DefinedFunction t) e' _ _
      | right pf => e
      end.
  
 Fixpoint df_subst {T Ann} (df: @DefinedFunction Ann T) (v:var_type) (e':@DefinedFunction UnitAnn (snd v)) :=
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
      fun e (ve':{v:var_type & @DefinedFunction UnitAnn (snd v)}) => 
        @df_subst T Ann e (projT1 ve') (projT2 ve').

    Definition df_subst_list {T} (e:DefinedFunction T)
               (l:list {v:var_type & DefinedFunction (snd v)}) : @DefinedFunction UnitAnn T
      := fold_left (@df_substp T UnitAnn) l e.

  End subst.

  Definition ConstVector {T} (n:nat) (c:T) : (Vector T n) := fun (n': {n':nat | n' < n}%nat) => c.
  Definition ConstMatrix {T} (n m : nat) (c:T) : (Matrix T n m) := fun (n': {n':nat | n' < n}%nat) (m':{m':nat | m' < m}%nat) => c.
  

(* restrict to scalar v? *)
    Fixpoint df_deriv {T} (df:@DefinedFunction UnitAnn T) (v:var_type) {struct df} : @DefinedFunction UnitAnn T
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

    Definition df_gradient {T} (df:DefinedFunction T) (lv:list var_type) : list (DefinedFunction T)
      := map (df_deriv df) lv.

  End deriv.
  
  Section eval.
    
    Definition transpose {A} {n m:nat} (mat:Matrix A n m) :=
      fun i j => mat j i.

    Definition matrix_vector_mult {n m} (l : Matrix float n m)(r : Vector float m) : Vector float n :=
      fun i => vsum (fun j => (l i j) * (r j)).

    Definition matrix_vector_add {n m} (l : Matrix float n m) (r : Vector float n) : Matrix float n m := fun i j => (l i j) + (r i).

    Definition matrix_mult {m n p} (l : Matrix float n m)(r : Matrix float m p) : Matrix float n p :=
      fun i k => vsum (fun j => (l i j) * (r j k)).

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

    Fixpoint df_eval {T Ann} (σ:df_env) (df:@DefinedFunction Ann T) : option (definition_function_types_interp T)
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

    Fixpoint df_eval_tree {T Ann} (σ:df_env) (df:@DefinedFunction Ann T) : option (@DefinedFunction EvalAnn T)
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
           | Some l', Some r' => Some (Minus ((get_annotation l') / (get_annotation r'))
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

    Definition eval_env_entry_type := {T:definition_function_types & (@DefinedFunction UnitAnn T) & definition_function_types_interp T}.
    Definition df_eval_env := list eval_env_entry_type.
    
    Definition mk_eval_env_entry {T} df val : eval_env_entry_type
      := let P := fun t => @DefinedFunction UnitAnn t in
         let Q := fun t => definition_function_types_interp t in
       existT2 P Q T df val.

    Definition pair_update_evals {T} (df:@DefinedFunction UnitAnn T) (val:definition_function_types_interp T) (dfevals : df_eval_env) : (definition_function_types_interp T * df_eval_env) :=
      (val, (mk_eval_env_entry df val)::dfevals).

    Fixpoint df_evals_list {T} (σ:df_env) (df:@DefinedFunction UnitAnn T) (dfevals : df_eval_env) : option (definition_function_types_interp T * df_eval_env)
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
      Fixpoint evalslookup {T} (l:df_eval_env) (df:@DefinedFunction UnitAnn T) : 
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
    Definition df_eval_symbolic_gradient {T} (σ:df_env) (df:@DefinedFunction UnitAnn T) (lv:list var_type) : option (list (definition_function_types_interp T))
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

    Fixpoint df_eval_deriv {T} (σ:df_env) (df:DefinedFunction T) (v:var_type) : option (definition_function_types_interp T)
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
             Some (((ld * re) - (le * rd)) / (re * re))
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
         | Sign _ e => Some 0
         | PSign _ e => Some 0
         | Max _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd =>
             if le <= re then Some rd else Some ld
           | _, _, _, _ => None
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

    Fixpoint df_eval_tree_deriv {T} (σ:df_env) (df:@DefinedFunction EvalAnn T) (v:var_type) : option (definition_function_types_interp T)
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
             Some (((ld * re) - (le * rd)) / (re * re))
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
         | Sign _ e => Some 0
         | PSign _ e => Some 0
         | Max _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in                       
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             if le <= re then Some rd else Some ld
           | _, _ => None
           end
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

    Definition two_vector_env_iter {n} {A B} (f: A -> B -> df_env -> option df_env)
               (env: df_env) (v: Vector A n) (w: Vector B n) : option df_env :=
      vector_env_iter (fun '(a,b) env => f a b env) env 
                      (vector_zip v w).

    Fixpoint bounded_seq (start len : nat) {struct len} : list {n':nat | n' < start+len}%nat.
    Proof.
      revert start.
      induction len; intros start.
      - exact nil.
      - apply cons.
        + exists start.
          omega.
        + rewrite Nat.add_succ_r.
          exact (IHlen (S start)).
    Defined.

    Definition bounded_seq0 len : list {n':nat | n' < len}%nat := bounded_seq 0 len.


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

    Definition matrix_to_list_list {T} {m n} (v:Matrix T m n) : (list (list T))
      := vector_to_list (fun i => vector_to_list (v i)).

    Definition matrix_to_list {T} {m n} (v:Matrix T m n) : (list T)
      := concat (matrix_to_list_list v).


(*
    Lemma lemma1 {x} : x = DTfloat -> definition_function_types_interp x = float.
    Proof.
      intros.
      subst.
      reflexivity.
    Defined.

    Lemma lemma2 {x} {n} : x = DTVector n -> definition_function_types_interp x = Vector float n.
    Proof.
      intros.
      subst.
      reflexivity.
    Defined.

    Lemma lemma3 {x} {n m} : x = DTMatrix n m -> definition_function_types_interp x = Matrix float n m.
    Proof.
      intros.
      subst.
      reflexivity.
    Defined.

    Definition coerce {A B} (pf:A=B) : forall x:A, B.
    Proof.
      intros a.
      destruct pf.
      exact a.
    Defined.

    Definition addvar (x : var_type) (grad_env:df_env) :=
      (match snd x as y return snd x = y -> definition_function_types_interp y -> definition_function_types_interp y with
       | DTfloat =>  fun pf grad => match vartlookup grad_env x with
                     | Some val => (coerce (lemma1 pf) val) + grad
                     | _ => grad
                     end
       | DTVector n => fun pf grad => match vartlookup grad_env x with
                       | Some val => fun i => ((coerce (lemma2 pf) val) i) + (grad i)
                       | _ => grad
                       end
       | DTMatrix m n => fun pf grad => match vartlookup grad_env x with
                         | Some val => fun i j => ((coerce (lemma3 pf) val) i j) + (grad i j)
                         | _ => grad
                         end
       end) (eq_refl _).
*)
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

    Fixpoint df_eval_backprop_deriv {T Ann} (σ:df_env) (df:@DefinedFunction Ann T) (grad_env:df_env) {struct df} : definition_function_types_interp T -> option df_env
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
                 match df_eval_backprop_deriv σ l grad_env  (grad / re) with                 
                 | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  (- le * grad / (re * re))
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
           match df_eval σ l, df_eval σ r with
           | Some le, Some re =>
             if le <= re then 
               (df_eval_backprop_deriv σ r grad_env  grad) else
               (df_eval_backprop_deriv σ l grad_env  grad)
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


    Fixpoint df_eval_tree_backprop_deriv {T} (σ:df_env) (df:@DefinedFunction EvalAnn T) (grad_env:df_env)  {struct df} : definition_function_types_interp T -> option df_env
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
                        if in_dec vart_dec x (map (@projT1 var_type _) grad_env) then 
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
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  (- le * grad / (re * re))
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

   Fixpoint is_scalar_function {Ann} {T} (df:@DefinedFunction Ann T) : Prop
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

   Lemma is_scalar_function_scalar {Ann} {T} (df:@DefinedFunction Ann T) :
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


    Definition df_eval_gradient {T} σ (df:DefinedFunction T) (lv:list var_type) : option (list (definition_function_types_interp T))
      := listo_to_olist (map (df_eval_deriv σ df) lv).
    
(*
   Fixpoint df_eval_gradient_alt {dft:definition_function_types} (σ:df_env) (df:DefinedFunction dft) (lv:list var_type) : option (definition_function_types_map_base list dft)
    := (match df with
        | Number _ => Some (map (fun _ => 0) lv)
        | Constant t x => Some 
            match t return definition_function_types_map_base list t with
            | DTfloat => map (fun _ => 0) lv
            | DTVector n => map (fun _ => ConstVector n 0) lv
            | DTMatrix m n => map (fun _ => ConstMatrix m n 0) lv
            end
        | DVector n v => vectoro_to_ovector (vmap (fun x => df_eval_gradient_alt σ x lv) v)
        | DMatrix n m df => matrixo_to_omatrix (vmap (fun x => vmap (fun y => df_eval_gradient_alt σ y lv) x) df)
         | Var x => Some (map (fun v => if x == v then 1 else 0) lv)
         | Plus l r => 
           match df_eval_gradient_alt σ l lv, df_eval_gradient_alt σ r lv with
           | Some ld, Some rd => Some  (map (fun '(x, y) => x+y) (combine ld rd))
           | _, _ => None
           end
         | Minus l r =>
           match df_eval_gradient_alt σ l lv, df_eval_gradient_alt σ r lv with
           | Some ld, Some rd => Some (map (fun '(x, y) => x-y) (combine ld rd))
           | _, _ => None
           end
         | Times l r =>
           match df_eval σ l, df_eval_gradient_alt σ l lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (map (fun '(lp,rp) => lp*re + le*rp) (combine ld rd))
           | _, _, _, _ => None
           end
         | Divide l r =>
           match df_eval σ l, df_eval_gradient_alt σ l lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (map (fun '(lp,rp) => (lp*re - le*rp)/(re * re)) (combine ld rd))
           | _, _, _, _ => None
           end
         | Square e =>
           match df_eval σ e, df_eval_gradient_alt σ e lv with
           | Some ee, Some ed => Some (map (fun pd => 2 * ee * pd) ed)
           | _, _  => None
           end
         | Exp e =>
           match df_eval σ e, df_eval_gradient_alt σ e lv with
           | Some ee, Some ed => Some (map (fun pd => pd * Fexp ee) ed)
           | _, _  => None
           end
         | Log e =>
           match df_eval σ e, df_eval_gradient_alt σ e lv with
           | Some ee, Some ed => Some (map (fun pd => (pd / ee)) ed)
           | _, _ => None
           end
         | Abs e =>
           match df_eval σ e, df_eval_gradient_alt σ e lv with
           | Some ee, Some ed => Some (map (fun d => d * (sign ee)) ed)
           | _, _ => None
           end
         | Sign e =>
           match df_eval σ e with
           | Some ee => Some (map (fun _ => 0) lv)
           | _ => None
           end
         | PSign e =>
           match df_eval σ e with
           | Some ee => Some (map (fun _ => 0) lv)
           | _ => None
           end
         | Max l r =>
           match df_eval σ l, df_eval_gradient_alt σ l lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             if le <= re then Some rd else Some ld
           | _, _, _, _ => None
           end
         | VectorElem n l i => 
           match (df_eval_gradient_alt σ l lv)  with
           | Some l' => Some (l' i)
           | _ => None
           end
         | MatrixElem m n l i j =>
           match (df_eval_gradient_alt σ l lv)  with
           | Some l' => Some (l' i j)
           | _ => None
           end
         | VectorSum n l => 
           match df_eval_gradient_alt σ l lv with
           | Some l' =>
             Some (vector_fold_right (fun a b => map (fun '(xp,rp) => xp + rp)
                                                     (combine a b)) 
                                     (map (fun _ => 0) lv) l')
           | _ => None
           end 
         | VectorDot n l r => 
           match df_eval σ l, df_eval_gradient_alt σ l lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (vector_fold_right (fun a b => map (fun '(xp,rp) => xp + rp)
                                                     (combine a b)) 
                                     (map (fun _ => 0) lv)
                                     (fun i => map (fun '(lp,rp) => lp*(re i) + (le i)*rp) 
                                                   (combine (ld i) (rd i))))
           | _, _, _, _ => None
           end
         | VectorScalMult n x r =>
           match df_eval σ x, df_eval_gradient_alt σ x lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some xe, Some xd, Some re, Some rd => 
             Some (fun j => map (fun '(xp,rp) => xe * rp + xp * (re j)) (combine xd (rd j)))
           | _, _, _, _ => None
           end
         | MatrixScalMult n m x r =>
           match df_eval σ x, df_eval_gradient_alt σ x lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some xe, Some xd, Some re, Some rd => 
             Some (fun i j => map (fun '(xp,rp) => xe * rp + xp * (re i j)) (combine xd (rd i j)))

           | _, _, _, _ => None
           end
         | MatrixVectorMult n m l r => 
           match df_eval σ l, df_eval_gradient_alt σ l lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i => 
                     (vector_fold_right (fun a b => map (fun '(xp,rp) => xp + rp)
                                                        (combine a b))
                                        (map (fun _ => 0) lv)
                                        (fun j => map (fun '(lp,rp) => lp*(re j) + (le i j)*rp) 
                                                      (combine (ld i j) (rd j)))))
           | _, _, _, _ => None
           end
         | MatrixMult n m p l r =>
           match df_eval σ l, df_eval_gradient_alt σ l lv, df_eval σ r, df_eval_gradient_alt σ r lv with
           | Some le, Some ld, Some re, Some rd =>
             Some (fun i k => 
                     (vector_fold_right (fun a b => map (fun '(xp,rp) => xp + rp)
                                                        (combine a b)) 
                                        (map (fun _ => 0) lv)
                                        (fun j => map (fun '(lp,rp) => lp*(re j k) + (le i j)*rp) 
                                                      (combine (ld i j) (rd j k)))))
           | _, _, _, _ => None
           end
         | VectorPlus n l r =>
           match df_eval_gradient_alt σ l lv, df_eval_gradient_alt σ r lv with           
           | Some ld, Some rd => Some (fun i => map (fun '(x, y) => x+y) (combine (ld i) (rd i)))
           | _, _ => None
           end
         | VectorMinus n l r =>
           match df_eval_gradient_alt σ l lv, df_eval_gradient_alt σ r lv with           
           | Some ld, Some rd => Some (fun i => map (fun '(x, y) => x-y) (combine (ld i) (rd i)))
           | _, _ => None
           end
         | MatrixPlus n m l r =>
           match df_eval_gradient_alt σ l lv, df_eval_gradient_alt σ r lv with           
           | Some ld, Some rd => Some (fun i j => map (fun '(x, y) => x+y) (combine (ld i j) (rd i j)))
           | _, _ => None
           end
         | MatrixMinus n m l r =>
           match df_eval_gradient_alt σ l lv, df_eval_gradient_alt σ r lv with           
           | Some ld, Some rd => Some (fun i j => map (fun '(x, y) => x-y) (combine (ld i j) (rd i j)))
           | _, _ => None
           end
         | VectorApply n x s r => 
           match df_eval σ r, df_eval_gradient_alt σ r lv with                      
           | Some re, Some rd => 
             vectoro_to_ovector 
               (fun i => match df_eval_gradient_alt (cons (x, re i) σ) s lv with
                         | Some sd => 
                           Some (map (fun '(x, y) => x*y) (combine (rd i) sd))
                         | _ => None
                         end)
           | _, _ => None                                                    
           end
         | Lossfun n v1 v2 s l r =>
           match df_eval σ l, df_eval_gradient_alt σ l lv with                      
           | Some le, Some ld => 
             match (vectoro_to_ovector 
                      (fun i => match df_eval_gradient_alt (cons (v1, (le i)) (cons (v2, r i) σ)) s lv with
                         | Some sd => Some (map (fun '(x, y) => x*y) (combine (ld i) sd))
                         | _ => None
                         end)) with
             | Some vv => Some (vector_fold_right (fun a b => map (fun '(xp,rp) => xp + rp)
                                                     (combine a b)) 
                                     (map (fun _ => 0) lv) vv)
             | _ => None
             end
           | _, _ => None
           end
          end).
*)
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
             {P:forall {T}, @DefinedFunction Ann T->Prop}
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
            (df:@DefinedFunction Ann T) {struct df} : is_scalar_function df -> P df.
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
             {P:@DefinedFunction Ann DTfloat->Prop}
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
             (df:@DefinedFunction Ann DTfloat) : is_scalar_function df -> P df.
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

   Lemma df_eval_backprop_deriv_preserves_lookup_not_none {Ann T} {env} {df:@DefinedFunction Ann T} {gradenv grad d} :
     df_eval_backprop_deriv env df gradenv grad = Some d ->
     forall xv,
     vartlookup gradenv xv <> None ->
     vartlookup d xv <> None.
   Proof.
   Admitted.



(*     
   Lemma backpropeq_gen (x : SubVar) (env : df_env) (dfexpr : @DefinedFunction UnitAnn DTfloat) :
      let xvar := (x, DTfloat) in 
      is_scalar_function dfexpr ->
      df_eval_deriv env dfexpr xvar  =  
      backprop_lookup (df_eval_backprop_deriv env dfexpr nil (xvar::nil) 1)
                      xvar.
    Proof.
      simpl.
      revert dfexpr.
      apply is_scalar_function_ind; simpl.
      - reflexivity.
      - reflexivity.
      - intros.
        destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (x, DTfloat)).
        + inversion e; subst.
          destruct (var_dec x x); [| congruence].
          simpl.
          destruct (@equiv_dec var_type _ _ _ (x, DTfloat) (x, DTfloat)); [| congruence].
          rewrite (var_type_UIP_refl e1); simpl.
          reflexivity.
        + destruct (var_dec x sv); [congruence | ].
          reflexivity.
    Admitted.
*)
(*
      - intros.
        rewrite H, H0; clear H H0.
        (* need lemma here *)
        case_eq (df_eval_backprop_deriv env l nil ((x, DTfloat) :: nil) 1)
        ; simpl in *; trivial; intros d eqd.
        
        
        case_eq (df_eval_backprop_deriv env r d ((x, DTfloat) :: nil) 1)
        ; simpl in *; trivial; intros dd eqdd.
        
        

   Qed.
*)
          


(*
   Lemma tree_backpropeq_gen (x : SubVar) (env : df_env) (dfexpr : @DefinedFunction EvalAnn DTfloat) :
      let xvar := (x, DTfloat) in 
      is_scalar_function dfexpr ->
      df_eval_tree_deriv env dfexpr xvar  =  
      backprop_lookup (df_eval_tree_backprop_deriv env dfexpr nil (xvar::nil) 1) 
                      xvar.
   Proof.
     simpl.
     revert dfexpr.
     apply is_scalar_function_ind; simpl.
     - reflexivity.
     - reflexivity.
     Admitted.
*)

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
    Definition MaxDerived (a b : @DefinedFunction UnitAnn  DTfloat) :=
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

  Definition vlconcat {A n} (v:Vector (list A) n) : list A
    := concat (vector_to_list v).

  Definition vlconcat_map {A B n} (f:A->list B) (v:Vector A n) : list B
    := vlconcat (vmap f v).

  Definition vin {A n} (x:A) (v:Vector A n) : Prop
    := exists i, v i = x.

(*
  Lemma nth_In :
    forall (n:nat) (l:list A) (d:A), n < length l -> In (nth n l d) l.

  Lemma In_nth l x d : In x l ->
    exists n, n < length l /\ nth n l d = x.
 *)
  
(*
  Lemma vector_list_n (n : nat) (A : Type) (v : Vector A n) :
    length (vector_to_list v) = n.
  Proof.
    induction n.
    reflexivity.
    intros.
*)

  Notation "x =v= y" := (vec_eq x y) (at level 70).

    Lemma vector_fold_right_dep_bounded_pf_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B m) bound pf1 pf2 :
      vector_fold_right_bounded_dep f init v bound pf1 = vector_fold_right_bounded_dep f init v bound pf2.
    Proof.
      revert pf1 pf2.
      induction bound; trivial; intros.
      simpl.
      f_equal.
      f_equal.
      apply index_pf_irrel.
      trivial.
  Qed.
  
  Lemma vector_fold_right_dep_bounded_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (x y:Vector B m) bound pf :
    x =v= y -> vector_fold_right_bounded_dep f init x bound pf = vector_fold_right_bounded_dep f init y bound pf.
  Proof.
    intros eqq.
    induction bound; simpl; congruence.
  Qed.

  Lemma vector_fold_right_dep_bounded_cut_down {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (x:Vector B (S m)) bound pf1 pf2 :
    vector_fold_right_bounded_dep f init x bound pf1 = vector_fold_right_bounded_dep f init (vdrop_last x) bound pf2.
  Proof.
    induction bound; simpl; trivial.
    f_equal.
    - f_equal.
      apply index_pf_irrel.
    - apply IHbound.
  Qed.

  Lemma vector_fold_right_dep_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} {x y:Vector B m} :
    x =v= y -> vector_fold_right_dep f init x = vector_fold_right_dep f init y.
  Proof.
    apply vector_fold_right_dep_bounded_ext.
  Qed.

  Lemma vector_fold_right_ext {A:Type} {B} (f:B->A->A) (init:A) {m:nat} {x y:Vector B m} :
    x =v= y -> vector_fold_right f init x = vector_fold_right f init y.
  Proof.
    apply (@vector_fold_right_dep_ext (fun _ => A)).
  Qed.

  Lemma veq_refl {T} {n} (x:Vector T n) : x =v= x.
  Proof.
    intros i; reflexivity.
  Qed.

  Lemma veq_sym {T} {n} {x y:Vector T n} : x =v= y -> y =v= x.
  Proof.
    intros eqq i; symmetry; trivial.
  Qed.

  Lemma veq_trans {T} {n} {x y z:Vector T n} : x =v= y -> y =v= z -> x =v= z.
  Proof.
    intros eqq1 eqq2 i; etransitivity; eauto.
  Qed.

  Lemma vdrop_last_proper {T} {n} (x y:Vector T (S n)) : x =v= y -> vdrop_last x =v= vdrop_last y.
  Proof.
    intros eqq [i pf].
    apply eqq.
  Qed.
  
  Lemma vector_fold_right_dep_Sn {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B (S m)) : vector_fold_right_dep f init v = f m (vlast v) (vector_fold_right_dep f init (vdrop_last v)).
  Proof.
    rewrite (vector_fold_right_dep_ext _ _ (vector_Sn_split v)).
    unfold vector_fold_right_dep.
    simpl.
    destruct (Nat.eq_dec m m) ; [ | congruence].
    f_equal. 
    erewrite vector_fold_right_dep_bounded_pf_ext.
    erewrite vector_fold_right_dep_bounded_cut_down.
    apply vector_fold_right_dep_bounded_ext.
    apply vdrop_last_proper.
    apply veq_sym.
    apply vector_Sn_split.
    Unshelve.
    omega.
  Qed.

  Lemma vector_fold_right_Sn {A:Type} {B} (f:B->A->A) (init:A%nat) {m:nat} (v:Vector B (S m)) : vector_fold_right f init v = f (vlast v) (vector_fold_right f init (vdrop_last v)).
  Proof.
    unfold vector_fold_right.
    apply (@vector_fold_right_dep_Sn (fun _ => A)).
  Qed.
  
  Lemma vector_to_list_In {A} (x:A) {n} (v:Vector A n) :
    vin x v -> In x (vector_to_list v).
  Proof.
    induction n.
    - intros [[i pf] eqqi].
      omega.
    - intros [[i pf] eqqi].
      unfold vector_to_list in *.
      rewrite vector_fold_right_Sn; simpl.
      destruct (Nat.eq_dec i n).
      + left.
        unfold vlast.
        subst.
        erewrite index_pf_irrel; eauto.
      + right.
        apply IHn.
        eexists (exist _ i _).
        simpl.
        erewrite index_pf_irrel; eauto.
        
        Unshelve.
        simpl; omega.
  Qed.

  Lemma vin_cons {A} x (a:A) {n} {v:Vector A n} : vin x (vcons a v) <-> (x = a \/ vin x v).
  Proof.
    unfold vcons.
    split.
    - intros [[i pf] eqq].
      destruct (Nat.eq_dec i n).
      + subst; eauto.
      + right.
        eexists (exist _ i _).
        erewrite index_pf_irrel; eauto.
        
        Unshelve.
        simpl; omega.
    - intros [eqq | inn].
      + red.
        eexists (exist _ n _).
        destruct (Nat.eq_dec n n); congruence.
      + destruct inn as [[i pf] eqq].
        eexists (exist _ i _).
        destruct (Nat.eq_dec i n); [omega | ].
        erewrite index_pf_irrel; eauto.
        Unshelve.
        simpl; omega.
        simpl; omega.
  Qed.        

  Lemma vin_proper {A} (x:A) {n} {v1 v2:Vector A n} : v1 =v= v2 -> vin x v1 <-> vin x v2.
  Proof.
    revert v1 v2.
    cut (forall (v1 v2:Vector A n), v1 =v= v2 -> vin x v1 -> vin x v2).
    { intros; split; [eauto| ].
      apply veq_sym in H0; eauto.
    }
    intros v1 v2 eqq1 [i eqq2].
    exists i.
    rewrite <- eqq1; trivial.
  Qed.
    
  Lemma vector_to_list_vin {A} (x:A) {n} (v:Vector A n) :
    In x (vector_to_list v) -> vin x v.
  Proof.
    unfold vector_to_list.
    revert v.
    induction n; [simpl; tauto|].
    intros v inn.
    rewrite vector_fold_right_Sn in inn.
    destruct inn as [eqq | inn].
    - eexists.
      apply eqq.
    - apply (@vin_proper A _ (S n) _ _ (vector_Sn_split v)).
      apply vin_cons.
      eauto.
  Qed.

  Section fv.

    Fixpoint df_free_variables {T} (f : DefinedFunction T) : list SubVar
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

    Definition df_closed {T} (f: DefinedFunction T) : Prop
      := match df_free_variables f with
         | nil => True
         | _ => False
         end.

    Lemma df_closed_nil {T} (f: DefinedFunction T) : df_closed f -> df_free_variables f = nil.
    Proof.
      unfold df_closed.
      destruct (df_free_variables f); tauto.
    Qed.

    Lemma vdrop_last_i {A} {n} (v:Vector A (S n)) i pf1 pf2 :
      vdrop_last v (exist (fun n' : nat => (n' < n)%nat) i pf1) =
      v (exist (fun n' : nat => (n' < S n)%nat) i pf2).
    Proof.
      unfold vdrop_last.
      erewrite index_pf_irrel; eauto.
    Qed.

    
    Lemma vmap_nth {A B : Type} (f : A -> B) {n} (v : Vector A n) i : 
      vmap f v i = f (v i).
    Proof.
      revert v i.
      unfold vmap.
      induction n; intros v [i pf].
      - omega.
      - rewrite vector_fold_right_dep_Sn.
        simpl.
        destruct (Nat.eq_dec i n).
        + subst.
          unfold vlast.
          erewrite index_pf_irrel; eauto.
        + specialize (IHn (vdrop_last v)).
          unfold vdrop_last.
          erewrite index_pf_irrel; rewrite IHn.
          erewrite vdrop_last_i; eauto.
          Unshelve.
          omega.
    Qed.

(*
    Lemma vin_vmap {A B : Type} (f : A -> B) {n} (v : Vector A n) (y : B) :
      vin y (vmap f v) -> (exists x : A, f x = y /\ vin x v).
    Proof.
      intros [i ieq].
      unfold vin.
      unfold vector_fold_right_dep.
      induction n; simpl; intros.
    Qed.
*)
    Require Import FunctionalExtensionality.

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

    Fixpoint df_apply {T} (e: DefinedFunction T) 
             (args: forall (v:var_type),  DefinedFunction (snd v)) : @DefinedFunction UnitAnn T :=
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
  
  Lemma MaxDerivedMax_eq (a b : @DefinedFunction floatish_R UnitAnn DTfloat) :
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

   Lemma backpropeq1 (x : SubVar) (env : df_env) :
      let xvar := (x, DTfloat) in 
      let dfexpr := (@Var _ UnitAnn xvar tt) in
      df_eval_deriv env dfexpr xvar  =  
      backprop_lookup (df_eval_backprop_deriv env dfexpr ((mk_env_entry xvar 0%R)::nil) 1%R)
                      (x, DTfloat).
   Proof.
     simpl.
     destruct (var_dec x x); [| congruence].
     simpl.
     case_eq (@equiv_dec var_type _ _ _ (x, DTfloat) (x, DTfloat)); [| congruence]; intros.
     simpl.
     rewrite H.
     f_equal.
     unfold addvar, vartlookup_obligation_1 .
     simpl.
     rewrite H.
     rewrite (var_type_UIP_refl e0).
     simpl.
     lra.
   Qed.

   Lemma backpropeq2 (x : SubVar) (env : df_env) :
      let xvar := (x, DTfloat) in 
      let dfexpr := (@Square _ UnitAnn tt (@Var _ UnitAnn xvar tt)) in
      df_eval_deriv env dfexpr xvar  =  
      backprop_lookup (df_eval_backprop_deriv env dfexpr ((mk_env_entry xvar 0%R)::nil) 1%R)
                      xvar.
   Proof.
     simpl.
     destruct (vartlookup env (x, DTfloat)); simpl; trivial.
     destruct (var_dec x x); [| congruence].
     simpl.
     case_eq (@equiv_dec var_type _ _ _ (x, DTfloat) (x, DTfloat)); [| congruence]; intros.
     unfold addvar, vartlookup_obligation_1.
     simpl.
     rewrite H.
     unfold addvar, vartlookup_obligation_1.
     simpl.
     rewrite (var_type_UIP_refl e0).
     simpl.
     f_equal.
     lra.
   Qed.

   Lemma backpropeq_gen (x : SubVar) (env gradenv : df_env) (dfexpr : @DefinedFunction _ UnitAnn DTfloat) (grad : float) :
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
     revert grad gradenv.
     pattern dfexpr.
     revert dfexpr is_scalar.
     apply is_scalar_function_ind; simpl.
     - intros _ _ grad gradenv xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - intros _ _ grad gradenv xinn.
       destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; [| tauto]; lra.
     - intros sv _ grad gradenv xinn.
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
     - intros _ l r IHl IHr grad gradenv xinn.
       case_eq (df_eval_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * specialize (IHl grad gradenv xinn).
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
           specialize (IHr grad ge').
           cut_to IHr; [ | congruence ].
           rewrite xv'eqq in IHr.
           destruct (backprop_lookup (df_eval_backprop_deriv env r ge' grad) (x, DTfloat)); trivial.
           lra.
         * case_eq ( df_eval_backprop_deriv env l gradenv grad ); simpl; trivial; intros.
           apply IHr.
           apply (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv xinn).
         case_eq (df_eval_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
         destruct (vartlookup d (x, DTfloat)); tauto.
   Admitted.
       
 Lemma tree_backpropeq_gen (x : SubVar) (env gradenv : df_env) 
       (dfexpr : @DefinedFunction _ EvalAnn DTfloat) (grad : float) :
   let xvar := (x, DTfloat) in 
   is_scalar_function dfexpr ->
   match df_eval_tree_deriv env dfexpr xvar, 
         backprop_lookup (Some gradenv) xvar,
         backprop_lookup (df_eval_tree_backprop_deriv env dfexpr gradenv (xvar::nil) grad) xvar
      with
      | Some dval, Some bval0, Some bval1 => (dval*grad + bval0)%R = bval1
      | None, _, None => True
      | _, _, _ => False
      end.
   Proof.
     simpl.
     revert dfexpr.
     apply is_scalar_function_ind; simpl.
     - destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; lra.
     - destruct (vartlookup gradenv (x, DTfloat)); simpl; intros; lra.
     - intros sv _.
       destruct (var_dec x sv); simpl.
       + destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (x, DTfloat)); [| congruence].
         subst.
         rewrite lookup_update.
         unfold addvar; simpl.
         case_eq (vartlookup gradenv (sv, DTfloat)); simpl; intros; lra.
       + destruct (@equiv_dec var_type _ _ _ (sv, DTfloat) (x, DTfloat)); [congruence | ].
         case_eq (vartlookup gradenv (x, DTfloat)); simpl; intros; lra.
     - intros _ l r IHl IHr.
       case_eq (df_eval_tree_deriv env l (x, DTfloat))
       ; [intros dl eqdl | intros eqdl]
       ; rewrite eqdl in IHl.
       + case_eq (df_eval_tree_deriv env r (x, DTfloat))
         ; [intros dr eqdr | intros eqdr]
         ; rewrite eqdr in IHr.
         * admit.
         * destruct ( df_eval_backprop_deriv env l gradenv ((x, DTfloat) :: Datatypes.nil) grad)
           ; simpl in *; trivial.
           
   Admitted.
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
