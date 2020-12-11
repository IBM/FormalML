Require Import String.
Require Import EquivDec.
Require Import RelationClasses.
Require Import List.
Require Import Permutation.
Require Import NPeano.
Require Import Lra Lia.
Require Reals.
Require Import Eqdep_dec.

Require Import Floatish.
Require Import Utils.
Require Import derivlemmas.
Require VectorDef.
Require Import nvector.

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
        | DTVector n => vector float n
        | DTMatrix m n => matrix float m n
        end.

    Inductive data_type : definition_function_types -> Type
     := DataFloat : data_type DTfloat
     | DataVector n (v:vector float n) : data_type (DTVector n)
     | DataMatrix m n (mat:matrix float m n) : data_type (DTMatrix m n).

    Definition var_type := (SubVar * definition_function_types)%type.
    
    Definition definition_function_types_dec : forall v1 v2 : definition_function_types, {v1 = v2} + {v1 <> v2}.
    Proof.
      decide equality; apply Nat.eq_dec.
    Defined.

    Definition vart_dec : forall v1 v2 : var_type, {v1 = v2} + {v1 <> v2}.
    Proof.
      decide equality.
      - apply definition_function_types_dec.
      - apply var_dec.
    Defined.

    Global Instance vart_eqdec : EqDec var_type eq. 
    Proof.
      intros ??.
      apply vart_dec.
    Defined.

    Lemma var_type_UIP_refl {x:var_type} (e:x=x) : e = eq_refl x.
    Proof.
      apply (UIP_dec vart_dec).
    Qed.

    Lemma definition_function_types_UIP_refl {x:definition_function_types} (e:x=x) : e = eq_refl x.
    Proof.
      apply (UIP_dec definition_function_types_dec).
    Qed.

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

    | DVector {n} (ann:Ann (DTVector n)) (x : vector (DefinedFunction DTfloat) n) : DefinedFunction (DTVector n)

    | DMatrix {n m} (ann:Ann (DTMatrix n m)) (x : matrix (DefinedFunction DTfloat) n m) : DefinedFunction (DTMatrix n m)


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
    | VLossfun {n} (ann:Ann DTfloat) (v1 v2:SubVar) (s:@DefinedFunction UnitAnn DTfloat) (l: DefinedFunction (DTVector n)) (r:vector float n) : DefinedFunction DTfloat
    | MLossfun {m n} (ann:Ann DTfloat) (v1 v2:SubVar) (s:@DefinedFunction UnitAnn DTfloat) (l: DefinedFunction (DTMatrix m n)) (r:matrix float m n) : DefinedFunction DTfloat
    .

    Global Arguments DefinedFunction : clear implicits.


Definition DefinedFunction_ind_unit
  (P : forall (d : definition_function_types), DefinedFunction UnitAnn d -> Prop)
  (f : forall (ann : UnitAnn DTfloat) (x : float),
       P DTfloat (Number ann x))
  (f0 : forall (t : definition_function_types) 
          (ann : UnitAnn t) (x : definition_function_types_interp t), P t (Constant ann x))
  (f1 : forall (n : nat) (ann : UnitAnn (DTVector n))
          (x : vector (DefinedFunction UnitAnn DTfloat) n)
          (f: vforall (P DTfloat) x),
         P (DTVector n) (DVector ann x))
  (f2 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
          (x : matrix (DefinedFunction UnitAnn DTfloat) n m)
          (f: mforall (P DTfloat) x),
         P (DTMatrix n m) (DMatrix ann x))
  (f3 : forall (v : var_type) (ann : UnitAnn (snd v)),
        P (snd v) (Var v ann))
  (f4 : forall (ann : UnitAnn DTfloat)
          (l : DefinedFunction UnitAnn DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Plus ann l r))
  (f5 : forall (ann : UnitAnn DTfloat)
          (l : DefinedFunction UnitAnn DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Minus ann l r))
  (f6 : forall (ann : UnitAnn DTfloat)
          (l : DefinedFunction UnitAnn DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Times ann l r))
  (f7 : forall (ann : UnitAnn DTfloat)
          (l : DefinedFunction UnitAnn DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Divide ann l r))
  (f8 : forall (ann : UnitAnn DTfloat)
          (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Square ann e))
  (f9 : forall (ann : UnitAnn DTfloat)
          (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Exp ann e))
  (f10 : forall (ann : UnitAnn DTfloat)
           (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Log ann e))
  (f11 : forall (ann : UnitAnn DTfloat)
           (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Abs ann e))
  (f12 : forall (ann : UnitAnn DTfloat)
           (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Sign ann e))
  (f13 : forall (ann : UnitAnn DTfloat)
           (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (PSign ann e))
  (f14 : forall (ann : UnitAnn DTfloat)
           (l : DefinedFunction UnitAnn DTfloat),
         P DTfloat l ->
         forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Max ann l r))
  (f15 : forall (n : nat) (ann : UnitAnn DTfloat)
           (l : DefinedFunction UnitAnn (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction UnitAnn (DTVector n),
         P (DTVector n) r -> P DTfloat (VectorDot ann l r))
  (f16 : forall (n : nat) (ann : UnitAnn DTfloat)
           (v : DefinedFunction UnitAnn (DTVector n)), P (DTVector n) v -> P DTfloat (VectorSum ann v))
  (f17 : forall (m n : nat) (ann : UnitAnn DTfloat)
           (v : DefinedFunction UnitAnn (DTMatrix m n)),
         P (DTMatrix m n) v -> P DTfloat (MatrixSum ann v))
  (f18 : forall (n : nat) (ann : UnitAnn DTfloat)
           (l : DefinedFunction UnitAnn (DTVector n)),
         P (DTVector n) l ->
         forall i : {x : nat | (x < n)%nat}, P DTfloat (VectorElem ann l i))
  (f19 : forall (m n : nat) (ann : UnitAnn DTfloat)
           (l : DefinedFunction UnitAnn (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall (i : {x : nat | (x < m)%nat}) (j : {x : nat | (x < n)%nat}),
         P DTfloat (MatrixElem ann l i j))
  (f20 : forall (m n : nat) (ann : UnitAnn (DTVector m))
           (l : DefinedFunction UnitAnn (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall r : DefinedFunction UnitAnn (DTVector n),
         P (DTVector n) r -> P (DTVector m) (MatrixVectorMult ann l r))
  (f21 : forall (m n : nat) (ann : UnitAnn (DTMatrix m n))
           (l : DefinedFunction UnitAnn (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall r : DefinedFunction UnitAnn (DTVector m),
         P (DTVector m) r -> P (DTMatrix m n) (MatrixVectorAdd ann l r))
  (f22 : forall (m p n : nat) (ann : UnitAnn (DTMatrix m n))
           (l : DefinedFunction UnitAnn (DTMatrix m p)),
         P (DTMatrix m p) l ->
         forall r : DefinedFunction UnitAnn (DTMatrix p n),
         P (DTMatrix p n) r -> P (DTMatrix m n) (MatrixMult ann l r))
  (f23 : forall (n : nat) (ann : UnitAnn (DTVector n))
           (l : DefinedFunction UnitAnn (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction UnitAnn (DTVector n),
         P (DTVector n) r -> P (DTVector n) (VectorPlus ann l r))
  (f24 : forall (n : nat) (ann : UnitAnn (DTVector n))
           (l : DefinedFunction UnitAnn (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction UnitAnn (DTVector n),
         P (DTVector n) r -> P (DTVector n) (VectorMinus ann l r))
  (f25 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
           (l : DefinedFunction UnitAnn (DTMatrix n m)),
         P (DTMatrix n m) l ->
         forall r : DefinedFunction UnitAnn (DTMatrix n m),
         P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixPlus ann l r))
  (f26 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
           (l : DefinedFunction UnitAnn (DTMatrix n m)),
         P (DTMatrix n m) l ->
         forall r : DefinedFunction UnitAnn (DTMatrix n m),
         P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixMinus ann l r))
  (f27 : forall (n : nat) (ann : UnitAnn (DTVector n))
           (x : DefinedFunction UnitAnn DTfloat),
         P DTfloat x ->
         forall l : DefinedFunction UnitAnn (DTVector n),
         P (DTVector n) l -> P (DTVector n) (VectorScalMult ann x l))
  (f28 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
           (x : DefinedFunction UnitAnn DTfloat),
         P DTfloat x ->
         forall l : DefinedFunction UnitAnn (DTMatrix n m),
         P (DTMatrix n m) l -> P (DTMatrix n m) (MatrixScalMult ann x l))
  (f29 : forall (n : nat) (ann : UnitAnn (DTVector n))
           (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
      P DTfloat s ->
         forall l : DefinedFunction UnitAnn (DTVector n),
         P (DTVector n) l -> P (DTVector n) (VectorApply ann v s l))
  (f30 : forall (m n : nat) (ann : UnitAnn (DTMatrix m n))
           (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         P DTfloat s ->
         forall l : DefinedFunction UnitAnn (DTMatrix m n),
         P (DTMatrix m n) l -> P (DTMatrix m n) (MatrixApply ann v s l))
  (f31 : forall (n : nat) (ann : UnitAnn DTfloat)
           (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         P DTfloat s ->
         forall l : DefinedFunction UnitAnn (DTVector n),
         P (DTVector n) l -> forall r : vector float n, P DTfloat (VLossfun ann v1 v2 s l r))
  (f32 : forall (m n : nat) (ann : UnitAnn DTfloat)
           (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         P DTfloat s ->
         forall l : DefinedFunction UnitAnn (DTMatrix m n),
         P (DTMatrix m n) l ->
         forall r : matrix float m n, P DTfloat (MLossfun ann v1 v2 s l r))
  := 
fix
F (d : definition_function_types) 
  (d0 : DefinedFunction UnitAnn d) {struct d0} : P d d0 :=
  match d0 as d2 in (DefinedFunction _ d1) return (P d1 d2) with
  | Number ann x => f ann x
  | @Constant _ t ann x => f0 t ann x
  | @DVector _ n ann x => 
    f1 n ann x        
       ((fix F1 n (x:vector (DefinedFunction UnitAnn DTfloat) n)  : vforall (P DTfloat) x :=
           match x with
           | Vector.nil => Vector.Forall_nil (P DTfloat)
           | Vector.cons h _ tl => Vector.Forall_cons _ _ _ (F DTfloat h) (F1 _ tl)
           end) n x)
  | @DMatrix _ n m ann x =>
    f2 n m ann x
       ((fix F2 n m (x:matrix (DefinedFunction UnitAnn DTfloat) n m)  : mforall (P DTfloat) x :=
           match x with
           | Vector.nil => Vector.Forall_nil (vforall (P DTfloat))

           | Vector.cons h _ tl => 
             Vector.Forall_cons _ _ _ 
                                ((fix F1 m (x:vector (DefinedFunction UnitAnn DTfloat) m)  : vforall (P DTfloat) x :=
                                    match x with
                                    | Vector.nil => Vector.Forall_nil (P DTfloat)
                                    | Vector.cons h _ tl => Vector.Forall_cons _ _ _ (F DTfloat h) (F1 _ tl)
                                    end) m h)
                                (F2 _ _ tl)
           end) n m x)
  | Var v ann => f3 v ann
  | Plus ann l r => f4 ann l (F DTfloat l) r (F DTfloat r)
  | Minus ann l r => f5 ann l (F DTfloat l) r (F DTfloat r)
  | Times ann l r => f6 ann l (F DTfloat l) r (F DTfloat r)
  | Divide ann l r => f7 ann l (F DTfloat l) r (F DTfloat r)
  | Square ann e => f8 ann e (F DTfloat e)
  | Exp ann e => f9 ann e (F DTfloat e)
  | Log ann e => f10 ann e (F DTfloat e)
  | Abs ann e => f11 ann e (F DTfloat e)
  | Sign ann e => f12 ann e (F DTfloat e)
  | PSign ann e => f13 ann e (F DTfloat e)
  | Max ann l r => f14 ann l (F DTfloat l) r (F DTfloat r)
  | @VectorDot _ n ann l r => f15 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @VectorSum _ n ann v => f16 n ann v (F (DTVector n) v)
  | @MatrixSum _ m n ann v => f17 m n ann v (F (DTMatrix m n) v)
  | @VectorElem _ n ann l i => f18 n ann l (F (DTVector n) l) i
  | @MatrixElem _ m n ann l i j => f19 m n ann l (F (DTMatrix m n) l) i j
  | @MatrixVectorMult _ m n ann l r =>
      f20 m n ann l (F (DTMatrix m n) l) r (F (DTVector n) r)
  | @MatrixVectorAdd _ m n ann l r =>
      f21 m n ann l (F (DTMatrix m n) l) r (F (DTVector m) r)
  | @MatrixMult _ m p n ann l r =>
      f22 m p n ann l (F (DTMatrix m p) l) r (F (DTMatrix p n) r)
  | @VectorPlus _ n ann l r => f23 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @VectorMinus _ n ann l r => f24 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @MatrixPlus _ n m ann l r => f25 n m ann l (F (DTMatrix n m) l) r (F (DTMatrix n m) r)
  | @MatrixMinus _ n m ann l r =>
      f26 n m ann l (F (DTMatrix n m) l) r (F (DTMatrix n m) r)
  | @VectorScalMult _ n ann x l => f27 n ann x (F DTfloat x) l (F (DTVector n) l)
  | @MatrixScalMult _ n m ann x l => f28 n m ann x (F DTfloat x) l (F (DTMatrix n m) l)
  | @VectorApply _ n ann v s l => f29 n ann v s (F DTfloat s) l (F (DTVector n) l)
  | @MatrixApply _ m n ann v s l =>
      f30 m n ann v s (F DTfloat s) l (F (DTMatrix m n) l)
  | @VLossfun _ n ann v1 v2 s l r =>
      f31 n ann v1 v2 s (F DTfloat s) l (F (DTVector n) l) r
  | @MLossfun _ m n ann v1 v2 s l r =>
      f32 m n ann v1 v2 s (F DTfloat s) l (F (DTMatrix m n) l) r
  end.

Definition DefinedFunction_ind_simpl {Ann}
  (P : forall (d : definition_function_types), DefinedFunction Ann d -> Prop)
  (f : forall (ann : Ann DTfloat) (x : float),
       P DTfloat (Number ann x))
  (f0 : forall (t : definition_function_types) 
          (ann : Ann t) (x : definition_function_types_interp t), P t (Constant ann x))
  (f1 : forall (n : nat) (ann : Ann (DTVector n))
          (x : vector (DefinedFunction Ann DTfloat) n)
          (f: vforall (P DTfloat) x),
        P (DTVector n) (DVector ann x))
  (f2 : forall (n m : nat) (ann : Ann (DTMatrix n m))
          (x : matrix (DefinedFunction Ann DTfloat) n m)
          (f: mforall (P DTfloat) x),
         P (DTMatrix n m) (DMatrix ann x))
  (f3 : forall (v : var_type) (ann : Ann (snd v)),
        P (snd v) (Var v ann))
  (f4 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Plus ann l r))
  (f5 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Minus ann l r))
  (f6 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Times ann l r))
  (f7 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Divide ann l r))
  (f8 : forall (ann : Ann DTfloat)
          (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Square ann e))
  (f9 : forall (ann : Ann DTfloat)
          (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Exp ann e))
  (f10 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Log ann e))
  (f11 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Abs ann e))
  (f12 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Sign ann e))
  (f13 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (PSign ann e))
  (f14 : forall (ann : Ann DTfloat)
           (l : DefinedFunction Ann DTfloat),
         P DTfloat l ->
         forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Max ann l r))
  (f15 : forall (n : nat) (ann : Ann DTfloat)
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P DTfloat (VectorDot ann l r))
  (f16 : forall (n : nat) (ann : Ann DTfloat)
           (v : DefinedFunction Ann (DTVector n)), P (DTVector n) v -> P DTfloat (VectorSum ann v))
  (f17 : forall (m n : nat) (ann : Ann DTfloat)
           (v : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) v -> P DTfloat (MatrixSum ann v))
  (f18 : forall (n : nat) (ann : Ann DTfloat)
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall i : {x : nat | (x < n)%nat}, P DTfloat (VectorElem ann l i))
  (f19 : forall (m n : nat) (ann : Ann DTfloat)
           (l : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall (i : {x : nat | (x < m)%nat}) (j : {x : nat | (x < n)%nat}),
         P DTfloat (MatrixElem ann l i j))
  (f20 : forall (m n : nat) (ann : Ann (DTVector m))
           (l : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P (DTVector m) (MatrixVectorMult ann l r))
  (f21 : forall (m n : nat) (ann : Ann (DTMatrix m n))
           (l : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall r : DefinedFunction Ann (DTVector m),
         P (DTVector m) r -> P (DTMatrix m n) (MatrixVectorAdd ann l r))
  (f22 : forall (m p n : nat) (ann : Ann (DTMatrix m n))
           (l : DefinedFunction Ann (DTMatrix m p)),
         P (DTMatrix m p) l ->
         forall r : DefinedFunction Ann (DTMatrix p n),
         P (DTMatrix p n) r -> P (DTMatrix m n) (MatrixMult ann l r))
  (f23 : forall (n : nat) (ann : Ann (DTVector n))
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P (DTVector n) (VectorPlus ann l r))
  (f24 : forall (n : nat) (ann : Ann (DTVector n))
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P (DTVector n) (VectorMinus ann l r))
  (f25 : forall (n m : nat) (ann : Ann (DTMatrix n m))
           (l : DefinedFunction Ann (DTMatrix n m)),
         P (DTMatrix n m) l ->
         forall r : DefinedFunction Ann (DTMatrix n m),
         P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixPlus ann l r))
  (f26 : forall (n m : nat) (ann : Ann (DTMatrix n m))
           (l : DefinedFunction Ann (DTMatrix n m)),
         P (DTMatrix n m) l ->
         forall r : DefinedFunction Ann (DTMatrix n m),
         P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixMinus ann l r))
  (f27 : forall (n : nat) (ann : Ann (DTVector n))
           (x : DefinedFunction Ann DTfloat),
         P DTfloat x ->
         forall l : DefinedFunction Ann (DTVector n),
         P (DTVector n) l -> P (DTVector n) (VectorScalMult ann x l))
  (f28 : forall (n m : nat) (ann : Ann (DTMatrix n m))
           (x : DefinedFunction Ann DTfloat),
         P DTfloat x ->
         forall l : DefinedFunction Ann (DTMatrix n m),
         P (DTMatrix n m) l -> P (DTMatrix n m) (MatrixScalMult ann x l))
  (f29 : forall (n : nat) (ann : Ann (DTVector n))
           (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTVector n),
         P (DTVector n) l -> P (DTVector n) (VectorApply ann v s l))
  (f30 : forall (m n : nat) (ann : Ann (DTMatrix m n))
           (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTMatrix m n),
         P (DTMatrix m n) l -> P (DTMatrix m n) (MatrixApply ann v s l))
  (f31 : forall (n : nat) (ann : Ann DTfloat)
           (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTVector n),
         P (DTVector n) l -> forall r : vector float n, P DTfloat (VLossfun ann v1 v2 s l r))
  (f32 : forall (m n : nat) (ann : Ann DTfloat)
           (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTMatrix m n),
         P (DTMatrix m n) l ->
         forall r : matrix float m n, P DTfloat (MLossfun ann v1 v2 s l r))
  := 
fix
F (d : definition_function_types) 
  (d0 : DefinedFunction Ann d) {struct d0} : P d d0 :=
  match d0 as d2 in (DefinedFunction _ d1) return (P d1 d2) with
  | Number ann x => f ann x
  | @Constant _ t ann x => f0 t ann x
  | @DVector _ n ann x => 
    f1 n ann x        
       ((fix F1 n (x:vector (DefinedFunction Ann DTfloat) n)  : vforall (P DTfloat) x :=
           match x with
           | Vector.nil => Vector.Forall_nil (P DTfloat)
           | Vector.cons h _ tl => Vector.Forall_cons _ _ _ (F DTfloat h) (F1 _ tl)
           end) n x)
  | @DMatrix _ n m ann x =>
    f2 n m ann x
       ((fix F2 n m (x:matrix (DefinedFunction Ann DTfloat) n m)  : mforall (P DTfloat) x :=
           match x with
           | Vector.nil => Vector.Forall_nil (vforall (P DTfloat))

           | Vector.cons h _ tl => 
             Vector.Forall_cons _ _ _ 
                                ((fix F1 m (x:vector (DefinedFunction Ann DTfloat) m)  : vforall (P DTfloat) x :=
                                    match x with
                                    | Vector.nil => Vector.Forall_nil (P DTfloat)
                                    | Vector.cons h _ tl => Vector.Forall_cons _ _ _ (F DTfloat h) (F1 _ tl)
                                    end) m h)
                                (F2 _ _ tl)
           end) n m x)
  | Var v ann => f3 v ann
  | Plus ann l r => f4 ann l (F DTfloat l) r (F DTfloat r)
  | Minus ann l r => f5 ann l (F DTfloat l) r (F DTfloat r)
  | Times ann l r => f6 ann l (F DTfloat l) r (F DTfloat r)
  | Divide ann l r => f7 ann l (F DTfloat l) r (F DTfloat r)
  | Square ann e => f8 ann e (F DTfloat e)
  | Exp ann e => f9 ann e (F DTfloat e)
  | Log ann e => f10 ann e (F DTfloat e)
  | Abs ann e => f11 ann e (F DTfloat e)
  | Sign ann e => f12 ann e (F DTfloat e)
  | PSign ann e => f13 ann e (F DTfloat e)
  | Max ann l r => f14 ann l (F DTfloat l) r (F DTfloat r)
  | @VectorDot _ n ann l r => f15 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @VectorSum _ n ann v => f16 n ann v (F (DTVector n) v)
  | @MatrixSum _ m n ann v => f17 m n ann v (F (DTMatrix m n) v)
  | @VectorElem _ n ann l i => f18 n ann l (F (DTVector n) l) i
  | @MatrixElem _ m n ann l i j => f19 m n ann l (F (DTMatrix m n) l) i j
  | @MatrixVectorMult _ m n ann l r =>
      f20 m n ann l (F (DTMatrix m n) l) r (F (DTVector n) r)
  | @MatrixVectorAdd _ m n ann l r =>
      f21 m n ann l (F (DTMatrix m n) l) r (F (DTVector m) r)
  | @MatrixMult _ m p n ann l r =>
      f22 m p n ann l (F (DTMatrix m p) l) r (F (DTMatrix p n) r)
  | @VectorPlus _ n ann l r => f23 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @VectorMinus _ n ann l r => f24 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @MatrixPlus _ n m ann l r => f25 n m ann l (F (DTMatrix n m) l) r (F (DTMatrix n m) r)
  | @MatrixMinus _ n m ann l r =>
      f26 n m ann l (F (DTMatrix n m) l) r (F (DTMatrix n m) r)
  | @VectorScalMult _ n ann x l => f27 n ann x (F DTfloat x) l (F (DTVector n) l)
  | @MatrixScalMult _ n m ann x l => f28 n m ann x (F DTfloat x) l (F (DTMatrix n m) l)
  | @VectorApply _ n ann v s l => f29 n ann v s l (F (DTVector n) l)
  | @MatrixApply _ m n ann v s l =>
      f30 m n ann v s l (F (DTMatrix m n) l)
  | @VLossfun _ n ann v1 v2 s l r =>
      f31 n ann v1 v2 s l (F (DTVector n) l) r
  | @MLossfun _ m n ann v1 v2 s l r =>
      f32 m n ann v1 v2 s l (F (DTMatrix m n) l) r
  end.
    
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


    Ltac refl_simpler := 
      repeat
        match goal with
        | [H: @eq var_type _ _ |- _ ] => try (inversion H; subst); rewrite (var_type_UIP_refl H)
        | [H: @equiv var_type _ _ _ _ |- _ ] => try (inversion H; subst); rewrite (var_type_UIP_refl H)
        | [H: @eq definition_function_types _ _ |- _ ] => try (inversion H; subst); rewrite (definition_function_types_UIP_refl H)
        | [H: @equiv definition_function_types _ _ _ _ |- _ ] => try (inversion H; subst); rewrite (definition_function_types_UIP_refl H)
        end.


  Definition df_plus  (df1 df2 : DefinedFunction UnitAnn DTfloat) : DefinedFunction UnitAnn DTfloat :=
    Plus tt df1 df2.

  Definition df_times (df1 df2 : DefinedFunction UnitAnn DTfloat) : DefinedFunction UnitAnn DTfloat :=
    Times tt df1 df2.

  Definition defined_sum {m} (v:vector (DefinedFunction UnitAnn DTfloat) m) : DefinedFunction UnitAnn DTfloat
    := Vector.fold_right (fun a b => Plus tt a b) v (Number tt 0).

  Definition vsum {m:nat} (v:vector float m) : float
      := Vector.fold_right Fplus v 0.

  Definition msum {m n:nat} (v:matrix float m n) : float :=
    vsum (vmap vsum v).

  Definition transpose {A} {n m:nat} (mat:matrix A n m) :=
    build_matrix (fun i j => mnth mat j i).

(* defined in nvector
  Definition matrix_vector_mult {n m} (l : Matrix float n m)(r : vector float m) : vector float n :=
      fun i => vsum (fun j => (l i j) * (r j)).

  Definition matrix_vector_add {n m} (l : Matrix float n m) (r : vector float n) : Matrix float n m := fun i j => (l i j) + (r i).

  Definition matrix_mult {n m p} (l : Matrix float n m)(r : Matrix float m p) : Matrix float n p :=
      fun i k => vsum (fun j => (l i j) * (r j k)).
*)

 Section deriv.
    

   Section subst.
     
     Definition substvar {Ann} (v vv:var_type) (e':DefinedFunction Ann (snd v)) (e:DefinedFunction Ann (snd vv)) : (DefinedFunction Ann (snd vv)) :=
      match snd v == snd vv  with
      | left pf => eq_rect _ (fun t => DefinedFunction Ann t) e' _ pf
      | right pf => e
      end.

 Fixpoint df_subst {T Ann} (df: DefinedFunction Ann T) (v:var_type) (e':DefinedFunction UnitAnn (snd v)) {struct df}  :=
      match df with
      | Number _ x => Number tt x
      | Constant t _ x => Constant tt x
      | DVector n _ df => DVector tt (vmap (fun x => df_subst x v e') df)
      | DMatrix n m _ df => DMatrix tt (mmap (fun x => df_subst x v e') df)
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
        VectorApply tt x s (df_subst l v e')
      | MatrixApply n m _ x s l => 
        MatrixApply tt x s (df_subst l v e')
      | VLossfun n _ v1 v2 s l r =>
        VLossfun tt v1 v2 s (df_subst l v e') r
      | MLossfun n m _ v1 v2 s l r =>
        MLossfun tt v1 v2 s (df_subst l v e') r
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
          | DVector n _ df => DVector tt (vmap (fun x => df_deriv x v) df)
          | DMatrix n m _ df => DMatrix tt (mmap (fun x => df_deriv x v) df)
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
          | Divide _ l r => Minus tt
                              (Divide tt (df_deriv l v) r)
                              (Divide tt (Times tt l (df_deriv r v))
                                      (Times tt r r))
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
            DVector tt (build_vector (fun i => Times tt (VectorElem tt rr i) (df_subst ss (x, DTfloat) (VectorElem tt r i))))
          | MatrixApply n m _ x s r => 
            let rr := df_deriv r v in
            let ss := df_deriv s (x, DTfloat) in
            DMatrix tt (build_matrix (fun i j => Times tt (MatrixElem tt rr i j) (df_subst ss (x, DTfloat) (MatrixElem tt r i j))))
          | VLossfun n _ v1 v2 s l r =>
            let ll := df_deriv l v in
            let ss := df_deriv s (v1, DTfloat) in
            VectorDot tt ll 
                      (DVector tt (build_vector (fun i => 
                                     df_subst (df_subst ss (v1, DTfloat) (VectorElem tt l i))
                                              (v2, DTfloat) (Number tt (vnth r i)))))
          | MLossfun n m _ v1 v2 s l r =>
            let ll := df_deriv l v in
            let ss := df_deriv s (v1, DTfloat) in
            MatrixSum tt
               (DMatrix tt 
                  (build_matrix (fun i j => 
                     (Divide tt 
                          (Times tt (MatrixElem tt ll i j)
                                 (df_subst (df_subst ss (v1, DTfloat) (MatrixElem tt l i j))
                                           (v2, DTfloat) (Number tt (mnth r i j))))
                     (Number tt (FfromZ (Z.of_nat m)))))))
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
         | DVector n _ dfs => vectoro_to_ovector (vmap (fun x => df_eval σ x) dfs)
         | DMatrix n m _ df => matrixo_to_omatrix (mmap (fun x => df_eval σ x) df)
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
           | Some l' => Some (vnth l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval σ l)  with
           | Some l' => Some (mnth l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some l', Some r' => Some (vsum (vmap2 Fmult l' r'))
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
           | Some x', Some r' => Some (vmap (fun rr => x' * rr) r')
           | _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval σ x, df_eval σ r with
           | Some x', Some r' => Some (mmap (fun rr => x' * rr) r')
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
           | Some l', Some r' => Some (vmap2 Fplus l' r')
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval σ l, df_eval σ r with           
           | Some l', Some r' => Some (vmap2 Fminus l' r')
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval σ l, df_eval σ r with           
           | Some l', Some r' => Some (mmap2 Fplus l' r')
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval σ l, df_eval σ r with           
           | Some l', Some r' => Some (mmap2 Fminus l' r')
           | _, _ => None
           end
         | VectorApply n _ x s r => 
           match df_eval σ r with           
           | Some r' => vectoro_to_ovector 
                          (vmap (fun re => 
                             let xv := (x, DTfloat):var_type in
                             df_eval (cons (mk_env_entry xv re) nil) s) r')
           | _ => None
           end
         | MatrixApply n m _ x s r => 
           match df_eval σ r with           
           | Some r' => matrixo_to_omatrix
                          (mmap (fun re => 
                             let xv := (x, DTfloat):var_type in
                             df_eval (cons (mk_env_entry xv re) nil) s) r')
           | _ => None
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_eval σ l with
           | Some l' => 
             match (vectoro_to_ovector 
                      (build_vector (fun i => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (vnth l' i)) 
                                       (cons (mk_env_entry xv2 (vnth r i)) nil)) s))) with
             | Some vv => Some (vsum vv)
             | _ => None
             end
           | _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           match df_eval σ l with
           | Some l' => 
             match (matrixo_to_omatrix
                      (build_matrix (fun i j => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (mnth l' i j)) 
                                       (cons (mk_env_entry xv2 (mnth r i j)) nil)) s))) with
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
           match vectoro_to_ovector (vmap (fun x => df_eval_tree σ x) dfs) with
           | Some val => Some (DVector (vmap get_annotation val) val)
           | _ => None
           end
         | DMatrix n m _ df => 
           match matrixo_to_omatrix (mmap (fun x => df_eval_tree σ x) df) with
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
                        Some (VectorElem (vnth vl' i) l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_tree σ l)  with
           | Some l' => let vl' := get_annotation l' in
                        Some (MatrixElem (mnth vl' i j) l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in 
                                 Some (VectorDot (vsum (build_vector (fun i => (vnth vl' i) * (vnth vr' i)))) l' r')
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
                                 let vec : vector float n := vmap (fun re => vx' * re) vr' in
                                 Some (VectorScalMult vec x' r')
           | _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval_tree σ x, df_eval_tree σ r with
           | Some x', Some r' => let vx' := get_annotation x' in
                                 let vr' := get_annotation r' in
                                 let mat : matrix float n m := mmap (fun re => vx' * re) vr' in
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
                                 let vec : vector float n := 
                                     vmap2 Fplus vl' vr' in
                                 Some (VectorPlus vec l' r')
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with           
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 let vec : vector float n := 
                                     vmap2 Fminus vl' vr' in
                                 Some (VectorMinus vec l' r')
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with           
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 let mat : matrix float n m := 
                                     mmap2 Fplus vl' vr' in
                                 Some (MatrixPlus mat l' r')
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_tree σ l, df_eval_tree σ r with           
           | Some l', Some r' => let vl' := get_annotation l' in
                                 let vr' := get_annotation r' in
                                 let mat : matrix float n m := 
                                     mmap2 Fminus vl' vr' in
                                 Some (MatrixMinus mat l' r')
           | _, _ => None
           end

         | VectorApply n _ x s r => 
           match df_eval_tree σ r with           
           | Some r' => 
             let vr' := get_annotation r' in
             match vectoro_to_ovector 
                     (build_vector (fun i => 
                        let xv := (x, DTfloat):var_type in
                        df_eval (cons (mk_env_entry xv (vnth vr' i)) nil) s)) with
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
                     (build_matrix (fun i j => 
                        let xv := (x, DTfloat):var_type in
                        df_eval (cons (mk_env_entry xv (mnth vr' i j)) nil) s)) with
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
                      (build_vector (fun i => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (vnth vl' i)) 
                                       (cons (mk_env_entry xv2 (vnth r i)) nil)) s))) with
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
                      (build_matrix (fun i j => 
                         let xv1 := (v1,DTfloat):var_type in
                         let xv2 := (v2,DTfloat):var_type in
                         df_eval (cons (mk_env_entry xv1 (mnth vl' i j)) 
                                       (cons (mk_env_entry xv2 (mnth r i j)) nil)) s))) with
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
           | Some (l', dfevals') => Some (pair_update_evals (VectorElem tt l i) (vnth l' i) dfevals')
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_evals_list σ l dfevals)  with
           | Some (l', dfevals') => Some (pair_update_evals (MatrixElem tt l i j) (mnth l' i j) dfevals')
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (VectorDot tt l r) 
                                          (vsum (vmap2 Fmult l' r')) dfevals'')
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
                  Some (pair_update_evals (VectorScalMult tt l r) 
                                          (vmap (fun re => l' * re) r') dfevals'')
             | _ => None
             end
           | _ => None
           end
         | MatrixScalMult n m _ l r =>
           match df_evals_list σ l dfevals with
           | Some (l', dfevals') => 
             match df_evals_list σ r dfevals' with
               Some (r', dfevals'') => 
                  Some (pair_update_evals (MatrixScalMult tt l r) 
                                          (mmap (fun re => l' * re) r') dfevals'')
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
                                          (vmap2 Fplus l' r') dfevals'')
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
                                          (vmap2 Fminus l' r') dfevals'')
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
                                          (mmap2 Fplus l' r') dfevals'')
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
                                          (mmap2 Fminus l' r') dfevals'')
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

    Fixpoint df_eval_deriv {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v:var_type) : option (definition_function_types_interp T)
      := (match df with
         | Number _ _ => Some 0
         | Constant t _ x => Some
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
         | DVector n _ dfs => vectoro_to_ovector (vmap (fun xe => df_eval_deriv σ xe v) dfs)
         | DMatrix n m _ df => matrixo_to_omatrix (mmap (fun xe => df_eval_deriv σ xe v) df)
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
           | Some l' => Some (vnth l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_deriv σ l v)  with
           | Some l' => Some (mnth l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd => 
               Some (Fplus (vsum (vmap2 Fmult le rd)) (vsum (vmap2 Fmult ld re)))
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
           | Some xe, Some xd, Some re, Some rd => 
             Some (vmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _, _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval σ x, df_eval_deriv σ x v, df_eval σ r, df_eval_deriv σ r v with
           | Some xe, Some xd, Some re, Some rd => 
             Some (mmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _, _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (build_vector (fun i => vsum (vmap4 (fun lei rde ldi ree => lei * rde + ldi * ree)
                                        (vnth le i) rd (vnth ld i) re)))
           | _, _, _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with
           | Some ld, Some rd =>
             Some (build_matrix (fun i j => (mnth ld i j) + (vnth rd i)))
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           match df_eval σ l, df_eval_deriv σ l v, df_eval σ r, df_eval_deriv σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (build_matrix (fun i k => vsum (build_vector (fun j => (mnth le i j)*(mnth rd j k) + (mnth ld i j)*(mnth re j k)))))
           | _, _, _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (vmap2 Fplus l' r')
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (vmap2 Fminus l' r')
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (mmap2 Fplus l' r')
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_deriv σ l v, df_eval_deriv σ r v with           
           | Some l', Some r' => Some (mmap2 Fminus l' r')
           | _, _ => None
           end
         | VectorApply n _ x s r =>
           match df_eval σ r, df_eval_deriv σ r v with                      
           | Some re, Some rd => 
             vectoro_to_ovector 
               (build_vector (fun i => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (vnth re i)) nil) s xv with
                         | Some sd => Some ((vnth rd i) * sd)
                         | _ => None
                         end))
           | _, _ => None                                                    
           end
         | MatrixApply n m _ x s r =>
           match df_eval σ r, df_eval_deriv σ r v with                      
           | Some re, Some rd => 
             matrixo_to_omatrix
               (build_matrix (fun i j => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (mnth re i j)) nil) s xv with
                         | Some sd => Some ((mnth rd i j) * sd)
                         | _ => None
                         end))
           | _, _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_eval σ l, df_eval_deriv σ l v with                      
           | Some le, Some ld => 
             match (vectoro_to_ovector 
                      (build_vector (fun i => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (vnth le i)) 
                                                   (cons (mk_env_entry xv2 (vnth r i)) nil)) s xv1 with
                         | Some sd => Some ((vnth ld i) * sd)
                         | _ => None
                         end))) with
             | Some vv => Some (vsum vv)
             | _ => None
             end
           | _, _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           match df_eval σ l, df_eval_deriv σ l v with                      
           | Some le, Some ld => 
             match (matrixo_to_omatrix
                      (build_matrix (fun i j => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (mnth le i j)) 
                                                   (cons (mk_env_entry xv2 (mnth r i j)) nil)) s xv1 with
                         | Some sd => Some ((mnth ld i j) * sd)
                         | _ => None
                         end))) with
             | Some vv => Some ((msum vv)/(FfromZ (Z.of_nat m)))
             | _ => None
             end
           | _, _ => None
           end
          end).

    Definition mk_genvar_env (s:SubVar) := mk_env_entry (s, DTfloat) (FfromZ (Z.of_nat 1)) :: nil.

 (* the v environment below pairs variables with their derivatives *)
     (* in some sense this is giving a directional derivative defined by v *)
    Fixpoint df_eval_deriv_genvar {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v:df_env) : option (definition_function_types_interp T)
      := (match df with
         | Number _ _ => Some 0
         | Constant t _ x => Some
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
         | DVector n _ dfs => vectoro_to_ovector (vmap (fun df1 => df_eval_deriv_genvar σ df1 v) dfs)
         | DMatrix n m _ df => matrixo_to_omatrix (mmap (fun df1 => df_eval_deriv_genvar σ df1 v) df)
         | Var x _ => Some (
           match vartlookup v x with
           | Some val => val
           | _ => 
             match (snd x) with
             | DTfloat => 0
             | DTVector n => ConstVector n 0
             | DTMatrix m n => ConstMatrix m n 0
             end
           end)
         | Plus _ l r => 
           match df_eval_deriv_genvar σ l v, df_eval_deriv_genvar σ r v with
           | Some le, Some lr => Some (le + lr)
           | _, _ => None
           end
         | Minus _ l r =>
           match df_eval_deriv_genvar σ l v, df_eval_deriv_genvar σ r v with
           | Some le, Some lr => Some (le - lr)
           | _, _ => None
           end
         | Times _ l r =>
           match df_eval σ l, df_eval_deriv_genvar σ l v, df_eval σ r, df_eval_deriv_genvar σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (le * rd + 
                   (ld * re))
           | _, _, _, _ => None
           end
         | Divide _ l r =>
           match df_eval σ l, df_eval_deriv_genvar σ l v, df_eval σ r, df_eval_deriv_genvar σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some ((ld / re) - ((le * rd) / (re * re)))
           | _, _, _, _ => None
           end
         | Square _ e =>
           match df_eval σ e, df_eval_deriv_genvar σ e v with
           | Some ee, Some ed => Some (2 * ee * ed)
           | _, _  => None
           end
         | Exp _ e =>
           match df_eval σ e, df_eval_deriv_genvar σ e v with
           | Some ee, Some ed => Some (ed * Fexp ee)
           | _, _  => None
           end
         | Log _ e =>
           match df_eval σ e, df_eval_deriv_genvar σ e v with
           | Some ee, Some ed => Some (ed / ee)
           | _, _ => None
           end
         | Abs _ e =>
           match df_eval σ e, df_eval_deriv_genvar σ e v with
           | Some ee, Some ed => Some (ed * (sign ee))
           | _, _ => None
           end
         | Sign _ e =>
           match df_eval_deriv_genvar σ e v with
           | Some _ => Some 0
           | None => None
           end
         | PSign _ e =>
           match df_eval_deriv_genvar σ e v with
           | Some _ => Some 0
           | None => None
           end
         | Max _ l r =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some re =>
             if le <= re then df_eval_deriv_genvar σ r v else df_eval_deriv_genvar σ l v
           | _, _ => None
           end
         | VectorElem n _ l i => 
           match (df_eval_deriv_genvar σ l v)  with
           | Some l' => Some (vnth l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_deriv_genvar σ l v)  with
           | Some l' => Some (mnth l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           match df_eval σ l, df_eval_deriv_genvar σ l v, df_eval σ r, df_eval_deriv_genvar σ r v with
           | Some le, Some ld, Some re, Some rd => 
               Some (vsum (vmap4 (fun le1 rd1 ld1 re1 => le1 * rd1 + ld1 * re1) le rd ld re))
           | _, _, _, _ => None
           end
         | VectorSum n _ l =>
           match df_eval_deriv_genvar σ l v with
           | Some ld =>
               Some (vsum ld)
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_eval_deriv_genvar σ l v with
           | Some ld =>
               Some (msum ld)
           | _ => None
           end
         | VectorScalMult n _ x r =>
           match df_eval σ x, df_eval_deriv_genvar σ x v, df_eval σ r, df_eval_deriv_genvar σ r v with
           | Some xe, Some xd, Some re, Some rd => 
             Some (vmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _, _, _ => None
           end
         | MatrixScalMult n m _ x r =>            
           match df_eval σ x, df_eval_deriv_genvar σ x v, df_eval σ r, df_eval_deriv_genvar σ r v with
           | Some xe, Some xd, Some re, Some rd => 
             Some (mmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _, _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           match df_eval σ l, df_eval_deriv_genvar σ l v, df_eval σ r, df_eval_deriv_genvar σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (build_vector (fun i => vsum (vmap4 (fun lei rde ldi ree => lei * rde + ldi * ree)
                                        (vnth le i) rd (vnth ld i) re)))
           | _, _, _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_deriv_genvar σ l v, df_eval_deriv_genvar σ r v with
           | Some ld, Some rd =>
             Some (build_matrix (fun i j => (mnth ld i j) + (vnth rd i)))
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           match df_eval σ l, df_eval_deriv_genvar σ l v, df_eval σ r, df_eval_deriv_genvar σ r v with
           | Some le, Some ld, Some re, Some rd =>
             Some (build_matrix (fun i k => vsum (build_vector (fun j => (mnth le i j)*(mnth rd j k) + (mnth ld i j)*(mnth re j k)))))
           | _, _, _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_deriv_genvar σ l v, df_eval_deriv_genvar σ r v with           
           | Some l', Some r' => Some (vmap2 Fplus l' r')
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_deriv_genvar σ l v, df_eval_deriv_genvar σ r v with           
           | Some l', Some r' => Some (vmap2 Fminus l' r')
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_deriv_genvar σ l v, df_eval_deriv_genvar σ r v with           
           | Some l', Some r' => Some (mmap2 Fplus l' r')
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_deriv_genvar σ l v, df_eval_deriv_genvar σ r v with           
           | Some l', Some r' => Some (mmap2 Fminus l' r')
           | _, _ => None
           end
         | VectorApply n _ x s r =>
           match df_eval σ r, df_eval_deriv_genvar σ r v with                      
           | Some re, Some rd => 
             vectoro_to_ovector 
               (build_vector (fun i => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv_genvar (mk_env_entry xv (vnth re i) :: nil) s 
                                             (mk_genvar_env x) with
                         | Some sd => Some ((vnth rd i) * sd)
                         | _ => None
                         end))
           | _, _ => None                                                    
           end
         | MatrixApply n m _ x s r =>
           match df_eval σ r, df_eval_deriv_genvar σ r v with                      
           | Some re, Some rd => 
             matrixo_to_omatrix
               (build_matrix (fun i j => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv_genvar  (mk_env_entry xv (mnth re i j) :: nil) s 
                                              (mk_genvar_env x) with
                         | Some sd => Some ((mnth rd i j) * sd)
                         | _ => None
                         end))
           | _, _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l r => 
           match df_eval σ l, df_eval_deriv_genvar σ l v with                      
           | Some le, Some ld => 
             match (vectoro_to_ovector 
                      (build_vector (fun i => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv_genvar ( mk_env_entry xv1 (vnth le i) ::
                                                      mk_env_entry xv2 (vnth r i) :: nil) s
                                                     (mk_genvar_env v1) with
                         | Some sd => Some ((vnth ld i) * sd)
                         | _ => None
                         end))) with
             | Some vv => Some (vsum vv)
             | _ => None
             end
           | _, _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           match df_eval σ l, df_eval_deriv_genvar σ l v with                      
           | Some le, Some ld => 
             match (matrixo_to_omatrix
                      (build_matrix (fun i j => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv_genvar  ( mk_env_entry xv1 (mnth le i j) ::
                                                      mk_env_entry xv2 (mnth r i j) :: nil) s 
                                                     ( mk_genvar_env v1) with
                         | Some sd => Some ((mnth ld i j) * sd)
                         | _ => None
                         end))) with
             | Some vv => Some ((msum vv)/(FfromZ (Z.of_nat m)))
             | _ => None
             end
           | _, _ => None
           end
          end).


    Definition definition_function_types_interp_prod (vart dft:definition_function_types) : Type
     := match vart with
        | DTfloat => definition_function_types_interp dft
        | DTVector n => Vector (definition_function_types_interp dft) n
        | DTMatrix m n => Matrix (definition_function_types_interp dft) m n
        end.


    Definition UnitVector (n:nat) (j : {n':nat | (n' < n)%nat}) : vector float n :=
      build_vector (fun i => if (proj1_sig i) == (proj1_sig j) then 1 else 0).

    Definition UnitMatrix (n m: nat) 
               (i : {n':nat | (n' < n)%nat}) 
               (j : {m':nat | (m' < m)%nat}) : matrix float n m :=
      build_matrix (fun a b => if (proj1_sig a) == (proj1_sig i) then 
                   (if (proj1_sig b) == (proj1_sig j) then 1 else 0)
                 else  0).

    Definition const_env (v : var_type) : df_env
      := match (snd v) with
         | DTfloat => ((mk_env_entry (fst v, DTfloat) 0)::nil)
         | DTVector n => ((mk_env_entry (fst v, DTVector n) (ConstVector n 0))::nil)
         | DTMatrix m n =>  ((mk_env_entry (fst v, DTMatrix m n) (ConstMatrix m n 0))::nil)
         end.

    Fixpoint df_eval_tree_deriv {T} (σ:df_env) (df:DefinedFunction EvalAnn T) (v:var_type) : option (definition_function_types_interp T)
      := (match df with
         | Number _ _ => Some 0
         | Constant t _ x => Some
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
         | DVector n _ dfs => vectoro_to_ovector (vmap (fun e => df_eval_tree_deriv σ e v) dfs)
         | DMatrix n m _ df => matrixo_to_omatrix (mmap (fun e => df_eval_tree_deriv σ e v) df)
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
           | Some l' => Some (vnth l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_tree_deriv σ l v)  with
           | Some l' => Some (mnth l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd => 
               Some (Fplus (vsum (vmap2 Fmult le rd)) (vsum (vmap2 Fmult ld re)))
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
           | Some xd, Some rd => 
             Some (vmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _ => None
           end
         | MatrixScalMult n m _ x r =>
           let '(xe,re) := (get_annotation x, get_annotation r) in           
           match df_eval_tree_deriv σ x v, df_eval_tree_deriv σ r v with
           | Some xd, Some rd =>
             Some (mmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in           
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some (build_vector (fun i => vsum (vmap4 (fun lei rde ldi ree => lei * rde + ldi * ree)
                                        (vnth le i) rd (vnth ld i) re)))
           | _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some (build_matrix (fun i j => (mnth ld i j) + (vnth rd i)))
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in                      
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with
           | Some ld, Some rd =>
             Some (build_matrix (fun i k => vsum (build_vector (fun j => (mnth le i j)*(mnth rd j k) + (mnth ld i j)*(mnth re j k)))))
           | _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (vmap2 Fplus l' r')
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (vmap2 Fminus l' r')
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (mmap2 Fplus l' r')
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_tree_deriv σ l v, df_eval_tree_deriv σ r v with           
           | Some l', Some r' => Some (mmap2 Fminus l' r')
           | _, _ => None
           end
         | VectorApply n _ x s r =>
           let re := get_annotation r in 
           match df_eval_tree_deriv σ r v with                      
           | Some rd => 
             vectoro_to_ovector 
               (build_vector (fun i => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (vnth re i)) nil ) s xv with
                         | Some sd => Some ((vnth rd i) * sd)
                         | _ => None
                         end))
           | _ => None                                                    
           end
         | MatrixApply n m _ x s r =>
           let re := get_annotation r in 
           match df_eval_tree_deriv σ r v with                      
           | Some rd => 
             matrixo_to_omatrix
               (build_matrix (fun i j => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv (cons (mk_env_entry xv (mnth re i j)) nil ) s xv with
                         | Some sd => Some ((mnth rd i j) * sd)
                         | _ => None
                         end))
           | _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l r => 
           let le := get_annotation l in 
           match df_eval_tree_deriv σ l v with                      
           | Some ld => 
             match (vectoro_to_ovector 
                      (build_vector (fun i => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (vnth le i)) 
                                                   (cons (mk_env_entry xv2 (vnth r i)) nil)) s xv1 with
                         | Some sd => Some ((vnth ld i) * sd)
                         | _ => None
                         end))) with
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
                   (build_matrix   (fun i j => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv (cons (mk_env_entry xv1 (mnth le i j)) 
                                                   (cons (mk_env_entry xv2 (mnth r i j)) nil )) s xv1 with
                         | Some sd => Some ((mnth ld i j) * sd)
                         | _ => None
                         end))) with
             | Some vv => Some ((msum vv) / (FfromZ (Z.of_nat m)))
             | _ => None
             end
           | _ => None
           end
          end).
    
    Fixpoint df_eval_tree_deriv_genvar {T} (σ:df_env) (df:DefinedFunction EvalAnn T) (v:df_env) : option (definition_function_types_interp T)
      := (match df with
         | Number _ _ => Some 0
         | Constant t _ x => Some
            match t return definition_function_types_interp t with
            | DTfloat => 0
            | DTVector n => ConstVector n 0
            | DTMatrix m n => ConstMatrix m n 0
            end
         | DVector n _ dfs => vectoro_to_ovector (vmap (fun e => df_eval_tree_deriv_genvar σ e v) dfs)
         | DMatrix n m _ df => matrixo_to_omatrix (mmap (fun e => df_eval_tree_deriv_genvar σ e v) df)
         | Var x _ => Some (
           match vartlookup v x with
           | Some val => val
           | _ => 
             match (snd x) with
             | DTfloat => 0
             | DTVector n => ConstVector n 0
             | DTMatrix m n => ConstMatrix m n 0
             end
           end)
         | Plus _ l r => 
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some le, Some lr => Some (le + lr)
           | _, _ => None
           end
         | Minus _ l r =>
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some le, Some lr => Some (le - lr)
           | _, _ => None
           end
         | Times _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some ld, Some rd =>
             Some (le * rd + 
                   (ld * re))
           | _, _ => None
           end
         | Divide _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in            
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some ld, Some rd =>
             Some ((ld / re) - ((le * rd) / (re * re)))
           | _, _ => None
           end
         | Square _ e =>
           let ee := get_annotation e in
           match df_eval_tree_deriv_genvar σ e v with
           | Some ed => Some (2 * ee * ed)
           | _  => None
           end
         | Exp _ e =>
           let ee := get_annotation e in           
           match df_eval_tree_deriv_genvar σ e v with
           | Some ed => Some (ed * Fexp ee)
           | _  => None
           end
         | Log _ e =>
           let ee := get_annotation e in                      
           match df_eval_tree_deriv_genvar σ e v with
           | Some ed => Some (ed / ee)
           | _ => None
           end
         | Abs _ e =>
           let ee := get_annotation e in                                 
           match df_eval_tree_deriv_genvar σ e v with
           | Some ed => Some (ed * (sign ee))
           | _ => None
           end
         | Sign _ e => 
           match df_eval_tree_deriv_genvar σ e v with
           | Some _ => Some 0
           | None => None
           end
         | PSign _ e => 
           match df_eval_tree_deriv_genvar σ e v with
           | Some _ => Some 0
           | None => None
           end
         | Max _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in                       
           if le <= re then df_eval_tree_deriv_genvar σ r v else df_eval_tree_deriv_genvar σ l v
         | VectorElem n _ l i => 
           match (df_eval_tree_deriv_genvar σ l v)  with
           | Some l' => Some (vnth l' i)
           | _ => None
           end
         | MatrixElem m n _ l i j =>
           match (df_eval_tree_deriv_genvar σ l v)  with
           | Some l' => Some (mnth l' i j)
           | _ => None
           end
         | VectorDot n _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some ld, Some rd => 
               Some (vsum (vmap4 (fun le1 rd1 ld1 re1 => le1 * rd1 + ld1 * re1) le rd ld re))
           | _, _ => None
           end
         | VectorSum n _ l =>
           match df_eval_tree_deriv_genvar σ l v with
           | Some ld =>
               Some (vsum ld)
           | _ => None
           end
         | MatrixSum n m _ l =>
           match df_eval_tree_deriv_genvar σ l v with
           | Some ld =>
               Some (msum ld)
           | _ => None
           end
         | VectorScalMult n _ x r =>
           let '(xe,re) := (get_annotation x, get_annotation r) in
           match df_eval_tree_deriv_genvar σ x v, df_eval_tree_deriv_genvar σ r v with
           | Some xd, Some rd =>
             Some (vmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _ => None
           end
         | MatrixScalMult n m _ x r =>
           let '(xe,re) := (get_annotation x, get_annotation r) in           
           match df_eval_tree_deriv_genvar σ x v, df_eval_tree_deriv_genvar σ r v with
           | Some xd, Some rd =>
             Some (mmap2 (fun rd1 re1 => xe * rd1 + xd * re1) rd re)
           | _, _ => None
           end
         | MatrixVectorMult n m _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in           
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some ld, Some rd =>
             Some (build_vector (fun i => vsum (vmap4 (fun lei rde ldi ree => lei * rde + ldi * ree)
                                        (vnth le i) rd (vnth ld i) re)))
           | _, _ => None
           end
         | MatrixVectorAdd n m _ l r =>
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some ld, Some rd =>
             Some (build_matrix (fun i j => (mnth ld i j) + (vnth rd i)))
           | _, _ => None
           end
         | MatrixMult n m p _ l r =>
           let '(le,re) := (get_annotation l, get_annotation r) in                      
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with
           | Some ld, Some rd =>
             Some (build_matrix (fun i k => vsum (build_vector (fun j => (mnth le i j)*(mnth rd j k) + (mnth ld i j)*(mnth re j k)))))
           | _, _ => None
           end
         | VectorPlus n _ l r =>
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with           
           | Some l', Some r' => Some (vmap2 Fplus l' r')
           | _, _ => None
           end
         | VectorMinus n _ l r =>
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with           
           | Some l', Some r' => Some (vmap2 Fminus l' r')
           | _, _ => None
           end
         | MatrixPlus n m _ l r =>
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with           
           | Some l', Some r' => Some (mmap2 Fplus l' r')
           | _, _ => None
           end
         | MatrixMinus n m _ l r =>
           match df_eval_tree_deriv_genvar σ l v, df_eval_tree_deriv_genvar σ r v with           
           | Some l', Some r' => Some (mmap2 Fminus l' r')
           | _, _ => None
           end
         | VectorApply n _ x s r =>
           let re := get_annotation r in 
           match df_eval_tree_deriv_genvar σ r v with                      
           | Some rd => 
             vectoro_to_ovector 
               (build_vector (fun i => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv_genvar (cons (mk_env_entry xv (vnth re i)) nil ) s 
                                             (mk_genvar_env x) with
                         | Some sd => Some ((vnth rd i) * sd)
                         | _ => None
                         end))
           | _ => None                                                    
           end
         | MatrixApply n m _ x s r =>
           let re := get_annotation r in 
           match df_eval_tree_deriv_genvar σ r v with                      
           | Some rd => 
             matrixo_to_omatrix
               (build_matrix (fun i j => 
                  let xv := (x, DTfloat):var_type in
                  match df_eval_deriv_genvar (cons (mk_env_entry xv (mnth re i j)) nil) s 
                                             (mk_genvar_env x) with
                         | Some sd => Some ((mnth rd i j) * sd)
                         | _ => None
                         end))
           | _ => None                                                    
           end
         | VLossfun n _ v1 v2 s l r => 
           let le := get_annotation l in 
           match df_eval_tree_deriv_genvar σ l v with                      
           | Some ld => 
             match (vectoro_to_ovector 
                      (build_vector (fun i => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv_genvar (cons (mk_env_entry xv1 (vnth le i)) 
                                                   (cons (mk_env_entry xv2 (vnth r i)) nil )) s 
                                                    (mk_genvar_env v1) with
                         | Some sd => Some ((vnth ld i) * sd)
                         | _ => None
                         end))) with
             | Some vv => Some (vsum vv)
             | _ => None
             end
           | _ => None
           end
         | MLossfun n m _ v1 v2 s l r => 
           let le := get_annotation l in 
           match df_eval_tree_deriv_genvar σ l v with                      
           | Some ld => 
             match (matrixo_to_omatrix
                      (build_matrix (fun i j => 
                         let xv1 := (v1, DTfloat):var_type in
                         let xv2 := (v2, DTfloat):var_type in                         
                         match df_eval_deriv_genvar (cons (mk_env_entry xv1 (mnth le i j)) 
                                                   (cons (mk_env_entry xv2 (mnth r i j)) nil)) s 
                                                    (mk_genvar_env v1) with
                         | Some sd => Some ((mnth ld i j) * sd)
                         | _ => None
                         end))) with
             | Some vv => Some ((msum vv) / (FfromZ (Z.of_nat m)))
             | _ => None
             end
           | _ => None
           end
          end).

    Definition vector_env_iter {n} {A} (f: A -> df_env -> option df_env)
             (env: df_env) (v : vector A n) : option df_env :=
      Vector.fold_right (fun a oenv => match oenv with
                                      | Some env => f a env
                                      | _ => None
                                      end)
                        v (Some env).
    
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

   Lemma list_env_iter_env_not_none {A} (f: A -> df_env -> option df_env) 
         (oenv : option df_env) (l: list A): 
     list_env_iter f oenv l <> None -> oenv <> None.
   Proof.
     intros.
     destruct oenv.
     + discriminate.
     + rewrite list_env_iter_none in H.
       tauto.
   Qed.

   Lemma list_env_iter_app {A} (f: A -> df_env -> option df_env)
         (oenv:option df_env) (l1 l2: list A) :
     list_env_iter f oenv (l1++l2) =
     list_env_iter f (list_env_iter f oenv l1) l2.
   Proof.
     revert l2 oenv.
     induction l1; intros l2 oenv; simpl.
     - now destruct oenv.
     - destruct oenv.
       + auto.
       + now rewrite list_env_iter_none.
   Qed.


   Lemma list_env_iter_ext {A} f1 f2 oenv (l:list A) :
     (forall x a, In x l -> f1 x a = f2 x a) ->
     list_env_iter f1 oenv l = list_env_iter f2 oenv l.
   Proof.
     intros fa.
     revert oenv.
     induction l; intros oenv; intros; simpl
     ; match_destr.
     rewrite fa; simpl; intuition.
   Qed.

   
    Definition two_vector_env_iter {n} {A B} (f: A -> B -> df_env -> option df_env)
               (env: df_env) (v: vector A n) (w: vector B n) : option df_env :=
      vector_env_iter (fun '(a,b) env => f a b env) env 
                      (vector_zip v w).

    Fixpoint two_vector_env_iter_alt2 {n1 n2} {A B} (f: A -> B -> df_env -> option df_env)
               (oenv: option df_env) (v: vector A n1) (w: vector B n2) : option df_env :=
      match oenv,v,w with
      | Some env, Vector.cons vx _ v', Vector.cons wx _ w'  => two_vector_env_iter_alt2 f (f vx wx env) v' w'
      | oenv',_,_ => oenv'
      end.

    Definition two_vector_env_iter_alt {n} {A B} (f: A -> B -> df_env -> option df_env)
               (env: df_env) (v: vector A n) (w: vector B n) : option df_env :=
      list_env_iter (fun '(a,b) env => f a b env) (Some env) (combine (Vector.to_list v) (Vector.to_list w)).

    Definition matrix_env_iter {m n} {A} (f: A -> df_env -> option df_env)
               (env: option df_env) (mat : matrix A m n) : option df_env :=
      Vector.fold_right
        (fun vec oenv =>
           Vector.fold_right (fun a oenv => match oenv with
                                      | Some env => f a env
                                      | _ => None
                                      end) vec oenv
        ) mat env.
    
    Definition two_matrix_env_iter {n m} {A B} (f: A -> B -> df_env -> option df_env)
               (env: option df_env) (v: matrix A n m) (w: matrix B n m) : option df_env :=
      let vw := matrix_zip v w in
      matrix_env_iter (fun '(a,b) e => f a b e) env vw.
          
    Definition two_matrix_env_iter_alt {n m} {A B} (f: A -> B -> df_env -> option df_env)
               (env: df_env) (v: matrix A n m) (w: matrix B n m) : option df_env :=
      list_env_iter (fun i env => list_env_iter (fun j env => f (mnth v i j) (mnth w i j) env)
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
                       | Some val => build_vector (fun i => (vnth grad i) + (vnth ((coerce _ val):vector float n) i))
                       | _ =>  grad
                       end
       | DTMatrix m n => fun pf grad => match vartlookup grad_env x with
                         | Some val => build_matrix (fun i j => (mnth ((coerce _ val):matrix float m n) i j) + (mnth grad i j))
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
         | DVector n _ dfs => 
           fun grad =>
             ((fix tv_env_iter {n1 n2}
               (oenv: option df_env) (v: vector _ n1) (w: vector _ n2) : option df_env :=
                 match oenv,v,w with
                 | Some env, Vector.cons vx _ v', Vector.cons wx _ w'  => 
                   tv_env_iter (df_eval_backprop_deriv σ vx env wx) v' w'
                 | oenv',_,_ => oenv'
                 end) 
                n n 
                (Some grad_env) dfs grad  )
         | DMatrix n m _ dfs => fun grad => 
             ((fix tm_env_iter {n1 m1 n2 m2}
               (oenv: option df_env) (v: matrix _ n1 m1) (w: matrix _ n2 m2) : option df_env :=
                 match oenv,v,w with
                 | Some env, Vector.cons vr _ v', Vector.cons wr _ w'  => 
                   let nenv :=
                       ((fix tv_env_iter {n1 n2}
                             (oenv: option df_env) (v: vector _ n1) (w: vector _ n2) : option df_env :=
                           match oenv,v,w with
                           | Some env, Vector.cons vx _ v', Vector.cons wx _ w'  => 
                             tv_env_iter (df_eval_backprop_deriv σ vx env wx) v' w'
                           | oenv',_,_ => oenv'
                           end) 
                          m1 m2
                          (Some env) vr wr  ) in
                   tm_env_iter nenv v' w'
                 | oenv',_,_ => oenv'
                 end) 
                n m n m
                (Some grad_env) dfs grad  )
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
           df_eval_backprop_deriv σ l grad_env  (build_vector grad')
         | MatrixElem m n _ l i j => fun grad => 
           let grad' := fun k1 k2 => 
                          if (proj1_sig k1 == proj1_sig i) then
                            if (proj1_sig k2 == proj1_sig j) then grad else 0
                            else 0 in
           df_eval_backprop_deriv σ l grad_env  (build_matrix grad')
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
             match df_eval_backprop_deriv σ x grad_env  (vsum (vmap2 Fmult re grad)) with
             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env' (vmap (fun e => xe * e) grad)
             | _ => None
             end
           | _, _ => None
           end
         | MatrixScalMult n m _ x r => fun grad =>
           match df_eval σ x, df_eval σ r with
           | Some xe, Some re => 
             match df_eval_backprop_deriv σ x grad_env (msum (mmap2 Fmult re  grad)) with
             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env' (mmap (fun e => e * xe) grad)
             | _ => None
             end
           | _, _ => None
           end
         | MatrixVectorMult n m _ l r => fun grad =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some re => 
             match df_eval_backprop_deriv σ l grad_env (build_matrix (fun i j => (vnth grad i) * (vnth re j))) with


             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env' (matrix_vector_mult (transpose le) grad)
             | _ => None
             end
           | _, _ => None
           end
         | MatrixVectorAdd n m _ l r => fun grad =>
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => 
             match list_env_iter 
                     (fun i env => df_eval_backprop_deriv σ r env  (vnth (transpose grad) i))
                     (Some grad_env') (bounded_seq0 m) with
               | Some grad_env'' => Some grad_env''
               | _ => None
               end
           | _ => None
           end
         | MatrixMult n m p _ l r => fun grad =>
           match df_eval σ l, df_eval σ r with
           | Some le, Some re => 
             match df_eval_backprop_deriv σ l grad_env  (matrix_mult grad (transpose re)) with


             | Some grad_env' => 
               df_eval_backprop_deriv σ r grad_env'  (matrix_mult (transpose le) grad)
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
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env' (vmap Fopp grad)
           | _ => None
           end
         | MatrixPlus n m _ l r => fun grad =>
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | MatrixMinus n m _ l r => fun grad =>
           match df_eval_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_backprop_deriv σ r grad_env' (mmap Fopp grad)
           | _ => None
           end
         | VectorApply n _ x s r => fun grad =>
           match df_eval σ r with
           | Some re => 
             let xv := (x, DTfloat):var_type in
             let s' := df_deriv s xv in
             let ograd := 
                 vmap (fun '(rei, g) => 

                         match df_eval (cons (mk_env_entry xv rei) nil) s' with
                         | Some se => Some (g * se)
                         | _ => None
                         end)
                      (vcombine re grad) in
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
                         match df_eval (cons (mk_env_entry xv rei) nil) s' with
                         | Some se => Some (g * se)
                         | _ => None
                         end)
                      (mcombine re grad) in
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
                                          (cons (mk_env_entry xv2 rei) nil) in
                         match df_eval senv s' with
                         | Some se => Some (grad * se)
                         | _ => None
                         end)
                      (vcombine le re) in
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
                                          (cons (mk_env_entry xv2 rei) nil) in
                         match df_eval senv s' with
                         | Some se => Some ((grad * se)/(FfromZ (Z.of_nat m)))
                         | _ => None
                         end)
                      (mcombine le re) in
             match matrixo_to_omatrix ograd with 
             | Some grad' => df_eval_backprop_deriv σ l grad_env  grad'
             | _ => None
             end
           | _ => None                                                    
           end
          end.

    Definition lifted_type (B:Type) T 
      := match T with
         | DTfloat => B
         | DTVector n => vector B n
         | DTMatrix m n => matrix B m n 
         end.

    Fixpoint df_eval_tree_backprop_deriv {T} (σ:df_env) (df:DefinedFunction EvalAnn T) (grad_env:df_env)  {struct df} : definition_function_types_interp T -> option df_env
      := match df with
         | Number _ _ => fun grad => Some grad_env
         | Constant _ _ _ => fun grad => Some grad_env
         | DVector n _ dfs => fun grad => 
             ((fix tv_env_iter {n1 n2}
               (oenv: option df_env) (v: vector _ n1) (w: vector _ n2) : option df_env :=
                 match oenv,v,w with
                 | Some env, Vector.cons vx _ v', Vector.cons wx _ w'  => 
                   tv_env_iter (df_eval_tree_backprop_deriv σ vx env wx) v' w'
                 | oenv',_,_ => oenv'
                 end) 
                n n 
                (Some grad_env) dfs grad  )
         | DMatrix n m _ dfs => fun grad => 
             ((fix tm_env_iter {n1 m1 n2 m2}
               (oenv: option df_env) (v: matrix _ n1 m1) (w: matrix _ n2 m2) : option df_env :=
                 match oenv,v,w with
                 | Some env, Vector.cons vr _ v', Vector.cons wr _ w'  => 
                   let nenv :=
                       ((fix tv_env_iter {n1 n2}
                             (oenv: option df_env) (v: vector _ n1) (w: vector _ n2) : option df_env :=
                           match oenv,v,w with
                           | Some env, Vector.cons vx _ v', Vector.cons wx _ w'  => 
                             tv_env_iter (df_eval_backprop_deriv σ vx env wx) v' w'
                           | oenv',_,_ => oenv'
                           end) 
                          m1 m2
                          (Some env) vr wr  ) in
                   tm_env_iter nenv v' w'
                 | oenv',_,_ => oenv'
                 end) 
                n m n m
                (Some grad_env) dfs grad  )
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
           let grad' := build_vector (fun k => if proj1_sig k == proj1_sig i then grad else 0) in
           df_eval_tree_backprop_deriv σ l grad_env  grad'
         | MatrixElem m n _ l i j => fun grad => 
           let grad' := build_matrix (fun k1 k2 => 
                          if (proj1_sig k1 == proj1_sig i) then
                            if (proj1_sig k2 == proj1_sig j) then grad else 0
                            else 0) in
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
           match df_eval_tree_backprop_deriv σ x grad_env  (vsum (vmap2 Fmult re grad)) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (vmap (fun ge => xe * ge) grad)
           | _ => None
           end
         | MatrixScalMult n m _ x r => fun grad =>
           let '(xe,re) := (get_annotation x, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ x grad_env  (msum (mmap2 Fmult re grad)) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (mmap (fun ge => ge*xe) grad)
           | _ => None
           end
         | MatrixVectorMult n m _ l r => fun grad =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ l grad_env  (build_matrix (fun i j => (vnth grad i) * (vnth re j))) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (matrix_vector_mult (transpose le) grad)
           | _ => None
           end
         | MatrixVectorAdd n m _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => 
             match list_env_iter 
                     (fun i env => df_eval_tree_backprop_deriv σ r env  (vnth (transpose grad) i))
                     (Some grad_env') (bounded_seq0 m) with
               | Some grad_env'' => Some grad_env''
               | _ => None
               end
           | _ => None
           end
         | MatrixMult n m p _ l r => fun grad =>
           let '(le,re) := (get_annotation l, get_annotation r) in 
           match df_eval_tree_backprop_deriv σ l grad_env  (matrix_mult grad (transpose re)) with
           | Some grad_env' => 
             df_eval_tree_backprop_deriv σ r grad_env'  (matrix_mult (transpose le) grad)
           | _ => None
           end
         | VectorPlus n _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | VectorMinus n _ l r => fun grad => 
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env' (vmap Fopp grad)
           | _ => None
           end
         | MatrixPlus n m _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  grad
           | _ => None
           end
         | MatrixMinus n m _ l r => fun grad =>
           match df_eval_tree_backprop_deriv σ l grad_env  grad with
           | Some grad_env' => df_eval_tree_backprop_deriv σ r grad_env'  (mmap Fopp grad)
           | _ => None
           end
         | VectorApply n _ x s r => fun grad =>
           let re := get_annotation r in 
           let xv := (x, DTfloat):var_type in
           let s' := df_deriv s xv in
           let ograd := 
               vmap (fun '(rei, g) => 
                       match df_eval (cons (mk_env_entry xv rei) nil) s' with
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
                       match df_eval (cons (mk_env_entry xv rei) nil) s' with
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
                                        (cons (mk_env_entry xv2 rei) nil) in
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
                                        (cons (mk_env_entry xv2 rei) nil) in
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
   
   Fixpoint has_scalar_functions {Ann} {T} 
            (df:DefinedFunction Ann T) {struct df}: Prop
     := match df with
         | Number _ _ => True
         | Constant _ _ _ => True
         | DVector n _ vec => 
           ((fix vforal  {n'} (v:vector (DefinedFunction Ann DTfloat) n') : Prop :=
               match v with
               | Vector.nil => True
               | Vector.cons vx _ v' => (has_scalar_functions vx) /\ (vforal v')
               end)
               n vec)
         | DMatrix n m _ mat => 
           ((fix mforall {n' m'} (mat:matrix (DefinedFunction Ann DTfloat) n' m') : Prop :=
               match mat with
               | Vector.nil => True
               | Vector.cons matr _ mat' => 
                 (mforall mat') /\
                 ((fix vforal  {n'} (v:vector (DefinedFunction Ann DTfloat) n') : Prop :=
                     match v with
                     | Vector.nil => True
                     | Vector.cons vx _ v' => (has_scalar_functions vx) /\ (vforal v')
                     end)
                    m' matr)
               end)
               n m mat)
         | Var _ _ => True
         | Plus _ l r => (has_scalar_functions l) /\ (has_scalar_functions r)
         | Minus _ l r => (has_scalar_functions l) /\ (has_scalar_functions r)
         | Times _ l r => (has_scalar_functions l) /\ (has_scalar_functions r)
         | Divide _ l r => (has_scalar_functions l) /\ (has_scalar_functions r)
         | Square _ l => has_scalar_functions l
         | Exp _ l => has_scalar_functions l
         | Log _ l => has_scalar_functions l
         | Abs _ l => has_scalar_functions l
         | Sign _ l => has_scalar_functions l
         | PSign _ l => has_scalar_functions l
         | Max _ l r => (has_scalar_functions l) /\ (has_scalar_functions r)
         | VectorDot n _ l r => (has_scalar_functions l) /\ 
                                (has_scalar_functions r)
         | VectorSum _ _ l => has_scalar_functions l
         | MatrixSum _ _ _ l => has_scalar_functions l
         | VectorElem _ _ vec i => has_scalar_functions vec
         | MatrixElem _ _ _ mat i j => has_scalar_functions mat
         | MatrixVectorMult _ _ _ l r => (has_scalar_functions l) /\ 
                                         (has_scalar_functions r)
         | MatrixVectorAdd _ _ _ l r =>  (has_scalar_functions l) /\ 
                                         (has_scalar_functions r)
         | MatrixMult _ _ _ _ l r => (has_scalar_functions l) /\ 
                                     (has_scalar_functions r)
         | VectorPlus _ _ l r =>  (has_scalar_functions l) /\ 
                                  (has_scalar_functions r)
         | VectorMinus _ _ l r =>  (has_scalar_functions l) /\ 
                                   (has_scalar_functions r)
         | MatrixPlus _ _ _ l r => (has_scalar_functions l) /\ 
                                   (has_scalar_functions r)
         | MatrixMinus _ _ _ l r => (has_scalar_functions l) /\ 
                                    (has_scalar_functions r)
         | VectorScalMult _ _ l r => (has_scalar_functions l) /\ 
                                    (has_scalar_functions r)
         | MatrixScalMult _ _ _ l r => (has_scalar_functions l) /\ 
                                       (has_scalar_functions r)
         | VectorApply _ _ _ s l => is_scalar_function s /\ has_scalar_functions l
         | MatrixApply _ _ _ _ s l => is_scalar_function s /\ has_scalar_functions l
         | VLossfun _ _ _ _ s l _ => is_scalar_function s /\ has_scalar_functions l
         | MLossfun _ _ _ _ _ s l _ => is_scalar_function s /\ has_scalar_functions l
        end.

   Lemma is_scalar_function_has_scalar_functions {Ann} {T} (df:DefinedFunction Ann T) :
     is_scalar_function df -> has_scalar_functions df.
   Proof.
     induction df; firstorder.
   Qed.

   Hint Resolve is_scalar_function_has_scalar_functions.

 Definition DefinedFunction_ind_unit_has_scalar_functions
              (P : forall (d : definition_function_types), DefinedFunction UnitAnn d -> Prop)
              (f : forall (ann : UnitAnn DTfloat) (x : float),
                  P DTfloat (Number ann x))
              (f0 : forall (t : definition_function_types) 
                           (ann : UnitAnn t) (x : definition_function_types_interp t), P t (Constant ann x))
              (f1 : forall (n : nat) (ann : UnitAnn (DTVector n))
                           (x : vector (DefinedFunction UnitAnn DTfloat) n)
                           (f: vforall (P DTfloat) x),
                  P (DTVector n) (DVector ann x))
              (f2 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
                           (x : matrix (DefinedFunction UnitAnn DTfloat) n m)
                           (f: mforall (P DTfloat) x),
                  P (DTMatrix n m) (DMatrix ann x))
              (f3 : forall (v : var_type) (ann : UnitAnn (snd v)),
                  P (snd v) (Var v ann))
              (f4 : forall (ann : UnitAnn DTfloat)
                           (l : DefinedFunction UnitAnn DTfloat),
                  P DTfloat l ->
                  forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Plus ann l r))
              (f5 : forall (ann : UnitAnn DTfloat)
                           (l : DefinedFunction UnitAnn DTfloat),
                  P DTfloat l ->
                  forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Minus ann l r))
              (f6 : forall (ann : UnitAnn DTfloat)
                           (l : DefinedFunction UnitAnn DTfloat),
                  P DTfloat l ->
                  forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Times ann l r))
              (f7 : forall (ann : UnitAnn DTfloat)
                           (l : DefinedFunction UnitAnn DTfloat),
                  P DTfloat l ->
                  forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Divide ann l r))
              (f8 : forall (ann : UnitAnn DTfloat)
                           (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Square ann e))
              (f9 : forall (ann : UnitAnn DTfloat)
                           (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Exp ann e))
              (f10 : forall (ann : UnitAnn DTfloat)
                            (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Log ann e))
              (f11 : forall (ann : UnitAnn DTfloat)
                            (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Abs ann e))
              (f12 : forall (ann : UnitAnn DTfloat)
                            (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (Sign ann e))
              (f13 : forall (ann : UnitAnn DTfloat)
                            (e : DefinedFunction UnitAnn DTfloat), P DTfloat e -> P DTfloat (PSign ann e))
              (f14 : forall (ann : UnitAnn DTfloat)
                            (l : DefinedFunction UnitAnn DTfloat),
                  P DTfloat l ->
                  forall r : DefinedFunction UnitAnn DTfloat, P DTfloat r -> P DTfloat (Max ann l r))
              (f15 : forall (n : nat) (ann : UnitAnn DTfloat)
                            (l : DefinedFunction UnitAnn (DTVector n)),
                  P (DTVector n) l ->
                  forall r : DefinedFunction UnitAnn (DTVector n),
                    P (DTVector n) r -> P DTfloat (VectorDot ann l r))
              (f16 : forall (n : nat) (ann : UnitAnn DTfloat)
                            (v : DefinedFunction UnitAnn (DTVector n)), P (DTVector n) v -> P DTfloat (VectorSum ann v))
              (f17 : forall (m n : nat) (ann : UnitAnn DTfloat)
                            (v : DefinedFunction UnitAnn (DTMatrix m n)),
                  P (DTMatrix m n) v -> P DTfloat (MatrixSum ann v))
              (f18 : forall (n : nat) (ann : UnitAnn DTfloat)
                            (l : DefinedFunction UnitAnn (DTVector n)),
                  P (DTVector n) l ->
                  forall i : {x : nat | (x < n)%nat}, P DTfloat (VectorElem ann l i))
              (f19 : forall (m n : nat) (ann : UnitAnn DTfloat)
                            (l : DefinedFunction UnitAnn (DTMatrix m n)),
                  P (DTMatrix m n) l ->
                  forall (i : {x : nat | (x < m)%nat}) (j : {x : nat | (x < n)%nat}),
                    P DTfloat (MatrixElem ann l i j))
              (f20 : forall (m n : nat) (ann : UnitAnn (DTVector m))
                            (l : DefinedFunction UnitAnn (DTMatrix m n)),
                  P (DTMatrix m n) l ->
                  forall r : DefinedFunction UnitAnn (DTVector n),
                    P (DTVector n) r -> P (DTVector m) (MatrixVectorMult ann l r))
              (f21 : forall (m n : nat) (ann : UnitAnn (DTMatrix m n))
                            (l : DefinedFunction UnitAnn (DTMatrix m n)),
                  P (DTMatrix m n) l ->
                  forall r : DefinedFunction UnitAnn (DTVector m),
                    P (DTVector m) r -> P (DTMatrix m n) (MatrixVectorAdd ann l r))
              (f22 : forall (m p n : nat) (ann : UnitAnn (DTMatrix m n))
                            (l : DefinedFunction UnitAnn (DTMatrix m p)),
                  P (DTMatrix m p) l ->
                  forall r : DefinedFunction UnitAnn (DTMatrix p n),
                    P (DTMatrix p n) r -> P (DTMatrix m n) (MatrixMult ann l r))
              (f23 : forall (n : nat) (ann : UnitAnn (DTVector n))
                            (l : DefinedFunction UnitAnn (DTVector n)),
                  P (DTVector n) l ->
                  forall r : DefinedFunction UnitAnn (DTVector n),
                    P (DTVector n) r -> P (DTVector n) (VectorPlus ann l r))
              (f24 : forall (n : nat) (ann : UnitAnn (DTVector n))
                            (l : DefinedFunction UnitAnn (DTVector n)),
                  P (DTVector n) l ->
                  forall r : DefinedFunction UnitAnn (DTVector n),
                    P (DTVector n) r -> P (DTVector n) (VectorMinus ann l r))
              (f25 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
                            (l : DefinedFunction UnitAnn (DTMatrix n m)),
                  P (DTMatrix n m) l ->
                  forall r : DefinedFunction UnitAnn (DTMatrix n m),
                    P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixPlus ann l r))
              (f26 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
                            (l : DefinedFunction UnitAnn (DTMatrix n m)),
                  P (DTMatrix n m) l ->
                  forall r : DefinedFunction UnitAnn (DTMatrix n m),
                    P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixMinus ann l r))
              (f27 : forall (n : nat) (ann : UnitAnn (DTVector n))
                            (x : DefinedFunction UnitAnn DTfloat),
                  P DTfloat x ->
                  forall l : DefinedFunction UnitAnn (DTVector n),
                    P (DTVector n) l -> P (DTVector n) (VectorScalMult ann x l))
              (f28 : forall (n m : nat) (ann : UnitAnn (DTMatrix n m))
                            (x : DefinedFunction UnitAnn DTfloat),
                  P DTfloat x ->
                  forall l : DefinedFunction UnitAnn (DTMatrix n m),
                    P (DTMatrix n m) l -> P (DTMatrix n m) (MatrixScalMult ann x l))
              (f29 : forall (n : nat) (ann : UnitAnn (DTVector n))
                            (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
                  is_scalar_function s ->
                  P DTfloat s ->
                  forall l : DefinedFunction UnitAnn (DTVector n),
                    P (DTVector n) l -> P (DTVector n) (VectorApply ann v s l))
              (f30 : forall (m n : nat) (ann : UnitAnn (DTMatrix m n))
                            (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
                  is_scalar_function s ->
                  P DTfloat s ->
                  forall l : DefinedFunction UnitAnn (DTMatrix m n),
                    P (DTMatrix m n) l -> P (DTMatrix m n) (MatrixApply ann v s l))
              (f31 : forall (n : nat) (ann : UnitAnn DTfloat)
                            (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
                  is_scalar_function s ->
                  P DTfloat s ->
                  forall l : DefinedFunction UnitAnn (DTVector n),
                    P (DTVector n) l -> forall r : vector float n, P DTfloat (VLossfun ann v1 v2 s l r))
              (f32 : forall (m n : nat) (ann : UnitAnn DTfloat)
                            (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
                  is_scalar_function s ->
                  P DTfloat s ->
                  forall l : DefinedFunction UnitAnn (DTMatrix m n),
                    P (DTMatrix m n) l ->
                    forall r : matrix float m n, P DTfloat (MLossfun ann v1 v2 s l r))
   : forall (d : definition_function_types) 
         (d0 : DefinedFunction UnitAnn d)
         (hs:has_scalar_functions d0), P d d0.
 Proof.
       refine (fix
         F (d : definition_function_types) 
         (d0 : DefinedFunction UnitAnn d)
          {struct d0} : has_scalar_functions d0 -> P d d0 :=
         match d0 as d2 in (DefinedFunction _ d1) return has_scalar_functions d2 -> (P d1 d2) with
         | Number ann x => fun hs => f ann x
         | @Constant _ t ann x => fun hs => f0 t ann x
         | @DVector _ n ann x => 
           fun hs =>
             f1 n ann x        
                ((fix F1 n (x:vector (DefinedFunction UnitAnn DTfloat) n)  : vforall (P DTfloat) x :=
                    match x with
                    | Vector.nil => Vector.Forall_nil (P DTfloat)
                    | Vector.cons h _ tl => Vector.Forall_cons _ _ _ (F DTfloat h _) (F1 _ tl)
                    end) n x) 
         | @DMatrix _ n m ann x => 
           fun hs => 
             f2 n m ann x
                ((fix F2 n m (x:matrix (DefinedFunction UnitAnn DTfloat) n m)  : mforall (P DTfloat) x :=
                    match x with
                    | Vector.nil => Vector.Forall_nil (vforall (P DTfloat))

                    | Vector.cons h _ tl => 
                      Vector.Forall_cons _ _ _ 
                        ((fix F1 m (x:vector (DefinedFunction UnitAnn DTfloat) m)  : vforall (P DTfloat) x :=
                            match x with
                            | Vector.nil => Vector.Forall_nil (P DTfloat)
                            | Vector.cons h _ tl => Vector.Forall_cons _ _ _ (F DTfloat h _) (F1 _ tl)
                            end) m h)
                        (F2 _ _ tl)
                    end) n m x)
         | Var v ann => fun hs => f3 v ann
         | Plus ann l r => fun hs => f4 ann l (F DTfloat l (proj1 hs)) r (F DTfloat r (proj2 hs))
         | Minus ann l r => fun hs => f5 ann l (F DTfloat l _) r (F DTfloat r _)
         | Times ann l r => fun hs => f6 ann l (F DTfloat l _) r (F DTfloat r _)
         | Divide ann l r => fun hs => f7 ann l (F DTfloat l _) r (F DTfloat r _)
         | Square ann e => fun hs => f8 ann e (F DTfloat e _)
         | Exp ann e => fun hs => f9 ann e (F DTfloat e _)
         | Log ann e => fun hs => f10 ann e (F DTfloat e _)
         | Abs ann e => fun hs => f11 ann e (F DTfloat e _)
         | Sign ann e => fun hs => f12 ann e (F DTfloat e _)
         | PSign ann e => fun hs => f13 ann e (F DTfloat e _)
         | Max ann l r => fun hs => f14 ann l (F DTfloat l _) r (F DTfloat r _)
         | @VectorDot _ n ann l r => fun hs => f15 n ann l (F (DTVector n) l  _) r (F (DTVector n) r  _)
         | @VectorSum _ n ann v => fun hs => f16 n ann v (F (DTVector n) v _)
         | @MatrixSum _ m n ann v => fun hs => f17 m n ann v (F (DTMatrix m n) v _)
         | @VectorElem _ n ann l i => fun hs => f18 n ann l (F (DTVector n) l _) i
         | @MatrixElem _ m n ann l i j => fun hs => f19 m n ann l (F (DTMatrix m n) l _) i j
         | @MatrixVectorMult _ m n ann l r => fun hs =>
           f20 m n ann l (F (DTMatrix m n) l _) r (F (DTVector n) r _)
         | @MatrixVectorAdd _ m n ann l r => fun hs =>
           f21 m n ann l (F (DTMatrix m n) l _) r (F (DTVector m) r _)
         | @MatrixMult _ m p n ann l r => fun hs =>
           f22 m p n ann l (F (DTMatrix m p) l _) r (F (DTMatrix p n) r _)
         | @VectorPlus _ n ann l r => fun hs => f23 n ann l (F (DTVector n) l _) r (F (DTVector n) r _)
         | @VectorMinus _ n ann l r => fun hs => f24 n ann l (F (DTVector n) l _) r (F (DTVector n) r _)
         | @MatrixPlus _ n m ann l r => fun hs => f25 n m ann l (F (DTMatrix n m) l _) r (F (DTMatrix n m) r _)
         | @MatrixMinus _ n m ann l r => fun hs =>
           f26 n m ann l (F (DTMatrix n m) l _) r (F (DTMatrix n m) r _)
         | @VectorScalMult _ n ann x l => fun hs => f27 n ann x (F DTfloat x _) l (F (DTVector n) l _)
         | @MatrixScalMult _ n m ann x l => fun hs => f28 n m ann x (F DTfloat x _) l (F (DTMatrix n m) l _)
         | @VectorApply _ n ann v s l => fun hs => f29 n ann v s _ (F DTfloat s _) l (F (DTVector n) l _)
         | @MatrixApply _ m n ann v s l => fun hs =>
           f30 m n ann v s _ (F DTfloat s _) l (F (DTMatrix m n) l _)
         | @VLossfun _ n ann v1 v2 s l r => fun hs =>
           f31 n ann v1 v2 s _ (F DTfloat s _) l (F (DTVector n) l _) r
         | @MLossfun _ m n ann v1 v2 s l r => fun hs =>
           f32 m n ann v1 v2 s _ (F DTfloat s _) l (F (DTMatrix m n) l _) r
         end); simpl in hs; intuition.
       - exact (proj1 (vforall_forall has_scalar_functions x) hs s).
       - rewrite vforall_forall in hs.
         specialize (hs s).
         rewrite vforall_forall in hs.
         specialize (hs s0).
         exact hs.
 Defined.

   Fixpoint is_df_rec_prop {Ann} {T} 
            (prop : forall TT:definition_function_types, 
                (DefinedFunction Ann TT) -> Prop)
            (df:DefinedFunction Ann T) {struct df}: Prop
     := prop T df /\
        match df with
         | Number _ _ => True
         | Constant _ _ _ => True
         | DVector n _ vec => 
           vforall (is_df_rec_prop prop) vec
         | DMatrix n m _ mat =>  
             vforall (vforall (is_df_rec_prop prop)) mat
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

      Fixpoint df_strip_annotations {Ann} {T} 
               (df:DefinedFunction Ann T) {struct df}: DefinedFunction UnitAnn T
     := 
        match df with
         | Number _ x1 => Number tt x1
         | Constant t _ x => Constant tt x
         | DVector n _ vec => DVector tt (vmap df_strip_annotations vec)
         | DMatrix n m _ mat => DMatrix tt (vmap (vmap df_strip_annotations) mat)
         | Var v _ => Var v tt
         | Plus _ l r => Plus tt (df_strip_annotations l) (df_strip_annotations r)
         | Minus _ l r => Minus tt (df_strip_annotations l) (df_strip_annotations r)
         | Times _ l r => Times tt (df_strip_annotations l) (df_strip_annotations r)
         | Divide _ l r => Divide tt (df_strip_annotations l) (df_strip_annotations r)
         | Square _ l => Square tt (df_strip_annotations l)
         | Exp _ l => Exp tt (df_strip_annotations l)
         | Log _ l => Log tt (df_strip_annotations l)
         | Abs _ l => Abs tt (df_strip_annotations l)
         | Sign _ l => Sign tt (df_strip_annotations l)
         | PSign _ l => PSign tt (df_strip_annotations l)
         | Max _ l r => Max tt (df_strip_annotations l) (df_strip_annotations r)
         | VectorDot n _ l r => VectorDot tt (df_strip_annotations l) (df_strip_annotations r)
         | VectorSum n _ l => VectorSum tt (df_strip_annotations l) 
         | MatrixSum m n _ l => MatrixSum tt (df_strip_annotations l) 
         | VectorElem n _ vec i => VectorElem tt (df_strip_annotations vec) i
         | MatrixElem m n _ mat i j => MatrixElem tt (df_strip_annotations mat) i j
         | MatrixVectorMult m n _ l r => MatrixVectorMult tt (df_strip_annotations l) (df_strip_annotations r)
         | MatrixVectorAdd m n _ l r =>  MatrixVectorAdd tt (df_strip_annotations l) (df_strip_annotations r)
         | MatrixMult m p n _ l r => MatrixMult tt (df_strip_annotations l) (df_strip_annotations r)
         | VectorPlus n _ l r => VectorPlus tt (df_strip_annotations l) (df_strip_annotations r)
         | VectorMinus n _ l r => VectorMinus tt (df_strip_annotations l) (df_strip_annotations r)
         | MatrixPlus m n _ l r =>  MatrixPlus tt (df_strip_annotations l) (df_strip_annotations r)
         | MatrixMinus m n _ l r =>  MatrixMinus tt (df_strip_annotations l) (df_strip_annotations r)
         | VectorScalMult n _ l r => VectorScalMult tt (df_strip_annotations l) (df_strip_annotations r)
         | MatrixScalMult m n _ l r => MatrixScalMult tt (df_strip_annotations l) (df_strip_annotations r)
         | VectorApply n _ v s l => VectorApply tt v (df_strip_annotations s) (df_strip_annotations l)
         | MatrixApply m n _ v s l => MatrixApply tt v (df_strip_annotations s) (df_strip_annotations l)
         | VLossfun n _ v1 v2 s l r => VLossfun tt v1 v2 (df_strip_annotations s) (df_strip_annotations l) r
         | MLossfun m n _ v1 v2 s l r => MLossfun tt v1 v2 (df_strip_annotations s) (df_strip_annotations l) r
         end.        

      Require Import Program.

      Lemma df_strip_annotations_id {T} (df:DefinedFunction UnitAnn T) : df_strip_annotations df = df.
      Proof.
        DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case; simpl; trivial
        ; destruct ann; trivial; try congruence.
        - Case "DVector"%string.
          f_equal.
          erewrite vmap_ext; [apply vmap_id | ]; intros.
          simpl.
          destruct H0 as [??]; subst.
          eapply H; eauto.
        - Case "DMatrix"%string.
          f_equal.
          erewrite vmap_ext; [apply vmap_id | ]; intros.
          simpl.
          erewrite vmap_ext; [apply vmap_id | ]; intros.
          simpl.
          destruct H0 as [??]; subst.
          destruct H1 as [??]; subst.
          eapply H; eauto.
      Qed.

      Definition df_eq_upto_annotations {Ann1 Ann2 T}
                 (df1:DefinedFunction Ann1 T) (df2:DefinedFunction Ann2 T) : Prop
        := df_strip_annotations df1 = df_strip_annotations df2.

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
       ; trivial
                ].
     
     - Case "Number"%string.
       inversion eqq; subst.
       simpl; tauto.
     - Case "Constant"%string.
       inversion eqq; subst. 
       simpl; tauto.
     - Case "DVector"%string.
       match_option_in eqq.
       invcs eqq.
       simpl.
       specialize (vectoro_to_ovector_forall_some_f eqq0)
       ; simpl
       ; clear eqq0; intros eqq0.
       split.
       + apply vectoro_to_ovector_forall_some_b_strong; intros i.
         specialize (H _ _ (eqq0 i)).
         apply is_df_rec_prop_top in H.
         simpl in *.
         rewrite vmap_nth; trivial.
       + apply vforall_forall; eauto.
     - Case "DMatrix"%string.
       match_option_in eqq.
       invcs eqq.
       simpl.
       unfold matrixo_to_omatrix in *.
       specialize (vectoro_to_ovector_forall_some_f eqq0)
       ; simpl
       ; clear eqq0; intros eqq0.
       split.
       + apply vectoro_to_ovector_forall_some_b_strong; intros i.
         apply vectoro_to_ovector_forall_some_b_strong; intros j.
         specialize (eqq0 i).
       specialize (vectoro_to_ovector_forall_some_f eqq0)
       ; simpl
       ; clear eqq0; intros eqq0.
       specialize (eqq0 j).
       specialize (H _ _ _ eqq0).
       apply is_df_rec_prop_top in H.
       simpl in *.
       repeat rewrite vmap_nth; trivial.
       + apply vforall_forall; intros.
         apply vforall_forall; intros.
         specialize (eqq0 i).
         specialize (vectoro_to_ovector_forall_some_f eqq0)
       ; simpl
       ; clear eqq0; intros eqq0.
         eauto.
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
       match_option_in eqq.
       invcs eqq.
       simpl.
       split; trivial.
       apply is_df_rec_prop_top in IHdf2.
       simpl in IHdf2.
       rewrite IHdf2; trivial.
     - Case "MatrixApply"%string.
       case_eq (df_eval_tree σ df2)
       ; [intros adf2 a2eqq | intros a2eqq]
       ; rewrite a2eqq in eqq 
       ; [| congruence].
       specialize (IHdf2 _ a2eqq).
       match_option_in eqq.
       invcs eqq.
       simpl.
       split; trivial.
       apply is_df_rec_prop_top in IHdf2.
       simpl in IHdf2.
       rewrite IHdf2; trivial.
     - Case "VLossfun"%string.
       case_eq (df_eval_tree σ df2)
       ; [intros adf2 a2eqq | intros a2eqq]
       ; rewrite a2eqq in eqq 
       ; [| congruence].
       specialize (IHdf2 _ a2eqq).
       match_option_in eqq.
       invcs eqq.
       simpl.
       split; trivial.
       apply is_df_rec_prop_top in IHdf2.
       simpl in IHdf2.
       rewrite IHdf2, eqq0; trivial.
     - Case "MLossfun"%string.
       case_eq (df_eval_tree σ df2)
       ; [intros adf2 a2eqq | intros a2eqq]
       ; rewrite a2eqq in eqq 
       ; [| congruence].
       specialize (IHdf2 _ a2eqq).
       match_option_in eqq.
       invcs eqq.
       simpl.
       split; trivial.
       apply is_df_rec_prop_top in IHdf2.
       simpl in IHdf2.
       rewrite IHdf2, eqq0; trivial.
   Qed.


   Lemma df_eval_tree_deriv_correct {T} {σ:df_env} {df:DefinedFunction EvalAnn T} :
     is_df_evalann_correct σ df ->
     forall (xv:var_type),
      (* let xv := (v, DTfloat) in *)
       df_eval_tree_deriv σ df xv = df_eval_deriv σ df xv.
   Proof.
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case;
      intro iscor; destruct iscor;
      simpl; intros; trivial; unfold is_df_evalann_correct in *
     ; try solve 
           [
             rewrite IHdf
             ; trivial
           |
           assert (is_df_evalann_correct_top σ df)
           ; [ apply is_df_rec_prop_top; trivial |
               unfold is_df_evalann_correct_top in H1
               ; rewrite H1
               ; rewrite IHdf
               ; trivial
             ]
           |
           rewrite IHdf1;
             [ rewrite IHdf2
               ; trivial
               ; tauto 
             | 
             tauto
             ]
           |
           rewrite IHdf1;
             [ assert (is_df_evalann_correct_top σ df2);
                 [ apply is_df_rec_prop_top; trivial
                 | unfold is_df_evalann_correct_top in H1;
                     rewrite H1; trivial]
             | tauto]
           |
           destruct H0; rewrite IHdf1;
             [rewrite IHdf2;
                [assert (is_df_evalann_correct_top σ df1);
                   [apply is_df_rec_prop_top; trivial 
                   | assert (is_df_evalann_correct_top σ df2);
                       [  apply is_df_rec_prop_top; trivial
                        |                                                   
                        unfold is_df_evalann_correct_top in H2;
                          unfold is_df_evalann_correct_top in H3;
                          rewrite H2; rewrite H3; trivial ]]
                |
                tauto]
             |
             tauto]
           ].
     - Case "DVector"%string.
       f_equal.
       apply FunctionalExtensionality.functional_extensionality.
       intro.
       apply H.
       destruct H0.
       rewrite vforall_forall in H1.
       eauto.
     - Case "DMatrix"%string.
       f_equal.
       apply FunctionalExtensionality.functional_extensionality.
       intro.
       apply FunctionalExtensionality.functional_extensionality.
       intros.
       apply H.
       destruct H0.
       rewrite vforall_forall in H1.
       specialize (H1 x0).
       rewrite vforall_forall in H1.
       eauto.
   Qed.

   Lemma df_eval_tree_backprop_deriv_correct {T} (σ gradenv:df_env) (df:DefinedFunction EvalAnn T) (grad : definition_function_types_interp T) : 
     is_df_evalann_correct σ df ->
       df_eval_tree_backprop_deriv σ df gradenv grad = df_eval_backprop_deriv σ df gradenv grad.
   Proof.
     revert gradenv grad.
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case;
      intros; simpl;trivial
     ; try solve [
       destruct H;
       assert (is_df_evalann_correct σ df);
       [ unfold is_df_evalann_correct; trivial
       | apply is_df_rec_prop_top in H0;
         rewrite IHdf;
         [ unfold is_df_evalann_correct_top in H0;
           rewrite H0; trivial
         | trivial]]
           |
       destruct H;
       apply IHdf;
       unfold is_df_evalann_correct; trivial
           |
       destruct H; destruct H0; rewrite IHdf1;
       [ case_eq (df_eval_backprop_deriv σ df1 gradenv grad); [|congruence];
         intros;
         rewrite IHdf2; trivial
       | unfold is_df_evalann_correct; trivial]

           |
       destruct H;
       assert (is_df_evalann_correct σ df2);
       [ unfold is_df_evalann_correct; trivial
       | apply is_df_rec_prop_top in H0;
         unfold is_df_evalann_correct_top in H0;
         rewrite H0;
         match_destr;
         rewrite IHdf1; trivial]
         |
       destruct H; destruct H0; assert (is_df_evalann_correct σ df1);
       [ unfold is_df_evalann_correct; trivial
       | assert (is_df_evalann_correct σ df2);
         [ unfold is_df_evalann_correct; trivial
         | rewrite IHdf1; trivial;
           apply is_df_rec_prop_top in H0;
           apply is_df_rec_prop_top in H1;
           unfold is_df_evalann_correct_top in H0;
           unfold is_df_evalann_correct_top in H1;
           rewrite H0; rewrite H1;
           match_destr;
           rewrite IHdf2; trivial]]
       ].
     - Case "DVector"%string.
       destruct H0.
       rewrite vforall_forall in H1.
       unfold two_vector_env_iter_alt.
       f_equal; apply FunctionalExtensionality.functional_extensionality; intros
       ; apply FunctionalExtensionality.functional_extensionality ; intros.
       apply H; unfold is_df_evalann_correct; apply H1.
     - Case "DMatrix"%string.
       destruct H0.
       rewrite vforall_forall in H1.       
       unfold two_matrix_env_iter_alt.
       f_equal; apply FunctionalExtensionality.functional_extensionality; intros
        ;  apply FunctionalExtensionality.functional_extensionality; intros.
       f_equal; apply FunctionalExtensionality.functional_extensionality; intros
        ;  apply FunctionalExtensionality.functional_extensionality; intros.
       apply H; unfold is_df_evalann_correct.
       specialize (H1 x0).
       rewrite vforall_forall in H1; apply H1.
     - Case "MatrixVectorAdd"%string.
       destruct H.
       destruct H0.
       assert (is_df_evalann_correct σ df1).
       unfold is_df_evalann_correct; trivial.
       assert (is_df_evalann_correct σ df2).
       unfold is_df_evalann_correct; trivial.
       rewrite IHdf1; trivial.
       match_destr.
       assert 
         (list_env_iter
            (fun (i : {m' : nat | (m' < n)%nat}) (env : df_env) =>
               df_eval_tree_backprop_deriv σ df2 env (transpose grad i)) 
            (Some d) (bounded_seq0 n) =
          list_env_iter
            (fun (i : {m' : nat | (m' < n)%nat}) (env : df_env) =>
               df_eval_backprop_deriv σ df2 env (transpose grad i)) (Some d) 
            (bounded_seq0 n)).
       f_equal.
       apply FunctionalExtensionality.functional_extensionality; intros.
       apply FunctionalExtensionality.functional_extensionality; intros.
       rewrite IHdf2; trivial.
       rewrite H4; trivial.
   Qed.

   Lemma df_eval_ignores_ann {Ann T} {σ:df_env} 
          (df:DefinedFunction Ann T) :
     df_eval σ df = df_eval σ (df_strip_annotations df).
   Proof.
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case; simpl; trivial
     ; try solve [
             rewrite IHdf; trivial
           |                             
             rewrite IHdf1;
             case_eq (df_eval σ (df_strip_annotations df1)); [|congruence];
             intros; rewrite IHdf2; trivial
           |
             rewrite IHdf1; trivial;
             case_eq (df_eval σ (df_strip_annotations df2)); [|congruence];
             intros; f_equal;
             apply FunctionalExtensionality.functional_extensionality; intros;
             f_equal; rewrite df_strip_annotations_id; trivial
           |
             rewrite IHdf1; trivial;
             case_eq (df_eval σ (df_strip_annotations df2)); [|congruence];
             intros; f_equal;
             rewrite df_strip_annotations_id; trivial
           ].

     - Case "DVector"%string.
       f_equal.
       apply FunctionalExtensionality.functional_extensionality; intros.
       rewrite H.
       rewrite vmap_nth; trivial.
     - Case "DMatrix"%string.
       f_equal.
       apply FunctionalExtensionality.functional_extensionality; intros.
       apply FunctionalExtensionality.functional_extensionality; intros.       
       specialize (H x0).
       rewrite H.
       rewrite vmap_nth.
       rewrite vmap_nth; trivial.       
   Qed.

   Lemma df_eval_ignores_ann2 {Ann1 Ann2 T} {σ:df_env} 
         (df1:DefinedFunction Ann1 T) (df2:DefinedFunction Ann2 T) :
     df_eq_upto_annotations df1 df2 ->
     df_eval σ df1 = df_eval σ df2.
   Proof.
     assert (df_eval σ df1 = df_eval σ (df_strip_annotations df1)) by apply df_eval_ignores_ann.
     assert (df_eval σ df2 = df_eval σ (df_strip_annotations df2)) by apply df_eval_ignores_ann.
     congruence.
   Qed.

   Lemma df_eval_deriv_ignores_ann {Ann T} {σ:df_env} 
          (df:DefinedFunction Ann T) :
     forall (xv:var_type),
       df_eval_deriv σ df xv = df_eval_deriv σ (df_strip_annotations df) xv.
   Proof.
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case; simpl; trivial
     ; try solve 
           [
             intro; rewrite IHdf1;
             case_eq (df_eval_deriv σ (df_strip_annotations df1) xv); [|congruence];
             intros;
             rewrite IHdf2; trivial
           |
             intro; rewrite df_eval_ignores_ann;
             case_eq (df_eval σ (df_strip_annotations df1)); [|congruence];
             intros; rewrite IHdf1; intros;
             case_eq (df_eval_deriv σ (df_strip_annotations df1) xv); [|congruence];
             intros; rewrite df_eval_ignores_ann;
             case_eq (df_eval σ (df_strip_annotations df2)); [|congruence];
             intros; rewrite IHdf2; trivial
           |
             intros; rewrite df_eval_ignores_ann;
             case_eq (df_eval σ (df_strip_annotations df)); [|congruence];
             intros; rewrite IHdf; intros;
             case_eq (df_eval_deriv σ (df_strip_annotations df) xv); [|congruence];
             trivial
           | 
             intros; rewrite IHdf; trivial
           |
             intro; rewrite df_eval_ignores_ann;
             case_eq (df_eval σ (df_strip_annotations df2)); [|congruence];
             intros; rewrite IHdf1; intros;
             rewrite df_strip_annotations_id; trivial
           ].

     - Case "DVector"%string.
       intros.
       f_equal.
       apply FunctionalExtensionality.functional_extensionality; intros.
       rewrite H.
       rewrite vmap_nth; trivial.
     - Case "DMatrix"%string.
       intros.
       f_equal.
       apply FunctionalExtensionality.functional_extensionality; intros.
       apply FunctionalExtensionality.functional_extensionality; intros.       
       specialize (H x0).
       rewrite H.
       rewrite vmap_nth.
       rewrite vmap_nth; trivial.
     - Case "Max"%string.
       intro; rewrite df_eval_ignores_ann.
       case_eq (df_eval σ (df_strip_annotations df1)); [|congruence].
       intros.
       rewrite df_eval_ignores_ann.
       case_eq (df_eval σ (df_strip_annotations df2)); [|congruence].
       intros.
       rewrite IHdf1.
       rewrite IHdf2; trivial.
    Qed.

   Lemma df_eval_deriv_ignores_ann2 {Ann1 Ann2 T} {σ:df_env} 
         (df1:DefinedFunction Ann1 T) (df2:DefinedFunction Ann2 T) :
     forall (xv:var_type),
            df_eq_upto_annotations df1 df2 ->
            df_eval_deriv σ df1 xv = df_eval_deriv σ df2 xv.
   Proof.
     intro.
     assert (df_eval_deriv σ df1 xv = df_eval_deriv σ (df_strip_annotations df1) xv) by  apply df_eval_deriv_ignores_ann.
     assert (df_eval_deriv σ df2 xv = df_eval_deriv σ (df_strip_annotations df2) xv) by  apply df_eval_deriv_ignores_ann.     
     congruence.
   Qed.

   (*
   Definition DefinedFunction_ind_equpto {Ann1 Ann2}
  (P : forall (d : definition_function_types), DefinedFunction Ann1 d -> DefinedFunction Ann2 d -> Prop)
  (f : forall (ann1 : Ann1 DTfloat) (ann2:Ann2 DTfloat) (x : float),
       P DTfloat (Number ann1 x) (Number ann2 x))
  (f0 : forall (t : definition_function_types) 
               (ann1 : Ann1 t) (ann2 : Ann2 t) (x : definition_function_types_interp t),
      P t (Constant ann1 x) (Constant ann2 x))
(*  (f1 : forall (n : nat) (ann : Ann (DTVector n))
          (x : Vector (DefinedFunction Ann DTfloat) n),
        (forall s : {n' : nat | (n' < n)%nat}, P DTfloat (x s)) ->
        P (DTVector n) (DVector ann x))
  (f2 : forall (n m : nat) (ann : Ann (DTMatrix n m))
          (x : Matrix (DefinedFunction Ann DTfloat) n m),
        (forall (s : {n' : nat | (n' < n)%nat}) (s0 : {m' : nat | (m' < m)%nat}),
         P DTfloat (x s s0)) -> P (DTMatrix n m) (DMatrix ann x))
  (f3 : forall (v : var_type) (ann : Ann (snd v)),
        P (snd v) (Var v ann))
  (f4 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Plus ann l r))
  (f5 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Minus ann l r))
  (f6 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Times ann l r))
  (f7 : forall (ann : Ann DTfloat)
          (l : DefinedFunction Ann DTfloat),
        P DTfloat l ->
        forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Divide ann l r))
  (f8 : forall (ann : Ann DTfloat)
          (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Square ann e))
  (f9 : forall (ann : Ann DTfloat)
          (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Exp ann e))
  (f10 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Log ann e))
  (f11 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Abs ann e))
  (f12 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (Sign ann e))
  (f13 : forall (ann : Ann DTfloat)
           (e : DefinedFunction Ann DTfloat), P DTfloat e -> P DTfloat (PSign ann e))
  (f14 : forall (ann : Ann DTfloat)
           (l : DefinedFunction Ann DTfloat),
         P DTfloat l ->
         forall r : DefinedFunction Ann DTfloat, P DTfloat r -> P DTfloat (Max ann l r))
  (f15 : forall (n : nat) (ann : Ann DTfloat)
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P DTfloat (VectorDot ann l r))
  (f16 : forall (n : nat) (ann : Ann DTfloat)
           (v : DefinedFunction Ann (DTVector n)), P (DTVector n) v -> P DTfloat (VectorSum ann v))
  (f17 : forall (m n : nat) (ann : Ann DTfloat)
           (v : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) v -> P DTfloat (MatrixSum ann v))
  (f18 : forall (n : nat) (ann : Ann DTfloat)
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall i : {x : nat | (x < n)%nat}, P DTfloat (VectorElem ann l i))
  (f19 : forall (m n : nat) (ann : Ann DTfloat)
           (l : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall (i : {x : nat | (x < m)%nat}) (j : {x : nat | (x < n)%nat}),
         P DTfloat (MatrixElem ann l i j))
  (f20 : forall (m n : nat) (ann : Ann (DTVector m))
           (l : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P (DTVector m) (MatrixVectorMult ann l r))
  (f21 : forall (m n : nat) (ann : Ann (DTMatrix m n))
           (l : DefinedFunction Ann (DTMatrix m n)),
         P (DTMatrix m n) l ->
         forall r : DefinedFunction Ann (DTVector m),
         P (DTVector m) r -> P (DTMatrix m n) (MatrixVectorAdd ann l r))
  (f22 : forall (m p n : nat) (ann : Ann (DTMatrix m n))
           (l : DefinedFunction Ann (DTMatrix m p)),
         P (DTMatrix m p) l ->
         forall r : DefinedFunction Ann (DTMatrix p n),
         P (DTMatrix p n) r -> P (DTMatrix m n) (MatrixMult ann l r))
  (f23 : forall (n : nat) (ann : Ann (DTVector n))
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P (DTVector n) (VectorPlus ann l r))
  (f24 : forall (n : nat) (ann : Ann (DTVector n))
           (l : DefinedFunction Ann (DTVector n)),
         P (DTVector n) l ->
         forall r : DefinedFunction Ann (DTVector n),
         P (DTVector n) r -> P (DTVector n) (VectorMinus ann l r))
  (f25 : forall (n m : nat) (ann : Ann (DTMatrix n m))
           (l : DefinedFunction Ann (DTMatrix n m)),
         P (DTMatrix n m) l ->
         forall r : DefinedFunction Ann (DTMatrix n m),
         P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixPlus ann l r))
  (f26 : forall (n m : nat) (ann : Ann (DTMatrix n m))
           (l : DefinedFunction Ann (DTMatrix n m)),
         P (DTMatrix n m) l ->
         forall r : DefinedFunction Ann (DTMatrix n m),
         P (DTMatrix n m) r -> P (DTMatrix n m) (MatrixMinus ann l r))
  (f27 : forall (n : nat) (ann : Ann (DTVector n))
           (x : DefinedFunction Ann DTfloat),
         P DTfloat x ->
         forall l : DefinedFunction Ann (DTVector n),
         P (DTVector n) l -> P (DTVector n) (VectorScalMult ann x l))
  (f28 : forall (n m : nat) (ann : Ann (DTMatrix n m))
           (x : DefinedFunction Ann DTfloat),
         P DTfloat x ->
         forall l : DefinedFunction Ann (DTMatrix n m),
         P (DTMatrix n m) l -> P (DTMatrix n m) (MatrixScalMult ann x l))
  (f29 : forall (n : nat) (ann : Ann (DTVector n))
           (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTVector n),
         P (DTVector n) l -> P (DTVector n) (VectorApply ann v s l))
  (f30 : forall (m n : nat) (ann : Ann (DTMatrix m n))
           (v : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTMatrix m n),
         P (DTMatrix m n) l -> P (DTMatrix m n) (MatrixApply ann v s l))
  (f31 : forall (n : nat) (ann : Ann DTfloat)
           (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTVector n),
         P (DTVector n) l -> forall r : Vector float n, P DTfloat (VLossfun ann v1 v2 s l r))
  (f32 : forall (m n : nat) (ann : Ann DTfloat)
           (v1 v2 : SubVar) (s : DefinedFunction UnitAnn DTfloat),
         forall l : DefinedFunction Ann (DTMatrix m n),
         P (DTMatrix m n) l ->
         forall r : Matrix float m n, P DTfloat (MLossfun ann v1 v2 s l r))
*) 
     : forall (d:definition_function_types) (df1:DefinedFunction Ann1 d) (df2:DefinedFunction Ann2 d)
              (eqq:df_eq_upto_annotations df1 df2), P d df1 df2.
     

fix
F (d : definition_function_types) 
  (d0 : DefinedFunction Ann d) {struct d0} : P d d0 :=
  match d0 as d2 in (DefinedFunction _ d1) return (P d1 d2) with
  | Number ann x => f ann x
  | @Constant _ t ann x => f0 t ann x
  | @DVector _ n ann x => f1 n ann x (fun s : {n' : nat | (n' < n)%nat} => F DTfloat (x s))
  | @DMatrix _ n m ann x =>
      f2 n m ann x
        (fun (s : {n' : nat | (n' < n)%nat}) (s0 : {m' : nat | (m' < m)%nat}) =>
         F DTfloat (x s s0))
  | Var v ann => f3 v ann
  | Plus ann l r => f4 ann l (F DTfloat l) r (F DTfloat r)
  | Minus ann l r => f5 ann l (F DTfloat l) r (F DTfloat r)
  | Times ann l r => f6 ann l (F DTfloat l) r (F DTfloat r)
  | Divide ann l r => f7 ann l (F DTfloat l) r (F DTfloat r)
  | Square ann e => f8 ann e (F DTfloat e)
  | Exp ann e => f9 ann e (F DTfloat e)
  | Log ann e => f10 ann e (F DTfloat e)
  | Abs ann e => f11 ann e (F DTfloat e)
  | Sign ann e => f12 ann e (F DTfloat e)
  | PSign ann e => f13 ann e (F DTfloat e)
  | Max ann l r => f14 ann l (F DTfloat l) r (F DTfloat r)
  | @VectorDot _ n ann l r => f15 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @VectorSum _ n ann v => f16 n ann v (F (DTVector n) v)
  | @MatrixSum _ m n ann v => f17 m n ann v (F (DTMatrix m n) v)
  | @VectorElem _ n ann l i => f18 n ann l (F (DTVector n) l) i
  | @MatrixElem _ m n ann l i j => f19 m n ann l (F (DTMatrix m n) l) i j
  | @MatrixVectorMult _ m n ann l r =>
      f20 m n ann l (F (DTMatrix m n) l) r (F (DTVector n) r)
  | @MatrixVectorAdd _ m n ann l r =>
      f21 m n ann l (F (DTMatrix m n) l) r (F (DTVector m) r)
  | @MatrixMult _ m p n ann l r =>
      f22 m p n ann l (F (DTMatrix m p) l) r (F (DTMatrix p n) r)
  | @VectorPlus _ n ann l r => f23 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @VectorMinus _ n ann l r => f24 n ann l (F (DTVector n) l) r (F (DTVector n) r)
  | @MatrixPlus _ n m ann l r => f25 n m ann l (F (DTMatrix n m) l) r (F (DTMatrix n m) r)
  | @MatrixMinus _ n m ann l r =>
      f26 n m ann l (F (DTMatrix n m) l) r (F (DTMatrix n m) r)
  | @VectorScalMult _ n ann x l => f27 n ann x (F DTfloat x) l (F (DTVector n) l)
  | @MatrixScalMult _ n m ann x l => f28 n m ann x (F DTfloat x) l (F (DTMatrix n m) l)
  | @VectorApply _ n ann v s l => f29 n ann v s l (F (DTVector n) l)
  | @MatrixApply _ m n ann v s l =>
      f30 m n ann v s l (F (DTMatrix m n) l)
  | @VLossfun _ n ann v1 v2 s l r =>
      f31 n ann v1 v2 s l (F (DTVector n) l) r
  | @MLossfun _ m n ann v1 v2 s l r =>
      f32 m n ann v1 v2 s l (F (DTMatrix m n) l) r
  end.

   Lemma df_eval_proper_annot {Ann1 Ann2 T} {df1:DefinedFunction Ann1 T} {df2:DefinedFunction Ann2 T} : 
     df_eq_upto_annotations df1 df2 ->
     forall σ,
       df_eval σ df1 = df_eval σ df2.
   Proof.
     unfold df_eq_upto_annotations.
     revert df2.
     DefinedFunction_cases (induction T, df1 using DefinedFunction_ind_simpl) Case.
     - intros.
       simpl.
       
       intros df2.
       dependent destruction df2; simpl; intros; try discriminate.
       + admit.
       + cut False; [tauto | ].
         revert H x.
         clear.
         revert ann0.
         generalize v (snd v).
         intros.

         congruence.
     DefinedFunction_cases (induction T, df2 using DefinedFunction_ind_simpl) Case.
     
     ; 
     - Case "Number"%string.
       simpl.
       
       
   Qed.



   Lemma df_eval_deriv_annot σ df v :
     df_eval_deriv σ df v =  df_eval_deriv σ df v.

   Lemma df_eval_tree_deriv_correct {T} {σ:df_env} {df:DefinedFunction EvalAnn T} :
      is_df_evalann_correct_top σ df ->
      forall (v:var_type),
        df_eval_tree_deriv σ df v = df_eval_deriv σ df v.
   Proof.
     
   Qed.


   (*
      Definition annotations_correct
     := is_df_rec_prop ()
              
    is_df_rec_prop {Ann} {T} 
            (prop : forall TT:definition_function_types, 
                (DefinedFunction Ann TT) -> Prop)
            (df:DefinedFunction Ann T) {struct df}: Prop
*)
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
       refl_simpler; simpl; trivial.
     - destruct a; simpl.
       case_eq (@equiv_dec var_type _ _ _ xv x); simpl; intros.
       + destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
         refl_simpler; simpl; trivial.
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
       refl_simpler; simpl; trivial.
     - destruct a; simpl.
       case_eq (@equiv_dec var_type _ _ _ xv x); simpl; intros.
       + destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
         refl_simpler; simpl; trivial.
       + destruct (@equiv_dec var_type _ _ _ xv xv); [| congruence].
         refl_simpler; simpl; trivial.
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
       induction (bounded_seq0 n); simpl.
       {  intros; inversion H0; subst; trivial. }
       intros gradenv d eqq.
       case_eq ((list_env_iter
             (fun (j : {m' : nat | (m' < m)%nat}) (env0 : df_env) =>
              df_eval_backprop_deriv env (x a j) env0 (grad a j)) (Some gradenv) 
             (bounded_seq0 m)))
       ; [ intros dd ddeqq | intros ddeqq]
       ; rewrite ddeqq in eqq
       ; simpl in eqq
       ; [| destruct l; simpl; discriminate].
       specialize (IHl _ _ eqq).
       cut (forall xv : var_type, vartlookup gradenv xv <> None -> vartlookup dd xv <> None)
       ; [ eauto | ].
       clear d IHl eqq.
       revert gradenv dd ddeqq.
       induction (bounded_seq0 m); simpl
       ; intros gradenv dd ddeqq
       ; simpl in ddeqq.
       { inversion ddeqq; subst; trivial. }
       case_eq (df_eval_backprop_deriv env (x a a0) gradenv (grad a a0))
       ; [intros dd2 ddeqq2 | intros ddeqq2]
       ; rewrite ddeqq2 in ddeqq
       ; simpl in ddeqq
       ; [| destruct l0; simpl; discriminate].
       eauto.
     - Case "Var"%string.
       intros.
       destruct (vartlookup gradenv v)  ; [|congruence].
       intros.
       inversion H.
       destruct (vart_dec v xv).
       + subst; rewrite lookup_update.
         discriminate.
       + rewrite lookup_update_neq; trivial.
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
       simpl in *.
       match_destr; simpl; eauto.
     - Case "MatrixApply"%string.
       intros grad gradenv d.
       destruct (df_eval env df2)  ; [|congruence].
       match_destr; simpl; eauto.
     - Case "VLossfun"%string.
       intros grad gradenv d.
       destruct (df_eval env df2)  ; [|congruence].
       match_destr; simpl; eauto.
     - Case "MLossfun"%string.
       intros grad gradenv d.
       destruct (df_eval env df2)  ; [|congruence].
       match_destr; simpl; eauto.
   Qed.

    Definition df_eval_deriv_gen_top {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v: var_type) :
      option (lifted_type (definition_function_types_interp T) (snd v)) :=
      match (snd v) as vt return option (lifted_type (definition_function_types_interp T) vt) with
        | DTfloat => df_eval_deriv_genvar σ df ((mk_env_entry (fst v, DTfloat) 1)::nil)
        | DTVector n => 
          vectoro_to_ovector 
            (fun i => df_eval_deriv_genvar σ df ((mk_env_entry (fst v, DTVector n) (UnitVector n i))::nil))
        | DTMatrix n m => 
          matrixo_to_omatrix
            (fun i j => df_eval_deriv_genvar σ df ((mk_env_entry (fst v, DTMatrix n m) (UnitMatrix n m i j))::nil))
      end.

    Program Definition subvar (x : var_type) (grad_env:df_env) :=
      (match snd x as y return snd x = y ->
                               definition_function_types_interp y -> 
                               definition_function_types_interp y with
       | DTfloat =>  fun pf grad => match vartlookup grad_env x with
                     | Some val => ((coerce _ val):float) - grad
                     | _ => Fopp grad
                     end
       | DTVector n => fun pf grad => match vartlookup grad_env x with
                       | Some val => fun i => (((coerce _ val):Vector float n) i) - (grad i) 
                       | _ => vmap Fopp grad
                       end
       | DTMatrix m n => fun pf grad => match vartlookup grad_env x with
                         | Some val => fun i j => (((coerce _ val):Matrix float m n) i j) - (grad i j)
                         | _ => vmap (vmap Fopp) grad
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
    
    Definition df_eval_backprop_delta {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v: var_type) (grad_env:df_env) (grad: definition_function_types_interp T) :
      option (definition_function_types_interp (snd v)) :=
      match vartlookup grad_env v with
      | Some old =>
        lift (fun e => subvar v e old) (df_eval_backprop_deriv σ df grad_env grad)
      | None => None
      end.

(*
    Program Definition df_eval_backward_gen_top {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v: var_type) (grad_env:df_env) :
      option (lifted_type (definition_function_types_interp (snd v)) T) :=
      (match T as vt return T = vt -> option (lifted_type (definition_function_types_interp (snd v)) vt) with
      | DTfloat => fun pf => df_eval_backprop_delta σ df v grad_env (coerce _ 1)
      | DTVector n => fun pf =>
                        vectoro_to_ovector 
                          (fun i => df_eval_backprop_delta σ df v grad_env (coerce _ (UnitVector n i)))
      | DTMatrix m n => fun pf =>
                          matrixo_to_omatrix
                            (fun i j => df_eval_backprop_delta σ df v grad_env (coerce _ (UnitMatrix m n i j)))
      end) (eq_refl _).
 *)
    
    Program Definition df_eval_backward_gen_top {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v: var_type) (grad_env:df_env) :
      option (lifted_type (definition_function_types_interp (snd v)) T) :=
      match vartlookup grad_env v with
      | Some old =>
        (match T as vt return T = vt -> option (lifted_type (definition_function_types_interp (snd v)) vt) with
         | DTfloat => fun pf => (lift (fun e => subvar v e old) (df_eval_backprop_deriv σ df grad_env (coerce _ 1)))
         | DTVector n => fun pf =>
                           vectoro_to_ovector 
                             (fun i => lift (fun e => subvar v e old) (df_eval_backprop_deriv σ df grad_env (coerce _ (UnitVector n i))))
         | DTMatrix m n => fun pf =>
                             matrixo_to_omatrix
                               (fun i j => lift (fun e => subvar v e old) (df_eval_backprop_deriv σ df grad_env (coerce _ (UnitMatrix m n i j))))
         end) (eq_refl _)
      | None => None
      end.

    (*
    Lemma df_eval_backward_gen_top_same {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (v: var_type) (grad_env1 grad_env2:df_env) :
      (vartlookup grad_env1 v <> None <-> vartlookup grad_env1 v <> None) ->
      df_eval_backward_gen_top σ df v grad_env1 = df_eval_backward_gen_top σ df v grad_env2.
    Proof.
    Admitted.
     *)


    Definition transpose_lifted_type {T1 T2} :
               lifted_type (definition_function_types_interp T1) T2 ->
      lifted_type (definition_function_types_interp T2) T1
      := match T1, T2 with
         | DTfloat, _ => fun inp => inp
         | _, DTfloat => fun inp => inp
         | DTVector n1, DTVector n2 => fun inp => fun i j => inp j i
         | DTMatrix m1 n1, DTMatrix m2 n2 => fun inp => fun i j p q => inp p q i j
         | DTVector n1, DTMatrix m2 n2 => fun inp => fun i p q => inp p q i
         | DTMatrix m1 n1, DTVector n2 => fun inp => fun i j p => inp p i j
         end.
    Section deriv_deriv.
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

    Fixpoint df_free_variables {Ann} {T} (f : DefinedFunction Ann T) : list var_type
      := match f with
         | Number _ x => nil
         | DVector n _ x => vlconcat_map df_free_variables x
         | Constant t _ x => nil
         | DMatrix n m _ x => vlconcat_map (fun a => vlconcat_map df_free_variables a) x
         | Var v _ => v::nil
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
         | VectorApply n _ x s l => (remove_all (x,DTfloat) (df_free_variables s)) 
                                      ++ (df_free_variables l)
         | MatrixApply n m _ x s l => (remove_all (x,DTfloat) (df_free_variables s)) 
                                        ++ (df_free_variables l)
         | VLossfun n _ v1 v2 s l r => (remove_all (v1,DTfloat) (remove_all (v2,DTfloat) (df_free_variables s)))
                                         ++ (df_free_variables l)
         | MLossfun n m _ v1 v2 s l r => (remove_all (v1,DTfloat) (remove_all (v2,DTfloat) (df_free_variables s)))
                                           ++ (df_free_variables l)
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

    Definition df_closed_over {Ann} {T} (f : DefinedFunction Ann T) (vl : list var_type) : Prop
      := incl (df_free_variables f) vl.

    Fixpoint fully_closed_over {Ann} {T} (df : DefinedFunction Ann T) (vl : list var_type) : Prop
      := 
         match df with
         | Number _ x => True
         | DVector n _ x => vforall (fun f => fully_closed_over f vl) x
         | Constant t _ x => True
         | DMatrix n m _ x => vforall (fun row => 
                                         (vforall (fun f => fully_closed_over f vl) row)) x
         | Var v _ => In v vl
         | Plus _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | Minus _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | Times _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | Divide _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | Max _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | Abs _ e => fully_closed_over e vl
         | Sign _ e => fully_closed_over e vl
         | PSign _ e => fully_closed_over e vl
         | Log _ e => fully_closed_over e vl
         | Square _ e => fully_closed_over e vl
         | Exp _ e => fully_closed_over e vl
         | VectorElem n _ l i => fully_closed_over l vl
         | MatrixElem m n _ l i j => fully_closed_over l vl
         | VectorDot n _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | VectorSum n _ l => fully_closed_over l vl
         | MatrixSum n m _ l => fully_closed_over l vl
         | VectorScalMult n _ x r => (fully_closed_over x vl) /\ (fully_closed_over r vl)
         | MatrixScalMult n m _ x r => (fully_closed_over x vl) /\ (fully_closed_over r vl)
         | MatrixVectorMult n m _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | MatrixVectorAdd n m _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | MatrixMult n m p _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | VectorPlus n _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | VectorMinus n _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | MatrixPlus n m _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | MatrixMinus n m _ l r => (fully_closed_over l vl) /\ (fully_closed_over r vl)
         | VectorApply n _ x s l => (fully_closed_over s ((x,DTfloat)::nil)) /\ 
                                    (fully_closed_over l vl)
         | MatrixApply n m _ x s l => (fully_closed_over s ((x,DTfloat)::nil)) /\ 
                                      (fully_closed_over l vl)
         | VLossfun n _ v1 v2 s l r => (fully_closed_over s ((v1,DTfloat)::(v2,DTfloat)::nil))
                                       /\ (fully_closed_over l vl)
         | MLossfun n m _ v1 v2 s l r => (fully_closed_over s ((v1,DTfloat)::(v2,DTfloat)::nil))
                                         /\ (fully_closed_over l vl)
         end.
        
    Definition In_compat_map (f : list var_type -> list var_type) : Prop :=
      forall (v : var_type) (vl : list var_type), 
        In v vl -> In v (f vl).
    
    Definition map_tl (f : list var_type -> list var_type) (vl : list var_type) :=
        match vl with
        | a :: vl1 => a :: f vl1 
        | _ => f vl
        end.

    Lemma In_compat_map_tl (f : list var_type -> list var_type) :
      In_compat_map f -> In_compat_map (map_tl f).
    Proof.
      unfold In_compat_map; intros.
      destruct vl.
      + now simpl.
      + simpl in *.
        destruct H0.
        * now left.
        * right; now apply H.
    Qed.

    Lemma fully_closed_over_map {T} (df : DefinedFunction UnitAnn T) (vl : list var_type) (f : list var_type -> list var_type) :
      In_compat_map f -> fully_closed_over df vl -> fully_closed_over df (f vl).
    Proof.
      revert f; revert vl.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; simpl; intros; try solve [
                       trivial
                         |
                    apply IHdf; trivial
                         |
                    split; destruct H0;
                    [apply IHdf1; trivial
                    | apply IHdf2; trivial]
                         ].
      - Case "DVector"%string.
        apply vforall_forall; intros.
        apply H; trivial.
        now rewrite vforall_forall in H1.
      - Case "DMatrix"%string.
        apply vforall_forall; intros.
        apply vforall_forall; intros.                
        apply H; trivial.
        rewrite vforall_forall in H1.
        specialize (H1 i).
        now rewrite vforall_forall in H1.
      - now apply H.
      - Case "VectorApply"%string.
        split; destruct H0; trivial.
        now apply IHdf2.
      - Case "MatrixApply"%string.
        split; destruct H0; trivial.
        now apply IHdf2.
      - Case "VLossfun"%string.
        split; destruct H0; trivial.
        now apply IHdf2.
      - Case "MLossfun"%string.
        split; destruct H0; trivial.
        now apply IHdf2.
    Qed.

  (*
    Lemma closed_is_fully_closed {Ann} {T} (df : DefinedFunction Ann T) (vl : list var_type) : 
      df_closed_over df vl <-> fully_closed_over df vl.
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

Ltac refl_simpler := 
  repeat
    match goal with
    | [H: @eq var_type _ _ |- _ ] => try (inversion H; subst); rewrite (var_type_UIP_refl H)
    | [H: @equiv var_type _ _ _ _ |- _ ] => try (inversion H; subst); rewrite (var_type_UIP_refl H)
    | [H: @eq definition_function_types _ _ |- _ ] => try (inversion H; subst); rewrite (definition_function_types_UIP_refl H)
    | [H: @equiv definition_function_types _ _ _ _ |- _ ] => try (inversion H; subst); rewrite (definition_function_types_UIP_refl H)
    end.

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
           apply (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv isc1 xinn).
         case_eq (df_eval_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
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
           apply (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + specialize (IHl grad gradenv isc1 xinn).
         case_eq (df_eval_backprop_deriv env l gradenv grad); simpl; trivial; intros.
         rewrite H in IHl.
         simpl in IHl.
         generalize (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
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
           apply (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + case_eq (df_eval env r);
           [ intros re eqre | intros eqre]
           ; simpl; trivial.
           specialize (IHl (re * grad)%R gradenv isc1 xinn).
           case_eq (df_eval_backprop_deriv env l gradenv (re * grad)%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
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
           apply (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn).
       + case_eq (df_eval env r);
           [ intros re eqre | intros eqre]
           ; simpl; trivial.
           specialize (IHl (grad / re)%R gradenv isc1 xinn).
           case_eq (df_eval_backprop_deriv env l gradenv (grad / re)%R); simpl; trivial; intros.
           rewrite H in IHl.
           simpl in IHl.
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none H (x, DTfloat) xinn); intros.
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

   (*

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
    *)

    Lemma eval_fully_closed_not_none {T} (σ:df_env) (df:DefinedFunction UnitAnn T) :
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> df_eval σ df <> None.
    Proof.
      revert σ.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; simpl; intros;
        try solve 
            [congruence
            |
            destruct H; simpl in *;
            specialize (IHdf1 σ); specialize (IHdf2 σ);
            match_option; [|tauto];
            cut_to IHdf2;
            [ match_option; tauto | easy]
            |
            specialize (IHdf σ); simpl in IHdf;
            cut_to IHdf;
            [ match_option; tauto | easy]
            ].
      - Case "DVector"%string.
        apply vectoro_to_ovector_not_none; intro.
        specialize (H i σ); simpl in H; apply H.
        rewrite vforall_forall in H0.
        now specialize (H0 i).
      - Case "DMatrix"%string.
        unfold matrixo_to_omatrix.
        apply vectoro_to_ovector_not_none; intro.
        apply vectoro_to_ovector_not_none; intro.        
        specialize (H i i0 σ); simpl in H; apply H.
        rewrite vforall_forall in H0; specialize (H0 i).
        rewrite vforall_forall in H0; now specialize (H0 i0).        
      - Case "Var"%string.
        induction σ.
        + simpl in H; tauto.
        + simpl in *.
          match_case; intros.
          destruct H.
          * congruence.
          * now apply IHσ.
      - Case "VectorApply"%string.
        destruct H; simpl in *.
        specialize (IHdf2 σ).
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        apply vectoro_to_ovector_not_none; intro.
        specialize (IHdf1  (mk_env_entry (v, DTfloat) (d i) :: nil)).
        now apply IHdf1.
      - Case "MatrixApply"%string.
        destruct H; simpl in *.
        specialize (IHdf2 σ).
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        unfold matrixo_to_omatrix.
        apply vectoro_to_ovector_not_none; intro.
        apply vectoro_to_ovector_not_none; intro.
        specialize (IHdf1 (mk_env_entry (v, DTfloat) (d i i0) :: nil)).
        now apply IHdf1.
      - Case "VLossfun"%string.
        destruct H; simpl in *.
        specialize (IHdf2 σ).
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        match_option.
        apply vectoro_to_ovector_not_none in eqq0.
        + tauto.
        + intros.
          specialize (IHdf1 (mk_env_entry (v1, DTfloat) (d i) :: mk_env_entry (v2, DTfloat) (r i) :: nil)).
          now apply IHdf1.
      - Case "MLossfun"%string.
        destruct H; simpl in *.
        specialize (IHdf2 σ).
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        unfold matrixo_to_omatrix.
        match_option.
        apply vectoro_to_ovector_not_none in eqq0.
        + tauto.
        + intros.
          apply vectoro_to_ovector_not_none; intros.
          specialize (IHdf1 (mk_env_entry (v1, DTfloat) (d i i0) :: mk_env_entry (v2, DTfloat) (r i i0) :: nil)).
          now apply IHdf1.
    Qed.

   Lemma eval_fully_closed_total {T} (σ:df_env) (df:DefinedFunction UnitAnn T) :
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> 
      {d:definition_function_types_interp T | df_eval σ df = Some d}.
   Proof.
     intros.
     case_eq (df_eval σ df); intros.
     - now exists d.
     - generalize (eval_fully_closed_not_none σ df).
       intros; simpl in *.
       cut_to H1; tauto.
  Qed.

   Lemma closed_over_cons {T} (df:DefinedFunction UnitAnn T) (v:var_type) (vl : list var_type): 
     df_closed_over df vl -> df_closed_over df (v::vl).
   Proof.
     unfold df_closed_over.
     intros.
     apply incl_tl.
     apply H.
   Qed.

   Lemma fully_closed_over_cons {T} (df:DefinedFunction UnitAnn T) (v:var_type) 
         (vl : list var_type): 
     fully_closed_over df vl -> fully_closed_over df (v::vl).
   Proof.
     intros.
     apply (fully_closed_over_map df vl (fun vl1 => cons v vl1)); trivial.
     unfold In_compat_map.
     intros.
     now apply in_cons.
   Qed.

   Lemma fully_closed_over_exchange_vars {T} (df:DefinedFunction UnitAnn T) (v1 v:var_type) 
         (vl : list var_type): 
     fully_closed_over df (v1 :: v :: vl) -> fully_closed_over df (v :: v1 :: vl).
     Proof.
       intros.
       apply (fully_closed_over_map df (v1 :: v :: vl) 
                                    (fun vl1 => match vl1 with
                                                | a :: b :: vl2  => b :: a :: vl2
                                                | _ => vl1
                                                end  )); trivial.
       unfold In_compat_map.
       intros.
       destruct vl0; trivial.
       destruct vl0; trivial.
       unfold In.
       unfold In in H0.
       tauto.
     Qed.

   Lemma fully_closed_over_singleton {T} (df:DefinedFunction UnitAnn T) (v:var_type) 
         (vl : list var_type): 
     fully_closed_over df (v::nil) -> fully_closed_over df (v::vl).
   Proof.
     intros.
     induction vl; trivial.
     apply fully_closed_over_exchange_vars.
     now apply fully_closed_over_cons.
   Qed.

   Lemma fully_closed_over_exchange_2vars {T} (df:DefinedFunction UnitAnn T) 
         (v1 v2 v:var_type) (vl : list var_type): 
     fully_closed_over df (v1 :: v2 :: v:: vl) -> fully_closed_over df (v :: v1 :: v2 :: vl).
     Proof.
       intros.
       apply (fully_closed_over_map df (v1 :: v2 :: v :: vl) 
                                    (fun vl1 => match vl1 with
                                                | a :: b :: c :: vl2  => c :: a :: b :: vl2
                                                | _ => vl1
                                                end  )); trivial.
       unfold In_compat_map.
       intros.
       destruct vl0; trivial.
       destruct vl0; trivial.
       destruct vl0; trivial.
       unfold In.
       unfold In in H0.
       tauto.
     Qed.

   Lemma fully_closed_over_pair {T} (df:DefinedFunction UnitAnn T) (v1 v2:var_type) 
         (vl : list var_type): 
     fully_closed_over df (v1::v2::nil) -> fully_closed_over df (v1::v2::vl).
   Proof.
     intros.
     induction vl; trivial.
     apply fully_closed_over_exchange_2vars.
     apply fully_closed_over_exchange_2vars.     
     now apply fully_closed_over_cons.
   Qed.

   Lemma fully_closed_subst {T} (vl:list var_type) (df:DefinedFunction UnitAnn T) (v:var_type)
     (e':DefinedFunction UnitAnn (snd v)):
     fully_closed_over df (v::vl) -> 
     fully_closed_over e' vl ->
     fully_closed_over (df_subst df v e') vl.
   Proof.
      revert vl.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; simpl; intros; try solve
        [easy
            |
        apply IHdf; [apply H | apply H0]
            |
       split; destruct H; simpl in *;
       [ apply IHdf1; [apply H | apply H0]
       | apply IHdf2; [apply H1 | apply H0]]
            ].
      - Case "DVector"%string.
        apply vforall_forall; intros; simpl in *.
        specialize (H i); apply H.
        rewrite vforall_forall in H0.
        specialize (H0 i). 
        apply H0.
        apply H1.
     - Case "DMatrix"%string.
       apply vforall_forall; intros.
       apply vforall_forall; intros; simpl in *.
       specialize (H i i0); apply H.
       rewrite vforall_forall in H0; specialize (H0 i).
       rewrite vforall_forall in H0; specialize (H0 i0).
       apply H0.
       apply H1.
     - Case "Var"%string.
       unfold substvar.
       destruct H.
       + subst.
         unfold substvar.
         match_destr; [ | congruence].
         refl_simpler.
         simpl; trivial.
       + destruct v; destruct v0.
         simpl in *.
         match_destr.
         red in e; subst.
         simpl; trivial.
     - Case "VectorApply"%string.
       destruct H; split; trivial.
       + apply IHdf2.
         * apply H1.
         * apply H0.
     - Case "MatrixApply"%string.
       destruct H; split; trivial.
       + apply IHdf2.
         * apply H1.
         * apply H0.
     - Case "VLossfun"%string.
       destruct H; split; trivial.
       + apply IHdf2.
         * apply H1.
         * apply H0.
     - Case "MLossfun"%string.
       destruct H; split; trivial.
       + apply IHdf2.
         * apply H1.
         * apply H0.
   Qed.

   Lemma fully_closed_deriv {T} (df:DefinedFunction UnitAnn T) (s:SubVar) 
         (vl : list var_type):
     fully_closed_over df vl -> 
     fully_closed_over (df_deriv df (s, DTfloat)) vl.
   Proof.
      revert s; revert vl.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; simpl; intros; try solve 
        [easy
            |
        apply IHdf,H
            |             
        split; try easy; now apply IHdf
            |
        destruct H; repeat split; try easy;
        [apply IHdf2, H0 |  apply IHdf1, H]
            |
        destruct H; repeat split; try easy;
        [ apply IHdf1, H |  apply IHdf2, H0]
            ].
      - Case "DVector"%string.
        apply vforall_forall; intros.
        apply H.
        rewrite vforall_forall in H0. 
        now apply H0.
      - Case "DMatrix"%string.
        apply vforall_forall; intros.
        apply vforall_forall; intros.        
        apply H.
        rewrite vforall_forall in H0. 
        specialize (H0 i).
        rewrite vforall_forall in H0. 
        now specialize (H0 i0).
      - Case "Max"%string.
        destruct H; repeat split; try easy.
        apply IHdf2, H0.
        apply IHdf1, H.        
        apply IHdf2, H0.        
        apply IHdf1, H.        
      - Case "VectorApply"%string.
        apply vforall_forall; intros; simpl in *.
        split; destruct H.
        apply IHdf2, H0.
        apply fully_closed_subst.
        + apply IHdf1.
          now apply fully_closed_over_singleton.
        + simpl; apply H0.
      - Case "MatrixApply"%string.
        apply vforall_forall; intros; simpl in *.
        apply vforall_forall; intros; simpl in *.        
        split; destruct H.
        apply IHdf2, H0.
        apply fully_closed_subst.
        + apply IHdf1.
          now apply fully_closed_over_singleton.
        + simpl; apply H0.
      - Case "VLossfun"%string.        
        intros; simpl in *.
        split; destruct H.
        apply IHdf2, H0.
        apply vforall_forall; intros; simpl in *.        
        apply fully_closed_subst.
        apply fully_closed_subst.
        + apply IHdf1.
          now apply fully_closed_over_pair.
        + simpl; apply fully_closed_over_cons; apply H0.
        + now simpl.
      - Case "MLossfun"%string.
        intros; simpl in *.
        apply vforall_forall; intros; simpl in *.        
        apply vforall_forall; intros; simpl in *.        
        destruct H; split; trivial.
        split.
        apply IHdf2, H0.
        apply fully_closed_subst.
        apply fully_closed_subst.
        + apply IHdf1.
          now apply fully_closed_over_pair.
        + simpl; apply fully_closed_over_cons; apply H0.
        + now simpl.
   Qed.        

   Lemma list_env_iter_total_fun {A} (f : A -> df_env -> option df_env) (env : df_env) (l : list A) :
     (forall (a:A) (env0: df_env), (f a env0) <> None) ->
     list_env_iter f (Some env) l <> None.
   Proof.
     intros.
     generalize env.
     induction l; [simpl; congruence|].
     simpl; intros.
     specialize (H a env0).
     case_eq (f a env0).
     - intros; apply (IHl d).
     - tauto.
   Qed.

    Lemma backprop_deriv_fully_closed_not_none {T} (σ:df_env) (df:DefinedFunction UnitAnn T) 
          (grad_env:df_env) (grad: definition_function_types_interp T):
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> df_eval_backprop_deriv σ df grad_env grad <> None.
    Proof.
      revert grad_env.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; simpl; intros;
        try solve [congruence 
                  | 
                  specialize (IHdf1 grad grad_env); simpl in IHdf1; destruct H;
                  match_option; [|tauto];
                  specialize (IHdf2 grad d); simpl in IHdf2;
                  now apply IHdf2
                  ].
      - Case "DVector"%string.
        unfold two_vector_env_iter_alt.
        rewrite vforall_forall in H0.
        apply (list_env_iter_total_fun 
                 (fun i env => df_eval_backprop_deriv σ (x i) env (grad i))    
                 grad_env (bounded_seq0 n)).
        intros.
        apply (H a (grad a) env0).
        apply (H0 a).
      - Case "DMatrix"%string.
        unfold two_matrix_env_iter_alt.
        rewrite vforall_forall in H0.
        apply (list_env_iter_total_fun 
                 (fun i env => 
                    list_env_iter
                      (fun j env0 =>
                         df_eval_backprop_deriv σ (x i j) env0 (grad i j))
                      (Some env) (bounded_seq0 m))
                 grad_env (bounded_seq0 n)).
        intros.
        apply (list_env_iter_total_fun 
                 (fun j env => df_eval_backprop_deriv σ (x a j) env (grad a j))    
                 env0 (bounded_seq0 m)).
        intros.
        apply (H a a0  (grad a a0) env1).
        specialize (H0 a).
        rewrite vforall_forall in H0.
        apply (H0 a0).
      - Case "Var"%string.
        match_destr.
      - Case "Minus"%string.
        specialize (IHdf1 grad grad_env); simpl in IHdf1; destruct H;
        match_option; [|tauto];
        specialize (IHdf2 (-grad)%R d); simpl in IHdf2;
        now apply IHdf2.
      - Case "Times"%string.
        destruct H.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H1.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H2.
        + match_option; [|tauto].
          specialize (IHdf1 (d0 * grad)%R grad_env); simpl in IHdf1.
          match_option; [|tauto].
          specialize (IHdf2 (d * grad)%R d1); simpl in IHdf2.
          now apply IHdf2.
      - Case "Divide"%string.          
        destruct H.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H1.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H2.
        + match_option; [|tauto].
          specialize (IHdf1 (grad / d0)%R grad_env); simpl in IHdf1.
          match_option; [|tauto].
          specialize (IHdf2 (-d / (d0 * d0) * grad)%R d1); simpl in IHdf2.
          now apply IHdf2.
      - Case "Square"%string.
        generalize (eval_fully_closed_not_none σ df); intros; simpl in H0.
        match_option; [|tauto].
        specialize (IHdf (2 * d * grad)%R grad_env); simpl in IHdf.
        now apply IHdf.
      - Case "Exp"%string.
        generalize (eval_fully_closed_not_none σ df); intros; simpl in H0.
        match_option; [|tauto].
        specialize (IHdf (grad * exp d)%R grad_env); simpl in IHdf.
        now apply IHdf.
      - Case "Log"%string.
        generalize (eval_fully_closed_not_none σ df); intros; simpl in H0.        
        match_option; [|tauto].
        specialize (IHdf (grad / d)%R grad_env); simpl in IHdf.        
        now apply IHdf.
      - Case "Abs"%string.
        generalize (eval_fully_closed_not_none σ df); intros; simpl in H0.        
        match_option; [|tauto].
        specialize (IHdf (grad * sign d)%R grad_env); simpl in IHdf.        
        now apply IHdf.
      - Case "Sign"%string.
        specialize (IHdf (0)%R grad_env); simpl in IHdf.        
        now apply IHdf.
      - Case "PSign"%string.
        specialize (IHdf (0)%R grad_env); simpl in IHdf.        
        now apply IHdf.
      - Case "Max"%string.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H0.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H1.
        match_option; [|tauto].
        match_destr.
        specialize (IHdf2 grad grad_env).
        now apply IHdf2.
        specialize (IHdf1 grad grad_env).
        now apply IHdf1.        
      - Case "VectorDot"%string.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H0.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H1.
        match_option; [|tauto].
        specialize (IHdf1 (vmap (fun rv : R => (rv * grad)%R) d0) grad_env); simpl in IHdf1.
        match_option; [|tauto].
        specialize (IHdf2 (vmap (fun lv : R => (lv * grad)%R) d) d1).
        now apply IHdf2.
      - Case "VectorSum"%string.
        specialize (IHdf (ConstVector n grad) grad_env).
        now apply IHdf.
      - Case "MatrixSum"%string.
        specialize (IHdf (ConstMatrix m n grad) grad_env).
        now apply IHdf.
      - Case "VectorElem"%string.
        specialize (IHdf (fun k : {n' : nat | n' < n} => if equiv_dec (` k) (` i) then grad else 0%R) grad_env).
        now apply IHdf.
      - Case "MatrixElem"%string.
        specialize (IHdf (fun (k1 : {n' : nat | n' < m}) 
                              (k2 : {m' : nat | m' < n}) =>
                            if equiv_dec (` k1) (` i) then if
                                equiv_dec (` k2) (` j) then grad else 0%R else 0%R)
                         grad_env).
        now apply IHdf.
      - Case "MatrixVectorMult"%string.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H0.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H1.
        match_option; [|tauto].
        specialize (IHdf1  (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) => (grad i * d0 j)%R)
                           grad_env); simpl in IHdf1.
        match_option; [|tauto].
        specialize (IHdf2 (matrix_vector_mult 
                             (fun (i : {n' : nat | n' < n}) 
                                  (j : {m' : nat | m' < m}) => d j i)
                             grad)
                          d1).
        now apply IHdf2.
      - Case "MatrixVectorAdd"%string.
        specialize (IHdf1 grad grad_env); simpl in IHdf1.
        match_option; [|tauto].
        match_option.
        generalize (list_env_iter_total_fun
                       (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                          df_eval_backprop_deriv σ df2 env (@transpose R m n grad i))
                       d (bounded_seq0 n)); intros.
        cut_to H0; [congruence|].
        intros; destruct H.
        now apply IHdf2.
      - Case "MatrixMult"%string.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H0.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H1.
        match_option; [|tauto].
        specialize (IHdf1 (matrix_mult grad (fun (i : {n' : nat | n' < n}) 
                                                 (j : {m' : nat | m' < p}) => d0 j i)) 
                          grad_env); simpl in IHdf1.
        match_option; [|tauto].
        specialize (IHdf2 (matrix_mult (fun (i : {n' : nat | n' < p}) 
                                            (j : {m' : nat | m' < m}) => d j i) grad) 
                          d1).
        now apply IHdf2.
      - Case "VectorMinus"%string.
        specialize (IHdf1 grad grad_env); simpl in IHdf1.
        match_option; [|tauto].
        specialize (IHdf2 (fun i : {n' : nat | n' < n} => (- grad i)%R) d).
        now apply IHdf2.
      - Case "MatrixMinus"%string.
        specialize (IHdf1 grad grad_env); simpl in IHdf1.
        match_option; [|tauto].
        specialize (IHdf2 (fun (i : {n' : nat | n' < n}) 
                               (j : {m' : nat | m' < m}) => (- grad i j)%R)
                          d).
        now apply IHdf2.
      - Case "VectorScalMult"%string.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H0.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H1.
        match_option; [|tauto].
        specialize (IHdf1 (vsum (fun j : {n' : nat | n' < n} => (d0 j * grad j)%R))
                          grad_env); simpl in IHdf1.
        match_option; [|tauto].
        specialize (IHdf2 (fun j : {n' : nat | n' < n} => (d * grad j)%R) d1).
        now apply IHdf2.
      - Case "MatrixScalMult"%string.
        generalize (eval_fully_closed_not_none σ df1); intros; simpl in H0.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H1.
        match_option; [|tauto].
        specialize (IHdf1 (msum
                             (fun (i : {n' : nat | n' < n}) 
                                  (j : {m' : nat | m' < m}) => (d0 i j * grad i j)%R))
                          grad_env); simpl in IHdf1.
        match_option; [|tauto].
        specialize (IHdf2 (fun (i : {n' : nat | n' < n}) 
                               (j : {m' : nat | m' < m}) => (grad i j * d)%R)
                          d1).
        now apply IHdf2.
      - Case "VectorApply"%string.
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H0.
        match_option; [|tauto].
        match_option.
        + specialize (IHdf2 v0 grad_env).
          now apply IHdf2.
        + apply vectoro_to_ovector_exists_None in eqq0.
          destruct eqq0.
          rewrite vmap_nth in e; simpl in e.
          destruct H.
          match_option_in e.
          generalize (fully_closed_deriv df1 v ((v,DTfloat):: nil)); intros.
          cut_to H2; trivial.
          generalize (eval_fully_closed_not_none (mk_env_entry (v, DTfloat) (d x) :: nil)
                                              (df_deriv df1 (v, DTfloat))); intros.
          simpl in H3; cut_to H3; tauto.
      - Case "MatrixApply"%string.     
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H0.
        match_option; [|tauto].
        match_option.
        + specialize (IHdf2 m0 grad_env).
          now apply IHdf2.
        + unfold matrixo_to_omatrix in eqq0.
          apply vectoro_to_ovector_exists_None in eqq0; destruct eqq0.
          apply vectoro_to_ovector_exists_None in e; destruct e.
          unfold mmap in e.
          rewrite vmap_nth in e; simpl in e.
          rewrite vmap_nth in e; simpl in e.
          destruct H.
          unfold matrix_zip in e.
          rewrite vmap_nth in e; simpl in e.
          match_option_in e.
          generalize (fully_closed_deriv df1 v ((v,DTfloat):: nil)).
          intros; cut_to H2; trivial.
          generalize (eval_fully_closed_not_none (mk_env_entry (v, DTfloat) (d x x0) :: nil)
                                              (df_deriv df1 (v, DTfloat))); intros.
          simpl in H3; cut_to H3; tauto.
      - Case "VLossfun"%string.
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H0.
        match_option; [|tauto].
        match_option.
        + specialize (IHdf2 v grad_env).
          now apply IHdf2.
        + apply vectoro_to_ovector_exists_None in eqq0.
          destruct eqq0.
          rewrite vmap_nth in e; simpl in e.
          destruct H.
          match_option_in e.
          generalize (fully_closed_deriv df1 v1 ((v1,DTfloat)::(v2,DTfloat)::nil)).
          intros; cut_to H2; trivial.
          generalize (eval_fully_closed_not_none (mk_env_entry (v1, DTfloat) (d x) ::
                                                        mk_env_entry (v2, DTfloat) (r x) :: nil)
                                              (df_deriv df1 (v1, DTfloat))); intros.
          simpl in H3; cut_to H3; tauto.
      - Case "MLossfun"%string.
        generalize (eval_fully_closed_not_none σ df2); intros; simpl in H0.
        match_option; [|tauto].
        match_option.
        + specialize (IHdf2 m0 grad_env).
          now apply IHdf2.
        + unfold matrixo_to_omatrix in eqq0.
          apply vectoro_to_ovector_exists_None in eqq0; destruct eqq0.
          apply vectoro_to_ovector_exists_None in e; destruct e.
          unfold mmap in e.
          rewrite vmap_nth in e; simpl in e.
          rewrite vmap_nth in e; simpl in e.
          destruct H.
          unfold matrix_zip in e.
          rewrite vmap_nth in e; simpl in e.
          match_option_in e.
          generalize (fully_closed_deriv df1 v1 ((v1,DTfloat)::(v2,DTfloat)::nil)).
          intros; cut_to H2; trivial.
          generalize (eval_fully_closed_not_none (mk_env_entry (v1, DTfloat) (d x x0) ::
                                                        mk_env_entry (v2, DTfloat) (r x x0) :: nil)
                                              (df_deriv df1 (v1, DTfloat))); intros.
          simpl in H3; cut_to H3; tauto.
    Qed.

    Lemma backprop_deriv_fully_closed_total {T} (σ:df_env) (df:DefinedFunction UnitAnn T) 
          (grad_env:df_env) (grad: definition_function_types_interp T):
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> 
      {d:df_env | df_eval_backprop_deriv σ df grad_env grad = Some d}.
    Proof.
     case_eq (df_eval_backprop_deriv σ df grad_env grad); intros.
     - now exists d.
     - generalize (backprop_deriv_fully_closed_not_none σ df grad_env grad).
       intros; simpl in *.
       cut_to H1; tauto.
    Qed.

    Lemma eval_deriv_fully_closed_not_none {T} (σ:df_env) (df:DefinedFunction UnitAnn T) 
          (v:var_type):
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> df_eval_deriv σ df v <> None.
    Proof.
      revert σ v.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; intros; simpl in *;
        try solve [
        congruence 
            |
        destruct H
        ; specialize (IHdf1 σ v); specialize (IHdf2 σ v)
        ;cut_to IHdf1; trivial
        ;match_option; [|tauto]
        ;cut_to IHdf2; trivial
        ;match_option; tauto
            |
        destruct H;
        specialize (IHdf1 σ v); specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df1); intros; simpl in H1;
        cut_to H1; trivial;
        match_option; [|tauto];
        cut_to IHdf1; trivial;
        match_option; [|tauto];
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H2;
        match_option; [|tauto];
        cut_to IHdf2; trivial;
        match_option; tauto
            |
        generalize (eval_fully_closed_not_none σ df); intros; 
        specialize (IHdf σ v);
        simpl in H0; cut_to H0; trivial;
        match_option; [|tauto];
        cut_to IHdf; trivial;
        match_option; tauto
            |
        specialize (IHdf σ v);
        generalize (eval_fully_closed_not_none σ df); intros;
        simpl in H0; cut_to H0; trivial;
        match_option; tauto
            ].
      - Case "DVector"%string.
        apply vectoro_to_ovector_not_none; intros; apply H.
        rewrite vforall_forall in H0; apply H0.
      - Case "DMatrix"%string.
        apply vectoro_to_ovector_not_none; intros.
        apply vectoro_to_ovector_not_none; intros; apply H.
        rewrite vforall_forall in H0; specialize (H0 i).
        rewrite vforall_forall in H0; apply H0.
      - Case "Max"%string.
        destruct H;
        specialize (IHdf1 σ v); specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df1); intros; simpl in H1;
        cut_to H1; trivial;
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H2;
        match_option; [|tauto].
        case_eq ( Rle_dec d d0 ); intros.
        cut_to IHdf2; trivial.
        cut_to IHdf1; trivial.
      - Case "VectorApply"%string.
        destruct H.
        specialize (IHdf2 σ v0);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        apply vectoro_to_ovector_not_none; intros.
        match_option.
        specialize (IHdf1 (mk_env_entry (v, DTfloat) (d i) :: nil) (v, DTfloat)).
        cut_to IHdf1; trivial.
        tauto.
      - Case "MatrixApply"%string.
        destruct H.
        specialize (IHdf2 σ v0);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        apply vectoro_to_ovector_not_none; intros.
        apply vectoro_to_ovector_not_none; intros.        
        specialize (IHdf1 (mk_env_entry (v, DTfloat) (d i i0) :: nil) (v, DTfloat)).
        cut_to IHdf1; trivial.
        match_option; tauto.
      - Case "VLossfun"%string.
        destruct H.
        specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        match_option.
        apply vectoro_to_ovector_not_none in eqq1.
        tauto.
        intros.
        specialize (IHdf1 (mk_env_entry (v1, DTfloat) (d i) :: mk_env_entry (v2, DTfloat) (r i) :: nil) (v1, DTfloat)).
        cut_to IHdf1; trivial.
        match_option; tauto.
      - Case "MLossfun"%string.
        destruct H.
        specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        match_option.
        unfold matrixo_to_omatrix in eqq1.
        apply vectoro_to_ovector_not_none in eqq1.
        tauto.
        intros.
        apply vectoro_to_ovector_not_none; intros.
        specialize (IHdf1 (mk_env_entry (v1, DTfloat) (d i i0) :: mk_env_entry (v2, DTfloat) (r i i0) :: nil)(v1, DTfloat)).
        cut_to IHdf1; trivial.
        match_option; tauto.
    Qed.

    Lemma eval_deriv_fully_closed_total {T} (σ:df_env) (df:DefinedFunction UnitAnn T) 
          (v:var_type):
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> 
      {d:definition_function_types_interp T | df_eval_deriv σ df v  = Some d}.
    Proof.
     case_eq (df_eval_deriv σ df v); intros.
     - now exists d.
     - generalize (eval_deriv_fully_closed_not_none σ df v).
       intros; simpl in *.
       cut_to H1; tauto.
    Qed.

    Lemma eval_deriv_genvar_fully_closed_not_none {T} (σ:df_env) (df:DefinedFunction UnitAnn T) 
          (v:df_env):
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> df_eval_deriv_genvar σ df v <> None.
    Proof.
      revert σ v.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; intros; simpl in *;
        try solve [
        congruence 
            |
        destruct H
        ; specialize (IHdf1 σ v); specialize (IHdf2 σ v)
        ;cut_to IHdf1; trivial
        ;match_option; [|tauto]
        ;cut_to IHdf2; trivial
        ;match_option; tauto
            |
        destruct H;
        specialize (IHdf1 σ v); specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df1); intros; simpl in H1;
        cut_to H1; trivial;
        match_option; [|tauto];
        cut_to IHdf1; trivial;
        match_option; [|tauto];
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H2;
        match_option; [|tauto];
        cut_to IHdf2; trivial;
        match_option; tauto
            |
        generalize (eval_fully_closed_not_none σ df); intros; 
        specialize (IHdf σ v);
        simpl in H0; cut_to H0; trivial;
        match_option; [|tauto];
        cut_to IHdf; trivial;
        match_option; tauto
            |
        specialize (IHdf σ v);
        generalize (eval_fully_closed_not_none σ df); intros;
        simpl in H0; cut_to H0; trivial;
        match_option; tauto
            ].
      - Case "DVector"%string.
        apply vectoro_to_ovector_not_none; intros; apply H.
        rewrite vforall_forall in H0; apply H0.
      - Case "DMatrix"%string.
        apply vectoro_to_ovector_not_none; intros.
        apply vectoro_to_ovector_not_none; intros; apply H.
        rewrite vforall_forall in H0; specialize (H0 i).
        rewrite vforall_forall in H0; apply H0.
      - Case "Max"%string.
        destruct H;
        specialize (IHdf1 σ v); specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df1); intros; simpl in H1;
        cut_to H1; trivial;
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H2;
        match_option; [|tauto].
        case_eq ( Rle_dec d d0 ); intros.
        cut_to IHdf2; trivial.
        cut_to IHdf1; trivial.
      - Case "VectorApply"%string.
        destruct H.
        specialize (IHdf2 σ v0);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        apply vectoro_to_ovector_not_none; intros.
        match_option.
        specialize (IHdf1 (mk_env_entry (v, DTfloat) (d i) :: nil) (mk_genvar_env v)).
        cut_to IHdf1; trivial.
        tauto.
      - Case "MatrixApply"%string.
        destruct H.
        specialize (IHdf2 σ v0);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        apply vectoro_to_ovector_not_none; intros.
        apply vectoro_to_ovector_not_none; intros.        
        specialize (IHdf1 (mk_env_entry (v, DTfloat) (d i i0) :: nil) (mk_genvar_env v)).
        cut_to IHdf1; trivial.
        match_option; tauto.
      - Case "VLossfun"%string.
        destruct H.
        specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        match_option.
        apply vectoro_to_ovector_not_none in eqq1.
        tauto.
        intros.
        specialize (IHdf1 (mk_env_entry (v1, DTfloat) (d i) :: mk_env_entry (v2, DTfloat) (r i) :: nil) (mk_genvar_env v1)).
        cut_to IHdf1; trivial.
        match_option; tauto.
      - Case "MLossfun"%string.
        destruct H.
        specialize (IHdf2 σ v);
        generalize (eval_fully_closed_not_none  σ df2); intros; simpl in H1.
        cut_to H1; trivial.
        match_option; [|tauto].
        cut_to IHdf2; trivial.
        match_option; [|tauto].
        match_option.
        unfold matrixo_to_omatrix in eqq1.
        apply vectoro_to_ovector_not_none in eqq1.
        tauto.
        intros.
        apply vectoro_to_ovector_not_none; intros.
        specialize (IHdf1 (mk_env_entry (v1, DTfloat) (d i i0) :: mk_env_entry (v2, DTfloat) (r i i0) :: nil) (mk_genvar_env v1)).
        cut_to IHdf1; trivial.
        match_option; tauto.
    Qed.

    Definition scalarMult (T : definition_function_types) (c : float) :=
      match T return 
            definition_function_types_interp T -> definition_function_types_interp T with
      | DTfloat => fun f => (c * f)%R
      | DTVector n => fun f => fun i => (c * f i)%R
      | DTMatrix n m => fun f => fun i j => (c * f i j)%R
      end.

    Definition dfti_gen_plus {T : definition_function_types} :=
      match T return 
            definition_function_types_interp T -> definition_function_types_interp T ->
            definition_function_types_interp T with
      | DTfloat => fun f g => (f + g)%R
      | DTVector n => fun f g => fun i => (f i + g i)%R
      | DTMatrix n m => fun f g => fun i j => (f i j + g i j)%R
      end.

    Lemma subvar_addvar_scalar_neq (env : df_env) (oval : float) (s : SubVar) (v: var_type) (grad : definition_function_types_interp (snd v)) : 
      let sv := (s, DTfloat) in
      vartlookup env sv = Some oval ->
      v <> sv -> 
      subvar sv (vart_update env v (addvar v env grad)) oval = 0%R.
    Proof.
      intros.
      unfold subvar; simpl.
      rewrite lookup_update_neq; trivial.
      rewrite H.
      lra.
    Qed.
  
    Lemma subvar_addvar_scalar_eq (env : df_env) (s : SubVar) (oval grad : float) :
      let v := (s, DTfloat) in
      vartlookup env v = Some oval ->
      subvar v (vart_update env v (addvar v env grad)) oval = grad.
      Proof.
        intros.
        unfold subvar; simpl.
        rewrite lookup_update.
        unfold addvar; simpl.
        rewrite H.
        lra.
      Qed.

      Lemma split_subvar (env1 env2: df_env) (oval val1 : float) (s : SubVar) :
        let v := (s, DTfloat) in
        vartlookup env1 v = Some val1 ->
        subvar v env2 oval = (subvar v env2 val1 + subvar v env1 oval)%R.
      Proof.
        intros.
        unfold subvar; simpl.
        rewrite H.
        case_eq (vartlookup env2 v); intros.
        lra.
        lra.
      Qed.
      
      Lemma vsum_nil : vsum vnil = 0%R.
      Proof.
        reflexivity.
      Qed.
  
      Lemma vsum_mult {n} (v : Vector float n) (c : float) :
        (c * vsum v)%R = vsum (fun j => (c * v j)%R).
      Proof.
        unfold vsum, vector_fold_right1, Datatypes.id; simpl.
        induction n; [ | destruct n].
        - repeat rewrite vector_fold_right1_dep_0; lra.
        - repeat rewrite vector_fold_right1_dep_1; lra.
        - repeat rewrite vector_fold_right1_dep_SSn.
          rewrite Rmult_plus_distr_l.
          specialize (IHn (vdrop_last v)); simpl in IHn.
          rewrite IHn.
          f_equal.
          apply vector_fold_right1_dep_ext.
          intros [i pf]; trivial.
      Qed.

      Lemma vsum_plus {m:nat} (v1 v2:Vector R m) :
        (vsum v1 + vsum v2)%R = vsum (fun i => (v1 i + v2 i)%R).
      Proof.
        unfold vsum, vector_fold_right1, Datatypes.id; simpl.
        induction m; [ | destruct m].
        - repeat rewrite vector_fold_right1_dep_0; lra.
        - repeat rewrite vector_fold_right1_dep_1; lra.
        - repeat rewrite vector_fold_right1_dep_SSn.
          specialize (IHm (vdrop_last v1) (vdrop_last v2)); simpl in IHm.
          rewrite (Rplus_comm (vlast v2)).
          rewrite (Rplus_assoc (vlast v1)).
          rewrite <- (Rplus_assoc _ _ (vlast v2)).
          rewrite IHm.
          rewrite (Rplus_comm _ (vlast v2)).
          rewrite <- Rplus_assoc.
          f_equal.
          apply vector_fold_right1_dep_ext.
          intros [i pf]; trivial.
      Qed.
      
     Lemma vmap_mult {n} (f: float -> float) (v : Vector float n) (c : float) :
       forall i : {n' : nat | n' < n},
       (c * (vmap f v) i)%R = (vmap (fun x => (c * f x)%R) v) i.
     Proof.
       intros.
       rewrite vmap_nth.
       now rewrite vmap_nth.       
     Qed.

    Lemma vsum_ext {n} (v v':Vector float n) : vec_eq v v' -> vsum v = vsum v'.
    Proof.
      apply vector_fold_right1_ext.
    Qed.

    Lemma msum_ext {m n} (mat mat':Matrix float m n) :
      (forall i j, mat i j = mat' i j) -> msum mat = msum mat'.
    Proof.
      intros.
      apply vsum_ext; intros ?.
      repeat rewrite vmap_nth.
      apply vsum_ext; intros ?; auto.
    Qed.

    Lemma msum_mult {m n} (mat : Matrix float m n) (c : float) :
       (c * msum mat)%R = msum (fun i j => (c * mat i j)%R).
     Proof.
       unfold msum.
       rewrite vsum_mult.
       apply vsum_ext; intros i.
       repeat rewrite vmap_nth.
       now rewrite vsum_mult.
     Qed.

     Lemma msum_mmap_mult {m n} (mat : Matrix float m n) (c : float) :
       (c * msum mat)%R = msum (mmap (fun x => c * x)%R mat).
     Proof.
       rewrite msum_mult.
       apply msum_ext; intros i j.
       now rewrite mmap_nth.
     Qed.

     Lemma msum_mmap_div_denom {m n} (mat : Matrix float m n) (c : float) : 
       msum (mmap (fun u : R => (u / c)%R) mat) = (msum mat / c)%R.
     Proof.
       transitivity (msum (mmap (fun u : R => (/ c * u)%R) mat)).
       - apply msum_ext; intros i j.
         repeat rewrite mmap_nth.
         lra.
       - rewrite <- msum_mmap_mult.
         lra.
     Qed.

    Lemma vsum0 n : vsum (fun _ : {n' : nat | (n' < n)%nat} => 0%R) = 0%R.
    Proof.
      generalize (vsum_mult (fun _ : {n' : nat | (n' < n)%nat} => 0%R) 0%R); intros HH.
      rewrite Rmult_0_l in HH.
      symmetry.
      simpl in *.
      erewrite vsum_ext; [eassumption | ].
      intro; simpl; lra.
    Qed.

     Lemma vsum_unitvector {n} (v:Vector R n) i :
       vsum (fun j => (v j * UnitVector n i j)%R) = v i.
     Proof.
       unfold vsum, vector_fold_right1, Datatypes.id, UnitVector; simpl.
       revert n v i.
       destruct i.
       induction n; [ | destruct n].
       - lia.
       - repeat rewrite vector_fold_right1_dep_1.
         destruct x; [ | lia]; simpl.
         field_simplify.
         now erewrite index_pf_irrel.
       - repeat rewrite vector_fold_right1_dep_SSn.
         unfold vlast, vdrop_last; simpl.
         destruct (equiv_dec (S n) x).
         + ring_simplify.
           simpl.
           destruct e.
           match goal with
           | [|- (_ + ?x)%R = _ ] => replace x with 0%R
           end.
           * ring_simplify.
             now erewrite index_pf_irrel.
           * rewrite <- (vsum0 (S n)) at 1.
             unfold vsum, vector_fold_right1, Fzero, Datatypes.id; simpl.
             apply (@vector_fold_right1_dep_ext (fun _ => R)).
             intros [??].
             destruct (equiv_dec x (S n)).
             -- destruct e.
                lia.
             -- lra.
         + ring_simplify.
           unfold equiv, complement in c.
           assert (pf:x < S n) by lia.
           specialize (IHn (vdrop_last v) pf).
           simpl in IHn.
           erewrite index_pf_irrel.
           rewrite <- IHn.
           apply (@vector_fold_right1_dep_ext (fun _ => R)).
           now intros [??].
     Qed.

     Lemma msum_unitmatrix {m n} (v:Matrix R m n) i j :
       msum (fun k l => (v k l * UnitMatrix m n i j k l)%R) = v i j.
     Proof.
       unfold msum.
       unfold UnitMatrix.
       rewrite (vsum_ext _ (
                       (fun (k : {n' : nat | n' < m}) => @vsum floatish_R _ 
                                                           (fun (l : {m' : nat | m' < n}) =>
                          (v k l *
                           (if equiv_dec (` k) (` i) then if equiv_dec (` l) (` j) then 1%R else 0%R else 0%R))%R))
                   
               ))
       by (intros ?; now rewrite vmap_nth).
       rewrite (vsum_ext _ (
                             (fun (k : {n' : nat | n' < m}) => (if equiv_dec (` k) (` i) then
                                                                  @vsum floatish_R _ 
                                                                        (fun (l : {m' : nat | m' < n}%nat) =>
                                                                           ((v k) l *
                           if equiv_dec (` l) (` j) then 1%R else 0%R))%R else 0%R))
                   
               )).
       - rewrite (vsum_ext _ (
                             (fun (k : {n' : nat | n' < m}) => (if equiv_dec (` k) (` i) then
                                                                  v k j else 0%R))
                   
                 )).
         + rewrite (vsum_ext _ (
                             (fun (k : {n' : nat | n' < m}) => ((transpose v) j k * @UnitVector floatish_R m i k)%R)
                   
                   )).
           * now rewrite vsum_unitvector.
           * unfold UnitVector; intros ?; simpl.
             dest_eqdec; unfold transpose; simpl
             ; lra.
         + intros ?.
           dest_eqdec; trivial.
           apply vsum_unitvector.
       - intros ?.
         dest_eqdec; trivial.
         rewrite <- (vsum0 n) at 1.
         apply vsum_ext.
         intros ?; lra.
     Qed.

     Ltac vectoro_assert_forall_in H i
       := match type of H with vectoro_to_ovector ?x = Some ?y => 
                               assert (forall i, x i = Some (y i)) end.

     Lemma vartlookup_list_env_iter {A}
           (s: SubVar) 
           (f : A -> df_env -> option df_env) 
           (l : list A) (env fenv: df_env):
       list_env_iter f (Some env) l = Some fenv ->
       vartlookup env (s, DTfloat) <> None ->
       (forall (env fenv: df_env) (i:A),
           f i env = Some fenv ->
           vartlookup env (s, DTfloat) <> None ->
           vartlookup fenv (s, DTfloat) <> None) ->
       vartlookup fenv (s, DTfloat) <> None.
     Proof.
       intros.
       revert H0 H.
       generalize env.
       induction l.
       - simpl; intros.
         now invcs H.
       - simpl; intros.
         generalize (list_env_iter_none f l); intros.
         assert (f a env0 <> None); [congruence | ].
         case_eq (f a env0); [|congruence].
         intros.
         apply (IHl d).
         + specialize (H1 env0 d a).
           now apply H1. 
         + now rewrite H4 in H.
    Qed.

     Theorem df_eval_deriv_same {T} (σ:df_env) (df:DefinedFunction UnitAnn T) (s:SubVar) :
        let v := (s, DTfloat) in 
        let vl := map (fun ve => projT1 ve) σ in
        fully_closed_over df vl -> 
        df_eval_deriv σ df v = df_eval σ (df_deriv df v).
      Proof.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
      ; simpl in *;trivial; intros
      ; try (destruct H; rewrite IHdf1; trivial; rewrite IHdf2; trivial)
      ; try (rewrite IHdf; trivial; do 2 match_option).      
      - Case "DVector"%string.
        f_equal.
        apply functional_extensionality; intros.
        rewrite vforall_forall in H0.
        specialize (H x0); simpl in H.
        specialize (H0 x0).
        apply H; trivial.
      - Case "DMatrix"%string.
        f_equal.
        apply functional_extensionality; intros.
        apply functional_extensionality; intros.         
        rewrite vforall_forall in H0.
        specialize (H x0); simpl in H.
        specialize (H0 x0).
        rewrite vforall_forall in H0.
        apply H; trivial.
      - case "Times"%string.
        intros; do 4 match_option.
      - Case "Divide"%string.
        intros; do 4 match_option.
      - Case "Sign"%string.
        match_option.
        generalize (eval_deriv_fully_closed_not_none  σ df (s, DTfloat)); tauto.
      - Case "PSign"%string.
        match_option.
        generalize (eval_deriv_fully_closed_not_none  σ df (s, DTfloat)); tauto.
      - Case "Max"%string.
        assert (df_eval σ df1 <> None) by (apply eval_fully_closed_not_none; trivial).
        assert (df_eval σ df2 <> None) by (apply eval_fully_closed_not_none; trivial).        
        match_option; [|congruence].
        match_option; [|congruence].        
        assert (df_eval σ (df_deriv df1 (s, DTfloat)) <> None).
        apply eval_fully_closed_not_none.
        apply fully_closed_deriv; trivial.
        assert (df_eval σ (df_deriv df2 (s, DTfloat)) <> None).
        apply eval_fully_closed_not_none.
        apply fully_closed_deriv; trivial.
        destruct (df_eval σ (df_deriv df1 (s, DTfloat))); [|congruence].
        destruct (df_eval σ (df_deriv df2 (s, DTfloat))); [|congruence].        
        unfold pos_sign; simpl.
        case_eq (Rle_dec d d0); intros; f_equal.
        destruct (Rge_dec (d0 - d) 0); lra.
        destruct (Rge_dec (d0 - d) 0); lra.        
      - Case "VectorDot"%string.
        do 4 match_option.
        rewrite vsum_plus.
        do 2 f_equal.
        f_equal.
        apply functional_extensionality; intros.         
        lra.
      - Case "MatrixVectorMult"%string.
        do 4 match_option.
        f_equal.
        apply functional_extensionality; intros.         
        unfold matrix_vector_mult.
        rewrite vsum_plus; simpl.
        f_equal.
        apply functional_extensionality; intros.         
        lra.
      - Case "MatrixMult"%string.
        do 4 match_option.
        f_equal.
        apply functional_extensionality; intros.
        apply functional_extensionality; intros.         
        unfold matrix_mult.
        rewrite vsum_plus; simpl; f_equal.
        apply functional_extensionality; intros.         
        lra.
      - Case "VectorScalMult"%string.
        do 4 match_option.
        f_equal.
        apply functional_extensionality; intros.         
        lra.
      - Case "MatrixScalMult"%string.
        do 4 match_option.
        f_equal.
        apply functional_extensionality; intros.
        apply functional_extensionality; intros.                  
        lra.
      - Case "VectorApply"%string.
        destruct H.
        assert (df_eval σ df2 <> None) by (apply eval_fully_closed_not_none; trivial).        
        match_option; [|congruence].
        rewrite IHdf2; trivial.
        match_option.
        + f_equal.
          apply functional_extensionality; intros.
          assert ( df_eval_deriv [mk_env_entry (v, DTfloat) (d x)] df1 (v, DTfloat) =
                   df_eval σ (df_subst (df_deriv df1 (v, DTfloat)) (v, DTfloat) 
                                       (VectorElem () df2 x))).
          admit.
          now rewrite H2.
        + assert ( df_eval σ (df_deriv df2 (s, DTfloat)) <> None ); [|tauto].
          apply eval_fully_closed_not_none.
          apply fully_closed_deriv; trivial.
      - Case "MatrixApply"%string.
        destruct H.
        assert (df_eval σ df2 <> None) by (apply eval_fully_closed_not_none; trivial).        
        match_option; [|congruence].
        rewrite IHdf2; trivial.
        match_option.
        + f_equal.
          apply functional_extensionality; intros.
          apply functional_extensionality; intros.          
          assert ( df_eval_deriv [mk_env_entry (v, DTfloat) (d x x0)] df1 (v, DTfloat) =
                   df_eval σ (df_subst (df_deriv df1 (v, DTfloat)) (v, DTfloat) 
                                       (MatrixElem () df2 x x0))).
          admit.
          now rewrite H2.
        + assert ( df_eval σ (df_deriv df2 (s, DTfloat)) <> None ); [|tauto].
          apply eval_fully_closed_not_none.
          apply fully_closed_deriv; trivial.
      - Case "VLossfun"%string.
        destruct H.
        assert (df_eval σ df2 <> None) by (apply eval_fully_closed_not_none; trivial).        
        match_option; [|congruence].
        rewrite IHdf2; trivial.
        match_option.
        do 2 match_option.
        + do 2 f_equal.
          apply functional_extensionality; intros.
          admit.
        + generalize (vectoro_to_ovector_exists_None eqq2).
          intros; destruct H2.
          assert (df_eval 
                    σ
                    (df_subst (df_subst (df_deriv df1 (v1, DTfloat)) (v1, DTfloat) (VectorElem () df2 x))
                              (v2, DTfloat) (Number () (r x))) <> None); [|tauto].
          apply eval_fully_closed_not_none.
          apply fully_closed_subst; simpl; [|trivial].
          apply fully_closed_subst; simpl.
          * apply fully_closed_deriv.
            now apply fully_closed_over_pair.
          * now apply fully_closed_over_cons.
        + generalize (vectoro_to_ovector_exists_None eqq1).
          intros; destruct H2.
          match_option_in e.
          assert (df_eval_deriv [mk_env_entry (v1, DTfloat) (d x); mk_env_entry (v2, DTfloat) (r x)]
           df1 (v1, DTfloat) <> None); [|tauto].
          apply eval_deriv_fully_closed_not_none; trivial.
      - Case "MLossfun"%string.
        destruct H.
        assert (df_eval σ df2 <> None) by (apply eval_fully_closed_not_none; trivial).        
        match_option; [|congruence].
        rewrite IHdf2; trivial.
        match_option.
        do 2 match_option.
        + do 2 f_equal.
          admit.
        + generalize (vectoro_to_ovector_exists_None eqq2); intros; destruct H2.
          generalize (vectoro_to_ovector_exists_None e); intros; destruct H2.
          match_option_in e0.
          match_option_in eqq3.
          assert (df_eval σ
           (df_subst
              (df_subst (df_deriv df1 (v1, DTfloat)) (v1, DTfloat) (MatrixElem () df2 x x0))
              (v2, DTfloat) (Number () (r x x0))) <> None); [|tauto].
          apply eval_fully_closed_not_none.
          apply fully_closed_subst; simpl; [|trivial].
          apply fully_closed_subst; simpl.
          * apply fully_closed_deriv.
            now apply fully_closed_over_pair.
          * now apply fully_closed_over_cons.
        + generalize (vectoro_to_ovector_exists_None eqq1).
          intros; destruct H2.
          generalize (vectoro_to_ovector_exists_None e).          
          intros; destruct H2.
          match_option_in e0.
          assert (df_eval_deriv [mk_env_entry (v1, DTfloat) (d x x0); 
                                 mk_env_entry (v2, DTfloat) (r x x0)]
           df1 (v1, DTfloat) <> None); [|tauto].
          apply eval_deriv_fully_closed_not_none; trivial.
      Admitted.          
     
     Theorem df_eval_deriv_scalar_same (σ:df_env) (df:DefinedFunction UnitAnn DTfloat) (s:SubVar) :
        let v := (s, DTfloat) in 
        let vl := map (fun ve => projT1 ve) σ in
        is_scalar_function df ->
        fully_closed_over df vl -> 
        df_eval_deriv σ df v = df_eval σ (df_deriv df v).
      Proof.
        simpl.
        intros is_scalar.
        generalize is_scalar.
        pattern df.
        revert df is_scalar.
        DefinedFunction_scalar_cases (apply is_scalar_function_ind) Case
        ; simpl; trivial; intros 
        ; try (destruct H1; destruct is_scalar; 
                 specialize (H H3 H1); specialize (H0 H4 H2); now rewrite H, H0)
        ; try (rewrite H; trivial; do 2 match_option).
        - Case "Times"%string.
          destruct H1.
          destruct is_scalar.
          cut_to H; trivial.
          cut_to H0; trivial.
          rewrite H, H0.
          do 4 match_option.
        - Case "Divide"%string.
          destruct H1.
          destruct is_scalar.
          cut_to H; trivial.
          cut_to H0; trivial.
          rewrite H, H0.
          do 4 match_option.
        - Case "Sign"%string.
          match_option.
          assert ( df_eval_deriv σ e (s, DTfloat) <> None); [|tauto].
          apply eval_deriv_fully_closed_not_none; trivial.
        - Case "PSign"%string.
          match_option.
          assert ( df_eval_deriv σ e (s, DTfloat) <> None); [|tauto].
          apply eval_deriv_fully_closed_not_none; trivial.
        - Case "Max"%string.
          destruct is_scalar; destruct H1.
          cut_to H; trivial.
          cut_to H0; trivial.
          rewrite H, H0.
          assert (df_eval σ l <> None) by (apply eval_fully_closed_not_none; trivial).
          assert (df_eval σ r <> None) by (apply eval_fully_closed_not_none; trivial).
          match_option; [|congruence].
          match_option; [|congruence].        
          assert (df_eval σ (df_deriv l (s, DTfloat)) <> None).
          apply eval_fully_closed_not_none.
          apply fully_closed_deriv; trivial.
          assert (df_eval σ (df_deriv r (s, DTfloat)) <> None).
          apply eval_fully_closed_not_none.
          apply fully_closed_deriv; trivial.
          destruct (df_eval σ (df_deriv l (s, DTfloat))); [|congruence].
          destruct (df_eval σ (df_deriv r (s, DTfloat))); [|congruence].        
          unfold pos_sign; simpl.
          case_eq (Rle_dec d d0); intros; f_equal.
          destruct (Rge_dec (d0 - d) 0); lra.
          destruct (Rge_dec (d0 - d) 0); lra.        
     Qed.

     Lemma vartlookup_list_env_iter2 {A}
           (s: SubVar) 
           {f : A -> df_env -> option df_env} 
           {l : list A} {env fenv: df_env}:
       list_env_iter f (Some env) l = Some fenv ->
       vartlookup env (s, DTfloat) <> None ->
       (forall (env fenv: df_env) (i:A),
           f i env = Some fenv ->
           vartlookup env (s, DTfloat) <> None ->
           vartlookup fenv (s, DTfloat) <> None) ->
       vartlookup fenv (s, DTfloat) <> None.
     Proof.
       apply (vartlookup_list_env_iter s f l env fenv).
     Qed.

     Lemma scalarMult_list_env_iter 
           (s: SubVar) (c val1 val2:float) (A :Type) 
           (f g : A -> df_env -> option df_env) 
           (l : list A) (env1 env2 fenv1 fenv2: df_env):
       list_env_iter f (Some env1) l = Some fenv1 ->
       list_env_iter g (Some env2) l = Some fenv2 ->
       vartlookup env1 (s, DTfloat) = Some val1 ->
       vartlookup env2 (s, DTfloat) = Some val2 ->
       (forall (i:A) (env1 env2 fenv1 fenv2: df_env) (v1 v2: float),
         vartlookup env1 (s, DTfloat) = Some v1 ->
         vartlookup env2 (s, DTfloat) = Some v2 ->         
         f i env1 = Some fenv1 -> g i env2 = Some fenv2 ->
         subvar (s, DTfloat) fenv1 v1 = (c * subvar (s, DTfloat) fenv2 v2)%R) ->
       (forall (env fenv: df_env) (i:A),
           f i env = Some fenv ->
           vartlookup env (s, DTfloat) <> None ->
           vartlookup fenv (s, DTfloat) <> None) ->
       (forall (env fenv: df_env) (i:A),
           g i env = Some fenv ->
           vartlookup env (s, DTfloat) <> None ->
           vartlookup fenv (s, DTfloat) <> None) ->        
       subvar (s, DTfloat) fenv1 val1 = (c * subvar (s, DTfloat) fenv2 val2)%R.
     Proof.
       intros.
       generalize (vartlookup_list_env_iter s f l env1 fenv1); intros.
       assert (vartlookup env1 (s, DTfloat) <> None).
       rewrite H1; discriminate.
       assert (vartlookup env2 (s, DTfloat) <> None).
       rewrite H2; discriminate.       
       specialize (H6 H H7 H4).
       generalize (vartlookup_list_env_iter s g l env2 fenv2); intros.         
       specialize (H9 H0 H8 H5).
       revert H1 H2 H H0.
       generalize env1 env2 val1 val2.
       induction l.
       - intros.
         unfold subvar; simpl.
         unfold list_env_iter in H; simpl in H.
         unfold list_env_iter in H0; simpl in H0.
         invcs H; invcs H0.
         rewrite H1; rewrite H2; lra.
       - simpl; intros.
         generalize (list_env_iter_none f l); intros.
         assert (f a env0 <> None); [congruence | ].
         case_eq (f a env0); [intros|congruence].
         generalize (list_env_iter_none g l); intros.
         assert (g a env3 <> None); [congruence | ].
         case_eq (g a env3); [intros|congruence].
         assert (vartlookup d (s, DTfloat) <> None).
         apply (H4 env0 d a); trivial; congruence.
         assert (vartlookup d0 (s, DTfloat) <> None).
         apply (H5 env3 d0 a); trivial; congruence.
         case_eq (vartlookup d (s, DTfloat)); [intros | tauto].
         case_eq (vartlookup d0 (s, DTfloat)); [intros | tauto].
         specialize (IHl d d0 d1 d2).
         specialize (H3 a env0 env3 d d0 val0 val3).
         rewrite (split_subvar d fenv1 val0 d1); trivial.
         rewrite (split_subvar d0 fenv2 val3 d2); trivial.         
         specialize (H3 H1 H2 H12 H15).
         rewrite H12 in H.
         rewrite H15 in H0.
         specialize (IHl H18 H19 H H0).
         lra.
      Qed.
       
     Lemma list_env_iter_subvar_env2
           (s: SubVar) (val1 val2:float) (A :Type) 
           (f g : A -> df_env -> option df_env) 
           (l : list A) (env1 env2 fenv1 fenv2: df_env):
       list_env_iter f (Some env1) l = Some fenv1 ->
       list_env_iter g (Some env2) l = Some fenv2 ->
       vartlookup env1 (s, DTfloat) = Some val1 ->
       vartlookup env2 (s, DTfloat) = Some val2 ->
       (forall (i:A) (env1 env2 fenv1 fenv2: df_env) (v1 v2: float),
         vartlookup env1 (s, DTfloat) = Some v1 ->
         vartlookup env2 (s, DTfloat) = Some v2 ->         
         f i env1 = Some fenv1 -> g i env2 = Some fenv2 ->
         subvar (s, DTfloat) fenv1 v1 = subvar (s, DTfloat) fenv2 v2) ->
       (forall (env fenv: df_env) (i:A),
           f i env = Some fenv ->
           vartlookup env (s, DTfloat) <> None ->
           vartlookup fenv (s, DTfloat) <> None) ->
       (forall (env fenv: df_env) (i:A),
           g i env = Some fenv ->
           vartlookup env (s, DTfloat) <> None ->
           vartlookup fenv (s, DTfloat) <> None) ->        
       subvar (s, DTfloat) fenv1 val1 = subvar (s, DTfloat) fenv2 val2.
      Proof.
        intros.
        generalize (scalarMult_list_env_iter s 1%R val1 val2 A f g l env1 env2 fenv1 fenv2).
        intros.
        specialize (H6 H H0 H1 H2).
        cut_to H6.
        now replace (1 * subvar (s, DTfloat) fenv2 val2)%R with (subvar (s, DTfloat) fenv2 val2) in H6 by lra.
        intros.
        replace  (1 * subvar (s, DTfloat) fenv3 v2)%R with (subvar (s, DTfloat) fenv3 v2) by lra.
        apply (H3 i env0 env3 fenv0 fenv3); trivial.
        apply H4.
        apply H5.
      Qed.

     Lemma scalarMult_backprop_grad_scalar {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (s: SubVar) (grad_env1 grad_env2:df_env) (grad : definition_function_types_interp T) (c:float) :
      let v := (s, DTfloat) in
      vartlookup grad_env1 v <> None -> vartlookup grad_env2 v <> None ->
      df_eval_backprop_deriv σ df grad_env1 (scalarMult T c grad) <> None ->
      df_eval_backprop_deriv σ df grad_env2 grad <> None ->
      df_eval_backprop_delta σ df v grad_env1 (scalarMult T c grad) =
      lift (fun e => scalarMult (snd v) c e) (df_eval_backprop_delta σ df v grad_env2 grad).
    Proof.
      revert grad_env1 grad_env2.
      unfold df_eval_backprop_delta.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case
      ; simpl; intros grad_env1 grad_env2 neq1 neq2; intros.
       - Case "Number"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [|tauto].
        intros; simpl; f_equal.
        unfold subvar; simpl.
        match_destr; match_destr.
        inversion H1; subst.
        inversion H2; subst.
        lra.
      - Case "Constant"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        intros; simpl; f_equal.
        unfold subvar; simpl.
        match_destr; match_destr.
        inversion H1; subst.
        inversion H2; subst.
        lra.
      - Case "DVector"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        intros; simpl.
        unfold lift.
        match_option; [|tauto].
        case_eq (two_vector_env_iter_alt
                   (fun (x0 : DefinedFunction Ann DTfloat) (g : R) (genv : df_env) =>
                      df_eval_backprop_deriv σ x0 genv g) grad_env2 x grad); [|tauto].
        unfold two_vector_env_iter_alt in *.
        intros; f_equal.
        apply (scalarMult_list_env_iter 
                 s c d0 d {n' : nat | n' < n}
                 (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                    df_eval_backprop_deriv σ (x i) env (c * grad i)%R)
                 (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                    df_eval_backprop_deriv σ (x i) env (grad i))
               (bounded_seq0 n) grad_env1 grad_env2); trivial.
        + intros.
          specialize (H i (grad i) env1 env2).
          assert (vartlookup env1 (s, DTfloat) <> None); [congruence|].
          assert (vartlookup env2 (s, DTfloat) <> None); [congruence|].        
          specialize (H H9 H10).
          assert (df_eval_backprop_deriv σ (x i) env1 (c * grad i)%R <> None); [congruence|].
          assert (df_eval_backprop_deriv σ (x i) env2 (grad i) <> None);  [congruence|].
          specialize (H H11 H12).
          unfold lift in H; simpl in H.
          rewrite H5, H6, H7, H8 in H.
          now inversion H.
        + intros.
          now apply (df_eval_backprop_deriv_preserves_lookup_not_none H5).
        + intros.
          now apply (df_eval_backprop_deriv_preserves_lookup_not_none H5).
      - Case "DMatrix"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        intros; simpl.
        unfold lift.
        match_option; [|tauto].
        case_eq (two_matrix_env_iter_alt
        (fun (x0 : DefinedFunction Ann DTfloat) (g : R) (genv : df_env) =>
         df_eval_backprop_deriv σ x0 genv g) grad_env2 x grad); [|tauto].
        intros; f_equal.
        unfold two_matrix_env_iter_alt in *.
        apply (scalarMult_list_env_iter 
                 s c d0 d {n' : nat | n' < n}
                 (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                    list_env_iter
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (x i j) env0 (c * grad i j)%R) 
                      (Some env) (bounded_seq0 m))
                 (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                    list_env_iter
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (x i j) env0 (grad i j)) (Some env) 
                      (bounded_seq0 m))
               (bounded_seq0 n) grad_env1 grad_env2); trivial.
        + intros.
          apply (scalarMult_list_env_iter 
                   s c v1 v2  {m' : nat | m' < m}
                   (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                      df_eval_backprop_deriv σ (x i j) env0 (c * grad i j)%R)
                   (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                      df_eval_backprop_deriv σ (x i j) env0 (grad i j))
                   (bounded_seq0 m) env1 env2); trivial.
          * intros.
            specialize (H i i0 (grad i i0) env0 env3).
            assert (vartlookup env0 (s, DTfloat) <> None); [congruence|].
            assert (vartlookup env3 (s, DTfloat) <> None); [congruence|].        
            specialize (H H13 H14).
            assert (df_eval_backprop_deriv σ (x i i0) env0 (c * grad i i0)%R <> None); [congruence|].
            assert (df_eval_backprop_deriv σ (x i i0) env3 (grad i i0) <> None);  [congruence|].
            specialize (H H15 H16).
            unfold lift in H; simpl in H.
            rewrite H9, H10, H11, H12 in H.
            now inversion H.
          * intros.            
            now apply (df_eval_backprop_deriv_preserves_lookup_not_none H9).
          * intros.
            now apply (df_eval_backprop_deriv_preserves_lookup_not_none H9).
        + intros.
          apply (vartlookup_list_env_iter 
                   s 
                   (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                      df_eval_backprop_deriv σ (x i j) env0 (c * grad i j)%R) 
                   (bounded_seq0 m) env fenv); trivial; intros.
          now apply (df_eval_backprop_deriv_preserves_lookup_not_none H7).          
        + intros.
          apply (vartlookup_list_env_iter 
                   s 
                   (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                      df_eval_backprop_deriv σ (x i j) env0 (grad i j))
                   (bounded_seq0 m) env fenv); trivial; intros.
          now apply (df_eval_backprop_deriv_preserves_lookup_not_none H7).                    
      - Case "Var"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        intros.
        destruct (vart_dec v (s, DTfloat)).
        + subst; simpl.
          rewrite H2; simpl.
          rewrite subvar_addvar_scalar_eq; trivial.
          rewrite H1; simpl.
          now rewrite subvar_addvar_scalar_eq.
        + case_eq (vartlookup grad_env1 v); intros; simpl.
          * case_eq (vartlookup grad_env2 v); intros; simpl; f_equal.
            -- rewrite subvar_addvar_scalar_neq; trivial.
               rewrite subvar_addvar_scalar_neq; trivial.
               lra.
            -- rewrite subvar_addvar_scalar_neq; trivial.
               unfold subvar; simpl.
               rewrite H1.
               lra.
          * case_eq (vartlookup grad_env2 v); intros; simpl; f_equal.
            -- rewrite subvar_addvar_scalar_neq; trivial.
               unfold subvar; simpl.
               rewrite H2.
               lra.
            -- unfold subvar; simpl.
               rewrite H2; rewrite H1.
               lra.
      - Case "Plus"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        specialize (IHdf1 grad grad_env1 grad_env2); intros.
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (c * grad)%R); intros.
        rewrite H3 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); intros.
        rewrite H4 in H0; simpl in H0.
        + specialize (IHdf2 grad d1 d2).
          rewrite H3 in IHdf1; rewrite H4 in IHdf1.
          assert (vartlookup d1 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H3 (s, DTfloat) neq1).
          case_eq (vartlookup d1 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d2 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
          case_eq (vartlookup d2 (s, DTfloat)); [ |tauto]; intros.
          rewrite H6 in IHdf2; rewrite H8 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d1 (c * grad)%R); [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d2 grad); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d1 d5 d0 d3) by trivial.
          rewrite (split_subvar d2 d6 d d4) by trivial.
          rewrite H9 in IHdf2; rewrite H10 in IHdf2; simpl in *.
          assert (Some (subvar (s, DTfloat) d1 d0) = Some (c * subvar (s, DTfloat) d2 d)%R) by
              (apply IHdf1; trivial; discriminate).
          assert (Some (subvar (s, DTfloat) d5 d3) = Some (c * subvar (s, DTfloat) d6 d4)%R) by
              (apply IHdf2; trivial; discriminate).
          inversion H11; inversion H12.
          rewrite H14; rewrite H15; lra.
        + now rewrite H4 in H0.
        + now rewrite H3 in H.
      - Case "Minus"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        specialize (IHdf1 grad grad_env1 grad_env2); intros.
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (c * grad)%R); intros.
        rewrite H3 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); intros.
        rewrite H4 in H0; simpl in H0.
        + specialize (IHdf2 (-grad)%R d1 d2).
          rewrite H3 in IHdf1; rewrite H4 in IHdf1.
          assert (vartlookup d1 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H3 (s, DTfloat) neq1).
          case_eq (vartlookup d1 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d2 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
          case_eq (vartlookup d2 (s, DTfloat)); [ |tauto]; intros.
          rewrite H6 in IHdf2; rewrite H8 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d1 (-(c * grad))%R); [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d2 (-grad)%R); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d1 d5 d0 d3) by trivial.
          rewrite (split_subvar d2 d6 d d4) by trivial.
          replace (c * -grad)%R with (-(c*grad))%R in IHdf2 by lra.
          rewrite H9 in IHdf2; rewrite H10 in IHdf2; simpl in *.
          assert (Some (subvar (s, DTfloat) d1 d0) = Some (c * subvar (s, DTfloat) d2 d)%R) by
              (apply IHdf1; trivial; discriminate).
          assert (Some (subvar (s, DTfloat) d5 d3) = Some (c * subvar (s, DTfloat) d6 d4)%R) by
              (apply IHdf2; trivial; discriminate).
          inversion H11; inversion H12.
          rewrite H14; rewrite H15; lra.
        + now rewrite H4 in H0.
        + now rewrite H3 in H.
      - Case "Times"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        case_eq ( df_eval σ df1); [|tauto].
        case_eq ( df_eval σ df2); [|tauto]; intros.
        specialize (IHdf1 (d * grad)%R grad_env1 grad_env2).
        rewrite H4 in IHdf1; rewrite H3 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (d * (c * grad))%R); intros.
        rewrite H1, H2, H5 in H; simpl in H.
        rewrite H1, H2 in H0; simpl in H0.        
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 (d * grad)%R); intros.
        rewrite H6 in H0; simpl in H0.
        + specialize (IHdf2 (d0 * grad)%R d3 d4).
          replace (c * (d * grad))%R with (d * (c * grad))%R in IHdf1 by lra.
          rewrite H5 in IHdf1; rewrite H6 in IHdf1; simpl in IHdf1.
          assert (vartlookup d3 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 (s, DTfloat) neq1).
          case_eq (vartlookup d3 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d4 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H6 (s, DTfloat) neq2).
          case_eq (vartlookup d4 (s, DTfloat)); [ |tauto]; intros.
          rewrite H8 in IHdf2; rewrite H10 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d3 (d0 * (c * grad))%R); [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d4 (d0 * grad)%R); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d3 d7 d2 d5) by trivial.
          rewrite (split_subvar d4 d8 d1 d6) by trivial.
          replace (c * (d0 * grad))%R with (d0 * (c*grad))%R in IHdf2 by lra.
          rewrite H11 in IHdf2; rewrite H12 in IHdf2; simpl in *.
          assert (Some (subvar (s, DTfloat) d3 d2) = Some (c * subvar (s, DTfloat) d4 d1)%R) by
              (apply IHdf1; trivial; discriminate).
          assert (Some (subvar (s, DTfloat) d7 d5) = Some (c * subvar (s, DTfloat) d8 d6)%R) by
              (apply IHdf2; trivial; discriminate).
          inversion H13; inversion H14.
          rewrite H16; rewrite H17; lra.
        + now rewrite H6 in H0.
        + rewrite H2 in H; rewrite H1 in H.
          now rewrite H5 in H.
      - Case "Divide"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        case_eq ( df_eval σ df1); [|tauto].
        case_eq ( df_eval σ df2); [|tauto]; intros.
        specialize (IHdf1 (grad / d)%R grad_env1 grad_env2).
        rewrite H4 in IHdf1; rewrite H3 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (c * grad / d)%R); intros.
        rewrite H1 in H; rewrite  H2 in H; simpl in H.
        rewrite H1 in H0; rewrite  H2 in H0; simpl in H0.        
        rewrite H5 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 (grad / d)%R); intros.
        rewrite H6 in H0; simpl in H0.
        + specialize (IHdf2 (- d0 / (d*d) * grad)%R d3 d4).
          replace (c * (grad / d))%R with (c * grad / d )%R in IHdf1 by lra.
          rewrite H5 in IHdf1; rewrite H6 in IHdf1; simpl in IHdf1.
          assert (vartlookup d3 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 (s, DTfloat) neq1).
          case_eq (vartlookup d3 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d4 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H6 (s, DTfloat) neq2).
          case_eq (vartlookup d4 (s, DTfloat)); [ |tauto]; intros.
          rewrite H8 in IHdf2; rewrite H10 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d3 (- d0 /(d * d) * (c * grad))%R); [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d4 (- d0 / (d * d) * grad)%R); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d3 d7 d2 d5) by trivial.
          rewrite (split_subvar d4 d8 d1 d6) by trivial.
          replace (c * (-d0 / (d * d) * grad))%R with (- d0/(d * d) * (c*grad))%R in IHdf2 by lra.
          rewrite H11 in IHdf2; rewrite H12 in IHdf2; simpl in *.
          assert (Some (subvar (s, DTfloat) d3 d2) = Some (c * subvar (s, DTfloat) d4 d1)%R) by
              (apply IHdf1; trivial; discriminate).
          assert (Some (subvar (s, DTfloat) d7 d5) = Some (c * subvar (s, DTfloat) d8 d6)%R) by
              (apply IHdf2; trivial; discriminate).
          inversion H13; inversion H14.
          rewrite H16; rewrite H17; lra.
        + now rewrite H6 in H0.
        + rewrite H2 in H; rewrite H1 in H.
          now rewrite H5 in H.
      - Case "Square"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        case_eq (df_eval σ df); [ | tauto]; intros.
        specialize (IHdf (2 * d1 * grad)%R grad_env1 grad_env2); simpl in *.
        rewrite H1 in IHdf; rewrite H2 in IHdf.
        replace (2 * d1 * (c * grad))%R with (c * (2 * d1 * grad))%R by lra.
        rewrite H3 in H; rewrite H3 in H0; simpl in *.
        replace (2 * d1 * (c * grad))%R with (c * (2 * d1 * grad))%R in H by lra.
        now apply IHdf.
      - Case "Exp"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        case_eq (df_eval σ df); [ | tauto]; intros.
        specialize (IHdf (grad * exp d1)%R grad_env1 grad_env2); simpl in *.
        replace (c * grad * exp d1)%R with (c * (grad * exp d1))%R by lra.
        rewrite H1 in IHdf; rewrite H2 in IHdf.
        rewrite H3 in H; rewrite H3 in H0.
        replace (c * grad * exp d1)%R with (c * (grad * exp d1))%R in H by lra.
        now apply IHdf.
      - Case "Log"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        case_eq (df_eval σ df); [ | tauto]; intros.
        specialize (IHdf (grad / d1)%R grad_env1 grad_env2 ); simpl in *.
        replace (c * grad / d1)%R with (c * (grad / d1))%R by lra.
        rewrite H1 in IHdf; rewrite H2 in IHdf.
        rewrite H3 in H; rewrite H3 in H0.
        replace (c * grad / d1)%R with (c * (grad / d1))%R in H by lra.
        now apply IHdf.
      - Case "Abs"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        case_eq (df_eval σ df); [ | tauto]; intros.
        specialize (IHdf (grad * sign d1)%R grad_env1 grad_env2); simpl in *.
        replace (c * grad * (@sign floatish_R d1))%R 
          with (c * (grad * (@sign floatish_R d1)))%R by lra.
        rewrite H1 in IHdf; rewrite H2 in IHdf.
        rewrite H3 in H; rewrite H3 in H0.
        replace (c * grad * (@sign floatish_R d1))%R 
          with (c * (grad * (@sign floatish_R d1)))%R in H by lra.
        now apply IHdf.
      - Case "Sign"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        specialize (IHdf (0)%R grad_env1 grad_env2); simpl in *.
        replace (0%R) with (c * 0)%R at 1 by lra.
        rewrite H1 in IHdf; rewrite H2 in IHdf.
        replace (0%R) with (c * 0)%R in H by lra.
        now apply IHdf.
      - Case "PSign"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        specialize (IHdf (0)%R grad_env1 grad_env2); simpl in *.
        replace (0%R) with (c * 0)%R at 1 by lra.
        rewrite H1 in IHdf; rewrite H2 in IHdf.
        replace (0%R) with (c * 0)%R in H by lra.
        now apply IHdf.
      - Case "Max"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        case_eq (df_eval σ df1); [ | tauto]; intros.
        case_eq (df_eval σ df2); [ | tauto]; intros.        
        rewrite H3 in H; rewrite H3 in H0.
        rewrite H4 in H; rewrite H4 in H0.
        case_eq  (Rle_dec d1 d2); intros.
        + specialize (IHdf2 grad grad_env1 grad_env2); simpl in *.
          rewrite H1 in IHdf2; rewrite H2 in IHdf2.
          rewrite H5 in H; rewrite H5 in H0.
          now apply IHdf2.
        + specialize (IHdf1 grad grad_env1 grad_env2); simpl in *.
          rewrite H1 in IHdf1; rewrite H2 in IHdf1.
          rewrite H5 in H; rewrite H5 in H0.
          now apply IHdf1.
      - Case "VectorDot"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        case_eq (df_eval σ df1); [ | tauto]; intros.
        case_eq (df_eval σ df2); [ | tauto]; intros.        
        specialize (IHdf1 (vmap (fun rv => (rv * grad)%R) d2) grad_env1 grad_env2).
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1
                                        (vmap (fun rv : R => (rv * (c * grad))%R) d2)); intros.
        rewrite H3 in H; rewrite  H4 in H; rewrite H5 in H; simpl in H.
        rewrite H3 in H0; rewrite H4 in H0; simpl in H0.        
        case_eq (df_eval_backprop_deriv σ df1 grad_env2
                                        (vmap (fun rv : R => (rv * grad)%R) d2)); intros.
        rewrite H6 in H0; simpl in H0.
        + specialize (IHdf2 (vmap (fun lv => (lv *grad)%R) d1) d3 d4).
          replace (fun i => (c * vmap (fun rv : R => rv * grad) d2 i)%R) with
              (vmap (fun rv : R => (rv * (c * grad))%R) d2) in IHdf1.
          rewrite H5 in IHdf1; rewrite H6 in IHdf1; simpl in IHdf1.
          assert (vartlookup d3 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 (s, DTfloat) neq1).
          case_eq (vartlookup d3 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d4 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H6 (s, DTfloat) neq2).
          case_eq (vartlookup d4 (s, DTfloat)); [ |tauto]; intros.
          rewrite H8 in IHdf2; rewrite H10 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d3
                                          (vmap (fun lv : R => (lv * (c * grad))%R) d1))
          ; [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d4 (vmap (fun lv : R => (lv * grad)%R) d1))
          ; [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d3 d7 d d5) by trivial.
          rewrite (split_subvar d4 d8 d0 d6) by trivial.
          replace
            (fun i : {n' : nat | n' < n} => (c * vmap (fun lv : R => lv * grad) d1 i)%R) with
              (vmap (fun lv : R => (lv * (c * grad))%R) d1) in IHdf2.
          rewrite H11 in IHdf2; rewrite H12 in IHdf2; simpl in *.
          assert (Some (subvar (s, DTfloat) d3 d) = Some (c * subvar (s, DTfloat) d4 d0)%R) by
              (apply IHdf1; trivial; discriminate).
          assert (Some (subvar (s, DTfloat) d7 d5) = Some (c * subvar (s, DTfloat) d8 d6)%R) by
              (apply IHdf2; trivial; discriminate).
          inversion H13; inversion H14.
          rewrite H16; rewrite H17; lra.
          apply FunctionalExtensionality.functional_extensionality; intros.
          rewrite vmap_mult.
          assert ((fun lv => (lv * (c * grad))%R) = (fun x0 => (c * (x0 * grad))%R)).
          apply FunctionalExtensionality.functional_extensionality; intros.
          lra.
          now rewrite H13.
          apply FunctionalExtensionality.functional_extensionality; intros.
          rewrite vmap_mult.          
          assert ((fun rv => (rv * (c * grad))%R) = (fun x0 => (c * (x0 * grad))%R)).
          apply FunctionalExtensionality.functional_extensionality; intros.
          lra.
          now rewrite H7.
        + now rewrite H6 in H0.
        + rewrite H3 in H; rewrite H4 in H.
          now rewrite H5 in H.
      - Case "VectorSum"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        specialize (IHdf (ConstVector n grad) grad_env1 grad_env2).
        rewrite H1 in IHdf; rewrite H2 in IHdf; simpl in IHdf.
        replace (ConstVector n (c * grad)%R) with 
            (fun i => (c * ConstVector n grad i)%R).
        now apply IHdf.
        now unfold ConstVector.
      - Case "MatrixSum"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        specialize (IHdf (ConstMatrix m n grad) grad_env1 grad_env2).
        rewrite H1 in IHdf; rewrite H2 in IHdf; simpl in IHdf.
        replace (ConstMatrix m n (c * grad)%R) with 
            (fun i j => (c * ConstMatrix m n grad i j)%R).
        now apply IHdf.
        now unfold ConstMatrix.
      - Case "VectorElem"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        specialize (IHdf (fun k =>
                            if equiv_dec (` k) (` i) then grad else 0%R) grad_env1 grad_env2).
        rewrite H1 in IHdf; rewrite H2 in IHdf; simpl in *.
        replace (fun i0 => (c * (if equiv_dec (` i0) (` i) then grad else 0))%R) with
            (fun k : {n' : nat | n' < n} => 
               if equiv_dec (` k) (` i) then (c * grad)%R else 0%R) in IHdf.
        now rewrite IHdf.
        apply FunctionalExtensionality.functional_extensionality; intros.
        destruct (equiv_dec (` x) (` i)); lra.
      - Case "MatrixElem"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        specialize (IHdf (fun (k1 : {n' : nat | n' < m}) (k2 : {m' : nat | m' < n}) =>
                            if equiv_dec (` k1) (` i)
                            then if equiv_dec (` k2) (` j) then grad else 0%R else 0%R)
                         grad_env1 grad_env2).
        rewrite H1 in IHdf; rewrite H2 in IHdf; simpl in *.
        replace (fun (k1 : {n' : nat | n' < m}) (k2 : {m' : nat | m' < n}) =>
                   if equiv_dec (` k1) (` i)
                   then if equiv_dec (` k2) (` j) then (c * grad)%R else 0%R else 0%R) with
            (fun (i0 : {n' : nat | n' < m}) (j0 : {m' : nat | m' < n}) =>
               (c *
                (if equiv_dec (` i0) (` i)
                 then if equiv_dec (` j0) (` j) then  grad else 0
                 else 0))%R) in *.
        + now rewrite IHdf.
        + apply FunctionalExtensionality.functional_extensionality; intros.
          apply FunctionalExtensionality.functional_extensionality; intros. 
          destruct (equiv_dec (` x) (` i)); [|lra].
          destruct (equiv_dec (` x0) (` j)); lra.
      - Case "MatrixVectorMult"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        case_eq ( df_eval σ df1); [|tauto].
        case_eq ( df_eval σ df2); [|tauto]; intros.
        specialize (IHdf1 (fun i j => (grad i * d j)%R) grad_env1 grad_env2).
        rewrite H4 in IHdf1; rewrite H3 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 
                                        (fun i j => (c * grad i * d j)%R)); intros.
        rewrite H1 in H; rewrite  H2 in H; simpl in H.
        rewrite H1 in H0; rewrite  H2 in H0; simpl in H0.        
        rewrite H5 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 
                                        (fun i j => (grad i * d j)%R)); intros.
        rewrite H6 in H0; simpl in H0.
        + specialize (IHdf2 (matrix_vector_mult (fun i j => d0 j i) grad) d3 d4).
          replace
            (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                (c * (grad i * d j))%R) with
            (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                (c * grad i * d j)%R) in IHdf1.
          * rewrite H5 in IHdf1; rewrite H6 in IHdf1; simpl in IHdf1.
            assert (vartlookup d3 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 (s, DTfloat) neq1).
            case_eq (vartlookup d3 (s, DTfloat)); [ |tauto]; intros.
            assert (vartlookup d4 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H6 (s, DTfloat) neq2).
            case_eq (vartlookup d4 (s, DTfloat)); [ |tauto]; intros.
            rewrite H8 in IHdf2; rewrite H10 in IHdf2; simpl in *.
            unfold lift; match_case; [|tauto]; intros.
            case_eq (df_eval_backprop_deriv σ df2 d4 
                                            (matrix_vector_mult (fun i j => d0 j i) grad))
              ; [|tauto]; intros; simpl; f_equal.
            rewrite (split_subvar d3 d7 d2 d5) by trivial.
            rewrite (split_subvar d4 d8 d1 d6) by trivial.
            replace  (fun i : {n' : nat | n' < n} =>
                (c *
                 (@matrix_vector_mult floatish_R _ _
                   (fun (i0 : {n' : nat | (n' < n)%nat}) (j : {m' : nat | (m' < m)%nat}) =>
                      d0 j i0) grad) i)%R) with
                 (matrix_vector_mult
                    (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => d0 j i)
                    (fun i : {n' : nat | n' < m} => (c * grad i)%R)) in IHdf2.
            -- rewrite H11 in IHdf2; rewrite H12 in IHdf2; simpl in *.
               assert (Some (subvar (s, DTfloat) d3 d2) = 
                       Some (c * subvar (s, DTfloat) d4 d1)%R) by
                   (apply IHdf1; trivial; discriminate).
               assert (Some (subvar (s, DTfloat) d7 d5) = 
                       Some (c * subvar (s, DTfloat) d8 d6)%R) by
                   (apply IHdf2; trivial; discriminate).
               inversion H13; inversion H14.
               rewrite H16; rewrite H17; lra.
            -- unfold matrix_vector_mult.
               apply FunctionalExtensionality.functional_extensionality; intros.
               rewrite vsum_mult; f_equal.
               apply FunctionalExtensionality.functional_extensionality; intros.               
               simpl; lra.
          * apply FunctionalExtensionality.functional_extensionality; intros.
            apply FunctionalExtensionality.functional_extensionality; intros.
            lra.
        + now rewrite H6 in H0.
        + rewrite H2 in H; rewrite H1 in H.
          now rewrite H5 in H.
      - Case "MatrixVectorAdd"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        specialize (IHdf1 grad grad_env1 grad_env2); intros.
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (fun i j => (c * grad i j)%R))
          ; intros.
        + rewrite H3 in H; simpl in H.
          case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); intros.
          * rewrite H4 in H0; simpl in H0.
            match_option_in H0; [|tauto].
            match_option_in H; [|tauto].
            rewrite H3 in IHdf1.
            unfold lift.
            f_equal.
            rewrite H4 in IHdf1.
            unfold lift in IHdf1.
            assert (vartlookup d1 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H3 (s, DTfloat) neq1).
            case_eq (vartlookup d1 (s, DTfloat)); [ |tauto]; intros.
            assert (vartlookup d2 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
            case_eq (vartlookup d2 (s, DTfloat)); [ |tauto]; intros.
            rewrite (split_subvar d1 d4 d0 d5) by trivial.
            rewrite (split_subvar d2 d3 d d6) by trivial.
            assert (Some (subvar (s, DTfloat) d1 d0) = Some (c * subvar (s, DTfloat) d2 d)%R) 
              by (apply IHdf1; trivial; discriminate). 
            inversion H9; rewrite H11.
            assert (Some (subvar (s, DTfloat) d4 d5) = Some (c * subvar (s, DTfloat) d3 d6)%R).
            -- f_equal.
               apply (scalarMult_list_env_iter 
                        s c d5 d6 {m' : nat | m' < n}
                        (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                           df_eval_backprop_deriv 
                             σ df2 env
                             (transpose
                                (fun (i0 : {n' : nat | n' < m}) 
                                     (j : {m' : nat | m' < n}) =>
                                   (c * grad i0 j)%R) i))
                        (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                           df_eval_backprop_deriv σ df2 env (transpose grad i))
                        (bounded_seq0 n) d1 d2 d4 d3); trivial.
               ++ intros.
                  assert (vartlookup env1 (s, DTfloat) <> None); [congruence|].
                  assert (vartlookup env2 (s, DTfloat) <> None); [congruence|].        
                  assert (df_eval_backprop_deriv 
                            σ df2 env1
                            (transpose
                               (fun (i0 : {n' : nat | n' < m}) 
                                    (j : {m' : nat | m' < n}) => (c * grad i0 j)%R) i) <> None)
                         ; [congruence|].
                  assert (df_eval_backprop_deriv σ df2 env2 (transpose grad i) <> None)
                  ;[congruence|].
                  specialize (IHdf2 (transpose grad i) env1 env2).
                  specialize (IHdf2 H15 H16).
                  specialize (IHdf2 H17 H18).
                  unfold lift in IHdf2; simpl in IHdf2.
                  rewrite H10, H12, H14 in IHdf2.
                  unfold transpose in IHdf2; unfold transpose in H13.
                  rewrite H13 in IHdf2; now inversion IHdf2.
               ++ intros.
                  now apply (df_eval_backprop_deriv_preserves_lookup_not_none H10).
               ++ intros.
                  now apply (df_eval_backprop_deriv_preserves_lookup_not_none H10).
            -- inversion H10; rewrite H13; lra.
          * rewrite H4 in H0; tauto.
        + rewrite H3 in H; tauto.
      - Case "MatrixMult"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        case_eq ( df_eval σ df1); [|tauto].
        case_eq ( df_eval σ df2); [|tauto]; intros.
        specialize (IHdf1 (matrix_mult grad (fun i j => d j i)) grad_env1 grad_env2).
        rewrite H4 in IHdf1; rewrite H3 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 
                                        (matrix_mult (fun i j => (c * grad i j)%R) 
                                                     (fun i j => d j i))); intros.
        rewrite H1 in H; rewrite  H2 in H; simpl in H.
        rewrite H1 in H0; rewrite  H2 in H0; simpl in H0.        
        rewrite H5 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 
                                        (matrix_mult grad (fun i j => d j i))); intros.
        rewrite H6 in H0; simpl in H0.
        + specialize (IHdf2 (matrix_mult (fun i j => d0 j i)  grad) d3 d4).
          replace (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < p}) =>
              (c *
               (@matrix_mult floatish_R m n p grad
                 (fun (i0 : {n' : nat | (n' < n)%nat}) (j0 : {m' : nat | (m' < p)%nat}) =>
                  d j0 i0)) i j)%R) with
              (matrix_mult (fun i j => (c * grad i j)%R) 
                           (fun i j => d j i)) in IHdf1.
          * rewrite H5 in IHdf1; rewrite H6 in IHdf1; simpl in IHdf1.
            assert (vartlookup d3 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 (s, DTfloat) neq1).
            case_eq (vartlookup d3 (s, DTfloat)); [ |tauto]; intros.
            assert (vartlookup d4 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H6 (s, DTfloat) neq2).
            case_eq (vartlookup d4 (s, DTfloat)); [ |tauto]; intros.
            rewrite H8 in IHdf2; rewrite H10 in IHdf2; simpl in *.
            unfold lift; match_case; [|tauto]; intros.
            case_eq (df_eval_backprop_deriv σ df2 d4 (matrix_mult (fun i j => d0 j i) grad))
              ; [|tauto]; intros; simpl; f_equal.
            rewrite (split_subvar d3 d7 d2 d5) by trivial.
            rewrite (split_subvar d4 d8 d1 d6) by trivial.
            replace (fun (i : {n' : nat | n' < p}) (j : {m' : nat | m' < n}) =>
                (c *
                 (@matrix_mult floatish_R p m n
                               (fun (i0 : {n' : nat | (n' < p)%nat}) 
                                    (j0 : {m' : nat | (m' < m)%nat}) =>
                                  d0 j0 i0) grad) i j)%R) with
               (matrix_mult (fun (i : {n' : nat | n' < p}) (j : {m' : nat | m' < m}) => d0 j i)
                            (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) => 
                               (c * grad i j)%R)) in IHdf2.
            -- rewrite H11 in IHdf2; rewrite H12 in IHdf2; simpl in *.
               assert (Some (subvar (s, DTfloat) d3 d2) = 
                       Some (c * subvar (s, DTfloat) d4 d1)%R) by
                   (apply IHdf1; trivial; discriminate).
               assert (Some (subvar (s, DTfloat) d7 d5) = 
                       Some (c * subvar (s, DTfloat) d8 d6)%R) by
                   (apply IHdf2; trivial; discriminate).
               inversion H13; inversion H14.
               rewrite H16; rewrite H17; lra.
            -- unfold matrix_mult.
               apply FunctionalExtensionality.functional_extensionality; intros.
               apply FunctionalExtensionality.functional_extensionality; intros.
               rewrite vsum_mult; f_equal.
               apply FunctionalExtensionality.functional_extensionality; intros.               
               simpl; lra.
          * unfold matrix_mult.
            apply FunctionalExtensionality.functional_extensionality; intros.
            apply FunctionalExtensionality.functional_extensionality; intros.
            rewrite vsum_mult; f_equal.
            apply FunctionalExtensionality.functional_extensionality; intros.
            simpl; lra.
        + now rewrite H6 in H0.
        + rewrite H2 in H; rewrite H1 in H.
          now rewrite H5 in H.
      - Case "VectorPlus"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        specialize (IHdf1 grad grad_env1 grad_env2); intros.
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (fun i  => (c * grad i)%R)); intros.
        rewrite H3 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); intros.
        rewrite H4 in H0; simpl in H0.
        + specialize (IHdf2 grad d1 d2).
          rewrite H3 in IHdf1; rewrite H4 in IHdf1.
          assert (vartlookup d1 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H3 (s, DTfloat) neq1).
          case_eq (vartlookup d1 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d2 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
          case_eq (vartlookup d2 (s, DTfloat)); [ |tauto]; intros.
          rewrite H6 in IHdf2; rewrite H8 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d1 (fun i  => (c * grad i)%R))
             ; [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d2 grad); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d1 d5 d0 d3) by trivial.
          rewrite (split_subvar d2 d6 d d4) by trivial.
          rewrite H9 in IHdf2; rewrite H10 in IHdf2; simpl in *.
          assert (Some (subvar (s, DTfloat) d1 d0) = Some (c * subvar (s, DTfloat) d2 d)%R) by
              (apply IHdf1; trivial; discriminate).
          assert (Some (subvar (s, DTfloat) d5 d3) = Some (c * subvar (s, DTfloat) d6 d4)%R) by
              (apply IHdf2; trivial; discriminate).
          inversion H11; inversion H12.
          rewrite H14; rewrite H15; lra.
        + now rewrite H4 in H0.
        + now rewrite H3 in H.
      - Case "VectorMinus"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        specialize (IHdf1 grad grad_env1 grad_env2); intros.
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (fun i  => (c * grad i )%R))
          ; intros.
        rewrite H3 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); intros.
        rewrite H4 in H0; simpl in H0.
        + specialize (IHdf2 (fun i => (- grad i)%R) d1 d2).
          rewrite H3 in IHdf1; rewrite H4 in IHdf1.
          assert (vartlookup d1 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H3 (s, DTfloat) neq1).
          case_eq (vartlookup d1 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d2 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
          case_eq (vartlookup d2 (s, DTfloat)); [ |tauto]; intros.
          rewrite H6 in IHdf2; rewrite H8 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d1 (fun i => (- (c * grad i))%R))
             ; [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d2 (fun i => (- grad i)%R)); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d1 d5 d0 d3) by trivial.
          rewrite (split_subvar d2 d6 d d4) by trivial.
          replace (fun i => (c * - grad i)%R) with (fun i => (-( c * grad i))%R) in IHdf2.
          * rewrite H9 in IHdf2; rewrite H10 in IHdf2; simpl in *.
            assert (Some (subvar (s, DTfloat) d1 d0) = Some (c * subvar (s, DTfloat) d2 d)%R) by
              (apply IHdf1; trivial; discriminate).
            assert (Some (subvar (s, DTfloat) d5 d3) = Some (c * subvar (s, DTfloat) d6 d4)%R) by
              (apply IHdf2; trivial; discriminate).
            inversion H11; inversion H12.
            rewrite H14; rewrite H15; lra.
          * apply FunctionalExtensionality.functional_extensionality; intros.
            lra.
        + now rewrite H4 in H0.
        + now rewrite H3 in H.
      - Case "MatrixPlus"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        specialize (IHdf1 grad grad_env1 grad_env2); intros.
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (fun i j => (c * grad i j)%R))
          ; intros.
        rewrite H3 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); intros.
        rewrite H4 in H0; simpl in H0.
        + specialize (IHdf2 grad d1 d2).
          rewrite H3 in IHdf1; rewrite H4 in IHdf1.
          assert (vartlookup d1 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H3 (s, DTfloat) neq1).
          case_eq (vartlookup d1 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d2 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
          case_eq (vartlookup d2 (s, DTfloat)); [ |tauto]; intros.
          rewrite H6 in IHdf2; rewrite H8 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d1 (fun i j => (c * grad i j)%R))
             ; [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d2 grad); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d1 d5 d0 d3) by trivial.
          rewrite (split_subvar d2 d6 d d4) by trivial.
          rewrite H9 in IHdf2; rewrite H10 in IHdf2; simpl in *.
          assert (Some (subvar (s, DTfloat) d1 d0) = Some (c * subvar (s, DTfloat) d2 d)%R) by
              (apply IHdf1; trivial; discriminate).
          assert (Some (subvar (s, DTfloat) d5 d3) = Some (c * subvar (s, DTfloat) d6 d4)%R) by
              (apply IHdf2; trivial; discriminate).
          inversion H11; inversion H12.
          rewrite H14; rewrite H15; lra.
        + now rewrite H4 in H0.
        + now rewrite H3 in H.
      - Case "MatrixMinus"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        specialize (IHdf1 grad grad_env1 grad_env2); intros.
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 (fun i j => (c * grad i j)%R))
          ; intros.
        rewrite H3 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); intros.
        rewrite H4 in H0; simpl in H0.
        + specialize (IHdf2 (fun i j => (- grad i j)%R) d1 d2).
          rewrite H3 in IHdf1; rewrite H4 in IHdf1.
          assert (vartlookup d1 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H3 (s, DTfloat) neq1).
          case_eq (vartlookup d1 (s, DTfloat)); [ |tauto]; intros.
          assert (vartlookup d2 (s, DTfloat) <> None) by
              apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
          case_eq (vartlookup d2 (s, DTfloat)); [ |tauto]; intros.
          rewrite H6 in IHdf2; rewrite H8 in IHdf2; simpl in *.
          case_eq (df_eval_backprop_deriv σ df2 d1 (fun i j  => (- (c * grad i j))%R))
             ; [|tauto]; intros.
          case_eq (df_eval_backprop_deriv σ df2 d2 (fun i j => (- grad i j)%R)); [|tauto]; intros; simpl; f_equal.
          rewrite (split_subvar d1 d5 d0 d3) by trivial.
          rewrite (split_subvar d2 d6 d d4) by trivial.
          replace (fun i j => (c * - grad i j)%R) with 
              (fun i j  => (-( c * grad i j))%R) in IHdf2.
          * rewrite H9 in IHdf2; rewrite H10 in IHdf2; simpl in *.
            assert (Some (subvar (s, DTfloat) d1 d0) = Some (c * subvar (s, DTfloat) d2 d)%R) by
              (apply IHdf1; trivial; discriminate).
            assert (Some (subvar (s, DTfloat) d5 d3) = Some (c * subvar (s, DTfloat) d6 d4)%R) by
              (apply IHdf2; trivial; discriminate).
            inversion H11; inversion H12.
            rewrite H14; rewrite H15; lra.
          * apply FunctionalExtensionality.functional_extensionality; intros.
            apply FunctionalExtensionality.functional_extensionality; intros.             
            lra.
        + now rewrite H4 in H0.
        + now rewrite H3 in H.
      - Case "VectorScalMult"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        case_eq ( df_eval σ df1); [|tauto].
        case_eq ( df_eval σ df2); [|tauto]; intros.
        specialize (IHdf1 (vsum (fun j => (d j * grad j)%R)) grad_env1 grad_env2).
        rewrite H4 in IHdf1; rewrite H3 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 
                                        (vsum (fun j => (d j * (c * grad j))%R)))
                                        
        ; intros.
        rewrite H1 in H; rewrite  H2 in H; simpl in H.
        rewrite H1 in H0; rewrite  H2 in H0; simpl in H0.        
        rewrite H5 in H; simpl in H.
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 
                                        (vsum (fun j => (d j * grad j)%R)))
        ; intros.
        rewrite H6 in H0; simpl in H0.
        + specialize (IHdf2 (fun j => (grad j * d0)%R) d3 d4).
          replace 
            (c *
             (@vsum floatish_R _
               (fun  (j : {n' : nat | (n' < n)%nat}) =>
                  d j * grad j)))%R with
              (vsum
                 (fun (j : {n' : nat | n' < n})  =>
                    (d j * (c * grad j))%R)) in IHdf1.
          * rewrite H5 in IHdf1; rewrite H6 in IHdf1; simpl in IHdf1.
            assert (vartlookup d3 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 (s, DTfloat) neq1).
            case_eq (vartlookup d3 (s, DTfloat)); [ |tauto]; intros.
            assert (vartlookup d4 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H6 (s, DTfloat) neq2).
            case_eq (vartlookup d4 (s, DTfloat)); [ |tauto]; intros.
            rewrite H8 in IHdf2; rewrite H10 in IHdf2; simpl in *.
            case_eq (df_eval_backprop_deriv σ df2 d3
                    (fun (j : {n' : nat | n' < n}) => 
                       (d0 * (c * grad j))%R))
               ; [|tauto]; intros.
            case_eq (df_eval_backprop_deriv σ df2 d4 (fun j => (d0 * grad j)%R))
              ; [|tauto]; intros; simpl; f_equal.
            rewrite (split_subvar d3 d7 d2 d5) by trivial.
            rewrite (split_subvar d4 d8 d1 d6) by trivial.
            replace  (fun i => (c * (grad i * d0))%R) with 
                (fun j => (d0 * (c * grad j))%R) in IHdf2.
            replace (fun j => (grad j * d0)%R) with (fun j => (d0 * grad j)%R) in IHdf2.
            -- rewrite H11 in IHdf2; rewrite H12 in IHdf2; simpl in *.
               assert (Some (subvar (s, DTfloat) d3 d2) = 
                       Some (c * subvar (s, DTfloat) d4 d1)%R) by
                   (apply IHdf1; trivial; discriminate).
               assert (Some (subvar (s, DTfloat) d7 d5) = 
                       Some (c * subvar (s, DTfloat) d8 d6)%R) by
                   (apply IHdf2; trivial; discriminate).
               inversion H13; inversion H14.
               rewrite H16; rewrite H17; lra.
            -- apply FunctionalExtensionality.functional_extensionality; intros.
               lra.
            -- apply FunctionalExtensionality.functional_extensionality; intros.
               lra.
          * rewrite vsum_mult; f_equal.
            apply FunctionalExtensionality.functional_extensionality; intros.
            lra.
        + now rewrite H6 in H0.
        + rewrite H2 in H; rewrite H1 in H.
          now rewrite H5 in H.
      - Case "MatrixScalMult"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto].        
        case_eq ( df_eval σ df1); [|tauto].
        case_eq ( df_eval σ df2); [|tauto]; intros.
        specialize (IHdf1 (msum (fun i j => (d i j * grad i j)%R)) grad_env1 grad_env2).
        rewrite H4 in IHdf1; rewrite H3 in IHdf1; simpl in *.
        case_eq (df_eval_backprop_deriv σ df1 grad_env1 
                                        (msum (fun i j => (d i j * (c * grad i j))%R)))
                                        
        ; intros.
        rewrite H1, H2, H5 in H; simpl in H.
        rewrite H1, H2 in H0; simpl in H0.        
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 
                                        (msum (fun i j => (d i j * grad i j)%R)))
        ; intros.
        rewrite H6 in H0; simpl in H0.
        + specialize (IHdf2 (fun i j => (grad i j * d0)%R) d3 d4).
          replace 
            (c *
             (@msum floatish_R _ _
               (fun (i : {n' : nat | (n' < n)%nat}) (j : {m' : nat | (m' < m)%nat}) =>
                  d i j * grad i j)))%R with

              (msum
                 (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                    (d i j * (c * grad i j))%R)) in IHdf1.
          * rewrite H5 in IHdf1; rewrite H6 in IHdf1; simpl in IHdf1.
            assert (vartlookup d3 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 (s, DTfloat) neq1).
            case_eq (vartlookup d3 (s, DTfloat)); [ |tauto]; intros.
            assert (vartlookup d4 (s, DTfloat) <> None) by
                apply (df_eval_backprop_deriv_preserves_lookup_not_none H6 (s, DTfloat) neq2).
            case_eq (vartlookup d4 (s, DTfloat)); [ |tauto]; intros.
            rewrite H8 in IHdf2; rewrite H10 in IHdf2; simpl in *.
            case_eq (df_eval_backprop_deriv σ df2 d3
                    (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => 
                       (c * grad i j * d0)%R))
               ; [|tauto]; intros.
            case_eq (df_eval_backprop_deriv σ df2 d4 (fun i j => (grad i j * d0)%R))
              ; [|tauto]; intros; simpl; f_equal.
            rewrite (split_subvar d3 d7 d2 d5) by trivial.
            rewrite (split_subvar d4 d8 d1 d6) by trivial.
            replace  (fun i j => (c * (grad i j * d0))%R) with 
                (fun i j => (c * grad i j * d0)%R) in IHdf2.
            -- rewrite H11 in IHdf2; rewrite H12 in IHdf2; simpl in *.
               assert (Some (subvar (s, DTfloat) d3 d2) = 
                       Some (c * subvar (s, DTfloat) d4 d1)%R) by
                   (apply IHdf1; trivial; discriminate).
               assert (Some (subvar (s, DTfloat) d7 d5) = 
                       Some (c * subvar (s, DTfloat) d8 d6)%R) by
                   (apply IHdf2; trivial; discriminate).
               inversion H13; inversion H14.
               rewrite H16; rewrite H17; lra.
            -- apply FunctionalExtensionality.functional_extensionality; intros.
               apply FunctionalExtensionality.functional_extensionality; intros.
               lra.
          * unfold msum.
            rewrite vsum_mult; f_equal.
            apply FunctionalExtensionality.functional_extensionality; intros.
            rewrite vmap_nth.
            rewrite vmap_nth.
            rewrite vsum_mult.
            f_equal.
            apply FunctionalExtensionality.functional_extensionality; intros.
            lra.
        + now rewrite H6 in H0.
        + rewrite H2 in H; rewrite H1 in H.
          now rewrite H5 in H.
      - Case "VectorApply"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        simpl in *.
        case_eq (df_eval σ df2); [ | tauto].
        intros.
        rewrite H3 in H; rewrite H3 in H0; simpl in *.
        match_option_in H0; [|tauto].
        specialize (IHdf1 v0 grad_env1 grad_env2). 
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in IHdf1.
        match_option_in H; [|tauto].
        vectoro_assert_forall_in eqq i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        vectoro_assert_forall_in eqq0 i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        assert (v1 = (fun i => (c * v0 i)%R)).
        apply FunctionalExtensionality.functional_extensionality; intros.        
        specialize (H4 x).
        specialize (H5 x).
        rewrite vmap_nth in H4; simpl in H4.
        rewrite vmap_nth in H5; simpl in H5.
        match_option_in H4.
        match_option_in H5.
        inversion H4; inversion H5; subst.
        assert (Some d2 = Some d3).
        rewrite <- eqq1.
        rewrite <- eqq2; trivial.
        inversion H6; subst; lra.
        subst.
        apply IHdf1; trivial; discriminate.
      - Case "MatrixApply"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        simpl in *.
        case_eq (df_eval σ df2); [ | tauto].
        intros.
        rewrite H3 in H; rewrite H3 in H0; simpl in *.
        match_option_in H0; [|tauto].
        match_option_in H; [|tauto].
        unfold matrixo_to_omatrix in eqq.
        unfold matrixo_to_omatrix in eqq0.
        vectoro_assert_forall_in eqq i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        vectoro_assert_forall_in eqq0 i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        assert (m1 = (fun i j => (c * m0 i j)%R)).
        apply FunctionalExtensionality.functional_extensionality; intros.
        apply FunctionalExtensionality.functional_extensionality; intros. 
        specialize (H4 x); specialize (H5 x); simpl in H4; simpl in H5.
        vectoro_assert_forall_in H4 j.
        apply vectoro_to_ovector_forall_some_f; trivial.
        vectoro_assert_forall_in H5 j.
        apply vectoro_to_ovector_forall_some_f; trivial.
        specialize (H6 x0); specialize (H7 x0).
        unfold mmap in H6; unfold mmap in H7.
        rewrite vmap_nth in H6; rewrite vmap_nth in H6; simpl in H6.
        rewrite vmap_nth in H7; rewrite vmap_nth in H7; simpl in H7.
        match_case_in H6; intros.
        rewrite H8 in H6; simpl in H6.
        match_case_in H7; intros.
        rewrite H9 in H7; simpl in H7.
        match_option_in H6.
        match_option_in H7.
        inversion H6; inversion H7.
        unfold matrix_zip in H8.
        unfold matrix_zip in H9.
        rewrite vmap_nth in H8.
        rewrite vmap_nth in H9.
        unfold vector_zip in H8.
        unfold vector_zip in H9.
        inversion H8; subst r r0.
        inversion H9; subst r1 r2.
        assert (Some d2 = Some d3).
        rewrite <- eqq1; rewrite <- eqq2; trivial.
        inversion H10; subst; lra.
        specialize (IHdf1 m0 grad_env1 grad_env2).
        rewrite H1, H2 in IHdf1; simpl in IHdf1.
        subst m1.
        apply IHdf1; trivial; discriminate.
      - Case "VLossfun"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        simpl in *.
        case_eq (df_eval σ df2); [ | tauto].
        intros.
        rewrite H3 in H; rewrite H3 in H0; simpl in *.
        match_option_in H0; [|tauto].
        match_option_in H; [|tauto].
        vectoro_assert_forall_in eqq i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        vectoro_assert_forall_in eqq0 i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        assert (v0 = (fun i => (c * v i)%R)).
        apply FunctionalExtensionality.functional_extensionality; intros. 
        specialize (H4 x); specialize (H5 x).
        rewrite vmap_nth in H4; simpl in H4.
        rewrite vmap_nth in H5; simpl in H5.
        match_option_in H4.
        match_option_in H5.
        assert (Some d2 = Some d3).
        rewrite <- eqq1; rewrite <- eqq2; trivial.
        inversion H6; subst.
        inversion H4; inversion H5; lra.
        subst.
        specialize (IHdf1 v grad_env1 grad_env2).
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in IHdf1.
        apply IHdf1; trivial; discriminate.
      - Case "MLossfun"%string.
        case_eq (vartlookup grad_env1 (s, DTfloat)); [ |tauto]; intros.
        case_eq (vartlookup grad_env2 (s, DTfloat)); [ |tauto]; intros.        
        simpl in *.
        case_eq (df_eval σ df2); [ | tauto].
        intros.
        rewrite H3 in H; rewrite H3 in H0; simpl in *.
        match_option_in H0; [|tauto].
        match_option_in H; [|tauto].
        unfold matrixo_to_omatrix in eqq.
        unfold matrixo_to_omatrix in eqq0.
        vectoro_assert_forall_in eqq i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        vectoro_assert_forall_in eqq0 i.
        apply vectoro_to_ovector_forall_some_f; trivial.
        assert (m1 = (fun i j => (c * m0 i j)%R)).
        apply FunctionalExtensionality.functional_extensionality; intros.
        apply FunctionalExtensionality.functional_extensionality; intros. 
        specialize (H4 x); specialize (H5 x); simpl in H4; simpl in H5.
        vectoro_assert_forall_in H4 j.
        apply vectoro_to_ovector_forall_some_f; trivial.
        vectoro_assert_forall_in H5 j.
        apply vectoro_to_ovector_forall_some_f; trivial.
        specialize (H6 x0); specialize (H7 x0).
        unfold mmap in H6; unfold mmap in H7.
        rewrite vmap_nth in H6; rewrite vmap_nth in H6; simpl in H6.
        rewrite vmap_nth in H7; rewrite vmap_nth in H7; simpl in H7.
        match_destr_in H6.
        match_option_in H6.
        match_option_in H7.
        assert (Some d2 = Some d3).
        rewrite <- eqq1; rewrite <- eqq2; trivial.
        inversion H8; subst.
        inversion H6; inversion H7.
        lra.
        rewrite H6.
        specialize (IHdf1 m0 grad_env1 grad_env2).
        rewrite H1 in IHdf1; rewrite H2 in IHdf1; simpl in IHdf1.
        subst.
        apply IHdf1; trivial; discriminate.
    Qed.

    Ltac simpl_closed_backprop :=
      match goal with
      | [|- context [
                match df_eval_backprop_deriv ?σ ?df1 ?grad_env1 ?grad with
                | Some _ => _
                | None => _
                end]] => case_eq (df_eval_backprop_deriv σ df1 grad_env1 grad)
                         ; [let env := fresh "env" in let eqq := fresh "eqq" in intros env eqq |
                            let eqq := fresh "eqq" in
                            intros eqq;
                            eelim backprop_deriv_fully_closed_not_none; [clear eqq | eapply eqq]; trivial
                           ]
      end.

    Ltac simpler2 :=
      trivial;
      repeat 
        match goal with
        | [ |- Some _ <> None ] => congruence
        | [ |- None <> Some _ ] => congruence

        | [H:vartlookup ?grad_env ?a <> None
           |- context [vartlookup ?grad_env ?a]] =>
          case_eq (vartlookup grad_env a); [
            let d := fresh "val" in
            let eqq := fresh "eqq" in
            intros d eqq; simpl in d 
          | intros ?; eelim H; solve[auto]]
        | [H: df_eval_backprop_deriv ?σ ?df1 ?grad_env1 _ = Some ?grad_env2
           |- context [vartlookup ?grad_env2 ?a]] =>
          case_eq (vartlookup grad_env2 a); [
            let d := fresh "val" in
            let eqq := fresh "eqq" in
            intros d eqq; simpl in d 
          | let eqq := fresh "eqq" in
            intros eqq; eelim df_eval_backprop_deriv_preserves_lookup_not_none; [apply H | idtac | apply eqq]; solve[auto]
          ]
                                              
        | [H:vartlookup ?grad_env ?a <> None
           |- context [vartlookup ?grad_env ?a]] =>
          case_eq (vartlookup grad_env a); [
            let d := fresh "val" in
            let eqq := fresh "eqq" in
            intros d eqq; simpl in d 
          | intros ?; eelim H; solve[auto || congruence]]
        | [H: df_eval_backprop_deriv ?σ ?df1 ?grad_env1 _ = Some ?grad_env2
           |- context [vartlookup ?grad_env2 ?a]] =>
          case_eq (vartlookup grad_env2 a); [
            let d := fresh "val" in
            let eqq := fresh "eqq" in
            intros d eqq; simpl in d 
          | let eqq := fresh "eqq" in
            intros eqq; eelim df_eval_backprop_deriv_preserves_lookup_not_none; [apply H | idtac | apply eqq]; solve[auto || congruence]
          ]
        | [H:vartlookup ?grad_env ?a <> None,
             H2:context [match vartlookup ?grad_env ?a with | _ => _ end] |- _] =>
          case_eq (vartlookup grad_env a); [
            let d := fresh "val" in
            let eqq := fresh "eqq" in
            intros d eqq; simpl in d; rewrite eqq in H2
          | intros ?; eelim H; solve[auto || congruence]]
        | [H: df_eval_backprop_deriv ?σ ?df1 ?grad_env1 _ = Some ?grad_env2,
           H2: context [match vartlookup ?grad_env2 ?a with _ => _ end] |- _] =>
          case_eq (vartlookup grad_env2 a); [
            let d := fresh "val" in
            let eqq := fresh "eqq" in
            intros d eqq; simpl in d; rewrite eqq in H2
          | let eqq := fresh "eqq" in
            intros eqq; eelim df_eval_backprop_deriv_preserves_lookup_not_none; [apply H | idtac | apply eqq]; solve[auto || congruence]]

        end.
    
    Lemma backprop_indep_env {T} (σ:df_env) (df:DefinedFunction UnitAnn T) (s:SubVar) 
          (grad_env1 grad_env2:df_env) (grad : definition_function_types_interp T) :
     let v := (s, DTfloat) in
     vartlookup grad_env1 v <> None ->
     vartlookup grad_env2 v <> None ->     
     let vl := map (fun ve => projT1 ve) σ in
     fully_closed_over df vl ->
     df_eval_backprop_delta σ df v grad_env1 grad =
     df_eval_backprop_delta σ df v grad_env2 grad.
    Proof.
      revert grad_env1 grad_env2.
      unfold df_eval_backprop_delta.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case
      ; simpl; intros grad_env1 grad_env2 neq1 neq2; intros.
      - Case "Number"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        unfold snd in *.
        f_equal.
        unfold subvar; simpl.
        rewrite eqq, eqq0.
        lra.
      - Case "Constant"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        unfold snd in *.
        f_equal.
        unfold subvar; simpl.
        rewrite eqq, eqq0.
        lra.
      - Case "DVector"%string.
        rewrite vforall_forall in H0.
        unfold two_vector_env_iter_alt.
        match_option; [|tauto].
        match_option; [|tauto].
        unfold lift; simpl.
        match_option.
        + match_option.
          f_equal.
          apply (list_env_iter_subvar_env2 
                   s d d0 {n' : nat | n' < n}
                   (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                      df_eval_backprop_deriv σ (x i) env (grad i))
                   (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                      df_eval_backprop_deriv σ (x i) env (grad i))
                   (bounded_seq0 n) grad_env1 grad_env2 d1 d2); trivial.
          * intros.
            specialize (H i (grad i) env1 env2).
            cut_to H; try congruence; eauto 3.
            rewrite H1, H2, H3, H4 in H.
            unfold lift in H.
            now inversion H.
          * intros.
            apply (df_eval_backprop_deriv_preserves_lookup_not_none H1); trivial.
          * intros.
            apply (df_eval_backprop_deriv_preserves_lookup_not_none H1); trivial.
          * assert (list_env_iter
                      (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                         df_eval_backprop_deriv σ (x i) env (grad i)) (Some grad_env2) 
                      (bounded_seq0 n) <> None).
            apply list_env_iter_total_fun; intros.
            apply backprop_deriv_fully_closed_not_none; trivial.
            tauto.
        + assert (list_env_iter
                    (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                       df_eval_backprop_deriv σ (x i) env (grad i)) (Some grad_env1) 
                    (bounded_seq0 n) <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none; trivial.
          tauto.
      - Case "DMatrix"%string.
        rewrite vforall_forall in H0.
        unfold two_matrix_env_iter_alt.
        match_option; [|tauto].
        match_option; [|tauto].
        unfold lift; simpl.
        match_option.
        + match_option.
          * f_equal.
            apply (list_env_iter_subvar_env2 
                     s d d0 {n' : nat | n' < n}
                     (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                        list_env_iter
                          (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                             df_eval_backprop_deriv σ (x i j) env0 (grad i j)) 
                          (Some env) (bounded_seq0 m))
                     (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                        list_env_iter
                          (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                             df_eval_backprop_deriv σ (x i j) env0 (grad i j)) 
                          (Some env) (bounded_seq0 m))
                     (bounded_seq0 n) grad_env1 grad_env2 d1 d2); trivial.
            -- intros.
               apply (list_env_iter_subvar_env2 
                        s v1 v2 {m' : nat | m' < m}
                        (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                           df_eval_backprop_deriv σ (x i j) env0 (grad i j))
                        (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                           df_eval_backprop_deriv σ (x i j) env0 (grad i j))
                        (bounded_seq0 m) env1 env2 fenv1 fenv2); trivial.
               ++ intros.
                  specialize (H i i0 (grad i i0) env0 env3).
                  cut_to H.
                  rewrite H5, H6, H7, H8 in H.
                  unfold lift in H.
                  now inversion H.
                  congruence.
                  congruence.
                  specialize (H0 i).
                  rewrite vforall_forall in H0.
                  apply (H0 i0).
               ++ intros.
                  apply (df_eval_backprop_deriv_preserves_lookup_not_none H5); trivial.
               ++ intros.
                  apply (df_eval_backprop_deriv_preserves_lookup_not_none H5); trivial.
            -- intros.
               apply (vartlookup_list_env_iter 
                        s 
                        (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                           df_eval_backprop_deriv σ (x i j) env0 (grad i j))
                        (bounded_seq0 m) env fenv); trivial.
               intros.
               apply (df_eval_backprop_deriv_preserves_lookup_not_none H3); trivial.
            -- intros.
               apply (vartlookup_list_env_iter 
                        s 
                        (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                           df_eval_backprop_deriv σ (x i j) env0 (grad i j))
                        (bounded_seq0 m) env fenv); trivial.
               intros.
               apply (df_eval_backprop_deriv_preserves_lookup_not_none H3); trivial.
          * assert (list_env_iter
                      (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                         list_env_iter
                           (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                              df_eval_backprop_deriv σ (x i j) env0 (grad i j)) 
                           (Some env) (bounded_seq0 m)) (Some grad_env2) (bounded_seq0 n) 
                    <> None).
            apply list_env_iter_total_fun; intros.
            apply list_env_iter_total_fun; intros.
            apply backprop_deriv_fully_closed_not_none; trivial.
            specialize (H0 a).
            rewrite vforall_forall in H0.
            apply (H0 a0).
            tauto.
       + assert (list_env_iter
                      (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                         list_env_iter
                           (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                              df_eval_backprop_deriv σ (x i j) env0 (grad i j)) 
                           (Some env) (bounded_seq0 m)) (Some grad_env1) (bounded_seq0 n) 
                    <> None).
            apply list_env_iter_total_fun; intros.
            apply list_env_iter_total_fun; intros.
            apply backprop_deriv_fully_closed_not_none; trivial.
            specialize (H0 a).
            rewrite vforall_forall in H0.
            apply (H0 a0).
            tauto.               
      - Case "Var"%string.
        match_option; [|tauto].
        case_eq  (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        unfold lift, subvar; simpl.
        destruct (v == (s,DTfloat)).
        + invcs e.
          unfold addvar; simpl.
          rewrite eqq, H0.
          rewrite lookup_update.
          rewrite lookup_update.
          f_equal; lra.
        + assert (v<> (s, DTfloat)) by congruence.
          case_eq (vartlookup grad_env1 v); intros.
          * rewrite lookup_update_neq; trivial.
            rewrite eqq.
            case_eq (vartlookup grad_env2 v); intros.
            -- rewrite lookup_update_neq; trivial.
               rewrite H0; f_equal; lra.
            -- rewrite H0; f_equal; lra.
          * rewrite eqq.
            case_eq (vartlookup grad_env2 v); intros.
            -- rewrite lookup_update_neq; trivial.
               rewrite H0; f_equal; lra.
            -- rewrite H0; f_equal; lra.
      - Case "Plus"%string.
        destruct H.
        unfold lift.
        repeat simpl_closed_backprop.
        simpler2.
        f_equal.
        specialize (IHdf1 grad grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1,eqq3,eqq4 in IHdf1.
        specialize (IHdf2 grad env env1).
        cut_to IHdf2; simpler2.
        unfold lift in IHdf1; inversion IHdf1.
        rewrite eqq2, eqq0 in IHdf2; unfold lift in IHdf2; inversion IHdf2.
        rewrite (split_subvar env env0 val val1); trivial.
        rewrite (split_subvar env1 env2 val0 val2); trivial.
        rewrite H2, H3; lra.
      - Case "Minus"%string.
        destruct H.
        unfold lift.
        repeat simpl_closed_backprop.
        simpler2.
        f_equal.
        specialize (IHdf1 grad grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1,eqq3,eqq4 in IHdf1.
        specialize (IHdf2 (-grad)%R env env1).
        cut_to IHdf2; simpler2.
        unfold lift in IHdf1; invcs IHdf1.
        rewrite eqq0,eqq2 in IHdf2; unfold lift in IHdf2; invcs IHdf2.
        rewrite (split_subvar env env0 val val1); trivial.
        rewrite (split_subvar env1 env2 val0 val2); trivial.
        rewrite H2, H3; lra.
      - Case "Times"%string.
        destruct H.
        match_option; [|tauto].
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        unfold lift.
        repeat simpl_closed_backprop.
        simpler2.
        f_equal.
        specialize (IHdf1 (d1 * grad)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq6,eqq2,eqq4 in IHdf1.
        specialize (IHdf2 (d0 * grad)%R env env1).
        cut_to IHdf2; simpler2.
        unfold lift in IHdf1; invcs IHdf1.
        rewrite eqq5, eqq3 in IHdf2; unfold lift in IHdf2; invcs IHdf2.
        rewrite (split_subvar env env0 d val0); trivial.
        rewrite (split_subvar env1 env2 val val1); trivial.
        rewrite H4, H5; lra.
      - Case "Divide"%string.
        destruct H.
        match_option; [|tauto].
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        unfold lift.
        repeat simpl_closed_backprop.
        simpler2.
        f_equal.
        specialize (IHdf1 (grad/d1)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq6,eqq2,eqq4 in IHdf1.
        specialize (IHdf2 (-d0/(d1*d1) * grad)%R env env1).
        cut_to IHdf2; simpler2.
        unfold lift in IHdf1; inversion IHdf1.
        rewrite eqq5, eqq3 in IHdf2; unfold lift in IHdf2; inversion IHdf2.
        rewrite (split_subvar env env0 d val0); trivial.
        rewrite (split_subvar env1 env2 val val1); trivial.
        rewrite H4, H5; lra.
      - Case "Square"%string.
        match_option; [|tauto].
        assert (df_eval σ df <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        unfold lift.
        repeat simpl_closed_backprop.
        f_equal.
        specialize (IHdf (2 * d0 * grad)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1,eqq2,eqq3 in IHdf.
        now unfold lift in IHdf; inversion IHdf.
      - Case "Exp"%string.
        match_option; [|tauto].
        assert (df_eval σ df <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        unfold lift.
        repeat simpl_closed_backprop.
        f_equal.
        specialize (IHdf (grad * exp d0)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1,eqq2, eqq3 in IHdf.
        now unfold lift in IHdf; inversion IHdf.
      - Case "Log"%string.
        match_option; [|tauto].
        assert (df_eval σ df <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env1 (grad/d0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        unfold lift.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env2 (grad/d0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf (grad / d0)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1 in IHdf.
        now rewrite eqq2, eqq3 in IHdf; unfold lift in IHdf; inversion IHdf.
      - Case "Abs"%string.
        match_option; [|tauto].
        assert (df_eval σ df <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env1 (grad * sign d0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        unfold lift.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env2 (grad * sign d0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf (grad * sign d0)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1 in IHdf.
        now rewrite eqq2, eqq3 in IHdf; unfold lift in IHdf; inversion IHdf.
      - Case "Sign"%string.
        match_option; [|tauto].
        assert (df_eval σ df <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env1 (0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        unfold lift.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env2 (0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf (0)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq0 in IHdf.
        now rewrite eqq1, eqq2 in IHdf; unfold lift in IHdf; inversion IHdf.
      - Case "PSign"%string.
        match_option; [|tauto].
        assert (df_eval σ df <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env1 (0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        unfold lift.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df grad_env2 (0)%R <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf (0)%R grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq0 in IHdf.
        now rewrite eqq1, eqq2 in IHdf; unfold lift in IHdf; inversion IHdf.
      - Case "Max"%string.
        destruct H.
        specialize (IHdf1 grad grad_env1 grad_env2 neq1 neq2 H).
        specialize (IHdf2 grad grad_env1 grad_env2 neq1 neq2 H0).        
        match_option; [|tauto].        
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        rewrite eqq, eqq2 in IHdf1.
        rewrite eqq, eqq2 in IHdf2.        
        destruct (Rle_dec d0 d1); trivial.
      - Case "VectorDot"%string.
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        specialize (IHdf1 (vmap (fun rv : R => (rv * grad)%R) d1) 
                          grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, H3 in IHdf1.
        assert (df_eval_backprop_deriv σ df1 grad_env1
                                       (vmap (fun rv : R => (rv * grad)%R) d1) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2
                                       (vmap (fun rv : R => (rv * grad)%R) d1) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (vartlookup d3 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq1).
        assert (vartlookup d4 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq3 (s, DTfloat) neq2).
        specialize (IHdf2 (vmap (fun lv : R => (lv * grad)%R) d0)
                          d3 d4 H6 H7 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv σ df2 d3
                                       (vmap (fun lv : R => (lv * grad)%R) d0) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d4
                                       (vmap (fun lv : R => (lv * grad)%R) d0) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        unfold lift in IHdf1.
        rewrite eqq2, eqq3 in IHdf1; inversion IHdf1.
        rewrite eqq6, eqq7 in IHdf2; inversion IHdf2.
        rewrite (split_subvar d3 d7 d d5); trivial.
        rewrite (split_subvar d4 d8 d2 d6); trivial.
        now rewrite H11, H12.
      - Case "VectorSum"%string.
        match_option; [|tauto].
        match_option; [|tauto].                
        specialize (IHdf (ConstVector n grad) grad_env1 grad_env2 neq1 neq2 H).
        now rewrite eqq, eqq0 in IHdf.
      - Case "MatrixSum"%string.
        match_option; [|tauto].
        match_option; [|tauto].                
        specialize (IHdf (ConstMatrix m n grad) grad_env1 grad_env2 neq1 neq2 H).        
        now rewrite eqq, eqq0 in IHdf.
      - Case "VectorElem"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (fun k : {n' : nat | n' < n} => if equiv_dec (` k) (` i) 
                                                         then grad else 0%R)
                         grad_env1 grad_env2 neq1 neq2 H).
        now rewrite eqq, eqq0 in IHdf.
      - Case "MatrixElem"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (fun (k1 : {n' : nat | n' < m}) (k2 : {m' : nat | m' < n}) =>
                            if equiv_dec (` k1) (` i) then 
                              if equiv_dec (` k2) (` j) then grad else 0%R else 0%R)
                         grad_env1 grad_env2 neq1 neq2 H).
        now rewrite eqq, eqq0 in IHdf.
      - Case "MatrixVectorMult"%string.
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        specialize (IHdf1 (fun (i : {n' : nat | n' < m}) 
                               (j : {m' : nat | m' < n}) => (grad i * d1 j)%R) 
                          grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, H3 in IHdf1.
        assert (df_eval_backprop_deriv σ df1 grad_env1
                                       (fun (i : {n' : nat | n' < m}) 
                                            (j : {m' : nat | m' < n}) => (grad i * d1 j)%R)
                                       <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2
                                       (fun (i : {n' : nat | n' < m}) 
                                            (j : {m' : nat | m' < n}) => (grad i * d1 j)%R)
                                       <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (vartlookup d3 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq1).
        assert (vartlookup d4 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq3 (s, DTfloat) neq2).
        specialize (IHdf2
                      (matrix_vector_mult
                         (fun (i : {n' : nat | n' < n}) 
                              (j : {m' : nat | m' < m}) => d0 j i) grad)
                          d3 d4 H6 H7 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv 
                  σ df2 d3
                  (matrix_vector_mult (fun (i : {n' : nat | n' < n}) 
                                           (j : {m' : nat | m' < m}) => d0 j i)
                                      grad) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d4
                  (matrix_vector_mult (fun (i : {n' : nat | n' < n}) 
                                           (j : {m' : nat | m' < m}) => d0 j i)
                                      grad) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        unfold lift in IHdf1.
        unfold lift in IHdf2.
        rewrite eqq2, eqq3 in IHdf1; inversion IHdf1.
        rewrite eqq6, eqq7 in IHdf2; inversion IHdf2.
        rewrite (split_subvar d3 d7 d d5); trivial.
        rewrite (split_subvar d4 d8 d2 d6); trivial.
        now rewrite H11, H12.
      - Case "MatrixVectorAdd"%string.
        destruct H.
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        specialize (IHdf1 grad 
                          grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, H1 in IHdf1.
        assert (df_eval_backprop_deriv σ df1 grad_env1 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        case_eq (df_eval_backprop_deriv σ df1 grad_env2 grad); [intros | tauto].
        rewrite eqq0, H4 in IHdf1.
        unfold lift in IHdf1.
        inversion IHdf1.
        assert (list_env_iter
                  (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                     df_eval_backprop_deriv σ df2 env (transpose grad i)) (Some d1)
                  (bounded_seq0 n) <> None).
        apply list_env_iter_total_fun; intros.
        apply backprop_deriv_fully_closed_not_none; trivial.
        match_option; [|tauto].
        assert (list_env_iter
                  (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                     df_eval_backprop_deriv σ df2 env (transpose grad i)) (Some d2)
                  (bounded_seq0 n) <> None).
        apply list_env_iter_total_fun; intros.
        apply backprop_deriv_fully_closed_not_none; trivial.
        match_option; [|tauto].
        unfold lift; f_equal.
        assert (vartlookup d1 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) neq1).
        assert (vartlookup d2 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none H4 (s, DTfloat) neq2).
        assert (vartlookup d3 (s, DTfloat) <> None).
        apply
            (vartlookup_list_env_iter 
                   s 
                   (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                      df_eval_backprop_deriv σ df2 env (transpose grad i))                     
                   (bounded_seq0 n) d1); trivial.
        intros.
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H10 (s, DTfloat) H11).
        assert (vartlookup d4 (s, DTfloat) <> None).
        apply
            (vartlookup_list_env_iter 
                   s 
                   (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                      df_eval_backprop_deriv σ df2 env (transpose grad i))                     
                   (bounded_seq0 n) d2); trivial.
        intros.
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H11 (s, DTfloat) H12).
        unfold subvar in IHdf1; simpl in IHdf1.
        match_option_in IHdf1; [|tauto].
        match_option_in IHdf1; [|tauto].
        rewrite (split_subvar d1 d3 d d5); trivial.
        rewrite (split_subvar d2 d4 d0 d6); trivial.
        rewrite H6.
        apply Rplus_eq_compat_r .
        apply (list_env_iter_subvar_env2 
                 s d5 d6  {m' : nat | m' < n}
                 (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                    df_eval_backprop_deriv σ df2 env (transpose grad i))
                 (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                    df_eval_backprop_deriv σ df2 env (transpose grad i))
                 (bounded_seq0 n) d1 d2 d3 d4); trivial.
        intros.
        specialize (IHdf2 (transpose grad i) env1 env2).
        rewrite H12, H13 in IHdf2.
        cut_to IHdf2; trivial.
        rewrite H14, H15 in IHdf2.
        unfold lift in IHdf2.
        now inversion IHdf2.
        discriminate.
        discriminate.
        intros.
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H12 (s, DTfloat) H13).        
        intros.
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H12 (s, DTfloat) H13).        
      - Case "MatrixMult"%string.
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        specialize (IHdf1
                      (matrix_mult grad (fun (i : {n' : nat | n' < n}) 
                                             (j : {m' : nat | m' < p}) => d1 j i))
                          grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, H3 in IHdf1.
        assert (df_eval_backprop_deriv σ df1 grad_env1
                      (matrix_mult grad (fun (i : {n' : nat | n' < n}) 
                                             (j : {m' : nat | m' < p}) => d1 j i)) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2
              (matrix_mult grad (fun (i : {n' : nat | n' < n}) 
                                             (j : {m' : nat | m' < p}) => d1 j i)) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        rewrite eqq2, eqq3 in IHdf1.
        unfold lift in IHdf1; inversion IHdf1.
        assert (vartlookup d3 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq1).
        assert (vartlookup d4 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq3 (s, DTfloat) neq2).
        specialize (IHdf2
                      (matrix_mult (fun (i : {n' : nat | n' < p}) 
                                        (j : {m' : nat | m' < m}) => d0 j i) grad)
                          d3 d4 H6 H8 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv 
                  σ df2 d3
                  (matrix_mult (fun (i : {n' : nat | n' < p}) 
                                    (j : {m' : nat | m' < m}) => d0 j i) grad) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv 
                  σ df2 d4
                  (matrix_mult (fun (i : {n' : nat | n' < p}) 
                                    (j : {m' : nat | m' < m}) => d0 j i) grad) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        unfold lift in IHdf1.
        unfold lift in IHdf2.
        rewrite eqq6, eqq7 in IHdf2; inversion IHdf2.
        rewrite (split_subvar d3 d7 d d5); trivial.
        rewrite (split_subvar d4 d8 d2 d6); trivial.
        now rewrite H7, H12.
      - Case "VectorPlus"%string.
        destruct H.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv σ df2 d0 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d2 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf1 grad grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1 in IHdf1.
        specialize (IHdf2 grad d0 d2).
        assert (vartlookup d0 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) neq1).
        assert (vartlookup d2 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq2).
        specialize (IHdf2 H5 H6 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].        
        rewrite eqq0, eqq2 in IHdf1; unfold lift in IHdf1; inversion IHdf1.
        rewrite eqq3, eqq4 in IHdf2; unfold lift in IHdf2; inversion IHdf2.
        rewrite (split_subvar d0 d3 d d5); trivial.
        rewrite (split_subvar d2 d4 d1 d6); trivial.
        lra.
      - Case "VectorMinus"%string.
        destruct H.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv 
                  σ df2 d0
                  (fun i : {n' : nat | n' < n} => (- grad i)%R) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d2
                                       (fun i : {n' : nat | n' < n} => (- grad i)%R) <> None)
               by (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf1 grad grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1 in IHdf1.
        specialize (IHdf2 (fun i : {n' : nat | n' < n} => (- grad i)%R) d0 d2).
        assert (vartlookup d0 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) neq1).
        assert (vartlookup d2 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq2).
        specialize (IHdf2 H5 H6 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].        
        rewrite eqq0, eqq2 in IHdf1; unfold lift in IHdf1; inversion IHdf1.
        rewrite eqq3, eqq4 in IHdf2; unfold lift in IHdf2; inversion IHdf2.
        rewrite (split_subvar d0 d3 d d5); trivial.
        rewrite (split_subvar d2 d4 d1 d6); trivial.
        lra.
      - Case "MatrixPlus"%string.
        destruct H.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv σ df2 d0 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d2 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf1 grad grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1 in IHdf1.
        specialize (IHdf2 grad d0 d2).
        assert (vartlookup d0 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) neq1).
        assert (vartlookup d2 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq2).
        specialize (IHdf2 H5 H6 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].        
        rewrite eqq0, eqq2 in IHdf1; unfold lift in IHdf1; inversion IHdf1.
        rewrite eqq3, eqq4 in IHdf2; unfold lift in IHdf2; inversion IHdf2.
        rewrite (split_subvar d0 d3 d d5); trivial.
        rewrite (split_subvar d2 d4 d1 d6); trivial.
        lra.
      - Case "MatrixMinus"%string.
        destruct H.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2 grad <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv 
                  σ df2 d0
                  (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (- grad i j)%R)
                  <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d2
                  (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (- grad i j)%R)
                  <> None) by                                       
                (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        specialize (IHdf1 grad grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, eqq1 in IHdf1.
        specialize (IHdf2
                      (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (- grad i j)%R)
                       d0 d2).
        assert (vartlookup d0 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) neq1).
        assert (vartlookup d2 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq2).
        specialize (IHdf2 H5 H6 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].        
        rewrite eqq0, eqq2 in IHdf1; unfold lift in IHdf1; inversion IHdf1.
        rewrite eqq3, eqq4 in IHdf2; unfold lift in IHdf2; inversion IHdf2.
        rewrite (split_subvar d0 d3 d d5); trivial.
        rewrite (split_subvar d2 d4 d1 d6); trivial.
        lra.
      - Case "VectorScalMult"%string.
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        specialize (IHdf1
                      (vsum (fun j : {n' : nat | n' < n} => (d1 j * grad j)%R))
                          grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, H3 in IHdf1.
        assert (df_eval_backprop_deriv 
                  σ df1 grad_env1
                  (vsum (fun j : {n' : nat | n' < n} => (d1 j * grad j)%R)) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2
                                    (vsum (fun j : {n' : nat | n' < n} => (d1 j * grad j)%R))
                                    <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (vartlookup d3 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq1).
        assert (vartlookup d4 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq3 (s, DTfloat) neq2).
        specialize (IHdf2 (fun j : {n' : nat | n' < n} => (d0 * grad j)%R)
                          d3 d4 H6 H7 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv σ df2 d3
                                       (fun j : {n' : nat | n' < n} => (d0 * grad j)%R)
                                        <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d4
                                       (fun j : {n' : nat | n' < n} => (d0 * grad j)%R)
                                        <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        unfold lift in IHdf1.
        rewrite eqq2, eqq3 in IHdf1; inversion IHdf1.
        rewrite eqq6, eqq7 in IHdf2; inversion IHdf2.
        rewrite (split_subvar d3 d7 d d5); trivial.
        rewrite (split_subvar d4 d8 d2 d6); trivial.
        now rewrite H11, H12.
      - Case "MatrixScalMult"%string.        
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df1 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        specialize (IHdf1
                      (msum
                         (fun (i : {n' : nat | n' < n}) 
                              (j : {m' : nat | m' < m}) => (d1 i j * grad i j)%R))
                          grad_env1 grad_env2 neq1 neq2 H).
        rewrite eqq, H3 in IHdf1.
        assert (df_eval_backprop_deriv 
                  σ df1 grad_env1
                      (msum
                         (fun (i : {n' : nat | n' < n}) 
                              (j : {m' : nat | m' < m}) => (d1 i j * grad i j)%R)) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2
                      (msum
                         (fun (i : {n' : nat | n' < n}) 
                              (j : {m' : nat | m' < m}) => (d1 i j * grad i j)%R)) <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (vartlookup d3 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) neq1).
        assert (vartlookup d4 (s, DTfloat) <> None) by
            apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq3 (s, DTfloat) neq2).
        specialize (IHdf2 (fun (i : {n' : nat | n' < n}) 
                               (j : {m' : nat | m' < m}) => (grad i j * d0)%R)
                          d3 d4 H6 H7 H0).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].
        unfold lift.
        assert (df_eval_backprop_deriv σ df2 d3
                                       (fun (i : {n' : nat | n' < n}) 
                                            (j : {m' : nat | m' < m}) => (grad i j * d0)%R) 
                                       <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d4
                                       (fun (i : {n' : nat | n' < n}) 
                                            (j : {m' : nat | m' < m}) => (grad i j * d0)%R) 
                                       <> None) by
            (apply backprop_deriv_fully_closed_not_none; trivial).
        match_option; [|tauto].
        f_equal.
        unfold lift in IHdf1.
        rewrite eqq2, eqq3 in IHdf1; inversion IHdf1.
        rewrite eqq6, eqq7 in IHdf2; inversion IHdf2.
        rewrite (split_subvar d3 d7 d d5); trivial.
        rewrite (split_subvar d4 d8 d2 d6); trivial.
        now rewrite H11, H12.
      - Case "VectorApply"%string.
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        match_option.
        specialize (IHdf1 v0 grad_env1 grad_env2 neq1 neq2 H0).
        now rewrite eqq, H2 in IHdf1.
      - Case "MatrixApply"%string.
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        match_option.
        specialize (IHdf1 m0 grad_env1 grad_env2 neq1 neq2 H0).
        now rewrite eqq, H2 in IHdf1.
      - Case "VLossfun"%string.
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        match_option.
        specialize (IHdf1 v grad_env1 grad_env2 neq1 neq2 H0).
        now rewrite eqq, H2 in IHdf1.
      - Case "MLossfun"%string.        
        destruct H.
        match_option; [|tauto].        
        assert (df_eval σ df2 <> None) by 
            (apply eval_fully_closed_not_none;trivial).
        match_option; [|tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros|tauto].
        match_option.
        specialize (IHdf1 m0 grad_env1 grad_env2 neq1 neq2 H0).
        now rewrite eqq, H2 in IHdf1.
      Qed.

    Lemma backprop_exchange_order {T} (σ:df_env) (df1 df2 :DefinedFunction UnitAnn T) (s: SubVar) 
          (env:df_env) (grad1 grad2 : definition_function_types_interp T) : 
     let v := (s, DTfloat) in
     vartlookup env v <> None ->
     let vl := map (fun ve => projT1 ve) σ in
     fully_closed_over df1 vl ->
     fully_closed_over df2 vl ->     
     match 
       df_eval_backprop_deriv σ df1 env grad1, df_eval_backprop_deriv σ df2 env grad2, vartlookup env v with
     | Some env1, Some env2, Some oval =>
       lift (fun e => subvar v e oval)
            (df_eval_backprop_deriv σ df1 env2 grad1) =
       lift (fun e => subvar v e oval)
            (df_eval_backprop_deriv σ df2 env1 grad2)
     | _, _, _ => True
     end.               
    Proof.
      intros.
      do 3 match_option.
      unfold lift.
      do 2 match_option.
      - assert (vartlookup d0 v <> None); simpler2.
        assert (vartlookup d v <> None); simpler2.
        case_eq (vartlookup d0 v); [intros|tauto].
        case_eq (vartlookup d v); [intros|tauto].      
        f_equal. subst v.
        rewrite (split_subvar d0 d2 d1 d4); trivial.
        rewrite (split_subvar d d3 d1 d5); trivial.      
        generalize (backprop_indep_env σ df1 s env d0 grad1); intros.
        generalize (backprop_indep_env σ df2 s env d grad2); intros.      
        simpl in H6; simpl in H7.
        cut_to H6; trivial; try congruence.
        cut_to H7; trivial; try congruence.
        unfold df_eval_backprop_delta in *.
        rewrite eqq1, H4 in H6.
        rewrite eqq1, H5 in H7.
        unfold lift in H6; simpl in H6.
        unfold lift in H7; simpl in H7.
        rewrite eqq,  eqq2 in H6.
        rewrite eqq0, eqq3 in H7.
        inversion H6; inversion H7.
        rewrite H9, H10; lra.
      - assert (df_eval_backprop_deriv σ df2 d grad2 <> None).
        apply backprop_deriv_fully_closed_not_none; trivial.
        tauto.
      - assert (df_eval_backprop_deriv σ df1 d0 grad1 <> None).
        apply backprop_deriv_fully_closed_not_none; trivial.
        tauto.
    Qed.
      
     Lemma list_env_iter_id {A} (env : df_env) (l : list A) :
       list_env_iter (fun (_ : A) (env : df_env) => Some env) 
                     (Some env) l = Some env.
     Proof.
       now induction l.
     Qed.

    Lemma backprop_grad_sum_list_env_iter {m} (σ:df_env) 
          (vecdf:Vector (DefinedFunction UnitAnn DTfloat) m) (s: SubVar) 
          (grad_env1 grad_env2 grad_env3:df_env) 
          (grad1 grad2 : (Vector float m))
          (val1 val2 val3 : float)
          (l : list {m' | m' < m} )
      :
     let v := (s, DTfloat) in
     (forall (i:{m' | m' < m}), 
         let vl := map (fun ve => projT1 ve) σ in
         fully_closed_over (vecdf i) vl) ->
     (forall (i:{m' | m' < m}) (env1 env2 env3 : df_env),
         vartlookup env1 v <> None ->
         vartlookup env2 v <> None ->
         vartlookup env3 v <> None ->     
         
         df_eval_backprop_delta σ (vecdf i) v env3 
                                (grad1 i + grad2 i)%R =
         lift2 dfti_gen_plus
               (df_eval_backprop_delta σ (vecdf i) v env1 (grad1 i))
               (df_eval_backprop_delta σ (vecdf i) v env2 (grad2 i))) ->
     
     vartlookup grad_env1 v = Some val1 ->
     vartlookup grad_env2 v = Some val2 ->
     vartlookup grad_env3 v = Some val3 ->     

     lift (fun e : df_env => subvar v e val3)
          (list_env_iter
             (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                df_eval_backprop_deriv σ (vecdf j) env (grad1 j + grad2 j)%R) 
             (Some grad_env3) l) = 
     lift2 dfti_gen_plus
           (lift (fun e : df_env => subvar v e val1)
                 (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (vecdf j) env (grad1 j)) (Some grad_env1) l))
           (lift (fun e : df_env => subvar v e val2)
                 (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (vecdf j) env (grad2 j)) (Some grad_env2) l)).
    Proof.
      intros.
      revert val1 val2 val3 grad_env1 grad_env2 grad_env3 H1 H2 H3.
      induction l.
      - intros.
        simpl; f_equal.
        unfold subvar; simpl.
        rewrite H1,H2,H3.
        lra.
      - intros.
        simpl.
        unfold df_eval_backprop_delta in H0.
        unfold lift, lift2.
        assert (df_eval_backprop_deriv σ (vecdf a) grad_env3 (grad1 a + grad2 a)%R <> None).
        apply backprop_deriv_fully_closed_not_none.  
        apply H.
        case_eq (df_eval_backprop_deriv σ (vecdf a) grad_env3 (grad1 a + grad2 a)%R)
        ; [intros | tauto].
        assert (df_eval_backprop_deriv σ (vecdf a) grad_env1 (grad1 a)%R <> None).
        apply backprop_deriv_fully_closed_not_none.  
        apply H.
        case_eq (df_eval_backprop_deriv σ (vecdf a) grad_env1 (grad1 a)%R)
        ; [intros | tauto].
        assert (df_eval_backprop_deriv σ (vecdf a) grad_env2 (grad2 a)%R <> None).
        apply backprop_deriv_fully_closed_not_none.  
        apply H.
        case_eq (df_eval_backprop_deriv σ (vecdf a) grad_env2 (grad2 a)%R)
        ; [intros | tauto].
        
        assert (vartlookup d v <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 v); congruence.
        assert (vartlookup d0 v <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H7 v); congruence.
        assert (vartlookup d1 v <> None).                    
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H9 v); congruence.

        case_eq (vartlookup d v); [intros v3 eq3  |tauto].
        case_eq (vartlookup d0 v); [intros v1 eq1 |tauto].
        case_eq (vartlookup d1 v); [intros v2 eq2 |tauto].          

        specialize (IHl v1 v2 v3 d0 d1 d eq1 eq2 eq3).
        unfold lift, lift2.
        match_option.
        case_eq (list_env_iter
                   (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                      df_eval_backprop_deriv σ (vecdf j) env (grad1 j)) (Some d0) l).
        case_eq (list_env_iter
                   (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                      df_eval_backprop_deriv σ (vecdf j) env (grad2 j)) (Some d1) l).
        + intros.
          rewrite eqq, H13, H14 in IHl.
          unfold lift, lift2 in IHl; simpl in IHl.
          f_equal.
          subst v.
          rewrite (split_subvar d d2 val3 v3); trivial.
          rewrite (split_subvar d0 d4 val1 v1); trivial.
          rewrite (split_subvar d1 d3 val2 v2); trivial.          
          inversion IHl.
          rewrite H16.
          specialize (H0 a grad_env1 grad_env2 grad_env3).
          cut_to H0; try congruence.
          rewrite H1,H2,H3 in H0.
          rewrite H5,H7,H9 in H0.
          unfold lift, lift2 in H0.
          inversion H0.
          rewrite H17; lra.
        + intros.
          assert (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (vecdf j) env (grad2 j)) (Some d1) l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply H.
          tauto.
        + intros.
          assert (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (vecdf j) env (grad1 j)) (Some d0) l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply H.
          tauto.
        + assert (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (vecdf j) env (grad1 j + grad2 j)%R) (Some d) l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply H.
          tauto.
    Qed.
          
    Lemma backprop_mat_grad_sum_list_env_iter {m n} (σ:df_env) 
          (df :  DefinedFunction UnitAnn (DTVector n)) (s: SubVar) 
          (grad_env1 grad_env2 grad_env3:df_env) 
          (grad1 grad2 : (Matrix float m n))
          (val1 val2 val3 : float)
          (l : list {m' | m' < m} )
      :
     let v := (s, DTfloat) in
     let vl := map (fun ve => projT1 ve) σ in
     fully_closed_over df vl ->
     (forall (i:{m' | m' < m}) (env1 env2 env3 : df_env),
         vartlookup env1 v <> None ->
         vartlookup env2 v <> None ->
         vartlookup env3 v <> None ->     

         df_eval_backprop_delta σ df v env3 (fun j => (grad1 i j +  grad2 i j)%R) =
         lift2 dfti_gen_plus
               (df_eval_backprop_delta σ df v env1 (grad1 i))
               (df_eval_backprop_delta σ df v env2 (grad2 i))) ->
     
     vartlookup grad_env1 v = Some val1 ->
     vartlookup grad_env2 v = Some val2 ->
     vartlookup grad_env3 v = Some val3 ->     

     lift (fun e : df_env => subvar v e val3)
          (list_env_iter
             (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                df_eval_backprop_deriv σ df env (fun k => (grad1 j k + grad2 j k)%R) )
             (Some grad_env3) l) = 
     lift2 dfti_gen_plus
           (lift (fun e : df_env => subvar v e val1)
                 (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ df env (grad1 j)) (Some grad_env1) l))
           (lift (fun e : df_env => subvar v e val2)
                 (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ df env (grad2 j)) (Some grad_env2) l)).
    Proof.
      intros.
      revert val1 val2 val3 grad_env1 grad_env2 grad_env3 H1 H2 H3.
      induction l.
      - intros.
        simpl; f_equal.
        unfold subvar; simpl.
        rewrite H1,H2,H3.
        lra.
      - intros.
        unfold df_eval_backprop_delta in *.
        simpl.
        unfold lift, lift2.
        assert (df_eval_backprop_deriv σ df grad_env3
         (fun k : {n' : nat | n' < n} => (grad1 a k + grad2 a k)%R) <> None).
        apply backprop_deriv_fully_closed_not_none.  
        apply H.
        case_eq (df_eval_backprop_deriv σ df grad_env3
         (fun k : {n' : nat | n' < n} => (grad1 a k + grad2 a k)%R))
        ; [intros | tauto].
        assert (df_eval_backprop_deriv σ df grad_env1 (grad1 a)%R <> None).
        apply backprop_deriv_fully_closed_not_none.  
        apply H.
        case_eq (df_eval_backprop_deriv σ df grad_env1 (grad1 a)%R)
        ; [intros | tauto].
        assert (df_eval_backprop_deriv σ df grad_env2 (grad2 a)%R <> None).
        apply backprop_deriv_fully_closed_not_none.  
        apply H.
        case_eq (df_eval_backprop_deriv σ df grad_env2 (grad2 a)%R)
        ; [intros | tauto].
        
        assert (vartlookup d v <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H5 v); congruence.
        assert (vartlookup d0 v <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H7 v); congruence.
        assert (vartlookup d1 v <> None).                    
        apply (df_eval_backprop_deriv_preserves_lookup_not_none H9 v); congruence.

        case_eq (vartlookup d v); [intros v3 eq3  |tauto].
        case_eq (vartlookup d0 v); [intros v1 eq1 |tauto].
        case_eq (vartlookup d1 v); [intros v2 eq2 |tauto].          

        specialize (IHl v1 v2 v3 d0 d1 d eq1 eq2 eq3).
        match_option.
        case_eq (list_env_iter
                   (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                      df_eval_backprop_deriv σ df env (grad1 j)) (Some d0) l).
        case_eq (list_env_iter
                   (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                      df_eval_backprop_deriv σ df env (grad2 j)) (Some d1) l).
        + intros.
          rewrite eqq, H13, H14 in IHl.
          unfold lift, lift2 in IHl; simpl in IHl.
          f_equal.
          subst v.
          rewrite (split_subvar d d2 val3 v3); trivial.
          rewrite (split_subvar d0 d4 val1 v1); trivial.
          rewrite (split_subvar d1 d3 val2 v2); trivial.          
          inversion IHl.
          rewrite H16.
          specialize (H0 a grad_env1 grad_env2 grad_env3).
          cut_to H0; try congruence.
          rewrite H1,H2,H3 in H0.
          rewrite H5,H7,H9 in H0.
          unfold lift, lift2 in H0.
          inversion H0.
          rewrite H17; lra.
        + intros.
          assert (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ df env (grad2 j)) (Some d1) l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply H.
          tauto.
        + intros.
          assert (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ df env (grad1 j)) (Some d0) l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply H.
          tauto.
        + assert (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ df env
                                 (fun k : {n' : nat | n' < n} => (grad1 j k + grad2 j k)%R))
                                 (Some d) l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply H.
          tauto.
    Qed.

    Lemma matrix_zip_m_n {T} {m n} {i j} {m1 m2 : Matrix T m n} :
      matrix_zip m1 m2 i j = (m1 i j, m2 i j).
    Proof. 
      unfold matrix_zip.
      rewrite vmap_nth; simpl.
      now unfold vector_zip.
    Qed.

    Lemma backprop_grad_sum {T} (σ:df_env) (df:DefinedFunction UnitAnn T) (s: SubVar) 
          (grad_env1 grad_env2 grad_env3:df_env) 
          (grad1 grad2 : definition_function_types_interp T) :
     let v := (s, DTfloat) in
     vartlookup grad_env1 v <> None ->
     vartlookup grad_env2 v <> None ->
     vartlookup grad_env3 v <> None ->     
     let vl := map (fun ve => projT1 ve) σ in
     fully_closed_over df vl ->
     df_eval_backprop_delta σ df (s,DTfloat) grad_env3 (dfti_gen_plus grad1 grad2) =
     lift2 dfti_gen_plus
       (df_eval_backprop_delta σ df (s,DTfloat) grad_env1 grad1)
       (df_eval_backprop_delta σ df (s,DTfloat) grad_env2 grad2).
    Proof.
      unfold df_eval_backprop_delta.
      revert grad_env1 grad_env2 grad_env3.
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_unit) Case
(*
      DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case
*)
      ; simpl; intros.
      - Case "Number"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].        
        unfold subvar; simpl.
        rewrite eqq, eqq0, eqq1.
        f_equal; lra.
      - Case "Constant"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].        
        unfold subvar; simpl.
        rewrite eqq, eqq0, eqq1.
        f_equal; lra.
      - Case "DVector"%string.
        unfold two_vector_env_iter_alt in *.
        rewrite vforall_forall in H3.
        revert grad_env1 grad_env2 grad_env3 H0 H1 H2.
        induction (bounded_seq0 n).
        + intros.
          simpl.
          match_option; [|tauto].
          match_option; [|tauto].
          match_option; [|tauto].        
          unfold subvar; simpl.
          rewrite eqq, eqq0, eqq1.
          f_equal; lra.
        + intros.
          match_option; [|tauto].
          match_option; [|tauto].
          match_option; [|tauto].        
          unfold lift; simpl in *.
          assert (df_eval_backprop_deriv σ (x a) grad_env3 (grad1 a + grad2 a)%R <> None).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3.
          assert (df_eval_backprop_deriv σ (x a) grad_env1 (grad1 a)%R <> None).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3.
          assert (df_eval_backprop_deriv σ (x a) grad_env2 (grad2 a)%R <> None).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3.
          case_eq (df_eval_backprop_deriv σ (x a) grad_env3 (grad1 a + grad2 a)%R)
          ; [intros|tauto].
          case_eq (df_eval_backprop_deriv σ (x a) grad_env1 (grad1 a)%R)
          ; [intros|tauto].
          case_eq (df_eval_backprop_deriv σ (x a) grad_env2 (grad2 a)%R)
          ; [intros|tauto].
          assert (list_env_iter
                    (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                       df_eval_backprop_deriv σ (x i) env (grad1 i + grad2 i)%R)
                    (Some d2) l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply (H3 a0).
          match_option; [|tauto].
          assert (list_env_iter
                    (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                       df_eval_backprop_deriv σ (x i) env (grad1 i)) (Some d3) 
                    l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply (H3 a0).
          match_option; [|tauto].
          assert (list_env_iter
                    (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                       df_eval_backprop_deriv σ (x i) env (grad2 i)) (Some d4) 
                    l <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          apply (H3 a0).
          match_option; [|tauto].        
          unfold lift2; simpl.

          assert (vartlookup d2 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H7 (s, DTfloat) H2).
          assert (vartlookup d3 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H8 (s, DTfloat) H0).
          assert (vartlookup d4 (s, DTfloat) <> None).                    
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H9 (s, DTfloat) H1).

          case_eq (vartlookup d2 (s, DTfloat)); [intros|tauto].
          case_eq (vartlookup d3 (s, DTfloat)); [intros|tauto].
          case_eq (vartlookup d4 (s, DTfloat)); [intros|tauto].          

          rewrite (split_subvar d2 d5 d d8); trivial.
          rewrite (split_subvar d3 d6 d0 d9); trivial.
          rewrite (split_subvar d4 d7 d1 d10); trivial.

          f_equal.

          specialize (IHl d3 d4 d2 H14 H15 H13).
          rewrite H16, H17, H18 in IHl.
          rewrite eqq2, eqq3, eqq4 in IHl.
          unfold lift, lift2 in IHl.
          inversion IHl.
          rewrite H20.

          specialize (H a (grad1 a) (grad2 a) grad_env1 grad_env2 grad_env3 H0 H1 H2).
          specialize (H (H3 a)).

          rewrite eqq,eqq0,eqq1 in H.
          rewrite H7, H8, H9 in H.
          unfold lift, lift2 in H.
          inversion H.
          rewrite H21.
          lra.
      - Case "DMatrix"%string.
        unfold two_matrix_env_iter_alt in *.
        rewrite vforall_forall in H3.
        revert grad_env1 grad_env2 grad_env3 H0 H1 H2.
        induction (bounded_seq0 n); induction (bounded_seq0 m).
        + intros.
          simpl.
          match_option; [|tauto].
          match_option; [|tauto].
          match_option; [|tauto].        
          unfold subvar; simpl.
          rewrite eqq, eqq0, eqq1.
          f_equal; lra.
        + intros.
          match_option; [|tauto].
          match_option; [|tauto].
          match_option; [|tauto].  
          simpl.
          unfold lift, lift2; simpl; f_equal.
          unfold subvar; simpl.
          rewrite eqq, eqq0, eqq1; simpl; lra.
        + intros.
          match_option; [|tauto].
          match_option; [|tauto].
          match_option; [|tauto].
          rewrite list_env_iter_id.
          rewrite list_env_iter_id.
          rewrite list_env_iter_id.            
          unfold subvar; simpl.
          rewrite eqq, eqq0, eqq1; simpl; f_equal; lra.
        + intros.
          match_option; [|tauto].
          match_option; [|tauto].
          match_option; [|tauto].
          simpl.
          assert (df_eval_backprop_deriv σ (x a a0) grad_env3 (grad1 a a0 + grad2 a a0)%R <> None).
          apply backprop_deriv_fully_closed_not_none.          
          specialize (H3 a); rewrite vforall_forall in H3; apply H3.
          assert (df_eval_backprop_deriv σ (x a a0) grad_env1 (grad1 a a0)%R <> None).
          apply backprop_deriv_fully_closed_not_none.          
          specialize (H3 a); rewrite vforall_forall in H3; apply H3.
          assert (df_eval_backprop_deriv σ (x a a0) grad_env2 (grad2 a a0)%R <> None).
          apply backprop_deriv_fully_closed_not_none.          
          specialize (H3 a); rewrite vforall_forall in H3; apply H3.
          case_eq (df_eval_backprop_deriv σ (x a a0) grad_env3 (grad1 a a0 + grad2 a a0)%R)
          ; [intros|tauto].
          case_eq (df_eval_backprop_deriv σ (x a a0) grad_env1 (grad1 a a0)%R)
          ; [intros|tauto].
          case_eq (df_eval_backprop_deriv σ (x a a0) grad_env2 (grad2 a a0)%R)
          ; [intros|tauto].
          assert (list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (x a j) env (grad1 a j + grad2 a j)%R)
                    (Some d2) l0 <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          specialize (H3 a); rewrite vforall_forall in H3; apply H3.            
          case_eq (list_env_iter
                     (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                        df_eval_backprop_deriv σ (x a j) env (grad1 a j + grad2 a j)%R) 
                     (Some d2) l0 ); [intros | tauto].
          assert (list_env_iter
                    (fun (i : {n' : nat | n' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (x a i) env (grad1 a i)) (Some d3) 
                    l0 <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          specialize (H3 a); rewrite vforall_forall in H3; apply H3.            
          case_eq (list_env_iter
                     (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                        df_eval_backprop_deriv σ (x a j) env (grad1 a j)%R) 
                     (Some d3) l0 ); [intros | tauto].
          assert (list_env_iter
                    (fun (i : {n' : nat | n' < m}) (env : df_env) =>
                       df_eval_backprop_deriv σ (x a i) env (grad2 a i)) (Some d4) 
                    l0 <> None).
          apply list_env_iter_total_fun; intros.
          apply backprop_deriv_fully_closed_not_none.
          specialize (H3 a); rewrite vforall_forall in H3; apply H3.            
          case_eq (list_env_iter
                     (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                        df_eval_backprop_deriv σ (x a j) env (grad2 a j)%R) 
                     (Some d4) l0 ); [intros | tauto].
          assert  
            (list_env_iter
               (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                  list_env_iter
                    (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                       df_eval_backprop_deriv σ (x i j) env0 (grad1 i j + grad2 i j)%R)
                    (df_eval_backprop_deriv σ (x i a0) env (grad1 i a0 + grad2 i a0)%R) l0) 
               (Some d5) l <> None).
          apply list_env_iter_total_fun; intros.
          assert (df_eval_backprop_deriv σ (x a1 a0) env0 (grad1 a1 a0 + grad2 a1 a0)%R <> None).
          apply backprop_deriv_fully_closed_not_none.
          specialize (H3 a1); rewrite vforall_forall in H3; apply H3.            
          case_eq (df_eval_backprop_deriv σ (x a1 a0) env0 (grad1 a1 a0 + grad2 a1 a0)%R); [intros|tauto].
          apply list_env_iter_total_fun; intros.            
          apply backprop_deriv_fully_closed_not_none.            
          specialize (H3 a1); rewrite vforall_forall in H3; apply H3.            
          unfold lift; simpl.
          match_option; [|tauto].

          assert  
              (list_env_iter
                 (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                    list_env_iter
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (x i j) env0 (grad1 i j)%R)
                      (df_eval_backprop_deriv σ (x i a0) env (grad1 i a0)%R) l0) 
                 (Some d6) l <> None).
          apply list_env_iter_total_fun; intros.
          assert (df_eval_backprop_deriv σ (x a1 a0) env0 (grad1 a1 a0)%R <> None).
          apply backprop_deriv_fully_closed_not_none.
          specialize (H3 a1); rewrite vforall_forall in H3; apply H3.            
          case_eq (df_eval_backprop_deriv σ (x a1 a0) env0 (grad1 a1 a0)%R); [intros|tauto].
          apply list_env_iter_total_fun; intros.            
          apply backprop_deriv_fully_closed_not_none.            
          specialize (H3 a1); rewrite vforall_forall in H3; apply H3.            
          match_option; [|tauto].

          assert  
              (list_env_iter
                 (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                    list_env_iter
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (x i j) env0 (grad2 i j)%R)
                      (df_eval_backprop_deriv σ (x i a0) env (grad2 i a0)%R) l0) 
                 (Some d7) l <> None).
          apply list_env_iter_total_fun; intros.
          assert (df_eval_backprop_deriv σ (x a1 a0) env0 (grad2 a1 a0)%R <> None).
          apply backprop_deriv_fully_closed_not_none.
          specialize (H3 a1); rewrite vforall_forall in H3; apply H3.            
          case_eq (df_eval_backprop_deriv σ (x a1 a0) env0 (grad2 a1 a0)%R); [intros|tauto].
          apply list_env_iter_total_fun; intros.            
          apply backprop_deriv_fully_closed_not_none.            
          specialize (H3 a1); rewrite vforall_forall in H3; apply H3.            
          match_option; [|tauto].
            
          unfold lift2; simpl; f_equal.
            
          assert (vartlookup d2 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H7 (s, DTfloat) H2).
          assert (vartlookup d3 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H8 (s, DTfloat) H0).
          assert (vartlookup d4 (s, DTfloat) <> None).                    
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H9 (s, DTfloat) H1).

          case_eq (vartlookup d2 (s, DTfloat)); [intros|tauto].
          case_eq (vartlookup d3 (s, DTfloat)); [intros|tauto].
          case_eq (vartlookup d4 (s, DTfloat)); [intros|tauto].

          assert (Hc := H).
          assert (H3c := H3).
            
          specialize (H a a0 (grad1 a a0) (grad2 a a0) grad_env1 grad_env2 grad_env3 
                        H0 H1 H2).
          
          specialize (H3 a).
          rewrite vforall_forall in H3.
          specialize (H (H3 a0)).
          rewrite eqq, eqq0, eqq1 in H; simpl in H.
          rewrite H7, H8, H9 in H; unfold lift, lift2 in H; simpl in H.
          
          assert (vartlookup d5 (s, DTfloat) <> None).
          apply (vartlookup_list_env_iter 
                     s (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                          df_eval_backprop_deriv σ (x a j) env (grad1 a j + grad2 a j)%R) 
                     l0 d2 d5); trivial; intros.
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H25 (s, DTfloat) H26).
          case_eq (vartlookup d5 (s, DTfloat)); [intros|tauto].
          assert (vartlookup d6 (s, DTfloat) <> None).
          apply (vartlookup_list_env_iter 
                     s (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                          df_eval_backprop_deriv σ (x a j) env (grad1 a j)%R) 
                     l0 d3 d6); trivial; intros.
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H27 (s, DTfloat) H28).
          case_eq (vartlookup d6 (s, DTfloat)); [intros|tauto].            
          assert (vartlookup d7 (s, DTfloat) <> None).                    
          apply (vartlookup_list_env_iter 
                     s (fun (j : {m' : nat | m' < m}) (env : df_env) =>
                          df_eval_backprop_deriv σ (x a j) env (grad2 a j)%R) 
                     l0 d4 d7); trivial; intros.
          apply (df_eval_backprop_deriv_preserves_lookup_not_none H29 (s, DTfloat) H30).
          case_eq (vartlookup d7 (s, DTfloat)); [intros|tauto].            
          
          specialize (IHl d6 d7 d5 H27 H29 H25).
          rewrite H28, H30, H26 in IHl; simpl in IHl.
          
          rewrite eqq2,eqq3,eqq4 in IHl.
          unfold lift, lift2 in IHl; simpl in IHl.

          rewrite (split_subvar d5 d8 d d14); trivial.
          rewrite (split_subvar d6 d9 d0 d15); trivial.
          rewrite (split_subvar d7 d10 d1 d16); trivial.

          rewrite (split_subvar d2 d5 d d11); trivial.
          rewrite (split_subvar d3 d6 d0 d12); trivial.
          rewrite (split_subvar d4 d7 d1 d13); trivial.

          inversion H.
          inversion IHl.
          rewrite H32, H33.

          generalize (backprop_grad_sum_list_env_iter 
                        σ (x a) s d3 d4 d2 (grad1 a) (grad2 a)
                        d12 d13 d11 l0); intros.
          specialize (H31 H3).
          cut_to H31.
          * rewrite H11,H13,H15 in H31.
            unfold lift, lift2 in H31.
            inversion H31.
            rewrite H35; lra.
          * intros.
            unfold df_eval_backprop_delta.
            specialize (Hc a i (grad1 a i) (grad2 a i) env1 env2 env3).
            specialize (Hc H34 H35 H36).
            specialize (Hc (H3 i)).
            apply Hc.
          * trivial.
          * trivial.  
          * trivial.
      - Case "Var"%string.
        match_option; [|tauto].
        case_eq (vartlookup grad_env1 (s, DTfloat)); [intros| tauto].
        case_eq (vartlookup grad_env2 (s, DTfloat)); [intros| tauto].
        destruct (v == (s,DTfloat)).
        + invcs e.
          rewrite eqq, H3, H4; simpl.
          f_equal.
          rewrite subvar_addvar_scalar_eq; trivial.
          rewrite subvar_addvar_scalar_eq; trivial.
          rewrite subvar_addvar_scalar_eq; trivial.
        + assert (v<> (s, DTfloat)) by congruence.
          match_option.
          * match_option.
            -- match_option; unfold lift, lift2; simpl; f_equal.
               ++ rewrite subvar_addvar_scalar_neq; trivial.
                  rewrite subvar_addvar_scalar_neq; trivial.
                  rewrite subvar_addvar_scalar_neq; trivial.
                  lra.
               ++ rewrite subvar_addvar_scalar_neq; trivial.
                  rewrite subvar_addvar_scalar_neq; trivial.
                  unfold subvar; simpl; rewrite H4; lra.
            -- unfold lift, lift2; simpl; f_equal.
               rewrite subvar_addvar_scalar_neq; trivial.               
               case_eq (vartlookup grad_env2 v); intros.
               ++ rewrite subvar_addvar_scalar_neq; trivial.               
                  f_equal; unfold subvar; simpl.
                  rewrite H3; lra.
               ++ unfold subvar; simpl.
                  rewrite H3, H4.
                  f_equal; lra.
          * match_option.
            -- match_option; unfold lift, lift2; simpl; f_equal.
               ++ rewrite subvar_addvar_scalar_neq; trivial.
                  rewrite subvar_addvar_scalar_neq; trivial.               
                  unfold subvar; simpl.
                  rewrite eqq; lra.
               ++ rewrite subvar_addvar_scalar_neq; trivial.               
                  unfold subvar; simpl.
                  rewrite eqq, H4; lra.
            -- match_option; unfold lift, lift2; simpl; f_equal.
               ++ rewrite subvar_addvar_scalar_neq; trivial.               
                  unfold subvar; simpl.
                  rewrite eqq, H3; lra.
               ++ unfold subvar; simpl.
                  rewrite eqq, H3, H4; lra.
      - Case "Plus"%string.
        destruct H2.
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        simpler2.
        specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 grad1 grad2 env1 env3 env).
        simpl in IHdf1.
        rewrite eqq5, eqq6, eqq7 in IHdf1.
        rewrite eqq, eqq1, eqq3 in IHdf1.
        unfold lift, lift2 in IHdf1; simpl in IHdf1.
        inversion IHdf1.
        cut_to IHdf2; simpler2.
        simpl in IHdf2.
        rewrite eqq0, eqq2, eqq4 in IHdf2.
        unfold lift, lift2 in IHdf2.
        inversion IHdf2.
        f_equal.
        rewrite (split_subvar env env0 val val2); trivial.
        rewrite (split_subvar env1 env2 val0 val3); trivial.
        rewrite (split_subvar env3 env4 val1 val4); trivial.
        rewrite H5, H6; lra.
      - Case "Minus"%string.       
        destruct H2.
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        simpler2.
        specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 (-grad1)%R (-grad2)%R env1 env3 env).
        simpl in IHdf1.
        rewrite eqq5, eqq6, eqq7 in IHdf1.
        rewrite eqq, eqq1, eqq3 in IHdf1.
        unfold lift, lift2 in IHdf1; simpl in IHdf1.
        inversion IHdf1.
        cut_to IHdf2; simpler2.
        simpl in IHdf2.
        replace (- grad1 + - grad2)%R with (- (grad1 + grad2))%R in IHdf2 by lra.
        rewrite eqq0, eqq2, eqq4 in IHdf2.
        unfold lift, lift2 in IHdf2; simpl in IHdf2.
        inversion IHdf2.
        rewrite (split_subvar env env0 val val2); trivial.
        rewrite (split_subvar env1 env2 val0 val3); trivial.
        rewrite (split_subvar env3 env4 val1 val4); trivial.
        f_equal; rewrite H5, H6; lra.
      - Case "Times"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        simpler2.
        specialize (IHdf1 (d1 * grad1)%R (d1 * grad2)%R grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 (d0 * grad1)%R (d0 * grad2)%R env1 env3 env).
        rewrite eqq8, eqq9, eqq in IHdf1.
        simpl in IHdf1.
        replace (d1 *grad1 + d1*grad2)%R with (d1 * (grad1 + grad2))%R in IHdf1 by lra.
        rewrite eqq2, eqq4, eqq6 in IHdf1.
        unfold lift, lift2 in IHdf1; inversion IHdf1.
        cut_to IHdf2; simpler2.
        simpl in IHdf2.
        replace (d0 *grad1 + d0 *grad2)%R with (d0 *(grad1 + grad2))%R in IHdf2 by lra.
        rewrite eqq3,eqq5,eqq7 in IHdf2.
        unfold lift, lift2 in IHdf2; inversion IHdf2.
        f_equal.
        rewrite (split_subvar env env0 d val1); trivial.
        rewrite (split_subvar env1 env2 val val2); trivial.
        rewrite (split_subvar env3 env4 val0 val3); trivial.
        rewrite H7, H8; lra.
      - Case "Divide"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        simpler2.
        specialize (IHdf1 (grad1/d1)%R (grad2/d1)%R grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 (-d0/(d1*d1) * grad1)%R (-d0/(d1*d1) * grad2)%R env1 env3 env).
        rewrite eqq, eqq8, eqq9 in IHdf1.
        simpl in IHdf1.
        replace (grad1/d1 + grad2/d1)%R with ((grad1 + grad2)/d1)%R in IHdf1 by lra.
        rewrite eqq2, eqq4, eqq6 in IHdf1.
        unfold lift, lift2 in IHdf1; inversion IHdf1.
        cut_to IHdf2; simpler2.
        simpl in IHdf2.
        replace (-d0/(d1*d1) *grad1 + -d0/(d1*d1) *grad2)%R with (-d0/(d1*d1) *(grad1 + grad2))%R in IHdf2 by lra.
        rewrite eqq3, eqq5, eqq7 in IHdf2.
        unfold lift, lift2 in IHdf2; inversion IHdf2.
        f_equal.
        rewrite (split_subvar env env0 d val1); trivial.
        rewrite (split_subvar env1 env2 val val2); trivial.
        rewrite (split_subvar env3 env4 val0 val3); trivial.
        rewrite H7, H8; lra.
      - Case "Square"%string.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df); intros.
        specialize (H3 H2).
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (2 * d0 *grad1)%R (2 * d0 *grad2)%R grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq1, eqq2 in IHdf.
        simpl in IHdf.
        replace (2 * d0 * grad1 + 2 * d0 * grad2)%R with (2 * d0 * (grad1 + grad2))%R in IHdf by lra.
        apply IHdf.
      - Case "Exp"%string.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df); intros.
        specialize (H3 H2).
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (grad1 * exp d0)%R (grad2*exp d0)%R grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq1, eqq2 in IHdf.
        simpl in IHdf.
        replace (grad1 * exp d0 + grad2 * exp d0)%R with ((grad1 + grad2) * exp d0)%R in IHdf by lra.
        apply IHdf.
      - Case "Log"%string.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df); intros.
        specialize (H3 H2).
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (grad1/d0)%R (grad2/d0)%R grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq1, eqq2 in IHdf.
        simpl in IHdf.
        replace (grad1/d0 + grad2/d0)%R with ((grad1 + grad2) / d0)%R in IHdf by lra.
        apply IHdf.
      - Case "Abs"%string.        
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df); intros.
        specialize (H3 H2).
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (grad1*sign d0)%R (grad2*sign d0)%R grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq1, eqq2 in IHdf.
        simpl in IHdf.
        replace (grad1*sign d0 + grad2*sign d0)%R with ((grad1 + grad2) * sign d0)%R in IHdf by lra.
        apply IHdf.
      - Case "Sign"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (0)%R (0)%R grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq0, eqq1 in IHdf.
        simpl in IHdf.
        replace (0 + 0)%R with 0%R in IHdf by lra.
        apply IHdf.
      - Case "PSign"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (0)%R (0)%R grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq0, eqq1 in IHdf.
        simpl in IHdf.
        replace (0 + 0)%R with 0%R in IHdf by lra.
        apply IHdf.
      - Case "Max"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        destruct (Rle_dec d0 d1).
        + match_option; [|tauto].
          match_option; [|tauto].        
          specialize (IHdf2 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H3).
          rewrite eqq, eqq2, eqq3 in IHdf2; simpl in IHdf2.
          apply IHdf2.
        + match_option; [|tauto].
          match_option; [|tauto].         
          specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
          rewrite eqq, eqq2, eqq3 in IHdf1; simpl in IHdf1.
          apply IHdf1.
      - Case "VectorDot"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        simpler2.
        specialize (IHdf1 
                      (vmap (fun rv : R => (rv * grad1)%R) d1)
                      (vmap (fun rv : R => (rv * grad2)%R) d1)                      
                       grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 
                      (vmap (fun lv : R => (lv * grad1)%R) d0)
                      (vmap (fun lv : R => (lv * grad2)%R) d0)                      
                      env1 env3 env).
        rewrite eqq, eqq8, eqq9 in IHdf1.
        simpl in IHdf1.
        replace
           (fun i : {n' : nat | n' < n} =>
                (vmap (fun rv : R => rv * grad1) d1 i + vmap (fun rv : R => rv * grad2) d1 i)%R)
          with
            (vmap (fun rv : R => (rv * (grad1 + grad2))%R) d1)
          in IHdf1.
        + rewrite eqq2, eqq4, eqq6 in IHdf1.
          unfold lift, lift2 in IHdf1; inversion IHdf1.
          simpl in IHdf2.
          cut_to IHdf2; simpler2.
          replace (fun i : {n' : nat | n' < n} =>
                   (vmap (fun lv : R => lv * grad1) d0 i + 
                    vmap (fun lv : R => lv * grad2) d0 i)%R) with
            (vmap (fun lv : R => (lv * (grad1 + grad2))%R) d0) in IHdf2.
          * rewrite eqq3, eqq5, eqq7 in IHdf2.
            unfold lift, lift2 in IHdf2; inversion IHdf2.
            f_equal.
            rewrite (split_subvar env env0 d val1); trivial.
            rewrite (split_subvar env1 env2 val val2); trivial.
            rewrite (split_subvar env3 env4 val0 val3); trivial.
            rewrite H7, H8; lra.
          * apply FunctionalExtensionality.functional_extensionality; intros. 
            rewrite vmap_nth.
            rewrite vmap_nth.
            rewrite vmap_nth.
            lra.
        + apply FunctionalExtensionality.functional_extensionality; intros.
          rewrite vmap_nth.
          rewrite vmap_nth.
          rewrite vmap_nth.
          lra.
      - Case "VectorSum"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (ConstVector n grad1) (ConstVector n grad2) grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq0, eqq1 in IHdf.
        simpl in IHdf.
        unfold ConstVector in IHdf.
        unfold ConstVector.
        apply IHdf.
      - Case "MatrixSum"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (ConstMatrix m n grad1) (ConstMatrix m n grad2) grad_env1 grad_env2 grad_env3).
        specialize (IHdf H H0 H1 H2).
        rewrite eqq, eqq0, eqq1 in IHdf.
        simpl in IHdf.
        unfold ConstMatrix in IHdf.
        unfold ConstMatrix.
        apply IHdf.
      - Case "VectorElem"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf (fun k : {n' : nat | n' < n} => 
                            if equiv_dec (` k) (` i) then grad1 else 0%R)
                         (fun k : {n' : nat | n' < n} => 
                            if equiv_dec (` k) (` i) then grad2 else 0%R)
                         grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        rewrite eqq, eqq0, eqq1 in IHdf.
        simpl in IHdf.
        replace (fun k : {n' : nat | n' < n} =>
                   if equiv_dec (` k) (` i) then (grad1 + grad2)%R else 0%R) with
                 (fun i0 : {n' : nat | n' < n} =>
                    ((if equiv_dec (` i0) (` i) then grad1 else 0) +
                     (if equiv_dec (` i0) (` i) then grad2 else 0))%R).
        apply IHdf.
        apply FunctionalExtensionality.functional_extensionality; intros.
        destruct (equiv_dec (` x) (` i)); lra.
      - Case "MatrixElem"%string.
        match_option; [|tauto].
        match_option; [|tauto].
        match_option; [|tauto].
        specialize (IHdf
                      (fun (k1 : {n' : nat | n' < m}) (k2 : {m' : nat | m' < n}) =>
                         if equiv_dec (` k1) (` i)
                         then if equiv_dec (` k2) (` j) then grad1 else 0%R
                         else 0%R)
                      (fun (k1 : {n' : nat | n' < m}) (k2 : {m' : nat | m' < n}) =>
                         if equiv_dec (` k1) (` i)
                         then if equiv_dec (` k2) (` j) then grad2 else 0%R
                         else 0%R)
                      grad_env1 grad_env2 grad_env3 H H0 H1 H2).                      
        rewrite eqq, eqq0, eqq1 in IHdf.
        simpl in IHdf.
        replace (fun (k1 : {n' : nat | n' < m}) (k2 : {m' : nat | m' < n}) =>
                   if equiv_dec (` k1) (` i)
                   then if equiv_dec (` k2) (` j) then (grad1 + grad2)%R else 0%R
                   else 0%R) with  
            (fun (i0 : {n' : nat | n' < m}) (j0 : {m' : nat | m' < n}) =>
               ((if equiv_dec (` i0) (` i)
                 then if equiv_dec (` j0) (` j) then grad1 else 0
                 else 0) +
                (if equiv_dec (` i0) (` i)
                 then if equiv_dec (` j0) (` j) then grad2 else 0
                 else 0))%R).
        apply IHdf.
        apply FunctionalExtensionality.functional_extensionality; intros.        
        destruct (equiv_dec (` x) (` i)).
        + apply FunctionalExtensionality.functional_extensionality; intros.        
          destruct (equiv_dec (` x0) (` j)); lra.
        + apply FunctionalExtensionality.functional_extensionality; intros.        
          lra.
      - Case "MatrixVectorMult"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        simpler2.
        specialize (IHdf1
                  (fun (i : {n' : nat | n' < m}) 
                       (j : {m' : nat | m' < n}) => (grad1 i * d1 j)%R)
                  (fun (i : {n' : nat | n' < m}) 
                       (j : {m' : nat | m' < n}) => (grad2 i * d1 j)%R)
                       grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        rewrite eqq, eqq8, eqq9 in IHdf1.
        specialize (IHdf2
                      (matrix_vector_mult
                         (fun (i : {n' : nat | n' < n}) 
                              (j : {m' : nat | m' < m}) => d0 j i) grad1)
                      (matrix_vector_mult
                         (fun (i : {n' : nat | n' < n}) 
                              (j : {m' : nat | m' < m}) => d0 j i) grad2)
                      env1 env3 env).
        simpl in IHdf1.
        replace
          (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
             (grad1 i * d1 j + grad2 i * d1 j)%R) with
            (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
               ((grad1 i + grad2 i) * d1 j)%R) in IHdf1.
        + rewrite eqq2, eqq4, eqq6 in IHdf1.
          unfold lift, lift2 in IHdf1; inversion IHdf1.
          cut_to IHdf2; simpler2.
          simpl in IHdf2.
          replace
            (fun i : {n' : nat | n' < n} =>
               (matrix_vector_mult
                  (fun (i0 : {n' : nat | (n' < n)%nat}) (j : {m' : nat | (m' < m)%nat}) =>
                     d0 j i0) grad1 i +
                matrix_vector_mult
                  (fun (i0 : {n' : nat | (n' < n)%nat}) (j : {m' : nat | (m' < m)%nat}) =>
                     d0 j i0) grad2 i)%R) with
              (matrix_vector_mult
                 (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => d0 j i)
                 (fun i : {n' : nat | n' < m} => (grad1 i + grad2 i)%R)) in IHdf2.
          * rewrite eqq3, eqq5, eqq7 in IHdf2.
            unfold lift, lift2 in IHdf2; inversion IHdf2.
            f_equal.
            rewrite (split_subvar env env0 d val1); trivial.
            rewrite (split_subvar env1 env2 val val2); trivial.
            rewrite (split_subvar env3 env4 val0 val3); trivial.
            rewrite H7, H8; lra.
          * apply FunctionalExtensionality.functional_extensionality; intros. 
            unfold matrix_vector_mult.
            rewrite vsum_plus; f_equal.
            apply FunctionalExtensionality.functional_extensionality; intros.          
            simpl; lra.
        + apply FunctionalExtensionality.functional_extensionality; intros.
          apply FunctionalExtensionality.functional_extensionality; intros.          
          lra.
      - Case "MatrixVectorAdd"%string.
        destruct H2.
        simpl; intros.
        repeat simpl_closed_backprop.
        simpler2.
        specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        simpl in IHdf1.
        rewrite eqq,eqq0,eqq1,eqq2,eqq3,eqq4 in IHdf1.
        unfold lift, lift2 in IHdf1.
        generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) H); intro.
        case_eq (vartlookup env0 (s, DTfloat)); [intros|tauto].            
        generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat) H0); intro.
        case_eq (vartlookup env1 (s, DTfloat)); [intros|tauto].            
        generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq (s, DTfloat) H1); intro.
        case_eq (vartlookup env (s, DTfloat)); [intros|tauto].
        generalize (backprop_mat_grad_sum_list_env_iter 
                      σ df2 s env0 env1 env (transpose grad1) (transpose grad2)
                      d d0 d1 (bounded_seq0 n)); intros.
        simpl in H10.
        specialize (H10 H3).
        cut_to H10; trivial.
        + do 3 match_option.
          * rewrite eqq6, eqq7 in H10.
            replace  (fun (j : {m' : nat | m' < n}) (env : df_env) =>
                        df_eval_backprop_deriv σ df2 env
                            (fun k : {n' : nat | n' < m} => ((@transpose R m n grad1 j k) + 
                                                             (@transpose R m n grad2 j k))%R))
              with
                (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                   df_eval_backprop_deriv σ df2 env
                                          (transpose
                 (fun (i0 : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                  (grad1 i0 j + grad2 i0 j)%R) i)) in H10.
            -- rewrite eqq5 in H10.
               unfold lift, lift2 in H10.
               unfold lift, lift2; f_equal.
               inversion IHdf1; inversion H10.
               rewrite (split_subvar env d2 val d1); trivial.
               rewrite (split_subvar env0 d3 val0 d); trivial.
               rewrite (split_subvar env1 d4 val1 d0); trivial.
               rewrite H12, H13; lra.
            -- apply FunctionalExtensionality.functional_extensionality; intros.
               apply FunctionalExtensionality.functional_extensionality; intros.          
               f_equal.
          * assert (list_env_iter
                      (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                         df_eval_backprop_deriv σ df2 env (transpose grad2 i)) 
                      (Some env1) (bounded_seq0 n) <> None).
            apply list_env_iter_total_fun; intros.          
            apply backprop_deriv_fully_closed_not_none; trivial.
            tauto.
          * assert (list_env_iter
           (fun (i : {m' : nat | m' < n}) (env : df_env) =>
            df_eval_backprop_deriv σ df2 env (transpose grad1 i)) 
           (Some env0) (bounded_seq0 n) <> None).
            apply list_env_iter_total_fun; intros.          
            apply backprop_deriv_fully_closed_not_none; trivial.
            tauto.
          * assert (list_env_iter
           (fun (i : {m' : nat | m' < n}) (env : df_env) =>
            df_eval_backprop_deriv σ df2 env (transpose grad1 i)) 
           (Some env0) (bounded_seq0 n) <> None).
            apply list_env_iter_total_fun; intros.          
            apply backprop_deriv_fully_closed_not_none; trivial.
            tauto.
          * assert (list_env_iter
           (fun (i : {m' : nat | m' < n}) (env : df_env) =>
            df_eval_backprop_deriv σ df2 env
              (transpose
                 (fun (i0 : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                  (grad1 i0 j + grad2 i0 j)%R) i)) (Some env) (bounded_seq0 n) <> None).
            apply list_env_iter_total_fun; intros.          
            apply backprop_deriv_fully_closed_not_none; trivial.
            tauto.
        + intros.
          apply IHdf2; trivial.
      - Case "MatrixMult"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        simpler2.
        specialize 
          (IHdf1
             (matrix_mult grad1
                          (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < p}) => d1 j i))
             (matrix_mult grad2
                          (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < p}) => d1 j i))
                       grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        rewrite eqq, eqq8, eqq9 in IHdf1.
        specialize (IHdf2
                      (matrix_mult (fun (i : {n' : nat | n' < p}) 
                                        (j : {m' : nat | m' < m}) => d0 j i)
                                   grad1)
                      (matrix_mult (fun (i : {n' : nat | n' < p}) 
                                        (j : {m' : nat | m' < m}) => d0 j i)
                                   grad2)
                      env1 env3 env).
        simpl in IHdf1.
        replace
          (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < p}) =>
                (matrix_mult grad1
                   (fun (i0 : {n' : nat | (n' < n)%nat}) (j0 : {m' : nat | (m' < p)%nat}) =>
                    d1 j0 i0) i j +
                 matrix_mult grad2
                   (fun (i0 : {n' : nat | (n' < n)%nat}) (j0 : {m' : nat | (m' < p)%nat}) =>
                      d1 j0 i0) i j)%R)
            with
              (matrix_mult
                 (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                    (grad1 i j + grad2 i j)%R)
                 (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < p}) => d1 j i)) in IHdf1.
        + rewrite eqq2, eqq4, eqq6 in IHdf1.
          unfold lift, lift2 in IHdf1; simpl in IHdf1.
          inversion IHdf1.
          cut_to IHdf2; simpler2.
          simpl in IHdf2.
          rewrite eqq5, eqq7 in IHdf2.
          replace
            (fun (i : {n' : nat | n' < p}) (j : {m' : nat | m' < n}) =>
                (matrix_mult
                   (fun (i0 : {n' : nat | (n' < p)%nat}) (j0 : {m' : nat | (m' < m)%nat}) =>
                    d0 j0 i0) grad1 i j +
                 matrix_mult
                   (fun (i0 : {n' : nat | (n' < p)%nat}) (j0 : {m' : nat | (m' < m)%nat}) =>
                    d0 j0 i0) grad2 i j)%R) with
              (matrix_mult (fun (i : {n' : nat | n' < p}) (j : {m' : nat | m' < m}) => d0 j i)
                           (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                              (grad1 i j + grad2 i j)%R))
            in IHdf2.
          * rewrite eqq3 in IHdf2.
            unfold lift, lift2 in IHdf2; simpl in IHdf2.
            inversion IHdf2.
            f_equal.
            rewrite (split_subvar env env0 d val1); trivial.
            rewrite (split_subvar env1 env2 val val2); trivial.
            rewrite (split_subvar env3 env4 val0 val3); trivial.
            rewrite H7, H8; lra.
          * unfold matrix_mult.
            apply FunctionalExtensionality.functional_extensionality; intros.
            apply FunctionalExtensionality.functional_extensionality; intros.
            rewrite vsum_plus; f_equal.
            apply FunctionalExtensionality.functional_extensionality; intros.
            simpl; lra.
        + unfold matrix_mult.
          apply FunctionalExtensionality.functional_extensionality; intros.
          apply FunctionalExtensionality.functional_extensionality; intros.          
          rewrite vsum_plus; f_equal.
          apply FunctionalExtensionality.functional_extensionality; intros.          
          simpl; lra.
      - Case "VectorPlus"%string.
        destruct H2.
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 grad1 grad2 env1 env3 env).
        simpler2.
        simpl in IHdf1.
        rewrite eqq1, eqq3, eqq in IHdf1.
        unfold lift, lift2 in IHdf1; simpl in IHdf1.
        inversion IHdf1.
        cut_to IHdf2; try congruence.
        simpl in IHdf2.
        rewrite eqq0, eqq2, eqq4 in IHdf2.
        unfold lift, lift2 in IHdf2; inversion IHdf2.
        f_equal.
        rewrite (split_subvar env env0 val val5); trivial.
        rewrite (split_subvar env1 env2 val0 val6); trivial.
        rewrite (split_subvar env3 env4 val1 val7); trivial.
        rewrite eqq5 in eqq8.
        rewrite eqq6 in eqq9.
        rewrite eqq7 in eqq10.
        invcs eqq8; invcs eqq9; invcs eqq10.
        rewrite H5, H6; lra.
      - Case "VectorMinus"%string.
        destruct H2.
        unfold lift, lift2.
        repeat simpl_closed_backprop.
        specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 (fun i : {n' : nat | n' < n} => (- grad1 i)%R)
                          (fun i : {n' : nat | n' < n} => (- grad2 i)%R)
                          env1 env3 env).
        simpler2.
        simpl in IHdf1.
        rewrite eqq, eqq1, eqq3 in IHdf1.
        unfold lift, lift2 in IHdf1; simpl in IHdf1.
        inversion IHdf1.
        cut_to IHdf2; try congruence.
        simpl in IHdf2.
        replace (fun i : {n' : nat | n' < n} => (- grad1 i + - grad2 i)%R) with
            (fun i : {n' : nat | n' < n} => (- (grad1 i + grad2 i))%R) in IHdf2.
        rewrite eqq0, eqq2, eqq4 in IHdf2.
        unfold lift, lift2 in IHdf2; simpl in IHdf2.
        inversion IHdf2.
        f_equal.
        rewrite (split_subvar env env0 val val5); trivial.
        rewrite (split_subvar env1 env2 val0 val6); trivial.
        rewrite (split_subvar env3 env4 val1 val7); trivial.
        rewrite eqq5 in eqq8; rewrite eqq6 in eqq9; rewrite eqq7 in eqq10.
        invcs eqq8; invcs eqq9; invcs eqq10.
        rewrite H5, H6; lra.
        apply FunctionalExtensionality.functional_extensionality; intros.          
        lra.
      - Case "MatrixPlus"%string.
        destruct H2.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv 
                  σ df1 grad_env3
                  (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (grad1 i j + grad2 i j)%R)
                <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].        
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 (grad1)%R <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2 (grad2)%R <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2 grad1 grad2 d2 d4 d0).
        rewrite eqq, eqq1, eqq3 in IHdf1.
        simpl in IHdf1.
        rewrite eqq0, eqq2, eqq4 in IHdf1.
        unfold lift, lift2 in IHdf1; simpl in IHdf1.
        inversion IHdf1.
        assert (vartlookup d2 (s, DTfloat) <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) H).
        assert (vartlookup d4 (s, DTfloat) <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq4 (s, DTfloat) H0).
        assert (vartlookup d0 (s, DTfloat) <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) H1).
        specialize (IHdf2 H7 H9 H10 H3).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].                
        simpl in IHdf2.
        unfold lift, lift2; simpl.
        assert (df_eval_backprop_deriv 
                  σ df2 d0
                  (fun (i : {n' : nat | n' < n}) 
                       (j : {m' : nat | m' < m}) => (grad1 i j + grad2 i j)%R) <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H3. 
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df2 d2 (grad1)%R <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H3. 
        case_eq (df_eval_backprop_deriv σ df2 d2 (grad1)%R); [intros|tauto].
        assert (df_eval_backprop_deriv σ df2 d4 (grad2)%R <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H3. 
        case_eq (df_eval_backprop_deriv σ df2 d4 (grad2)%R); [intros|tauto].
        simpl in IHdf2.
        rewrite eqq8, H13, H15 in IHdf2.
        unfold lift, lift2 in IHdf2; simpl in IHdf2.
        inversion IHdf2.
        f_equal.
        rewrite (split_subvar d0 d8 d d5); trivial.
        rewrite (split_subvar d2 d9 d1 d6); trivial.
        rewrite (split_subvar d4 d10 d3 d7); trivial.
        rewrite H8, H17; lra.
      - Case "MatrixMinus"%string.
        destruct H2.
        match_option; [|tauto].
        assert (df_eval_backprop_deriv 
                  σ df1 grad_env3
                  (fun (i : {n' : nat | n' < n}) 
                       (j : {m' : nat | m' < m}) => (grad1 i j + grad2 i j)%R) <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].        
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 (grad1)%R <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2 (grad2)%R <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        specialize (IHdf1 grad1 grad2 grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2
                      (fun (i : {n' : nat | n' < n}) 
                           (j : {m' : nat | m' < m}) => (- grad1 i j)%R)
                      (fun (i : {n' : nat | n' < n}) 
                           (j : {m' : nat | m' < m}) => (- grad2 i j)%R)
                          d2 d4 d0).
        rewrite eqq, eqq1, eqq3 in IHdf1.
        simpl in IHdf1.
        rewrite eqq0, eqq2, eqq4 in IHdf1.
        unfold lift, lift2 in IHdf1; simpl in IHdf1.
        inversion IHdf1.
        assert (vartlookup d2 (s, DTfloat) <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) H).
        assert (vartlookup d4 (s, DTfloat) <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq4 (s, DTfloat) H0).
        assert (vartlookup d0 (s, DTfloat) <> None).
        apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq0 (s, DTfloat) H1).
        specialize (IHdf2 H7 H9 H10 H3).
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].
        match_option_in IHdf2; [|tauto].                
        unfold lift, lift2; simpl.
        assert (df_eval_backprop_deriv 
                  σ df2 d0
                  (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
       (- (grad1 i j + grad2 i j))%R) <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H3. 
        match_option; [|tauto].
        assert (df_eval_backprop_deriv 
                  σ df2 d2
                  (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (- grad1 i j)%R)
                  <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H3. 
        case_eq (df_eval_backprop_deriv σ df2 d2
                 (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (- grad1 i j)%R))
        ; [intros |tauto].
        assert (df_eval_backprop_deriv σ df2 d4
                 (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (- grad2 i j)%R)
               <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H3. 
        case_eq (df_eval_backprop_deriv σ df2 d4
                  (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => (- grad2 i j)%R))
        ; [intros | tauto].
        simpl in IHdf2.
        replace
          (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
             (- grad1 i j + - grad2 i j)%R) with
            (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
               (- (grad1 i j + grad2 i j))%R) in IHdf2.
        rewrite eqq8, H13, H15 in IHdf2.
        unfold lift, lift2 in IHdf2; simpl in IHdf2.
        inversion IHdf2.
        f_equal.
        rewrite (split_subvar d0 d8 d d5); trivial.
        rewrite (split_subvar d2 d9 d1 d6); trivial.
        rewrite (split_subvar d4 d10 d3 d7); trivial.
        rewrite H8, H17; lra.
        apply FunctionalExtensionality.functional_extensionality; intros.
        apply FunctionalExtensionality.functional_extensionality; intros.                  
        lra.
      - Case "VectorScalMult"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env3
                        (vsum (fun j : {n' : nat | n' < n} => (d1 j * (grad1 j + grad2 j))%R))
                        <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].        
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 
                              (vsum (fun j : {n' : nat | n' < n} => (d1 j * grad1 j)%R))
                                        <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2
                              (vsum (fun j : {n' : nat | n' < n} => (d1 j * grad2 j)%R))
                <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        specialize (IHdf1
                      (vsum (fun j : {n' : nat | n' < n} => (d1 j * grad1 j)%R))
                      (vsum (fun j : {n' : nat | n' < n} => (d1 j * grad2 j)%R))
                       grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2
                      (fun j : {n' : nat | n' < n} => (d0 * grad1 j)%R)
                      (fun j : {n' : nat | n' < n} => (d0 * grad2 j)%R)
                      d4 d6 d2).
        rewrite eqq, eqq3, eqq5 in IHdf1.
        simpl in IHdf1.
        replace
          (@vsum floatish_R n (fun j : {n' : nat | (n' < n)%nat} => d1 j * grad1 j) +
           @vsum floatish_R n (fun j : {n' : nat | (n' < n)%nat} => d1 j * grad2 j))%R with
            (vsum (fun j : {n' : nat | n' < n} => (d1 j * (grad1 j + grad2 j))%R)) in IHdf1.
        + rewrite eqq2, eqq4, eqq6 in IHdf1.
          unfold lift, lift2 in IHdf1; simpl in IHdf1.
          inversion IHdf1.
          assert (vartlookup d2 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) H1).
          assert (vartlookup d4 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq4 (s, DTfloat) H).
          assert (vartlookup d6 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq6 (s, DTfloat) H0).
          specialize (IHdf2 H11 H12 H9 H3).
          match_option_in IHdf2; [|tauto].
          match_option_in IHdf2; [|tauto].
          match_option_in IHdf2; [|tauto].                
          unfold lift, lift2; simpl.
          assert (df_eval_backprop_deriv 
                    σ df2 d2
                    (fun j : {n' : nat | n' < n} => (d0 * (grad1 j + grad2 j))%R)
                                       <> None).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3. 
          match_option; [|tauto].
          assert (df_eval_backprop_deriv σ df2 d4
                                         (fun j : {n' : nat | n' < n} => (d0 * grad1 j)%R)
                                         <> None).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3. 
          case_eq (df_eval_backprop_deriv σ df2 d4
                                          (fun j : {n' : nat | n' < n} => (d0 * grad1 j)%R))
          ; [intros | tauto].
          assert (df_eval_backprop_deriv σ df2 d6
                                         (fun j : {n' : nat | n' < n} => (d0 * grad2 j)%R)
                 <> None ).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3. 
          case_eq (df_eval_backprop_deriv σ df2 d6
                                         (fun j : {n' : nat | n' < n} => (d0 * grad2 j)%R))
                  ; [intros | tauto].
          simpl in IHdf2.
          replace 
            (fun i : {n' : nat | n' < n} => (d0 * grad1 i + d0 * grad2 i)%R) with
               (fun j : {n' : nat | n' < n} => (d0 * (grad1 j + grad2 j))%R) in IHdf2.
          * rewrite eqq10, H15, H17 in IHdf2.
            unfold lift, lift2 in IHdf2; simpl in IHdf2.
            inversion IHdf2.
            f_equal.
            rewrite (split_subvar d2 d10 d d7); trivial.
            rewrite (split_subvar d4 d11 d3 d8); trivial.
            rewrite (split_subvar d6 d12 d5 d9); trivial.
            rewrite H10, H19; lra.
          * apply FunctionalExtensionality.functional_extensionality; intros. 
            lra.
        + simpl.
          rewrite vsum_plus.
          f_equal.
          apply FunctionalExtensionality.functional_extensionality; intros. 
          lra.
      - Case "MatrixScalMult"%string.
        destruct H2.
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df1); intros.
        specialize (H4 H2).
        match_option; [|tauto].
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H5 H3).
        match_option; [|tauto].
        assert (df_eval_backprop_deriv 
                  σ df1 grad_env3
                  (msum
                     (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                        (d1 i j * (grad1 i j + grad2 i j))%R))
                <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].        
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env1 
                  (msum
                     (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                        (d1 i j * grad1 i j)%R))
                                        <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        match_option; [|tauto].
        assert (df_eval_backprop_deriv σ df1 grad_env2
                  (msum
                     (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                        (d1 i j * grad2 i j)%R))
                                        <> None).
        apply backprop_deriv_fully_closed_not_none.          
        apply H2.
        match_option; [|tauto].
        specialize (IHdf1
                  (msum
                     (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                        (d1 i j * grad1 i j)%R))
                  (msum
                     (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                        (d1 i j * grad2 i j)%R))
                       grad_env1 grad_env2 grad_env3 H H0 H1 H2).
        specialize (IHdf2
                      (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => 
                         (grad1 i j * d0)%R)
                      (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) => 
                         (grad2 i j * d0)%R)
                      d4 d6 d2).
        rewrite eqq, eqq3, eqq5 in IHdf1.
        simpl in IHdf1.
        replace
          (@msum floatish_R n m
             (fun (i : {n' : nat | (n' < n)%nat}) (j : {m' : nat | (m' < m)%nat}) =>
                d1 i j * grad1 i j) +
           @msum floatish_R n m
             (fun (i : {n' : nat | (n' < n)%nat}) (j : {m' : nat | (m' < m)%nat}) =>
                d1 i j * grad2 i j))%R with
            (msum
            (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
             (d1 i j * (grad1 i j + grad2 i j))%R)) in IHdf1.
        + rewrite eqq2, eqq4, eqq6 in IHdf1.
          unfold lift, lift2 in IHdf1; simpl in IHdf1.
          inversion IHdf1.
          assert (vartlookup d2 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat) H1).
          assert (vartlookup d4 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq4 (s, DTfloat) H).
          assert (vartlookup d6 (s, DTfloat) <> None).
          apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq6 (s, DTfloat) H0).
          specialize (IHdf2 H11 H12 H9 H3).
          match_option_in IHdf2; [|tauto].
          match_option_in IHdf2; [|tauto].
          match_option_in IHdf2; [|tauto].                
          unfold lift, lift2; simpl.
          assert (df_eval_backprop_deriv 
                    σ df2 d2
                    (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                       ((grad1 i j + grad2 i j) * d0)%R)
                                       <> None).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3. 
          match_option; [|tauto].
          assert (df_eval_backprop_deriv σ df2 d4
                                         (fun (i : {n' : nat | n' < n}) 
                                              (j : {m' : nat | m' < m}) => (grad1 i j * d0)%R)
                                         <> None).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3. 
          case_eq (df_eval_backprop_deriv σ df2 d4
                                         (fun (i : {n' : nat | n' < n}) 
                                              (j : {m' : nat | m' < m}) => (grad1 i j * d0)%R))
          ; [intros | tauto].
          assert (df_eval_backprop_deriv σ df2 d6
                                         (fun (i : {n' : nat | n' < n}) 
                                              (j : {m' : nat | m' < m}) => (grad2 i j * d0)%R)
                 <> None ).
          apply backprop_deriv_fully_closed_not_none.          
          apply H3. 
          case_eq (df_eval_backprop_deriv σ df2 d6
                                         (fun (i : {n' : nat | n' < n}) 
                                              (j : {m' : nat | m' < m}) => (grad2 i j * d0)%R))
                  ; [intros | tauto].
          simpl in IHdf2.
          replace 
            (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
               (grad1 i j * d0 + grad2 i j * d0)%R) with
              (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                 ((grad1 i j + grad2 i j) * d0)%R) in IHdf2.
          * rewrite eqq10, H15, H17 in IHdf2.
            unfold lift, lift2 in IHdf2; simpl in IHdf2.
            inversion IHdf2.
            f_equal.
            rewrite (split_subvar d2 d10 d d7); trivial.
            rewrite (split_subvar d4 d11 d3 d8); trivial.
            rewrite (split_subvar d6 d12 d5 d9); trivial.
            rewrite H10, H19; lra.
          * apply FunctionalExtensionality.functional_extensionality; intros.
            apply FunctionalExtensionality.functional_extensionality; intros.             
            lra.
        + unfold msum.
          rewrite vsum_plus.
          f_equal.
          apply FunctionalExtensionality.functional_extensionality; intros.
          rewrite vmap_nth.
          rewrite vmap_nth.
          rewrite vmap_nth.
          rewrite vsum_plus.
          f_equal.
          apply FunctionalExtensionality.functional_extensionality; intros.
          lra.
      - Case "VectorApply"%string.
        destruct H2.
        simpler2.
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H4 H3).
        match_option.
        match_option.
        + match_option.
          * match_option.
            -- unfold lift.
               repeat simpl_closed_backprop.
               unfold lift2.
               specialize (apply vectoro_to_ovector_forall_some_f eqq3);intros.          
               specialize (apply vectoro_to_ovector_forall_some_f eqq4);intros.          
               specialize (apply vectoro_to_ovector_forall_some_f eqq5);intros.
               specialize (IHdf2 v1 v2 grad_env1 grad_env2 grad_env3).
               cut_to IHdf2; try congruence.
               rewrite eqq, eqq0, eqq1, eqq7, eqq8 in IHdf2; simpl in IHdf2.
               replace (fun i : {n' : nat | n' < n} => (v1 i + v2 i)%R) with v0 in IHdf2.
               rewrite eqq6 in IHdf2.
               unfold lift, lift2 in IHdf2.
               apply IHdf2.
               apply FunctionalExtensionality.functional_extensionality; intros.
               specialize (H5 x);rewrite vmap_nth in H5; simpl in H5.
               specialize (H6 x);rewrite vmap_nth in H6; simpl in H6.
               specialize (H7 x);rewrite vmap_nth in H7; simpl in H7.               
               match_option_in H5; invcs H5.
               match_option_in H6; invcs H6.
               match_option_in H7; invcs H7.
               rewrite eqq9 in eqq10; invcs eqq10.
               rewrite eqq9 in eqq11; invcs eqq11.
               lra.
            -- specialize (apply vectoro_to_ovector_exists_None eqq5); intros.
               destruct H5.
               rewrite vmap_nth in e; simpl in e.
               match_option_in e.
               assert (df_eval [mk_env_entry (v, DTfloat) (d x)] (df_deriv df1 (v, DTfloat)) <> None).
               apply eval_fully_closed_not_none.
               now apply fully_closed_deriv.
               tauto.
          * specialize (apply vectoro_to_ovector_exists_None eqq4); intros.
            destruct H5.
            rewrite vmap_nth in e; simpl in e.
            match_option_in e.
            assert (df_eval [mk_env_entry (v, DTfloat) (d x)] (df_deriv df1 (v, DTfloat)) <> None).
            apply eval_fully_closed_not_none.
            now apply fully_closed_deriv.
            tauto.
        + specialize (apply vectoro_to_ovector_exists_None eqq3); intros.
          destruct H5.
          rewrite vmap_nth in e; simpl in e.
          match_option_in e.
          assert (df_eval [mk_env_entry (v, DTfloat) (d x)] (df_deriv df1 (v, DTfloat)) <> None).
          apply eval_fully_closed_not_none.
          now apply fully_closed_deriv.
          tauto.
      - Case "MatrixApply"%string.
        destruct H2.
        simpler2.
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H4 H3).
        match_option.
        match_option.
        + match_option.
          * match_option.
            -- unfold lift.
               repeat simpl_closed_backprop.
               unfold lift2.
               unfold matrixo_to_omatrix in *.
               specialize (apply vectoro_to_ovector_forall_some_f eqq3);intros.          
               specialize (apply vectoro_to_ovector_forall_some_f eqq4);intros.          
               specialize (apply vectoro_to_ovector_forall_some_f eqq5);intros.
               specialize (IHdf2 m1 m2 grad_env1 grad_env2 grad_env3).
               cut_to IHdf2; try congruence.
               rewrite eqq, eqq0, eqq1, eqq7, eqq8 in IHdf2; simpl in IHdf2.
               replace (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                          (m1 i j + m2 i j)%R) with m0 in IHdf2.
               rewrite eqq6 in IHdf2.
               unfold lift, lift2 in IHdf2.
               apply IHdf2.
               apply FunctionalExtensionality.functional_extensionality; intros.
               apply FunctionalExtensionality.functional_extensionality; intros.               
               specialize (H5 x); specialize (H6 x); specialize (H7 x).
               unfold mmap in H5; unfold mmap in H6; unfold mmap in H7.
               specialize (apply vectoro_to_ovector_forall_some_f H5);intros.          
               specialize (apply vectoro_to_ovector_forall_some_f H6);intros.          
               specialize (apply vectoro_to_ovector_forall_some_f H7);intros.
               specialize (H8 x0); do 2 rewrite vmap_nth in H8.
               specialize (H9 x0); do 2 rewrite vmap_nth in H9.
               specialize (H10 x0); do 2 rewrite vmap_nth in H10.
               rewrite  matrix_zip_m_n in H8.
               rewrite  matrix_zip_m_n in H9.
               rewrite  matrix_zip_m_n in H10.               
               match_option_in H8.
               rewrite eqq9 in H9; rewrite eqq9 in H10.
               invcs H8; invcs H9; invcs H10.
               lra.
            -- specialize (apply vectoro_to_ovector_exists_None eqq5); intros; destruct H5.
               specialize (apply vectoro_to_ovector_exists_None e); intros; destruct H5.
               unfold mmap in e0.
               do 2 rewrite vmap_nth in e0; simpl in e0.
               rewrite matrix_zip_m_n in e0.
               match_option_in e0.
               assert (df_eval [mk_env_entry (v, DTfloat) (d x x0)] (df_deriv df1 (v, DTfloat)) <> None).
               apply eval_fully_closed_not_none.
               now apply fully_closed_deriv.
               tauto.
          * specialize (apply vectoro_to_ovector_exists_None eqq4); intros; destruct H5.
            specialize (apply vectoro_to_ovector_exists_None e); intros; destruct H5.
            unfold mmap in e0.
            do 2 rewrite vmap_nth in e0; simpl in e0.
            rewrite matrix_zip_m_n in e0.
            match_option_in e0.
            assert (df_eval [mk_env_entry (v, DTfloat) (d x x0)] (df_deriv df1 (v, DTfloat)) <> None).
            apply eval_fully_closed_not_none.
            now apply fully_closed_deriv.
            tauto.
        + specialize (apply vectoro_to_ovector_exists_None eqq3); intros; destruct H5.
          specialize (apply vectoro_to_ovector_exists_None e); intros; destruct H5.          
          unfold mmap in e0.
          do 2 rewrite vmap_nth in e0; simpl in e0.
          rewrite matrix_zip_m_n in e0.
          match_option_in e0.
          assert (df_eval [mk_env_entry (v, DTfloat) (d x x0)] (df_deriv df1 (v, DTfloat)) <> None).
          apply eval_fully_closed_not_none.
          now apply fully_closed_deriv.
          tauto.
      - Case "VLossfun"%string.
        destruct H2.
        simpler2.
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H4 H3).
        match_option.
        match_option.
        + match_option.
          * match_option.
            -- unfold lift.
               repeat simpl_closed_backprop.
               unfold lift2.
               specialize (apply vectoro_to_ovector_forall_some_f eqq3);intros.
               specialize (apply vectoro_to_ovector_forall_some_f eqq4);intros.
               specialize (apply vectoro_to_ovector_forall_some_f eqq5);intros.
               specialize (IHdf2 v0 v3 grad_env1 grad_env2 grad_env3).               
               cut_to IHdf2; try congruence.
               rewrite eqq, eqq0, eqq1 in IHdf2.
               rewrite eqq7, eqq8 in IHdf2.
               simpl in IHdf2.
               replace (fun i : {n' : nat | n' < n} => (v0 i + v3 i)%R) with v in IHdf2.
               rewrite eqq6 in IHdf2.
               unfold lift, lift2 in IHdf2.
               apply IHdf2.
               apply FunctionalExtensionality.functional_extensionality; intros.
               specialize (H5 x);rewrite vmap_nth in H5; simpl in H5.
               specialize (H6 x);rewrite vmap_nth in H6; simpl in H6.
               specialize (H7 x);rewrite vmap_nth in H7; simpl in H7.
               match_option_in H5.
               rewrite eqq9 in H6; rewrite eqq9 in H7.
               invcs H5; invcs H6; invcs H7.
               lra.
            -- specialize (apply vectoro_to_ovector_exists_None eqq5); intros.
               destruct H5.
               rewrite vmap_nth in e; simpl in e.
               match_option_in e.
               assert ( df_eval [mk_env_entry (v1, DTfloat) (d x); 
                                 mk_env_entry (v2, DTfloat) (r x)]
                                (df_deriv df1 (v1, DTfloat)) <> None).
               apply eval_fully_closed_not_none.
               now apply fully_closed_deriv.
               tauto.
          * specialize (apply vectoro_to_ovector_exists_None eqq4); intros.
            destruct H5.
            rewrite vmap_nth in e; simpl in e.
            match_option_in e.
            assert (df_eval [mk_env_entry (v1, DTfloat) (d x); 
                             mk_env_entry (v2, DTfloat) (r x)]
                            (df_deriv df1 (v1, DTfloat)) <> None).
            apply eval_fully_closed_not_none.
            now apply fully_closed_deriv.
            tauto.
        + specialize (apply vectoro_to_ovector_exists_None eqq3); intros.
          destruct H5.
          rewrite vmap_nth in e; simpl in e.
          match_option_in e.
          assert (df_eval [mk_env_entry (v1, DTfloat) (d x); mk_env_entry (v2, DTfloat) (r x)]
                          (df_deriv df1 (v1, DTfloat)) <> None).
          apply eval_fully_closed_not_none.
          now apply fully_closed_deriv.
          tauto.
      - Case "MLossfun"%string.
        destruct H2.
        simpler2.
        generalize (eval_fully_closed_not_none σ df2); intros.
        specialize (H4 H3).
        match_option.
        match_option.
        + match_option.
          * match_option.
            -- unfold lift.
               repeat simpl_closed_backprop.
               unfold lift2.
               specialize (apply vectoro_to_ovector_forall_some_f eqq3);intros.
               specialize (apply vectoro_to_ovector_forall_some_f eqq4);intros.
               specialize (apply vectoro_to_ovector_forall_some_f eqq5);intros.
               specialize (IHdf2 m1 m2 grad_env1 grad_env2 grad_env3).               
               cut_to IHdf2; try congruence.
               rewrite eqq, eqq0, eqq1 in IHdf2.
               rewrite eqq7, eqq8 in IHdf2.
               simpl in IHdf2.
               replace (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                (m1 i j + m2 i j)%R) with m0 in IHdf2.
               rewrite eqq6 in IHdf2.
               unfold lift, lift2 in IHdf2.
               apply IHdf2.
               apply FunctionalExtensionality.functional_extensionality; intros.
               specialize (H5 x); simpl in H5.
               specialize (H6 x); simpl in H6.
               specialize (H7 x); simpl in H7.
               specialize (apply vectoro_to_ovector_forall_some_f H5);intros.
               specialize (apply vectoro_to_ovector_forall_some_f H6);intros.
               specialize (apply vectoro_to_ovector_forall_some_f H7);intros.
               apply FunctionalExtensionality.functional_extensionality; intros.
               specialize (H8 x0); unfold mmap in H8;do 2 rewrite vmap_nth in H8; simpl in H8.
               specialize (H9 x0); unfold mmap in H9;do 2 rewrite vmap_nth in H9; simpl in H9.
               specialize (H10 x0); unfold mmap in H10;do 2 rewrite vmap_nth in H10; simpl in H10.
               rewrite matrix_zip_m_n in H8.
               rewrite matrix_zip_m_n in H9.
               rewrite matrix_zip_m_n in H10.               
               match_option_in H8.
               rewrite eqq9 in H9; rewrite eqq9 in H10.
               invcs H8; invcs H9; invcs H10.
               lra.
            -- specialize (apply vectoro_to_ovector_exists_None eqq5); intros.
               destruct H5.
               specialize (apply vectoro_to_ovector_exists_None e); intros.
               destruct H5.               
               unfold mmap in e0; do 2 rewrite vmap_nth in e0; simpl in e0.
               rewrite matrix_zip_m_n in e0.
               match_option_in e0.
               assert ( df_eval [mk_env_entry (v1, DTfloat) (d x x0); 
                                 mk_env_entry (v2, DTfloat) (r x x0)]
                                (df_deriv df1 (v1, DTfloat)) <> None).
               apply eval_fully_closed_not_none.
               now apply fully_closed_deriv.
               tauto.
          * specialize (apply vectoro_to_ovector_exists_None eqq4); intros.
            destruct H5.
            specialize (apply vectoro_to_ovector_exists_None e); intros.
            destruct H5.               
            unfold mmap in e0; do 2 rewrite vmap_nth in e0; simpl in e0.
            rewrite matrix_zip_m_n in e0.
            match_option_in e0.
            assert (df_eval [mk_env_entry (v1, DTfloat) (d x x0); 
                             mk_env_entry (v2, DTfloat) (r x x0)]
                            (df_deriv df1 (v1, DTfloat)) <> None).
            apply eval_fully_closed_not_none.
            now apply fully_closed_deriv.
            tauto.
        + specialize (apply vectoro_to_ovector_exists_None eqq3); intros.
          destruct H5.
          specialize (apply vectoro_to_ovector_exists_None e); intros.
          destruct H5.               
          unfold mmap in e0; do 2 rewrite vmap_nth in e0; simpl in e0.
          rewrite matrix_zip_m_n in e0.
          match_option_in e0.
          assert (df_eval [mk_env_entry (v1, DTfloat) (d x x0); 
                           mk_env_entry (v2, DTfloat) (r x x0)]
                          (df_deriv df1 (v1, DTfloat)) <> None).
          apply eval_fully_closed_not_none.
          now apply fully_closed_deriv.
          tauto.
    Qed.

    Lemma vectoro_to_ovector_eNone_None {A n} {vo:Vector (option A) n} :
      {i | vo i = None} ->
      vectoro_to_ovector vo = None.
    Proof.
      intros.
      destruct H.
      now apply (vectoro_to_ovector_None_None x).
    Qed.

    Definition ConstSplitVector {T} (middle theend:nat)  (part1 part2:T)  : (Vector T theend) :=
      fun (i: {n':nat | n' < theend}%nat) =>
        if lt_dec (proj1_sig i) middle then part1 else part2.

    Definition mergeVectorZero {T} {n} (middle:nat) (part1 : Vector T n) (c:T) : (Vector T n) :=
      fun (i: {n':nat | n' < n}%nat) =>
        if lt_dec (proj1_sig i) middle then (part1 i) else c.

    Definition scaleUnitVector {T} (n:nat) (j : {n':nat | (n' < n)%nat}) (c:T) (zero:T) : Vector T n :=
      fun i => if (proj1_sig i) == (proj1_sig j) then c else zero%R.

    Lemma ConstSplitVectorSzero bound n (pf:bound < n) :
          (ConstSplitVector (S bound) n 1%R 0%R) =
          dfti_gen_plus (T:=DTVector n) (ConstSplitVector bound n 1%R 0%R) (UnitVector n (exist _ bound pf)).
    Proof.
      simpl.
      apply functional_extensionality.
      intros.
      unfold ConstSplitVector, UnitVector, equiv_dec, nat_eq_eqdec; simpl.
      destruct x as [x pff]; simpl.
      destruct (lt_dec x (S bound))
      ; destruct (lt_dec x bound)
      ; destruct (Nat.eq_dec x bound)
      ; try lia; try lra.
    Qed.

    Lemma mergeVectorSzero {n} (bound:nat) (pf:bound < n) (part1 : Vector R n):
      let ind := (exist _ bound pf) in
          (@mergeVectorZero (@float floatish_R) n (S bound) part1 0%R) =
          dfti_gen_plus (T:=DTVector n) (@mergeVectorZero (@float floatish_R) n bound part1 0%R)
                        (scaleUnitVector n ind (part1 ind) 0%R).
    Proof.
      simpl.
      apply functional_extensionality.
      intros.
      unfold mergeVectorZero, scaleUnitVector, equiv_dec, nat_eq_eqdec; simpl.
      destruct x as [x pff]; simpl.
      destruct (lt_dec x (S bound))
      ; destruct (lt_dec x bound)
      ; destruct (Nat.eq_dec x bound)
      ; try lia; try lra.
      subst; simpl.
      ring_simplify.
      erewrite index_pf_irrel; eauto.
    Qed.

    Lemma mergeVectorSzero_mat {n m} (bound:nat) pf (part1 : Matrix float n m) :
      let ind := (exist _ bound pf) in 
          (@mergeVectorZero (Vector float m) n (S bound) part1 (ConstVector m 0%R)) =
          dfti_gen_plus (T:=DTMatrix n m) (@mergeVectorZero (Vector float m) n bound part1 (ConstVector m 0%R))
                        (scaleUnitVector (T:=Vector float m) n ind (part1 ind) (ConstVector m 0%R)).
    Proof.
      simpl.
      do 2 (apply functional_extensionality; intros).
      unfold mergeVectorZero, scaleUnitVector, ConstVector, equiv_dec, nat_eq_eqdec; simpl.
      destruct x as [x pff]; simpl.
      destruct (lt_dec x (S bound))
      ; destruct (lt_dec x bound)
      ; destruct (Nat.eq_dec x bound)
      ; simpl
      ; try lia; try lra.
      subst; simpl.
      rewrite Rplus_0_l.
      erewrite index_pf_irrel; eauto.
    Qed.

    Lemma vsum_alt_eq {m:nat} (v:Vector R m) : vsum v = vector_fold_right Fplus 0%R v.
    Proof.
      apply vector_fold_right1_as_vector_fold_right.
      unfold Datatypes.id; simpl; intros; lra.
    Qed.
    
    Lemma vsum_cons {m:nat} x (v:Vector R m) :
      vsum (vcons x v) = (x + vsum v)%R.
    Proof.
      repeat rewrite vsum_alt_eq.
      apply vector_fold_right_vcons.
    Qed.      

    Lemma constSplitVectorZero {n} :
      ConstSplitVector 0 n 1%R 0%R = ConstVector n 0%R.
    Proof.
      unfold ConstSplitVector, ConstVector; simpl.
      now apply functional_extensionality.
    Qed.

    Lemma df_eval_backprop_delta_by_unit_partvec_bounded {n} bound (pf:(bound<=n)%nat)
          (σ:df_env) (df:DefinedFunction UnitAnn (DTVector n)) (s: SubVar) grad_env (grad d:Vector float n):

           fully_closed_over df
                             (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve) σ) ->
           vartlookup grad_env (s, DTfloat) <> None ->
           
           (forall i : {n' : nat | n' < n},
         (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                 (scaleUnitVector n i (grad i) 0%R)) = Some (d i)) ->
         (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                 (mergeVectorZero bound grad 0%R)) = Some (vsum (vfirstn d bound pf)).
    Proof.
      intros closed lo fa.
      induction bound.
      - replace (mergeVectorZero 0 grad 0%R) with (scalarMult (DTVector n) 0%R (mergeVectorZero 0 grad 0%R)).
        + erewrite scalarMult_backprop_grad_scalar; try eassumption.
          * simpl.
            unfold df_eval_backprop_delta.
            simpler2.
            unfold lift.
            simpl_closed_backprop.
            f_equal.
            vm_compute; lra.
          * apply backprop_deriv_fully_closed_not_none; trivial. 
          * apply backprop_deriv_fully_closed_not_none; trivial. 
        + unfold scalarMult, mergeVectorZero.
          apply functional_extensionality; intros; simpl.
          lra.
      - assert (pf2:bound < n) by lia.
        assert (pf3:bound <= n) by lia.
        rewrite (mergeVectorSzero _ pf2 _ ).
        erewrite backprop_grad_sum; try eassumption.
        specialize (IHbound pf3).
        rewrite IHbound.
        rewrite fa.
        simpl.
        f_equal.
        destruct n; [lia | ].
        generalize (vector_Sn_split (vfirstn d (S bound) pf)); intros eqq1.
        apply vec_eq_eq in eqq1.
        simpl in *.
        rewrite eqq1.
        erewrite vfirstn_vdrop_last.
        erewrite vlast_vfirstn.
        rewrite vsum_cons.
        rewrite Rplus_comm.
        f_equal.
    Qed.

    Lemma df_eval_backprop_delta_by_unit_partvec {n} 
          (σ:df_env) (df:DefinedFunction UnitAnn (DTVector n)) (s: SubVar) grad_env (grad d:Vector float n):

           fully_closed_over df
                             (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve) σ) ->
           vartlookup grad_env (s, DTfloat) <> None ->
           
           (forall i : {n' : nat | n' < n},
               (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                       (scaleUnitVector n i (grad i) 0%R)) = Some (d i)) ->
           df_eval_backprop_delta σ df (s, DTfloat) grad_env grad = 
           Some (vsum d).
      Proof.
      intros.
      replace (grad) with (mergeVectorZero n grad 0%R).
      - erewrite df_eval_backprop_delta_by_unit_partvec_bounded; try eassumption.
        now rewrite vfirstn_eq.
      - apply functional_extensionality; unfold mergeVectorZero; intros [x pff]; simpl.
        destruct (lt_dec x n); trivial; lia.
        Unshelve.
        lia.
    Qed.

    Lemma df_eval_backprop_delta_by_unit_parts {n} 
          (σ:df_env) (df:DefinedFunction UnitAnn (DTVector n)) (s: SubVar) grad_env (d:Vector float n):

      fully_closed_over df
                        (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve) σ) ->
      vartlookup grad_env (s, DTfloat) <> None ->
      
      (forall i : {n' : nat | n' < n},
          (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                  
                                  (UnitVector n i)) = Some (d i)) ->
      (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                              (ConstVector n 1%R)) = Some (vsum d).
    Proof.
      intros.
      replace (ConstVector n 1%R) with (mergeVectorZero n (ConstVector n 1%R) 0%R).
      - erewrite df_eval_backprop_delta_by_unit_partvec_bounded; try eassumption.
        now rewrite vfirstn_eq.
      - apply functional_extensionality; unfold mergeVectorZero, ConstVector; intros [x pff]; simpl.
        destruct (lt_dec x n); trivial; lia.
        Unshelve.
        lia.
    Qed.

    Lemma scalarMult_mult {T} a b grad : scalarMult T a (scalarMult T b grad) = scalarMult T (a*b)%R grad.
    Proof.
      destruct T; simpl.
      - lra.
      - apply vec_eq_eq; intros ?; lra.
      - do 2 (apply vec_eq_eq; intros ?); lra.
    Qed.

    Corollary scalarMult_backprop_grad0 {Ann} {T} (σ:df_env) (df:DefinedFunction Ann T) (s: SubVar) (grad_env :df_env) (grad : definition_function_types_interp T) :
      let v := (s, DTfloat) in
      vartlookup grad_env v <> None -> 
      df_eval_backprop_deriv σ df grad_env (scalarMult T 0%R grad) <> None ->
      df_eval_backprop_delta σ df v grad_env (scalarMult T 0%R grad) = Some 0%R.
    Proof.
      simpl; intros.
      (* This allows us to drop the (unneeded) assumption
         df_eval_backprop_deriv σ df grad_env1 grad <> None
       *)
      replace (scalarMult T 0%R grad) with (scalarMult T 0%R (scalarMult T 0%R grad)).
      - erewrite scalarMult_backprop_grad_scalar; try eassumption.
        + simpl.
          unfold df_eval_backprop_delta.
          simpler2; simpl.
          destruct (df_eval_backprop_deriv σ df grad_env (scalarMult T 0%R grad)); simpl; [| congruence].
          f_equal; lra.
        + now rewrite scalarMult_mult, Rmult_0_l.
      - now rewrite scalarMult_mult, Rmult_0_l.
    Qed.
    
    Lemma scaleUnitVec_vec_plus_distr m n i (x y:Vector float m) c :
      vec_eq c (dfti_gen_plus (T:=DTVector m) c c) ->
      (scaleUnitVector n i (dfti_gen_plus (T:=DTVector m) x y) c) =
      (dfti_gen_plus (T:=DTMatrix n m) (scaleUnitVector n i x c) (scaleUnitVector n i y c)).
    Proof.
      intros fa.
      do 2 (apply functional_extensionality; intro).
      unfold scaleUnitVector; simpl.
      match_destr.
      now specialize (fa x1); simpl in fa.
    Qed.


    Lemma df_eval_backprop_delta_by_unit_partmat_outer_bounded {n m} bound (pf:(bound<=n)%nat)
          (σ:df_env) (df:DefinedFunction UnitAnn (DTMatrix n m)) (s: SubVar) grad_env (grad d:Matrix float n m):
      

           fully_closed_over df
                             (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve) σ) ->
           vartlookup grad_env (s, DTfloat) <> None ->
           
           (forall (i : {n' : nat | n' < n}),
         (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                 (scaleUnitVector n i (grad i) (ConstVector m 0%R))) = Some (vsum (d i))) ->

           (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                   (mergeVectorZero bound grad (ConstVector m 0%R))) = Some (vsum (vfirstn (vmap vsum d) bound pf)).
    Proof.
      intros closed lo fa.
      induction bound.
      - rewrite vfirstn0, vsum_nil.
        
        replace (mergeVectorZero 0 grad (ConstVector m 0%R)) with (scalarMult (DTMatrix n m) 0%R (mergeVectorZero 0 grad (ConstVector m 0%R))).
        + apply scalarMult_backprop_grad0; simpl in *; trivial.
          apply backprop_deriv_fully_closed_not_none; trivial. 
        + unfold scalarMult, ConstVector, mergeVectorZero.
          do 2 (apply functional_extensionality; intros); simpl.
          lra.
      - assert (pf2:bound < n) by lia.
        assert (pf3:bound <= n) by lia.
        simpl.
        generalize (mergeVectorSzero_mat (m:=m) _ pf2 grad ); intros HH; unfold Vector in HH.
        simpl float in *.
        rewrite HH; clear HH.
        erewrite backprop_grad_sum; try eassumption.
        specialize (IHbound pf3).
        rewrite IHbound.
        rewrite fa.
        simpl.
        f_equal.
        generalize (vector_Sn_split (vfirstn (vmap vsum d) (S bound) pf)); intros eqq1.
        apply vec_eq_eq in eqq1.
        simpl in *.
        rewrite eqq1.
        erewrite vfirstn_vdrop_last.
        erewrite vlast_vfirstn.
        rewrite vsum_cons.
        rewrite Rplus_comm.
        f_equal.
        rewrite vmap_nth.
        eauto.
    Qed.

    Lemma df_eval_backprop_delta_by_unit_partmat_inner_bounded {n m} bound (pf:(bound<=m)%nat)
          (σ:df_env) (df:DefinedFunction UnitAnn (DTMatrix n m)) (s: SubVar) grad_env (grad d:Matrix float n m) i:
      

           fully_closed_over df
                             (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve) σ) ->
           vartlookup grad_env (s, DTfloat) <> None ->
           
           (forall j : {n' : nat | n' < m},
         (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                 ((scaleUnitVector n i
         (scaleUnitVector m j (grad i j) 0%R) (ConstVector m 0%R)))) = Some (d i j)) ->

           (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                   (scaleUnitVector n i (mergeVectorZero bound (grad i) 0%R) (ConstVector m 0%R))) = Some (vsum (vfirstn (d i) bound pf)).
    Proof.
      intros closed lo fa.
      induction bound.
      - rewrite vfirstn0, vsum_nil.
        replace (scaleUnitVector n i (mergeVectorZero 0 (grad i) 0%R) (ConstVector m 0%R)) with (scalarMult (DTMatrix n m) 0%R (mergeVectorZero 0 grad (ConstVector m 0%R))).
        + apply scalarMult_backprop_grad0; simpl in *; trivial.
          apply backprop_deriv_fully_closed_not_none; trivial. 
        + unfold scalarMult, ConstVector, mergeVectorZero, scaleUnitVector.
          do 2 (apply functional_extensionality; intros); simpl.
          match_destr; lra.
      - assert (pf2:bound < m) by lia.
        assert (pf3:bound <= m) by lia.
        simpl.
        generalize (mergeVectorSzero _ pf2 (grad i) ); intros HH; unfold Vector in HH.
        simpl float in *.
        rewrite HH; clear HH.
        rewrite (scaleUnitVec_vec_plus_distr m n i) by (intros ?; unfold ConstVector; simpl; lra).
        erewrite backprop_grad_sum; try eassumption.
        specialize (IHbound pf3).
        simpl in *.
        rewrite IHbound.
        simpl.
        rewrite fa.
        simpl.
        f_equal.
        generalize (vector_Sn_split (vfirstn (d i) (S bound) pf)); intros eqq1.
        apply vec_eq_eq in eqq1.
        simpl in *.
        rewrite eqq1.
        erewrite vfirstn_vdrop_last.
        erewrite vlast_vfirstn.
        rewrite vsum_cons.
        rewrite Rplus_comm.
        f_equal.
    Qed.
    
    Lemma df_eval_backprop_delta_by_unit_partmat {n m} 
          (σ:df_env) (df:DefinedFunction UnitAnn (DTMatrix n m)) (s: SubVar) grad_env
          (grad d:Matrix float n m):
      fully_closed_over 
        df
        (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve)
             σ) ->
      vartlookup grad_env (s, DTfloat) <> None ->
      (forall (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) ,
          (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                  (scalarMult (DTMatrix n m) (grad i j) 
                                              (UnitMatrix n m i j))) = 
          Some (d i j)) ->
      df_eval_backprop_delta σ df (s, DTfloat) grad_env grad = 
      Some (msum d).
    Proof.
      intros closed lo fa.
      replace (grad) with (mergeVectorZero n grad (ConstVector m 0%R)).
      - erewrite df_eval_backprop_delta_by_unit_partmat_outer_bounded; try eassumption.
        + now rewrite vfirstn_eq.
        + intros i.
          specialize (fa i).
          simpl in fa.
          replace (grad i) with (mergeVectorZero m (grad i) 0%R).
          2: {
            unfold mergeVectorZero; simpl; apply functional_extensionality; intros; destruct x.
            simpl.
            match_destr; lia.
          }

          erewrite (df_eval_backprop_delta_by_unit_partmat_inner_bounded m (le_refl m) σ df s grad_env)
          ; try eassumption.
          * now rewrite vfirstn_eq.
          * intros j.
            specialize (fa j); simpl in *.
            rewrite <- fa.
            f_equal.
            do 2 (apply functional_extensionality; intros).
            unfold scaleUnitVector, ConstVector, UnitMatrix; simpl.
            repeat match_destr; lra.
      - apply functional_extensionality; unfold mergeVectorZero; intros [x pff]; simpl.
        destruct (lt_dec x n); trivial; lia.
        Unshelve.
        lia.
    Qed.

    Lemma df_eval_backprop_delta_by_unit_parts_mat {n m} 
          (σ:df_env) (df:DefinedFunction UnitAnn (DTMatrix n m)) (s: SubVar) grad_env
          (d:Matrix float n m):
      fully_closed_over 
        df
        (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve)
             σ) ->
      vartlookup grad_env (s, DTfloat) <> None ->
      
      (forall (i : {n' : nat | n' < n})  (j : {m' : nat | m' < m}) ,
          (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                                  
                                  (UnitMatrix n m i j)) = Some (d i j)) ->
      (df_eval_backprop_delta σ df (s, DTfloat) grad_env
                              (ConstMatrix n m 1%R)) = Some (msum d).
    Proof.
      intros.
      apply df_eval_backprop_delta_by_unit_partmat; trivial.
      intros.
      rewrite scalarMult_backprop_grad_scalar with (grad_env2 := grad_env); trivial.
      unfold lift.
      rewrite H1.
      f_equal.
      unfold scalarMult, ConstMatrix; simpl; lra.
      apply backprop_deriv_fully_closed_not_none; trivial.
      apply backprop_deriv_fully_closed_not_none; trivial.      
    Qed.
    
    Corollary scalarMult_backprop_list_env_iter_grad0 {T} (σ:df_env) (s: SubVar) (grad_env :df_env) (grad : definition_function_types_interp T) old n x l :
          let v := (s, DTfloat) in
          (forall j : {n' : nat | n' < n},
              fully_closed_over (x j)
                                (map (fun ve : {v : var_type & definition_function_types_interp (snd v)} => projT1 ve) σ)) ->
      vartlookup grad_env v = Some old -> 
      lift (fun e => subvar v e old)
           (list_env_iter
              (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                 df_eval_backprop_deriv (Ann:=UnitAnn) σ (x i) env (scalarMult T 0%R grad)) (Some grad_env) l) = Some 0%R.
    Proof.
      simpl; intros.
      revert grad_env old H0.
      induction l; simpl; intros.
      - unfold subvar; simpl.
        rewrite H0; f_equal.
        lra.
      - unfold lift in *.
        case_eq (df_eval_backprop_deriv σ (x a) grad_env (scalarMult T 0%R grad))
        ; intros.
        + apply IHl.
          * generalize (scalarMult_backprop_grad0 σ (x a) s grad_env grad); intros HH.
            simpl in HH.
            cut_to HH; try congruence.
            unfold df_eval_backprop_delta in HH.
            rewrite H0 in HH.
            rewrite H1 in HH.
            simpl in HH.
            invcs HH.
            unfold subvar in H3; simpl in H3.
            simpler2.
            rewrite eqq in eqq0; invcs eqq0; subst.
            f_equal.
            lra.
        + eelim backprop_deriv_fully_closed_not_none; eauto.
    Qed.

    Lemma list_env_iter_gen_delta0 {n}  (s: SubVar) (init_env : df_env)
          (f:  {n' : nat | n' < n} -> df_env -> option df_env) (l : list {n' : nat | n' < n}):
      let v := (s,DTfloat) in 
      vartlookup init_env v <> None ->
      (forall (i :  {n' : nat | n' < n}) (env : df_env),
          (f i env) <> None /\
          (vartlookup env v <> None -> 
           match f i env with
           | Some xenv => vartlookup xenv v <> None
           | _ => True
           end ) /\
          (In i l -> vartlookup env v <> None ->
           lift2  (fun e val => subvar v e val) (f i env) 
                  (vartlookup env v) = Some 0%R)) -> 
           lift2 (fun e old => subvar v e old) 
                 (list_env_iter f (Some init_env) l)
                 (vartlookup init_env v) = Some 0%R.
      Proof.
        simpl; intros.
        revert init_env H H0.
        induction l.
        - intros.
          simpl; f_equal.
          unfold subvar; simpl.
          match_option; [|tauto].
          f_equal.
          lra.
        - intros.
          assert (H0c := H0).
          specialize (H0 a init_env).
          destruct H0; destruct H1.
          simpl.
          case_eq (f a init_env); [intros|tauto].
          specialize (IHl d).
          replace (vartlookup init_env (s, DTfloat)) with (vartlookup d (s, DTfloat)).
          + apply IHl.
            * specialize (H1 H).
              now rewrite H3 in H1.
            * intros.
              specialize (H0c i env).
              destruct H0c; destruct H5.
              split; trivial.
              split; trivial.
              intros.
              cut_to H6; trivial.
              simpl; tauto.
          + case_eq (vartlookup init_env (s, DTfloat)); [intros|tauto].
            rewrite H3, H4 in H2; simpl in H2.
            cut_to H2; try tauto.
            unfold lift2 in H2; simpl in H2.
            inversion H2.
            unfold subvar in H6; simpl in H6.
            rewrite H3 in H1.
            specialize (H1 H).
            case_eq ( vartlookup d (s, DTfloat)); [intros|tauto].
            rewrite H5 in H6.
            f_equal; lra.
            congruence.
       Qed.

    Lemma list_env_iter_gen_delta {n}  (s: SubVar) (init_env : df_env) (old : float)
          (f:  {n' : nat | n' < n} -> df_env -> option df_env) (i0 :  {n' : nat | n' < n}):
      let v := (s,DTfloat) in 
      vartlookup init_env v = Some old ->
      (forall (i :  {n' : nat | n' < n}) (env : df_env),
          (f i env) <> None /\
          (vartlookup env v <> None -> 
           match f i env with
           | Some xenv => vartlookup xenv v <> None
           | _ => True
           end ) /\
          (forall (env2 : df_env),
              match vartlookup env v, vartlookup env2 v, f i env, f i env2 with
              | Some val1, Some val2, Some xenv, Some xenv2 =>
                subvar v xenv val1 = subvar v xenv2 val2
              | _, _, _, _ => True
              end) /\
          ( i <> i0 -> vartlookup env v <> None ->
            lift2  (fun e val => subvar v e val) (f i env) 
                    (vartlookup env v) = Some 0%R)) ->
      lift (fun e => subvar v e old) (f i0 init_env) = 
      lift (fun e => subvar v e old) 
           (list_env_iter f 
                          (Some init_env) (bounded_seq0 n)).
    Proof.
      simpl; intros.
      unfold bounded_seq0.
      destruct (bounded_seq_break_at 0 n i0) as [b [c [eqq1 [fa1 fa2]]]]; [lia |].
      rewrite eqq1.
      rewrite list_env_iter_app; simpl.
      match_option.
      -
        assert (eqq': subvar (s, DTfloat) d old = 0%R).
        + generalize (list_env_iter_gen_delta0 s init_env f b); intros.
          simpl in H1.
          cut_to H1; try congruence.
          * unfold lift2 in H1.
            rewrite H, eqq in H1.
            now inversion H1.
          * intros.
            specialize (H0 i env).
            destruct H0; destruct H2; destruct H3.
            split; trivial.
            split; trivial.
            intros.
            cut_to H4; trivial.
            rewrite Forall_forall in fa1.
            specialize (fa1 i H5).
            intro eq1; rewrite eq1 in fa1; lia.
        + generalize (vartlookup_list_env_iter s f b); intros vart.
          * specialize (vart init_env d eqq).
            assert (vartinit: vartlookup init_env (s, DTfloat) <> None) by congruence.
            specialize (vart vartinit).
            assert (f i0 d <> None) by apply H0.
            case_eq (f i0 d); [intros | tauto].
            generalize (list_env_iter_gen_delta0 s d0 f c); simpl; intros.
            cut_to H3; try congruence.
            -- unfold lift at 2.
               unfold lift2 in H3.
               match_option.
               ++ rewrite eqq0 in H3.
                  match_option_in H3.
                  rewrite (split_subvar d0 d1 old d2);trivial.
                  inversion H3.
                  rewrite H5.
                  unfold lift.
                  match_option.
                  ** f_equal.
                     case_eq (vartlookup d (s, DTfloat)); intros.
                     --- rewrite (split_subvar d d0 old d4); trivial.
                         rewrite eqq'.
                         specialize (H0 i0 init_env).
                         destruct H0; destruct H6; destruct H7.
                         specialize (H7 d).
                         rewrite H, H4, eqq3, H2 in H7.
                         rewrite H7; lra.
                     --- cut_to vart; [tauto|].
                         intros.
                         specialize (H0 i env).
                         destruct H0; destruct H8.
                         specialize (H8 H7).
                         now rewrite H6 in H8.
                  ** specialize (H0 i0 init_env).
                     destruct H0; congruence.
               ++ generalize (list_env_iter_total_fun f d0 c); intros.
                  cut_to H4; try congruence.
                  apply H0.
            -- cut_to vart.
               ++ specialize (H0 i0 d).
                  destruct H0; destruct H4.
                  rewrite H2 in H4.
                  apply H4; trivial.
               ++ intros.
                  specialize (H0 i env).
                  destruct H0;destruct H6.
                  specialize (H6 H5).
                  now rewrite H4 in H6.
            -- intros.
               specialize (H0 i env).
               split.
               apply H0.
               split.
               apply H0.
               intros.
               assert (i <> i0).
               ++ rewrite Forall_forall in fa2.
                  specialize (fa2 i H4).
                  intro eq1; rewrite eq1 in fa2; lia.
               ++ now apply H0.
        - generalize (list_env_iter_total_fun f init_env b); intros.
          cut_to H1; trivial.
          tauto.
          intros.
          apply H0.
    Qed.

    Lemma list_env_iter_vec_delta {n} (σ:df_env) 
          (x:Vector (DefinedFunction UnitAnn DTfloat) n) (s: SubVar) grad_env
          (i0 :  {n' : nat | n' < n}) (old : float) :
      let v := (s, DTfloat) in 
      vartlookup grad_env v = Some old ->
      (forall (j: {n' : nat | n' < n}) ,
          let vl := map (fun ve => projT1 ve) σ in
          fully_closed_over (x j) vl) -> 
      lift (fun e => subvar v e old) 
           (df_eval_backprop_deriv σ (x i0) grad_env 1%R) = 
      lift (fun e => subvar v e old) 
           (list_env_iter
              (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                 df_eval_backprop_deriv σ (x i) env (UnitVector n i0 i))
              (Some grad_env) (bounded_seq0 n)).
      Proof.
          simpl; intros.
          generalize (list_env_iter_gen_delta 
                        s grad_env old
                        (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                           df_eval_backprop_deriv σ (x i) env (UnitVector n i0 i)) 
                        i0).
          simpl; intros.
          specialize (H1 H).
          rewrite <- H1.
          - unfold UnitVector; simpl.
            now destruct (equiv_dec (` i0) (` i0)); [|congruence].
          - clear H1.
            intros.
            split; [|split].
            + apply backprop_deriv_fully_closed_not_none; auto.
            + intros.
              match_option.
              now apply df_eval_backprop_deriv_preserves_lookup_not_none with (xv := (s,DTfloat)) in eqq;trivial.
            + split.
              * intros.
                do 4 match_option.
                generalize (backprop_indep_env σ (x i) s env env2 
                                               (UnitVector n i0 i)); simpl; intros HH.
                cut_to HH; trivial; try congruence.
                unfold df_eval_backprop_delta in HH.
                rewrite eqq,eqq0,eqq1,eqq2 in HH.
                unfold lift in HH.
                now inversion HH.
              * intros.
                unfold UnitMatrix; simpl.
                destruct (equiv_dec (` i) (` i0)).
                elim H1; destruct i; destruct i0; simpl in *; red in e; subst; apply index_pf_irrel.
                unfold lift2.
                generalize (scalarMult_backprop_grad0 σ (x i) s env 0%R); simpl; intros.
                unfold df_eval_backprop_delta in H3.
                specialize (H3 H2).
                replace (0 * 0)%R with 0%R in H3 by lra.
                match_option.
                match_option; [|tauto].
                -- rewrite eqq0 in H3.
                   replace (UnitVector n i0 i) with Fzero in eqq; simpl in eqq.
                   ++ rewrite eqq in H3; unfold lift in H3.
                      apply H3; congruence.
                   ++ unfold UnitVector; simpl.
                      destruct (equiv_dec (` i) (` i0)); [|trivial].
                      elim H1; destruct i; destruct i0; simpl in *; red in e; subst; apply index_pf_irrel.                      
                -- assert (df_eval_backprop_deriv σ (x i) env (UnitVector n i0 i) <> None).
                   now apply backprop_deriv_fully_closed_not_none.
                   tauto.
      Qed.


   Lemma list_env_iter_backprop_indep_env_vec {m} (σ:df_env) 
          (vecdf: Vector (DefinedFunction UnitAnn DTfloat) m) 
          (s:SubVar) (env env2:df_env) (grad: Vector float m)
          (old1 old2: float) :
      let v := (s, DTfloat) in
      vartlookup env v = Some old1 ->
      vartlookup env2 v = Some old2 ->     
      (let vl := map (fun ve => projT1 ve) σ in
      forall j : {m' : nat | m' < m},
               fully_closed_over (vecdf j) vl) ->
      lift (fun e => subvar (s, DTfloat) e old1)
           (list_env_iter
              (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                 df_eval_backprop_deriv σ (vecdf j) env0 (grad j))
              (Some env) (bounded_seq0 m)) = 
      lift (fun e => subvar (s, DTfloat) e old2)
           (list_env_iter
              (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                 df_eval_backprop_deriv σ (vecdf j) env0 (grad j))
              (Some env2) (bounded_seq0 m)).
    Proof.
      intros.
      subst v.
      revert old1 old2 env env2 H H0.
      induction (bounded_seq0 m).
      - intros.
        simpl.
        unfold subvar; simpl.
        rewrite H, H0.
        f_equal; lra.
      - intros.
        simpl.
        case_eq (df_eval_backprop_deriv σ (vecdf a) env (grad a)); intros.
        case_eq (df_eval_backprop_deriv σ (vecdf a) env2 (grad a)); intros.        
        case_eq (vartlookup d (s, DTfloat)); intros.
        case_eq (vartlookup d0 (s, DTfloat)); intros.        
        + specialize (IHl d1 d2 d d0 H4 H5).
          unfold lift.
          do 2 match_option.
          * rewrite eqq, eqq0 in IHl.
            unfold lift in IHl.
            inversion IHl.
            f_equal.
            rewrite (split_subvar d d3 old1 d1); trivial.
            rewrite (split_subvar d0 d4 old2 d2); trivial.
            rewrite H7.
            generalize (backprop_indep_env 
                          σ (vecdf a) s
                          env env2 (grad a)); simpl; intros.
            cut_to H6; trivial; try congruence.
            unfold df_eval_backprop_delta in H6.
            rewrite H, H0, H2, H3 in H6.
            unfold lift in H6.
            inversion H6.
            rewrite H9; lra.
          * generalize (list_env_iter_total_fun  
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (vecdf j) env0 (grad j))
                      d0 l); intros.
            cut_to H6; [tauto|].
            intros.
            apply backprop_deriv_fully_closed_not_none; auto.
          * generalize (list_env_iter_total_fun  
                          (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                             df_eval_backprop_deriv σ (vecdf j) env0 (grad j))
                          d l); intros.
            cut_to H6; [tauto|].
            intros.
            apply backprop_deriv_fully_closed_not_none; auto.
        + apply df_eval_backprop_deriv_preserves_lookup_not_none with (xv := (s,DTfloat)) in H3
        ;trivial; congruence.
        + apply df_eval_backprop_deriv_preserves_lookup_not_none with (xv := (s,DTfloat)) in H2
        ;trivial; congruence.
        + assert (df_eval_backprop_deriv σ (vecdf a) env2 (grad a) <> None) by
            (apply backprop_deriv_fully_closed_not_none; auto); tauto.
        + assert (df_eval_backprop_deriv σ (vecdf a) env (grad a) <> None) by
            (apply backprop_deriv_fully_closed_not_none; auto); tauto.
    Qed.

    Lemma list_env_iter_mat_delta {n m} (σ:df_env) 
          (x:Matrix (DefinedFunction UnitAnn DTfloat) n m) (s: SubVar) grad_env 
          (i0 :  {n' : nat | n' < n}) 
          (j0 :  {m' : nat | m' < m}) (old : float) :      
      let v := (s, DTfloat) in 
      vartlookup grad_env v = Some old ->
      (forall (i: {n' : nat | n' < n}) (j: {m' : nat | m' < m}) ,
          let vl := map (fun ve => projT1 ve) σ in
          fully_closed_over (x i j) vl) -> 
      lift (fun e => subvar v e old) 
           (df_eval_backprop_deriv σ (x i0 j0) grad_env 1%R) = 
      lift (fun e => subvar v e old) 
           (list_env_iter
              (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                 list_env_iter
                   (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                      df_eval_backprop_deriv 
                        σ (x i j) env0
                        (UnitMatrix n m i0 j0 i j)) (Some env) 
                   (bounded_seq0 m)) (Some grad_env) (bounded_seq0 n)).
      Proof.
      simpl; intros.
      generalize (list_env_iter_gen_delta 
                    s grad_env old
                    (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                       list_env_iter
                         (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                            df_eval_backprop_deriv 
                              σ (x i j) env0
                              (UnitMatrix n m i0 j0 i j)) (Some env) 
                         (bounded_seq0 m)) i0); simpl.
      intros.
      specialize (H1 H).
      rewrite <- H1.
      - clear H1.
        generalize (list_env_iter_gen_delta 
                      s grad_env old
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (x i0 j) env0 (UnitMatrix n m i0 j0 i0 j))
                      j0); simpl.
        intros.
        specialize (H1 H).
        rewrite <- H1.
        + unfold UnitMatrix; simpl.
          destruct (equiv_dec (` i0) (` i0)); [|congruence].
          now destruct (equiv_dec (` j0) (` j0)); [|congruence].
        + clear H1.
          intros.
          split; [|split].
          * apply backprop_deriv_fully_closed_not_none; auto.
          * intros.
            match_option.
            now apply df_eval_backprop_deriv_preserves_lookup_not_none with (xv := (s,DTfloat)) in eqq;trivial.
         * split.
           -- intros.
              do 4 match_option.
              generalize (backprop_indep_env σ (x i0 i) s env env2 
                                             (UnitMatrix n m i0 j0 i0 i)); simpl; intros HH.
              cut_to HH; trivial; try congruence.
              unfold df_eval_backprop_delta in HH.
              rewrite eqq,eqq0,eqq1,eqq2 in HH.
              unfold lift in HH.
              now inversion HH.
           -- intros.
              unfold UnitMatrix; simpl.
              destruct (equiv_dec (` i0) (` i0)); [|congruence].
              destruct (equiv_dec (` i) (` j0)).
              elim H1; destruct i; destruct j0; simpl in *; red in e0; subst; apply index_pf_irrel.
              unfold lift2.
              generalize (scalarMult_backprop_grad0 σ (x i0 i) s env 0%R); simpl; intros.
              unfold lift2.
              replace (0 * 0)%R with 0%R in H3 by lra.
              unfold df_eval_backprop_delta in H3.
              match_option.
              match_option.
              rewrite eqq0, eqq in H3; unfold lift in H3.
              cut_to H3; congruence.
              rewrite eqq0 in H3.
              apply H3; trivial.
              tauto.
              congruence.
              assert (df_eval_backprop_deriv σ (x i0 i) env 0%R <> None).
              apply backprop_deriv_fully_closed_not_none; trivial.
              tauto.
      - split.
        generalize (list_env_iter_total_fun 
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (x i j) env0 (UnitMatrix n m i0 j0 i j))
                      env (bounded_seq0 m)); intros.
        apply H2.
        intros.
        apply backprop_deriv_fully_closed_not_none; trivial.
        split.
        + intros.
          match_option.
          apply (vartlookup_list_env_iter 
                   s (fun (j : {m' : nat | m' < m})
                          (env0 : df_env) =>
                        df_eval_backprop_deriv σ (x i j) env0 (UnitMatrix n m i0 j0 i j))
                   (bounded_seq0 m) env d); trivial.
          intros.
          apply df_eval_backprop_deriv_preserves_lookup_not_none with (xv := (s,DTfloat)) in H3; trivial.
        + split.
          * intros.
            do 4 match_option.
            generalize (list_env_iter_backprop_indep_env_vec 
                          σ (x i) s env env2 
                          (UnitMatrix n m i0 j0 i)
                          d d0); simpl; intros.
            specialize (H2 eqq eqq0).
            specialize (H2 (H0 i)).
            rewrite eqq1, eqq2 in H2.
            unfold lift in H2.
            now inversion H2.
          * intros.
            replace (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                       df_eval_backprop_deriv σ (x i j) env0 (UnitMatrix n m i0 j0 i j))
                    with
                      (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                         df_eval_backprop_deriv σ (x i j) env0 
                                                (scalarMult DTfloat 0%R 0%R)).
            case_eq (vartlookup env (s, DTfloat)); [intros | tauto].
            apply scalarMult_backprop_list_env_iter_grad0; trivial.
            apply functional_extensionality; intros.
            apply functional_extensionality; intros.            
            f_equal.
            unfold scalarMult, UnitMatrix; simpl.
            destruct (equiv_dec (` i) (` i0)).
            red in e.
            elim H2; destruct i; destruct i0; simpl in *; subst.
            apply index_pf_irrel.
            lra.
      Qed.
               
      Lemma list_env_iter_matvec_delta {m n} (σ:df_env) 
          (df2:DefinedFunction UnitAnn (DTVector m)) (s: SubVar) grad_env 
          (i0 :  {n' : nat | n' < n}) 
          (j0 :  {m' : nat | m' < m}) (old : float) :      
      vartlookup grad_env (s, DTfloat) = Some old ->
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df2 vl -> 
      (lift (fun e => subvar (s, DTfloat) e old)
            (df_eval_backprop_deriv 
               σ df2 grad_env 
               (UnitVector m j0)) = 
       (lift (fun e => subvar (s, DTfloat) e old)
             (list_env_iter
                (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                   df_eval_backprop_deriv 
                     σ df2 env
                     ((UnitMatrix n m i0 j0) i))
                (Some grad_env) 
                (bounded_seq0 n)))).
        Proof.
          simpl; intros.
          generalize (list_env_iter_gen_delta 
                        s grad_env old
                        (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                           df_eval_backprop_deriv 
                             σ df2 env
                             ((UnitMatrix n m i0 j0) i))
                        i0).
          simpl; intros.
          specialize (H1 H).
          rewrite <- H1.
          - unfold UnitMatrix, UnitVector; simpl.
            now destruct (equiv_dec (` i0) (` i0)); [|congruence].
          - clear H1.
            intros.
            split; [|split].
            + apply backprop_deriv_fully_closed_not_none; auto.
            + intros.
              match_option.
              now apply df_eval_backprop_deriv_preserves_lookup_not_none with (xv := (s,DTfloat)) in eqq;trivial.
            + split.
              * intros.
                do 4 match_option.
                generalize (backprop_indep_env σ df2 s env env2 
                                               (UnitMatrix n m i0 j0 i)); simpl; intros HH.
                cut_to HH; trivial; try congruence.
                unfold df_eval_backprop_delta in HH.
                rewrite eqq,eqq0,eqq1,eqq2 in HH.
                unfold lift in HH.
                now inversion HH.
              * intros.
                unfold UnitMatrix; simpl.
                destruct (equiv_dec (` i) (` i0)).
                elim H1; destruct i; destruct i0; simpl in *; red in e; subst; apply index_pf_irrel.
                unfold lift2.
                generalize (scalarMult_backprop_grad0 σ df2 s env (ConstVector m 0%R)); simpl; intros.
                unfold df_eval_backprop_delta in H3.
                specialize (H3 H2).
                match_option.
                match_option; [|tauto].
                -- rewrite eqq0 in H3.
                   replace (fun i : {n' : nat | n' < m} => (0 * ConstVector m 0 i)%R) with
                       (fun i : {n' : nat | n' < m} => 0%R) in H3.
                   ++ rewrite eqq in H3; unfold lift in H3.
                      apply H3; congruence.
                   ++ apply functional_extensionality; intros.
                      unfold ConstVector; simpl.
                      lra.
                -- assert (df_eval_backprop_deriv σ df2 env (fun _ => 0%R) <> None).
                   apply backprop_deriv_fully_closed_not_none; trivial.
                   tauto.
      Qed.

      Lemma vmap_eta {A B} {n} (f:A->B) (d:Vector A n) : vmap f d = vmap (fun x => f x) d.
      Proof.
        now apply vmap_ext.
      Qed.

      Lemma vsum_eta {n} (d:Vector float n) : vsum d = vsum (fun i => d i).
      Proof.
        now apply vsum_ext.
      Qed.

      Lemma msum_unitvector m n x d1 d0 :
        msum
          (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
             (UnitVector m x i * d1 i j * d0 j)%R) =
        vsum
          (fun j : {n' : nat | n' < n} =>
             (d1 x j * d0 j)%R).
      Proof.
        unfold msum.

        transitivity (
            vsum
              (fun i : {n' : nat | n' < m} =>
                 vsum
                      (fun (j : {m' : nat | m' < n}) => (UnitVector m x i * d1 i j * d0 j)%R))).
        { apply vsum_ext; intros ?.
          now rewrite vmap_nth.
        }
        transitivity (
          vsum
            (fun i : {n' : nat | n' < m} =>
               ((UnitVector m x i * vsum
                 (fun (j : {m' : nat | m' < n}%nat) => d1 i j * d0 j))%R))).
        {
          apply vsum_ext; intros ?.
          rewrite vsum_mult.
          apply vsum_ext; intros ?.
          lra.
        }
        transitivity (
          vsum
            (fun i : {n' : nat | n' < m} =>
               (vsum (fun j : {m' : nat | (m' < n)%nat} => d1 i j * d0 j) * UnitVector m x i)%R)).
        {
          apply vsum_ext; intros ?; lra.
        }
        now rewrite vsum_unitvector.
      Qed.

      Lemma vsum_as_sum {n} (v:Vector float n) : vsum v = fold_right Rplus R0 (vector_to_list v).
      Proof.
        rewrite vsum_alt_eq.
        unfold vector_to_list, vector_fold_right.
        induction n.
        - rewrite vector_fold_right_dep_0; trivial.
        - repeat rewrite vector_fold_right_dep_Sn.
          now rewrite IHn.
      Qed.

      Lemma msum_as_sum {m n} (mat:Matrix float m n) : msum mat = fold_right Rplus R0 (matrix_to_list mat).
      Proof.
        unfold msum, matrix_to_list, matrix_to_list_list.
        transitivity
          (vsum (fun i => fold_right Rplus R0 (vector_to_list (mat i)))).
        { apply vsum_ext; intros [??].
          now rewrite vmap_nth, vsum_as_sum.
        }
        rewrite vsum_as_sum.
        rewrite fold_right_plus_concat.
        rewrite map_vector_to_list_vmap.
        f_equal.
        apply vector_to_list_ext.
        intros [??].
        now rewrite vmap_nth.
      Qed.
      
      Lemma transpose_perm_bounded {m n : nat} (mat : Matrix float m n) bound_m pf_m bound_n pf_n:
        Permutation
          (concat
             (vector_fold_right_bounded_dep (fun _ : nat => Datatypes.cons) []
                                            (fun i : {n' : nat | n' < m} =>
                                               vector_fold_right_bounded_dep (fun _ : nat => Datatypes.cons) [] (mat i) bound_n pf_n) bound_m pf_m))
          (concat
             (vector_fold_right_bounded_dep (fun _ : nat => Datatypes.cons) []
                                            (fun i : {n' : nat | n' < n} =>
                                               vector_fold_right_bounded_dep (fun _ : nat => Datatypes.cons) [] (transpose mat i) bound_m pf_m) bound_n pf_n)).
      Proof.
        Hint Constructors Permutation.
        revert bound_n pf_n.
        induction bound_m; intros; simpl.
        - induction bound_n; simpl; trivial.
        - rewrite IHbound_m.
          clear IHbound_m.
          induction bound_n; simpl; trivial.
          rewrite <- IHbound_n.
          clear IHbound_n.
          apply Permutation_cons; trivial.
          unfold transpose; simpl.
          repeat rewrite <- app_ass.
          apply Permutation_app; trivial.
          apply Permutation_app_comm.
      Qed.
    
      Lemma transpose_perm {m n} (mat : Matrix float m n) :
        Permutation (matrix_to_list mat) (matrix_to_list (transpose mat)).
      Proof.
        apply transpose_perm_bounded.
      Qed.
      
      Lemma msum_transpose {m n} (mat : Matrix float m n) :
        msum mat = msum (transpose mat).
      Proof.
        repeat rewrite msum_as_sum.
        apply fold_right_perm; intros; try lra.
        apply transpose_perm.
      Qed.

    Ltac match_nested_case :=
      match goal with
      | [|- context[match match ?x with _ => _ end with _ => _ end]] =>
        let eqq := fresh "eqq" in
        case_eq x
        ; [intros ? eqq | intros eqq]
      end.

    Ltac match_nested_case_in H :=
      match H with
      | context[match match ?x with _ => _ end with _ => _ end] =>
        let eqq := fresh "eqq" in
        case_eq x
        ; [intros ? eqq | intros eqq]
        ; rewrite eqq in H
      end.

    Theorem df_eval_deriv_genvar_same (σ:df_env) (df:DefinedFunction UnitAnn DTfloat) (v:SubVar) :
      let vl := map (fun ve => projT1 ve) σ in
      is_scalar_function df ->
      fully_closed_over df vl -> 
      let forward := df_eval_deriv_gen_top σ df (v, DTfloat) in
      lift transpose_lifted_type forward = df_eval σ (df_deriv df (v,DTfloat)).
    Proof.
     simpl.
     intros is_scalar.
     generalize is_scalar.
     pattern df.
     revert df is_scalar.
     DefinedFunction_scalar_cases (apply is_scalar_function_ind) Case; simpl; trivial; intros
     ; try
       (  cut_to H; trivial
       ;rewrite <- H
       ;assert (df_eval σ e <> None) by (apply eval_fully_closed_not_none; trivial)
       ;unfold lift, df_eval_deriv_gen_top; simpl
       ;match_nested_case; [|tauto]
       ;now match_nested_case).

     - Case "Var"%string.
       match_nested_case.
       + red in e.
         inversion e; subst.
         now refl_simpler; simpl.
       + now intros.
     - Case "Plus"%string.
       destruct H1.
       destruct is_scalar.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold lift, df_eval_deriv_gen_top in *; simpl in *.
       match_option_in H.
       + match_option_in H0.                       
         * rewrite <- H.
           now rewrite <- H0.
         * assert ( df_eval_deriv_genvar σ r [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
           apply eval_deriv_genvar_fully_closed_not_none; trivial.
       + assert (df_eval_deriv_genvar σ l [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
         apply eval_deriv_genvar_fully_closed_not_none; trivial.
     - Case "Minus"%string.
       destruct H1.
       destruct is_scalar.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold lift, df_eval_deriv_gen_top in *; simpl in *.
       match_option_in H.
       + match_option_in H0.                       
         * rewrite <- H.
           now rewrite <- H0.
         * assert ( df_eval_deriv_genvar σ r [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
           apply eval_deriv_genvar_fully_closed_not_none; trivial.
       + assert (df_eval_deriv_genvar σ l [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
         apply eval_deriv_genvar_fully_closed_not_none; trivial.
     - Case "Times"%string.
       destruct H1.
       destruct is_scalar.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold lift, df_eval_deriv_gen_top in *; simpl in *.
       match_nested_case; trivial.
       match_option_in H.
       + match_nested_case.
         * match_option_in H0.
           -- rewrite <- H.
              now rewrite <- H0.
           -- assert ( df_eval_deriv_genvar σ r [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
              apply eval_deriv_genvar_fully_closed_not_none; trivial.
         * assert (df_eval σ r <> None)
           ; [apply eval_fully_closed_not_none; trivial | tauto].
       + assert (df_eval_deriv_genvar σ l [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
         apply eval_deriv_genvar_fully_closed_not_none; trivial.
     - Case "Divide"%string.
       destruct H1.
       destruct is_scalar.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold lift, df_eval_deriv_gen_top in *; simpl in *.
       match_nested_case; trivial.
       match_option_in H.
       + match_nested_case.
         * match_option_in H0.
           -- rewrite <- H.
              now rewrite <- H0.
           -- assert ( df_eval_deriv_genvar σ r [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
              apply eval_deriv_genvar_fully_closed_not_none; trivial.
         * assert (df_eval σ r <> None)
           ; [apply eval_fully_closed_not_none; trivial | tauto].
       + assert (df_eval_deriv_genvar σ l [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
         apply eval_deriv_genvar_fully_closed_not_none; trivial.
       + assert (df_eval σ l <> None)
           ; [apply eval_fully_closed_not_none; trivial | tauto].
     - Case "Sign"%string.
       unfold lift, df_eval_deriv_gen_top in *; simpl in *.
       match_nested_case; [trivial|].
       assert (df_eval_deriv_genvar σ e [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
       apply eval_deriv_genvar_fully_closed_not_none; trivial.
     - Case "PSign"%string.
       unfold lift, df_eval_deriv_gen_top in *; simpl in *.
       match_nested_case; [trivial|].
       assert (df_eval_deriv_genvar σ e [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
       apply eval_deriv_genvar_fully_closed_not_none; trivial.
     - Case "Max"%string.
       destruct is_scalar; destruct H1.
       cut_to H; trivial.
       cut_to H0; trivial.
       unfold lift, df_eval_deriv_gen_top in *; simpl in *.
       assert (df_eval σ l <> None) by (apply eval_fully_closed_not_none; trivial).
       assert (df_eval σ r <> None) by (apply eval_fully_closed_not_none; trivial).
       match_nested_case; [|tauto].
       match_nested_case; [|tauto].
       match_option_in H.
       match_option_in H0.
       + rewrite <- H.
         rewrite <- H0.
         unfold pos_sign; simpl.
         case_eq (Rle_dec d d0); intros; f_equal.
         destruct (Rge_dec (d0 - d) 0); lra.
         destruct (Rge_dec (d0 - d) 0); lra.        
       + assert (df_eval_deriv_genvar σ r [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
         apply eval_deriv_genvar_fully_closed_not_none; trivial.
       + assert (df_eval_deriv_genvar σ l [mk_env_entry (v, DTfloat) 1%R] <> None); [|tauto].
         apply eval_deriv_genvar_fully_closed_not_none; trivial.
    Qed.

    Lemma yay {T} (σ:df_env) (df:DefinedFunction UnitAnn T) (hs:has_scalar_functions df) (s: SubVar) grad_env :
      let v := (s, DTfloat) in 
      vartlookup grad_env v <> None ->
      let vl := map (fun ve => projT1 ve) σ in
      fully_closed_over df vl -> 
      let forward := df_eval_deriv_gen_top σ df v in
      let backward := df_eval_backward_gen_top σ df v grad_env in
      lift transpose_lifted_type forward = backward.
    Proof.
      simpl.
      intros vin closed.
      revert grad_env vin closed.
      unfold df_eval_deriv_gen_top, df_eval_backward_gen_top.
      pattern T, df.
      revert T df hs.
      DefinedFunction_cases (apply DefinedFunction_ind_unit_has_scalar_functions) Case
      ; simpl; intros.
      - Case "Number"%string.
         unfold subvar; simpl.
         match_destr; [ | tauto].
         f_equal; lra.
       - Case "Constant"%string.
         unfold subvar; simpl.
         match_destr; simpl.
         + match_destr; [ | tauto].
           f_equal; lra.
         + match_destr; [ | tauto].
           erewrite vectoro_to_ovector_forall_some_b_strong
           ; simpl; trivial; intros.
           unfold ConstVector.
           f_equal; lra.
         + match_destr; [ | tauto].
          unfold matrixo_to_omatrix.
          repeat (erewrite vectoro_to_ovector_forall_some_b_strong
                  ; simpl; trivial; intros).
           unfold ConstMatrix.
           f_equal; lra.
       - Case "DVector"%string.
         unfold lift, two_vector_env_iter_alt.
         case_eq (vartlookup grad_env (s, DTfloat)); [intros|tauto].
         match_option.
         + specialize (apply vectoro_to_ovector_forall_some_f eqq); intros.
           symmetry.
           apply vectoro_to_ovector_forall_some_b_strong; intros.
           unfold snd in H.
           specialize (H i grad_env); simpl in H.
           rewrite vforall_forall in closed.
           assert (closedb := closed).
           specialize (closed i).
           specialize (H vin closed); simpl in H.
           rewrite H0 in H.
           specialize (H1 i); simpl in H1.
           rewrite H1 in H; simpl in H.
           unfold lift in H.
           match_option_in H.
           specialize (apply vectoro_to_ovector_forall_some_f eqq); intros.
           specialize (H2 i); simpl in H2.
           destruct i; simpl.
           unfold UnitVector; simpl.
           generalize (list_env_iter_total_fun
                         (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                            df_eval_backprop_deriv σ (x i) env 
                                                   (if equiv_dec (` i) x0 then 1%R else 0%R))
                         grad_env (bounded_seq0 n)); intros.
           cut_to H3.
           match_option; [|tauto].
           * rewrite H.
             generalize (list_env_iter_vec_delta σ x s grad_env
                                                 (exist (fun n' : nat => n' < n) x0 l) d).
             intros.
             simpl in H4.
             specialize (H4 H0 closedb).
             rewrite eqq0 in H4.
             unfold UnitVector in H4; simpl in H4.
             rewrite eqq1 in H4.
             unfold lift in H4.
             symmetry; trivial.
           * intros.
             apply backprop_deriv_fully_closed_not_none.
             apply closedb.
         + specialize (vectoro_to_ovector_exists_None eqq); intros.
           destruct H1.
           generalize (eval_deriv_genvar_fully_closed_not_none σ (x x0) [mk_env_entry (s, DTfloat) 1%R]); intros.
           rewrite vforall_forall in closed.
           now specialize (H1 (closed x0)).
       - Case "DMatrix"%string.
         unfold lift, matrixo_to_omatrix.
         case_eq (vartlookup grad_env (s, DTfloat)); [intros|tauto].         
         match_option.
         + specialize (apply vectoro_to_ovector_forall_some_f eqq); intros.
           symmetry.
           apply vectoro_to_ovector_forall_some_b_strong; intros.
           apply vectoro_to_ovector_forall_some_b_strong; intros.           
           specialize (H1 i); simpl in H1.
           specialize (apply vectoro_to_ovector_forall_some_f H1); intros.           
           specialize (H2 i0); simpl in H2.
           unfold two_matrix_env_iter_alt.
           specialize (H i i0 grad_env); simpl in H.
           rewrite vforall_forall in closed.
           assert (closedb := closed).
           specialize (closed i). 
           rewrite vforall_forall in closed.
           specialize (closed i0).           
           specialize (H vin closed); simpl in H.
           rewrite H2 in H; simpl in H.
           rewrite H0 in H; simpl in H.
           unfold lift in H.
           match_option_in H.
           rewrite H.
           destruct i.
           destruct i0.
           unfold lift; simpl.
           generalize (list_env_iter_total_fun
                         (fun (i : {n' : nat | n' < n}) (env : df_env) =>
                            list_env_iter
                              (fun (j : {m' : nat | m' < m}) (env0 : df_env) =>
                                 df_eval_backprop_deriv 
                                   σ (x i j) env0
                                   (UnitMatrix n m (exist (fun n' : nat => n' < n) x0 l)
                                               (exist (fun n' : nat => n' < m) x1 l0) i j)) 
                              (Some env) 
                              (bounded_seq0 m))
                         grad_env (bounded_seq0 n)); intros.
           cut_to H3.
           match_option; [|tauto].
           * generalize (list_env_iter_mat_delta σ x s grad_env
                                                 (exist (fun n' : nat => n' < n) x0 l)
                                                 (exist (fun n' : nat => n' < m) x1 l0) d).
             intros.
             simpl in H4.
             specialize (H4 H0).
             cut_to H4.
             rewrite eqq0 in H4.
             rewrite eqq1 in H4.
             unfold lift in H4.
             symmetry; trivial.
             intros.
             specialize (closedb i).
             rewrite vforall_forall in closedb.
             apply closedb.
           * intros.
             apply list_env_iter_total_fun; intros.
             apply backprop_deriv_fully_closed_not_none.
             specialize (closedb a).
             rewrite vforall_forall in closedb.
             apply closedb.
         + specialize (vectoro_to_ovector_exists_None eqq); intros.
           destruct H1.
           specialize (vectoro_to_ovector_exists_None e); intros.
           destruct H1.
           symmetry.
           generalize (eval_deriv_genvar_fully_closed_not_none σ (x x0 x1) [mk_env_entry (s, DTfloat) 1%R]); intros.
           rewrite vforall_forall in closed.
           specialize (closed x0).
           rewrite vforall_forall in closed.
           now specialize (H1 (closed x1)).
       - Case "Var"%string.
         unfold equiv_dec, vart_eqdec; simpl.
         destruct (vart_dec v (s, DTfloat)).
         + destruct v.
           inversion e.
           subst; simpl.
           refl_simpler; simpl.
           case_eq (vartlookup grad_env (s, DTfloat)); [intros |tauto].
           simpl; f_equal.
           symmetry.
           now apply subvar_addvar_scalar_eq.
         + case_eq (vartlookup grad_env (s, DTfloat)); [intros|tauto].
           destruct v.
           unfold snd.
           destruct d0.
           * simpl.
             unfold lift.
             destruct (vartlookup grad_env (s0, DTfloat)).
             -- f_equal; simpl; symmetry.
                now apply subvar_addvar_scalar_neq.
             -- f_equal; symmetry.
                unfold subvar; simpl.
                rewrite H; lra.
           * simpl; symmetry.
             apply vectoro_to_ovector_forall_some_b_strong; intros; unfold lift.
             destruct (vartlookup grad_env (s0, DTVector n0)).
             -- f_equal; simpl.
                unfold ConstVector.
                now apply subvar_addvar_scalar_neq.
             -- f_equal; unfold ConstVector.
                unfold subvar; simpl.
                rewrite H; lra.
           * simpl; symmetry.
             unfold matrixo_to_omatrix.
             apply vectoro_to_ovector_forall_some_b_strong; intros.
             apply vectoro_to_ovector_forall_some_b_strong; intros.
             unfold lift.
             destruct (vartlookup grad_env (s0, DTMatrix m n0)).
             -- f_equal; unfold ConstMatrix.
                now apply subvar_addvar_scalar_neq.             
             -- f_equal; unfold ConstMatrix.
                unfold subvar; simpl.
                rewrite H; lra.
       - Case "Plus"%string.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H.
        case_eq (df_eval_backprop_deriv σ l grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
        destruct closed.
        specialize (H H1).
        invcs H.
        { specialize (H0 d1).
          cut_to H0;
            [| now apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))| apply H2].
          match_option
          ; rewrite eqq2 in H0
          ; simpl in *.
          - match_option_in H0.
            unfold lift in H0.
            match_option_in H0.
            invcs H0.
            simpl.
            f_equal.
            unfold subvar; simpl.
            rewrite eqq3.
            match_option; lra.
          - match_option_in H0; simpl.
            + unfold lift in *.
              match_option_in H0.
            + elim (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat) vin eqq3).
        }
         + destruct closed.
           specialize (H H1).
           congruence.
         + destruct closed.
           specialize (H H1).
           congruence.
         + destruct closed.
           specialize (H H1).           
           case_eq (df_eval_backprop_deriv σ l grad_env 1%R)
           ; [intros ? eqq2 | intros eqq2].
           rewrite eqq2 in H.
           simpl in *.
           congruence.
           rewrite eqq2 in H.
           now apply H.
       - Case "Minus"%string.          
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H.
        case_eq (df_eval_backprop_deriv σ l grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
        invcs H.
        { specialize (H0 d1).
          cut_to H0;
            [| now apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
             | apply H2].
          match_option
          ; rewrite eqq2 in H0
          ; simpl in *.
          - match_option_in H0.
            unfold lift in H0.
            match_option_in H0.
            invcs H0.
            simpl.
            f_equal.
            unfold subvar; simpl.
            rewrite eqq3.
            match_option.
            + case_eq (df_eval_backprop_deriv σ r d1 (- (1))%R); intros.
              * unfold lift.
                f_equal.
                match_option.
                -- generalize (scalarMult_backprop_grad_scalar σ r s d1 d1 1%R (-1)%R)
                   ; intros; simpl in H0.
                   cut_to H0.
                   ++ unfold df_eval_backprop_delta in H0.
                      rewrite eqq3 in H0; unfold lift in H0; simpl in H0.
                      replace (-1 * 1)%R with (- (1))%R in H0 by lra.
                      rewrite H, eqq4 in H0; inversion H0.
                      unfold subvar in H0; simpl in H0.
                      rewrite eqq6, eqq5 in H0.
                      inversion H0.
                      lra.
                  ++ congruence.
                  ++ congruence.
                  ++ simpl; replace (-1 * 1)%R with (- (1))%R by lra; congruence.
                  ++ congruence.
                -- generalize (df_eval_backprop_deriv_preserves_lookup_not_none H (s,DTfloat))
                   ; intros.
                   cut_to H0; congruence.
              * generalize (backprop_deriv_fully_closed_not_none σ r d1 (- (1))%R); intros.
                destruct H0; trivial.
            + generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq4 (s,DTfloat))
              ; intros.
              cut_to H; congruence.
          - match_option_in H0.
            + unfold lift.
              unfold lift in H0.
              match_option_in H0.
              match_option.
              specialize (df_eval_backprop_deriv_preserves_lookup_not_none  eqq5).
              intros.
              specialize (H (s, DTfloat)).
              generalize (backprop_deriv_fully_closed_not_none σ r d1 (1%R)); intros.
              now destruct H3.
           + generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s,DTfloat))
             ; intros.
             cut_to H; congruence.
        } 
         + unfold lift in H; simpl in H.
           match_option_in H.
    - Case "Times"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        generalize (eval_fully_closed_not_none σ r); intros.
        specialize (H5 H2).
        case_eq (df_eval σ r); [intros|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        case_eq (df_eval_backprop_deriv σ l grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
        generalize (scalarMult_backprop_grad_scalar σ l s grad_env grad_env 1%R d1)
        ; intros; simpl in H7.
        unfold df_eval_backprop_delta in H7.
        rewrite eqq1 in H7; simpl in H7.
        specialize (H7 vin vin).
        rewrite eqq0 in H7.
        generalize (backprop_deriv_fully_closed_not_none σ l grad_env (d1 * 1)%R); intros.
        specialize (H8 H1); specialize (H7 H8).
        cut_to H7; try discriminate.
        invcs H.
        { specialize (H0 d3).
          cut_to H0;
            [| now apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
             | apply H2].
           unfold lift in H7; simpl in H7.
           match_option_in H7.
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
           ;intros.
           specialize (H vin).
           generalize (backprop_deriv_fully_closed_not_none σ r d3 1%R); intros.
           specialize (H9 H2).           
           case_eq (vartlookup d3 (s, DTfloat)); [intros | congruence].
           rewrite H10 in H0.
           unfold lift; simpl.
           unfold lift in H0.
           match_option_in H0.
           - generalize (scalarMult_backprop_grad_scalar σ r s d2 d3 1%R d)
             ; intros.
             unfold df_eval_backprop_delta in H11; simpl in H11.
             generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat));intros.
             specialize (H12 vin).
             case_eq (vartlookup d2 (s, DTfloat)); [intros | congruence].
             specialize (H11 H12 H).
             rewrite H10, H13 in H11.
             generalize (backprop_deriv_fully_closed_not_none σ r d2 (d * 1)%R); intros.
             specialize (H14 H2); specialize (H11 H14 H9).
             unfold lift in H11.
             match_option_in H11; [|congruence]; f_equal.
             rewrite (split_subvar d2 d7 d0 d6); trivial.
             match_option_in H0; invcs H0.
             rewrite eqq5 in H11; invcs H11; invcs H7.
             lra.
           - now match_option_in H0.
         }   
        unfold lift in H.
        match_case_in H; intros.
        rewrite H7 in H; congruence.
        generalize (backprop_deriv_fully_closed_not_none σ l grad_env 1%R); intros.        
        now specialize (H8 H1).
     - Case "Divide"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        generalize (eval_fully_closed_not_none σ r); intros.
        specialize (H5 H2).
        case_eq (df_eval σ r); [intros|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        case_eq (df_eval_backprop_deriv σ l grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
        generalize (scalarMult_backprop_grad_scalar σ l s grad_env grad_env 1%R (1 / d1)%R)
        ; intros; simpl in H7.
        unfold df_eval_backprop_delta in H7.
        rewrite eqq1 in H7; simpl in H7.
        specialize (H7 vin vin).
        rewrite eqq0 in H7.
        generalize (backprop_deriv_fully_closed_not_none σ l grad_env (1 / d1 * 1)%R); intros.
        specialize (H8 H1) ; specialize (H7 H8).
        cut_to H7; try discriminate.
        replace (1 / d1 * 1)%R with (1/d1)%R in H7 by lra.
        invcs H.
        { specialize (H0 d3).
          cut_to H0;
            [| now apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
             | apply H2].
           unfold lift in H7; simpl in H7.
           match_option_in H7. 
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
           ;intros.
           specialize (H vin).
           generalize (backprop_deriv_fully_closed_not_none σ r d3 1%R); intros.
           specialize (H9 H2).           
           case_eq (vartlookup d3 (s, DTfloat)); [intros | congruence].
           rewrite H10 in H0.
           unfold lift; simpl.
           unfold lift in H0.
           match_option_in H0.
           - generalize (scalarMult_backprop_grad_scalar σ r s d2 d3 1%R (- d / (d1 * d1))%R)
             ; intros; simpl in H11.
             unfold df_eval_backprop_delta in H11; simpl in H11.
             generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat));intros.
             specialize (H12 vin).
             case_eq (vartlookup d2 (s, DTfloat)); [intros | congruence].
             specialize (H11 H12 H).
             rewrite H10, H13 in H11.
             generalize (backprop_deriv_fully_closed_not_none σ r d2 (- d / (d1 * d1) * 1)%R); intros.
             specialize (H14 H2); specialize (H11 H14 H9).
             unfold lift in H11.
             match_option_in H11; [|congruence]; f_equal.
             rewrite (split_subvar d2 d7 d0 d6); trivial.
             match_option_in H0; invcs H0.
             rewrite eqq5 in H11; invcs H11; invcs H7.
             lra.
           - now match_option_in H0.
         }   
        unfold lift in H.
        match_case_in H; intros.
        rewrite H7 in H; congruence.
        generalize (backprop_deriv_fully_closed_not_none σ l grad_env 1%R); intros.        
        now specialize (H8 H1).
      - Case "Square"%string.
        specialize (H grad_env vin closed).
        simpl in *.
        generalize (eval_fully_closed_not_none σ e); intros.
        specialize (H0 closed).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        + case_eq (df_eval_backprop_deriv σ e grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
          generalize (scalarMult_backprop_grad_scalar σ e s grad_env grad_env 1%R (2 * d)%R)
          ; intros; simpl in H2.
          unfold df_eval_backprop_delta in H2.
          rewrite eqq1 in H2; simpl in H2.
          specialize (H2 vin vin).
          rewrite eqq0 in H2.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env (2 * d * 1)%R); intros.
          specialize (H3 closed); specialize (H2 H3).
          cut_to H2; try discriminate.
          invcs H.
          unfold lift in H2; match_option_in H2.
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
          ;intros.
          unfold lift; now rewrite H2.
        + unfold lift in H.
          match_case_in H; intros.
          rewrite H2 in H; congruence.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env 1%R); intros.        
          now specialize (H3 closed).
      - Case "Exp"%string.
        specialize (H grad_env vin closed).
        simpl in *.
        generalize (eval_fully_closed_not_none σ e); intros.
        specialize (H0 closed).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        + case_eq (df_eval_backprop_deriv σ e grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
          generalize (scalarMult_backprop_grad_scalar σ e s grad_env grad_env 1%R (exp d)%R)
          ; intros; simpl in H2.
          unfold df_eval_backprop_delta in H2.
          rewrite eqq1 in H2; simpl in H2.
          specialize (H2 vin vin).
          rewrite eqq0 in H2.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env (exp d * 1)%R); intros.
          specialize (H3 closed); specialize (H2 H3).
          cut_to H2; try discriminate.
          invcs H.
          replace (1 * exp d)%R with (exp d * 1)%R by lra.
          unfold lift in H2; match_option_in H2.
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
          ;intros.
          unfold lift; rewrite H2.
          f_equal; lra.
        + unfold lift in H.
          match_case_in H; intros.
          rewrite H2 in H; congruence.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env 1%R); intros.        
          now specialize (H3 closed).
      - Case "Log"%string.
        specialize (H grad_env vin closed).
        simpl in *.
        generalize (eval_fully_closed_not_none σ e); intros.
        specialize (H0 closed).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        + case_eq (df_eval_backprop_deriv σ e grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
          generalize (scalarMult_backprop_grad_scalar σ e s grad_env grad_env 1%R (1 / d)%R)
          ; intros; simpl in H2.
          unfold df_eval_backprop_delta in H2.
          rewrite eqq1 in H2; simpl in H2.
          specialize (H2 vin vin).
          rewrite eqq0 in H2.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env (1 / d * 1)%R); intros.
          specialize (H3 closed); specialize (H2 H3).
          cut_to H2; try discriminate.
          invcs H.
          replace (1 / d)%R with (1 /  d * 1)%R by lra.
          unfold lift in H2; match_option_in H2.
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
          ;intros.
          unfold lift; rewrite H2.
          f_equal; lra.
        + unfold lift in H.
          match_case_in H; intros.
          rewrite H2 in H; congruence.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env 1%R); intros.        
          now specialize (H3 closed).
      - Case "Abs"%string.
        specialize (H grad_env vin closed).
        simpl in *.
        generalize (eval_fully_closed_not_none σ e); intros.
        specialize (H0 closed).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        + case_eq (df_eval_backprop_deriv σ e grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
          generalize (scalarMult_backprop_grad_scalar σ e s grad_env grad_env 1%R (sign d)%R)
          ; intros; simpl in H2.
          unfold df_eval_backprop_delta in H2.
          rewrite eqq1 in H2; simpl in H2.
          specialize (H2 vin vin).
          rewrite eqq0 in H2.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env (sign d * 1)%R); intros.
          specialize (H3 closed); specialize (H2 H3).
          cut_to H2; try discriminate.
          invcs H.
          replace (1 * (@sign floatish_R d))%R with ((@sign floatish_R d) * 1)%R by lra.
          unfold lift in H2; match_option_in H2.
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
          ;intros.
          unfold lift; rewrite H2.
          f_equal; lra.
        + unfold lift in H.
          match_case_in H; intros.
          rewrite H2 in H; congruence.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env 1%R); intros.        
          now specialize (H3 closed).
      - Case "Sign"%string.        
        specialize (H grad_env vin closed).
        simpl in *.
        generalize (eval_fully_closed_not_none σ e); intros.
        specialize (H0 closed).
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        + case_eq (df_eval_backprop_deriv σ e grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
          generalize (scalarMult_backprop_grad_scalar σ e s grad_env grad_env 1%R (0)%R)
          ; intros H1; simpl in H1.
          unfold df_eval_backprop_delta in H1.
          rewrite eqq1 in H1; simpl in H1.
          specialize (H1 vin vin).
          rewrite eqq0 in H1.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env (0 * 1)%R); intros.
          specialize (H2 closed); specialize (H1 H2).
          cut_to H1; try discriminate.
          invcs H.
          replace (0)%R with (0 * 1)%R by lra.
          unfold lift in H1; match_option_in H1.
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
          ;intros.
          unfold lift; rewrite H1.
          f_equal; lra.
        + unfold lift in H.
          match_case_in H; intros.
          rewrite H1 in H; congruence.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env 1%R); intros.        
          now specialize (H2 closed).
      - Case "PSign"%string.        
        specialize (H grad_env vin closed).
        simpl in *.
        generalize (eval_fully_closed_not_none σ e); intros.
        specialize (H0 closed).
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        + case_eq (df_eval_backprop_deriv σ e grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
          generalize (scalarMult_backprop_grad_scalar σ e s grad_env grad_env 1%R (0)%R)
          ; intros H1; simpl in H1.
          unfold df_eval_backprop_delta in H1.
          rewrite eqq1 in H1; simpl in H1.
          specialize (H1 vin vin).
          rewrite eqq0 in H1.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env (0 * 1)%R); intros.
          specialize (H2 closed); specialize (H1 H2).
          cut_to H1; try discriminate.
          invcs H.
          replace (0)%R with (0 * 1)%R by lra.
          unfold lift in H1; match_option_in H1.
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
          ;intros.
          unfold lift; rewrite H1.
          f_equal; lra.
        + unfold lift in H.
          match_case_in H; intros.
          rewrite H1 in H; congruence.
          generalize (backprop_deriv_fully_closed_not_none σ e grad_env 1%R); intros.        
          now specialize (H2 closed).
      - Case "Max"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        specialize (H0 grad_env vin H2).        
        simpl in *.
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        generalize (eval_fully_closed_not_none σ r); intros.
        specialize (H5 H2).
        case_eq (df_eval σ r); [intros|tauto].
        rewrite eqq0 in H.
        rewrite eqq0 in H0.        
        destruct (Rle_dec d d1).
        + apply H0.
        + apply H.
      - Case "VectorDot"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        generalize (eval_fully_closed_not_none σ r); intros.
        specialize (H5 H2).
        case_eq (df_eval σ r); [intros | tauto].
        replace (fun rv : R => (rv * 1)%R) with id.
        rewrite vmap_id; rewrite vmap_id.
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d1 eqq1 | tauto].
        symmetry in H.
        generalize (backprop_deriv_fully_closed_not_none σ l grad_env d0); intros.
        specialize (H7 H1).
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq1 in H.
        specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H8.
        match_option.
        + match_option; [|tauto].
          generalize (backprop_deriv_fully_closed_not_none σ r d4 d); intros.        
          specialize (H9 H2).
          unfold lift.
          match_option; [|tauto].
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat));intros.
          specialize (H10 vin).
          specialize (H0 d4 H10 H2).
          rewrite eqq0 in H0.
          match_option_in H0.
          symmetry in H0.
          unfold lift in H0.
          specialize (apply vectoro_to_ovector_forall_some_f H0); intros.
          simpl in H11.
          f_equal.
          unfold lift in H8.
          rewrite (split_subvar d4 d5 d1 d6); trivial.
          rewrite <- vsum_plus.
          generalize (df_eval_backprop_delta_by_unit_partvec σ l s grad_env d0 
                                                             (fun i => (d2 i * d0 i)%R)); intros.
          specialize (H12 H1 vin).
          generalize (df_eval_backprop_delta_by_unit_partvec σ r s d4 d 
                                                             (fun i => (d i * d3 i)%R)); intros.
          specialize (H13 H2 H10).
          cut_to H12.
          cut_to H13.
          * unfold df_eval_backprop_delta in H12.
            rewrite eqq1 in H12.
            unfold df_eval_backprop_delta in H13.
            rewrite eqq4 in H13.
            unfold lift in H12.
            unfold lift in H13.
            rewrite eqq2 in H12.
            rewrite eqq3 in H13.
            invcs H12; invcs H13.
            rewrite H14, H15; lra.
          * intros.
            replace (@scaleUnitVector (@float floatish_R) n i (d i) (IZR Z0)) with
                (scalarMult (DTVector n) (d i) (UnitVector n i)).
            rewrite scalarMult_backprop_grad_scalar with (grad_env1 := d4) (grad_env2:=d4);trivial.
            unfold df_eval_backprop_delta, lift.
            rewrite eqq4.
            specialize (H11 i).
            destruct i; simpl in H11.
            simpl_closed_backprop.
            f_equal.
            rewrite eqq5 in H11.
            invcs H11.
            rewrite H15.
            now unfold scalarMult; simpl.
            apply backprop_deriv_fully_closed_not_none; trivial.
            apply backprop_deriv_fully_closed_not_none; trivial.            
            unfold scalarMult, UnitVector, scaleUnitVector; simpl.
            apply functional_extensionality; intros.
            destruct (equiv_dec (` x) (` i)); lra.
          * intros.
            replace (@scaleUnitVector (@float floatish_R) n i (d0 i) (IZR Z0)) with
                (scalarMult (DTVector n) (d0 i) (UnitVector n i)). 
            rewrite scalarMult_backprop_grad_scalar with (grad_env1 := grad_env) (grad_env2:=grad_env);trivial.        
            unfold df_eval_backprop_delta, lift.            
            rewrite eqq1.
            specialize (H8 i).
            destruct i; simpl in H8.
            simpl_closed_backprop.
            f_equal.
            rewrite eqq5 in H8.
            invcs H8.
            rewrite H15.
            now unfold scalarMult; simpl; lra.
            apply backprop_deriv_fully_closed_not_none; trivial.
            apply backprop_deriv_fully_closed_not_none; trivial.            
            unfold scalarMult, UnitVector, scaleUnitVector; simpl.
            apply functional_extensionality; intros.
            destruct (equiv_dec (` x) (` i)); lra.
        + generalize (eval_deriv_genvar_fully_closed_not_none σ r [mk_env_entry (s, DTfloat) 1%R]); intros.
          now specialize (H9 H2).
        + generalize (eval_deriv_genvar_fully_closed_not_none σ l [mk_env_entry (s, DTfloat) 1%R]); intros.
          now specialize (H8 H1).
        + apply FunctionalExtensionality.functional_extensionality.
          intros; unfold id; lra.
      - Case "VectorSum"%string.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H closed).
          symmetry in H.
          generalize (vectoro_to_ovector_forall_some_f H); intros HH; clear H.
          replace (@lift (@df_env floatish_R) R
                         (fun e : df_env => subvar (s, DTfloat) e d0)
                         (df_eval_backprop_deriv σ v grad_env
                                                  (ConstVector n 1%R)))
                   with
                     (df_eval_backprop_delta σ v (s, DTfloat) grad_env
                              (ConstVector n 1%R)).
          rewrite df_eval_backprop_delta_by_unit_parts with (d1 := d); trivial.
          * intros.
            specialize (HH i).
            unfold df_eval_backprop_delta.
            rewrite eqq0.
            replace (UnitVector n i) with 
                (coerce
                   (df_eval_backward_gen_top_obligation_2 UnitAnn (DTVector n) v n eq_refl i)
                   (UnitVector n i)); trivial.
            destruct i.
            now simpl.
          * unfold df_eval_backprop_delta.
            now rewrite eqq0.
        + specialize (H closed).
          symmetry in H.
          specialize (vectoro_to_ovector_exists_None H); intros.
          destruct H0.
          unfold lift in e.
          match_option_in e.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ v grad_env
                        (coerce
                           (df_eval_backward_gen_top_obligation_2
                              UnitAnn (DTVector n) v n eq_refl x)
                           (UnitVector n x))); intros.
          specialize (H0 closed); tauto.
      - Case "MatrixSum"%string.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H closed).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros HH; simpl in HH.
          replace (@lift (@df_env floatish_R) R
                         (fun e : df_env => subvar (s, DTfloat) e d0)
                         (df_eval_backprop_deriv σ v grad_env
                                                  (ConstMatrix m n 1%R)))
                   with
                     (df_eval_backprop_delta σ v (s, DTfloat) grad_env
                              (ConstMatrix m n 1%R)).
          rewrite df_eval_backprop_delta_by_unit_parts_mat with (d1 := d); trivial.
          * intros.
            specialize (HH i).
            specialize (apply vectoro_to_ovector_forall_some_f HH); intros.
            specialize (H0 j); simpl in H0.
            unfold df_eval_backprop_delta.
            rewrite eqq0.
            replace (UnitMatrix m n i j) with
                (coerce
                   (df_eval_backward_gen_top_obligation_3 
                      UnitAnn (DTMatrix m n) v m n eq_refl i j) 
                   (UnitMatrix m n i j)); trivial.
            destruct i; destruct j.
            now simpl.
          * unfold df_eval_backprop_delta.
            now rewrite eqq0.
        + specialize (H closed).
          symmetry in H.
          specialize (vectoro_to_ovector_exists_None H); intros.
          destruct H0.
          unfold lift in e.
          specialize (vectoro_to_ovector_exists_None e); intros.
          destruct H0.
          match_option_in e0.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ v grad_env
                        (coerce
                           (df_eval_backward_gen_top_obligation_3 
                              UnitAnn (DTMatrix m n) v m n eq_refl x x0)
                           (UnitMatrix m n x x0))); intros.
          specialize (H0 closed); tauto.
      - Case "VectorElem"%string.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H closed).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H.
          unfold lift.
          replace (fun k : {n' : nat | n' < n} => if equiv_dec (` k) (` i) then 1%R else 0%R)
            with
              (UnitVector n i).
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env (UnitVector n i)); intros.
          specialize (H1 closed).
          specialize (H0 i).
          match_option; symmetry; [|tauto].
          destruct i; simpl in *.
          unfold lift in H0; f_equal.
          rewrite eqq1 in H0.
          now invcs H0.
          unfold UnitVector.
          apply FunctionalExtensionality.functional_extensionality; intros. 
          trivial.
        + specialize (H closed).
          symmetry in H.
          specialize (vectoro_to_ovector_exists_None H); intros.
          destruct H0.
          unfold lift in e.
          match_option_in e.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env
                        (coerce
                           (df_eval_backward_gen_top_obligation_2
                              UnitAnn (DTVector n) l n eq_refl x)
                           (UnitVector n x))); intros.
          specialize (H0 closed); tauto.
      - Case "MatrixElem"%string.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H closed).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H.
          unfold lift.
          replace
            (fun (k1 : {n' : nat | n' < m}) (k2 : {m' : nat | m' < n}) =>
               if equiv_dec (` k1) (` i) then 
                 if equiv_dec (` k2) (` j) then 1%R else 0%R else 0%R)
            with (UnitMatrix m n i j).
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env (UnitMatrix m n i j)); intros.
          specialize (H1 closed).
          specialize (H0 i).
          specialize (apply vectoro_to_ovector_forall_some_f H0); intros; simpl in H2.    
          specialize (H2 j).
          match_option; symmetry; [|tauto].
          destruct i; destruct j; simpl in *.
          unfold lift in H2; f_equal.
          rewrite eqq1 in H2.
          now invcs H2.
          unfold UnitMatrix.
          apply FunctionalExtensionality.functional_extensionality; intros.
          apply FunctionalExtensionality.functional_extensionality; intros.           
          trivial.
        + specialize (H closed).
          symmetry in H.
          specialize (vectoro_to_ovector_exists_None H); intros.
          destruct H0.
          unfold lift in e.
          specialize (vectoro_to_ovector_exists_None e); intros.
          destruct H0.          
          match_option_in e0.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env
                        (coerce
                           (df_eval_backward_gen_top_obligation_3 
                              UnitAnn (DTMatrix m n) l m n eq_refl x x0)
                           (UnitMatrix m n x x0))); intros.
          specialize (H0 closed); tauto.
      - Case "MatrixVectorMult"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        generalize (eval_fully_closed_not_none σ r); intros.
        specialize (H5 H2).
        case_eq (df_eval σ r); [intros | tauto].
        assert (df_eval_deriv_genvar σ l [mk_env_entry (s, DTfloat) 1%R] <> None).
        apply eval_deriv_genvar_fully_closed_not_none; trivial.
        match_option; [|tauto].
        assert (df_eval_deriv_genvar σ r [mk_env_entry (s, DTfloat) 1%R] <> None).
        apply eval_deriv_genvar_fully_closed_not_none; trivial.
        match_option; [|tauto].
        match_option; [|tauto].
        unfold lift.
        symmetry.
        apply vectoro_to_ovector_forall_some_b_strong; intros.
        simpl_closed_backprop.
        simpl_closed_backprop.
        f_equal.
        rewrite eqq1, eqq in H.
        unfold lift in H; symmetry in H.
        specialize (vectoro_to_ovector_forall_some_f H); intros.
        specialize (H0 env).
        simpler2.
        cut_to H0; try congruence.
        rewrite eqq0 in H0.
        rewrite (split_subvar env env0 d3 val); trivial.
        specialize (H9 i); simpl in H9.
        specialize (vectoro_to_ovector_forall_some_f H9); intros.
        replace (@vsum floatish_R n (fun j : {n' : nat | n' < n} => (d i j * d2 j + d1 i j * d0 j)%R))
          with ((vsum (fun j => (d i j * d2 j)%R)) + (vsum (fun j => (d1 i j * d0 j)%R)))%R
        ; [|rewrite vsum_plus; f_equal].
        unfold lift in H0; symmetry in H0.
        specialize (vectoro_to_ovector_forall_some_f H0); intros.        
        simpl in H11; simpl in H10.
        destruct i; simpl in eqq2; simpl in eqq3.
        unfold matrix_vector_mult in eqq3; simpl in eqq3.
        unfold UnitVector in eqq2; simpl in eqq2.
        replace (fun i : {n' : nat | n' < n} =>
                   (@vsum floatish_R m
                          (fun j : {n' : nat | n' < m} =>
                             (d j i * (@UnitVector floatish_R m (exist (fun n' : nat => (n' < m)%nat) x l0)
                                                 j)%R)%R)))
          with (d (exist (fun n' : nat => (n' < m)%nat) x l0)) in eqq3.
        + generalize (df_eval_backprop_delta_by_unit_partvec 
                        σ r s env (d (exist (fun n' : nat => n' < m) x l0 ))  
                        (fun i => ((d (exist (fun n' : nat => (n' < m)%nat) x l0 ) i) * (d2 i))%R))
          ; intros.
          specialize (H12 H2).
          cut_to H12; try congruence.
          * unfold df_eval_backprop_delta in H12.
            rewrite eqq3, eqq4 in H12.
            unfold lift in H12.
            invcs H12.
            apply Rplus_eq_compat_l.
            generalize (df_eval_backprop_delta_by_unit_partmat
                          σ l s grad_env
                          (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                             ((if equiv_dec (` i) x then 1 else 0) * d0 j)%R)
                          (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                             ((if equiv_dec (` i) x then 1 else 0) * (d1 i j) * (d0 j))%R))
            ; intros.
            specialize (H12 H1).
            cut_to H12; try congruence.
            -- unfold df_eval_backprop_delta in H12.
               rewrite eqq1 in H12.
               unfold lift in H12.
               rewrite eqq2 in H12.
               invcs H12.
               rewrite H15.
               replace 
                 (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                    ((if equiv_dec (` i) x then 1 else 0) * d1 i j * d0 j)%R)  with
                   (fun (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}) =>
                      (UnitVector m (exist _ x l0) i * d1 i j * d0 j)%R).
               now rewrite msum_unitvector.
               apply FunctionalExtensionality.functional_extensionality; intros.
               apply FunctionalExtensionality.functional_extensionality; intros.               
               now unfold UnitVector; simpl.
            -- intros.
               rewrite scalarMult_backprop_grad_scalar with (grad_env2:=grad_env)
               ;trivial; try congruence.               
               unfold lift.
               unfold df_eval_backprop_delta.
               rewrite eqq1.
               unfold lift.
               specialize (vectoro_to_ovector_forall_some_f H); intros.
               specialize (H13 i); simpl in H13.
               specialize (vectoro_to_ovector_forall_some_f H13); intros.               
               specialize (H15 j); intros; simpl in H15.
               destruct i; destruct j; simpl in H15.
               match_option_in H15.
               f_equal; simpl.
               destruct (equiv_dec x0 x).
               invcs H15.
               rewrite H17; lra.
               lra.
               apply backprop_deriv_fully_closed_not_none; trivial.
               apply backprop_deriv_fully_closed_not_none; trivial.               
          * intros.
            replace (@scaleUnitVector (@float floatish_R) n i (d (@exist nat (fun n' : nat => lt n' m) x l0) i) (IZR Z0)) with
                    (scalarMult (DTVector n) (d (exist (fun n' : nat => n' < m) x l0) i) (UnitVector n i)). 
            rewrite scalarMult_backprop_grad_scalar with (grad_env1 := env) (grad_env2:=env);trivial; try congruence.
            unfold scalarMult; simpl.
            unfold lift; simpl.
            specialize (H11 i).
            destruct i; simpl in H11.
            match_option_in H11.
            unfold df_eval_backprop_delta.
            rewrite eqq4,eqq5.
            unfold lift; f_equal.
            now invcs H11.
            apply backprop_deriv_fully_closed_not_none; trivial.
            apply backprop_deriv_fully_closed_not_none; trivial.
            unfold scalarMult, scaleUnitVector.
            apply FunctionalExtensionality.functional_extensionality; intros.
            unfold UnitVector.
            destruct (equiv_dec (` x0) (` i)); simpl; lra.
        + apply FunctionalExtensionality.functional_extensionality; intros.
          now rewrite vsum_unitvector.
      - Case "MatrixVectorAdd"%string.
        destruct closed.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H3.
          match_option; symmetry.
          * apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H3 i).
            specialize (apply vectoro_to_ovector_forall_some_f H3); intros; simpl in H4.
            apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H4 i0).
            unfold lift in H4; unfold lift.
            match_option_in H4.
            unfold lift in H0.
            rewrite eqq1 in H0.
            generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat))
            ;intros.
            specialize (H5 vin).
            specialize (H0 d2 H5 H2).
            match_option_in H0.
            symmetry in H0.
            specialize (apply vectoro_to_ovector_forall_some_f H0); intros; simpl in H6.
            specialize (H6 i).
            destruct i; destruct i0;  simpl; simpl in eqq2; simpl in H6.
            rewrite eqq2.
            match_option_in H6.
            generalize (list_env_iter_total_fun
                          (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                             df_eval_backprop_deriv 
                               σ r env
                               (transpose
                                  (UnitMatrix m n (exist (fun n' : nat => n' < m) x l0)
                                              (exist (fun n' : nat => n' < n) x0 l1)) i)) 
                          d2 (bounded_seq0 n)); intros.
            cut_to H7.
            -- case_eq (list_env_iter
                          (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                             df_eval_backprop_deriv 
                               σ r env
                               (@transpose R m n
                                  (UnitMatrix m n (exist (fun n' : nat => n' < m) x l0)
                                              (exist (fun n' : nat => n' < n) x0 l1)) i)) 
                          (Some d2) 
                          (bounded_seq0 n)); [intros |tauto].
               f_equal.
               rewrite (split_subvar d2 d5 d0 d3); trivial.
               invcs H4.
               invcs H6.
               generalize (list_env_iter_matvec_delta
                             σ r s d2
                             (exist (fun n' : nat => n' < n) x0 l1)
                             (exist (fun n' : nat => n' < m) x l0) d3).
               intros.
               specialize (H4 eqq3 H2).
               rewrite eqq4 in H4.
               replace  (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                           df_eval_backprop_deriv 
                             σ r env
                             (UnitMatrix n m (exist (fun n' : nat => n' < n) x0 l1)
                                         (exist (fun n' : nat => n' < m) x l0) i)) with
                   (fun (i : {m' : nat | m' < n}) (env : df_env) =>
                      df_eval_backprop_deriv 
                        σ r env
                        (@transpose R m n
                           (UnitMatrix m n (exist (fun n' : nat => n' < m) x l0)
                                       (exist (fun n' : nat => n' < n) x0 l1)) i)) in H4.
               ++ rewrite H8 in H4.
                  unfold lift in H4.
                  invcs H4; lra.
               ++ apply FunctionalExtensionality.functional_extensionality; intros.
                  apply FunctionalExtensionality.functional_extensionality; intros.
                  f_equal.
                  unfold transpose, UnitMatrix.
                  apply FunctionalExtensionality.functional_extensionality; intros.
                  simpl.
                  match_case; intros.
                  match_case; intros.
            -- intros.
               apply backprop_deriv_fully_closed_not_none; trivial.
          * assert (df_eval_deriv_genvar σ r [mk_env_entry (s, DTfloat) 1%R] <> None).
            apply eval_deriv_genvar_fully_closed_not_none; trivial.
            tauto.
        + assert (df_eval_deriv_genvar σ l [mk_env_entry (s, DTfloat) 1%R] <> None).
          apply eval_deriv_genvar_fully_closed_not_none; trivial.
          tauto.
      - Case "MatrixMult"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        generalize (eval_fully_closed_not_none σ r); intros.
        specialize (H5 H2).
        case_eq (df_eval σ r); [intros | tauto].
        assert (df_eval_deriv_genvar σ l [mk_env_entry (s, DTfloat) 1%R] <> None).
        apply eval_deriv_genvar_fully_closed_not_none; trivial.
        match_option; [|tauto].
        assert (df_eval_deriv_genvar σ r [mk_env_entry (s, DTfloat) 1%R] <> None).
        apply eval_deriv_genvar_fully_closed_not_none; trivial.
        match_option; [|tauto].
        match_option; [|tauto].
        unfold lift.
        symmetry.
        apply vectoro_to_ovector_forall_some_b_strong; intros.
        apply vectoro_to_ovector_forall_some_b_strong; intros.        
        simpl_closed_backprop.
        simpl_closed_backprop.
        f_equal.
        rewrite eqq1, eqq in H.
        unfold lift in H; symmetry in H.
        specialize (vectoro_to_ovector_forall_some_f H); intros.
        specialize (H0 env).
        simpler2.
        cut_to H0; try congruence.
        rewrite eqq0 in H0.
        rewrite (split_subvar env env0 d3 val); trivial.
        specialize (H9 i); simpl in H9.
        specialize (vectoro_to_ovector_forall_some_f H9); intros.
        replace (@vsum floatish_R p (fun j  => (d i j * d2 j i0 + d1 i j * d0 j i0)%R))
          with ((vsum (fun j => (d i j * d2 j i0)%R)) + (vsum (fun j => (d1 i j * d0 j i0)%R)))%R
        ; [|rewrite vsum_plus; f_equal].
        unfold lift in H0; symmetry in H0.
        specialize (vectoro_to_ovector_forall_some_f H0); intros.        
        simpl in H10; simpl in H11.
        destruct i; destruct i0; simpl in eqq2; simpl in eqq3.
        unfold matrix_mult,UnitMatrix in eqq3; simpl in eqq3.
        unfold matrix_mult,UnitMatrix in eqq2; simpl in eqq2.
        generalize (df_eval_backprop_delta_by_unit_partmat
                      σ l s grad_env
                      (fun (i : {n' : nat | n' < m}) (k : {m' : nat | m' < p}) =>
                         vsum
                           (fun j : {n' : nat | n' < n} =>
                              ((if equiv_dec (` i) x then 
                                  if equiv_dec (` j) x0 then 1 else 0 else 0) * d0 k j)%R))
                      (fun (i : {n' : nat | n' < m}) (k : {m' : nat | m' < p}) =>
                         vsum
                           (fun j : {n' : nat | n' < n} =>
                              ((if equiv_dec (` i) x then 
                                  if equiv_dec (` j) x0 then 1 else 0 else 0) * 
                               (d1 i k) * d0 k j)%R)))
        ; intros.
        specialize (H12 H1 vin).
        cut_to H12; try congruence.
        + unfold df_eval_backprop_delta in H12.
          rewrite eqq1 in H12.
          unfold lift in H12.
          rewrite eqq2 in H12.
          invcs H12.
          rewrite H14.
          assert  (msum
                     (fun (i : {n' : nat | (n' < m)%nat}) (k : {m' : nat | (m' < p)%nat}) =>
                        vsum
                          (fun j : {n' : nat | (n' < n)%nat} =>
                             (if equiv_dec (` i) x then 
                                if equiv_dec (` j) x0 then 1 else 0 else 0) 
                             * d1 i k * d0 k j))%R =
                   vsum
                     (fun j : {n' : nat | (n' < p)%nat} =>
                        d1 (exist (fun n' : nat => (n' < m)%nat) x l0) j *
                        d0 j (exist (fun n' : nat => (n' < n)%nat) x0 l1))%R).
          * rewrite msum_transpose.
            unfold msum.
            f_equal.
            unfold transpose; simpl.
            replace  (fun (i : {m' : nat | m' < p}) (j : {n' : nat | n' < m}) =>
                        (@vsum floatish_R n
                          (fun j0 : {n' : nat | n' < n} =>
                             ((if equiv_dec (` j) x then 
                                 if equiv_dec (` j0) x0 then 1 else 0 
                               else 0) * d1 j i * d0 i j0)%R))) with
                (fun (i : {m' : nat | m' < p}) (j : {n' : nat | n' < m}) =>
                   if equiv_dec (` j) x then
                     (d1 (exist _ x l0) i * d0 i (exist _ x0 l1))%R
                   else 0%R).
            -- apply FunctionalExtensionality.functional_extensionality; intros.
               rewrite vmap_nth.
               replace  (fun j : {n' : nat | n' < m} =>
                           if equiv_dec (` j) x
                           then
                             (d1 (exist (fun n' : nat => (n' < m)%nat) x l0) x1 *
                              d0 x1 (exist (fun m' : nat => (m' < n)%nat) x0 l1))%R
                           else 0%R) with
                   (fun j : {n' : nat | n' < m} =>
                      ((d1 (exist (fun n' : nat => (n' < m)%nat) x l0) x1 *
                        d0 x1 (exist (fun m' : nat => (m' < n)%nat) x0 l1))%R *
                       (@UnitVector floatish_R m (exist _ x l0) j))%R).
               now rewrite vsum_unitvector.
               apply FunctionalExtensionality.functional_extensionality; intros.
               unfold UnitVector; simpl.
               destruct (equiv_dec (` x2) x); lra.
            -- apply FunctionalExtensionality.functional_extensionality; intros.
               apply FunctionalExtensionality.functional_extensionality; intros.
               destruct ( equiv_dec (` x2) x).
               ++ replace
                     (fun j0 : {n' : nat | n' < n} =>
                        ((if equiv_dec (` j0) x0 then 1 else 0) * d1 x2 x1 * d0 x1 j0)%R)
                     with
                     (fun j0 : {n' : nat | n' < n} =>
                        ((d1 x2 x1 * d0 x1 j0) * (UnitVector n (exist _ x0 l1) j0))%R).
                  ** rewrite vsum_unitvector.
                     red in e.
                     subst.
                     destruct x2.
                     simpl.
                     erewrite index_pf_irrel; eauto.
                  ** apply FunctionalExtensionality.functional_extensionality; intros.
                     unfold UnitVector; simpl.
                     destruct (equiv_dec (` x3) x0); lra.
               ++ rewrite <- vsum_mult.
                  lra.
          * rewrite H12.
            apply Rplus_eq_compat_r.
            generalize (df_eval_backprop_delta_by_unit_partmat
                          σ r s env
                          (fun (i : {n' : nat | n' < p}) (k : {m' : nat | m' < n}) =>
                             vsum
                               (fun j : {n' : nat | n' < m} =>
                                  (d j i *
                                   (if equiv_dec (` j) x then 
                                      if equiv_dec (` k) x0 then 1 else 0 else 0))%R))
                          (fun (i : {n' : nat | n' < p}) (k : {m' : nat | m' < n}) =>
                             vsum
                               (fun j : {n' : nat | n' < m} =>
                                  (d j i * d2 i k * 
                                   (if equiv_dec (` j) x then 
                                      if equiv_dec (` k) x0 then 1 else 0 else 0))%R)))
            ; intros.
            specialize (H13 H2).
            cut_to H13; try congruence.
            -- unfold df_eval_backprop_delta in H13.
               rewrite eqq4 in H13.
               unfold lift in H13.
               rewrite eqq3 in H13.
               invcs H13.
               rewrite H16.
               unfold msum; f_equal.
               apply FunctionalExtensionality.functional_extensionality; intros.
               rewrite vmap_nth.
               replace
                  (fun k : {m' : nat | m' < n} =>
                     (@vsum floatish_R m
                       (fun j : {n' : nat | n' < m} =>
                          (d j x1 * d2 x1 k *
                           (if equiv_dec (` j) x then 
                              if equiv_dec (` k) x0 then 1 else 0 else 0))%R))) with
                  (fun k : {m' : nat | m' < n} =>
                     (vsum
                       (fun j =>
                          (d j x1 * d2 x1 k *
                           (UnitVector m (exist _ x l0) j))%R)
                       * (UnitVector n (exist _ x0 l1) k))%R).
               ++ rewrite vsum_unitvector.
                  rewrite vsum_unitvector.
                  lra.
               ++ apply FunctionalExtensionality.functional_extensionality; intros.
                  rewrite Rmult_comm.
                  rewrite vsum_mult.
                  f_equal.
                  apply FunctionalExtensionality.functional_extensionality; intros.
                  unfold UnitVector; simpl.
                  destruct (equiv_dec (` x2) x0); destruct (equiv_dec (` x3) x); lra.
            -- intros.
               rewrite scalarMult_backprop_grad_scalar with (grad_env2:=env); trivial; try congruence.
               ++ unfold lift.
                  unfold df_eval_backprop_delta.
                  rewrite eqq4.
                  unfold lift.
                  specialize (H11 i); simpl in H11.
                  specialize (vectoro_to_ovector_forall_some_f H11); intros.               
                  specialize (H15 j); intros; simpl in H15.
                  destruct i; destruct j; simpl in H15.
                  match_option_in H15.
                  f_equal; simpl.
                  invcs H15.
                  rewrite H17.
                  rewrite Rmult_comm.
                  rewrite vsum_mult.
                  f_equal.
                  apply FunctionalExtensionality.functional_extensionality; intros. 
                  lra.
               ++ apply backprop_deriv_fully_closed_not_none; trivial.
               ++ apply backprop_deriv_fully_closed_not_none; trivial.
        + intros.
          rewrite scalarMult_backprop_grad_scalar with (grad_env2:=grad_env); trivial; try congruence.
          * unfold lift.
            unfold df_eval_backprop_delta.
            rewrite eqq1.
            unfold lift.
            specialize (vectoro_to_ovector_forall_some_f H i); intros; simpl in H11.
            specialize (vectoro_to_ovector_forall_some_f H13 j); intros; simpl in H14.
            destruct i; destruct j; simpl in H14.
            match_option_in H14.
            f_equal; simpl.
            invcs H14.
            rewrite H16.
            rewrite Rmult_comm.
            rewrite vsum_mult.
            f_equal.
            apply FunctionalExtensionality.functional_extensionality; intros. 
            lra.
          * apply backprop_deriv_fully_closed_not_none; trivial.
          * apply backprop_deriv_fully_closed_not_none; trivial.
      - Case "VectorPlus"%string.
        destruct closed.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H3.
          match_option; symmetry.
          * apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H3 i).
            unfold lift in H3; unfold lift.
            match_option_in H3.
            unfold lift in H0.
            rewrite eqq1 in H0.
            generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat))
            ;intros.
            specialize (H4 vin).
            specialize (H0 d2 H4 H2).
            match_option_in H0.
            symmetry in H0.
            specialize (apply vectoro_to_ovector_forall_some_f H0); intros; simpl in H5.
            specialize (H5 i).
            destruct i; simpl in H1; simpl; simpl in eqq2; simpl in H5.
            rewrite eqq2.
            generalize (backprop_deriv_fully_closed_not_none 
                          σ r d2 
                          (UnitVector n (exist (fun n' : nat => n' < n) x l0)))
            ; intros;  specialize (H6 H2).
            match_option; [|tauto]; f_equal.
            rewrite eqq4 in H5; inversion H5.
            rewrite (split_subvar d2 d4 d0 d3); trivial.
            inversion H3; lra.
          * generalize (eval_deriv_genvar_fully_closed_not_none σ r [mk_env_entry (s, DTfloat) 1%R]); intros.
            specialize (H4 H2).
            tauto.
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_exists_None H); intros.
          destruct H3.
          unfold lift in e.
          match_option_in e.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env
                        (coerce
                           (df_eval_backward_gen_top_obligation_2
                              UnitAnn (DTVector n) l n eq_refl x)
                           (UnitVector n x))); intros.
          specialize (H3 H1); tauto.
      - Case "VectorMinus"%string.
        destruct closed.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H3.
          match_option; symmetry.
          * apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H3 i).
            unfold lift in H3; unfold lift.
            match_option_in H3.
            unfold lift in H0.
            rewrite eqq1 in H0.
            generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat))
            ;intros.
            specialize (H4 vin).
            specialize (H0 d2 H4 H2).
            match_option_in H0.
            symmetry in H0.
            specialize (apply vectoro_to_ovector_forall_some_f H0); intros; simpl in H5.
            specialize (H5 i).
            destruct i; simpl in H0; simpl; simpl in eqq2; simpl in H5.
            rewrite eqq2.
            generalize (backprop_deriv_fully_closed_not_none 
                          σ r d2 
                          (UnitVector n (exist (fun n' : nat => n' < n) x l0)))
            ; intros;  specialize (H6 H2).
            generalize (scalarMult_backprop_grad_scalar 
                          σ r s d2 d2
                          (UnitVector n (exist (fun n' : nat => n' < n) x l0))
                          (-1)%R ); intros.
            specialize (H7 H4 H4).
            generalize (backprop_deriv_fully_closed_not_none 
                          σ r d2
                          (scalarMult (DTVector n) (-1)%R 
                                      (UnitVector n (exist (fun n' : nat => n' < n) x l0))))
            ; intros;  specialize (H8 H2).
            specialize (H7 H8 H6).
            unfold df_eval_backprop_delta in H7; simpl in H7.
            rewrite eqq3 in H7.
            unfold lift in H7; simpl in H7.
            replace (fun i : {n' : nat | n' < n} =>
                       (- (@UnitVector floatish_R n (exist (fun n' : nat => (n' < n)%nat) x l0)) i)%R)
                    with
                      (fun i : {n' : nat | n' < n} =>
                         (-1 * UnitVector n (exist (fun n' : nat => (n' < n)%nat) x l0) i)%R).
            match_option; [|tauto]; f_equal.
            rewrite eqq4 in H7.
            rewrite (split_subvar d2 d4 d0 d3); trivial.
            rewrite H5 in H7.
            inversion H7.
            rewrite H10.
            inversion H3; lra.
            apply FunctionalExtensionality.functional_extensionality; intros. 
            lra.
          * generalize (eval_deriv_genvar_fully_closed_not_none σ r [mk_env_entry (s, DTfloat) 1%R]); intros.
            specialize (H4 H2).
            tauto.
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_exists_None H); intros.
          destruct H3.
          unfold lift in e.
          match_option_in e.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env
                        (coerce
                           (df_eval_backward_gen_top_obligation_2 UnitAnn (DTVector n) l n eq_refl x)
                           (UnitVector n x))); intros.
          specialize (H3 H1); tauto.
      - Case "MatrixPlus"%string.
        destruct closed.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H1.
          match_option; symmetry.
          * apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H3 i).
            specialize (apply vectoro_to_ovector_forall_some_f H3); intros; simpl in H4.
            apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H4 i0).
            unfold lift in H4; unfold lift.
            match_option_in H4.
            unfold lift in H0.
            rewrite eqq1 in H0.
            generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat))
            ;intros.
            specialize (H5 vin).
            specialize (H0 d2 H5 H2).
            match_option_in H0.
            symmetry in H0.
            specialize (apply vectoro_to_ovector_forall_some_f H0); intros; simpl in H6.
            specialize (H6 i).
            specialize (apply vectoro_to_ovector_forall_some_f H6); intros; simpl in H7.
            specialize (H7 i0).
            destruct i; destruct i0;  simpl; simpl in eqq2; simpl in H7.
            rewrite eqq2.
            generalize (backprop_deriv_fully_closed_not_none 
                          σ r d2
                          (UnitMatrix n m (exist (fun n' : nat => n' < n) x l0)
                                      (exist (fun n' : nat => n' < m) x0 l1)))
            ; intros;  specialize (H8 H2).
            match_option; [|tauto]; f_equal.
            rewrite eqq4 in H7; inversion H7.
            rewrite (split_subvar d2 d4 d0 d3); trivial.
            inversion H4; lra.
          * generalize (eval_deriv_genvar_fully_closed_not_none σ r [mk_env_entry (s, DTfloat) 1%R]); intros.
            now specialize (H4 H2).
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_exists_None H); intros.
          destruct H3.
          specialize (apply vectoro_to_ovector_exists_None e); intros.
          destruct H3.
          unfold lift in e0.
          match_option_in e0.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env
                         (coerce
              (df_eval_backward_gen_top_obligation_3 UnitAnn (DTMatrix n m) l n m eq_refl x
                 x0) (UnitMatrix n m x x0))); intros.
          specialize (H3 H1); tauto.
      - Case "MatrixMinus"%string.
        destruct closed.
        specialize (H grad_env vin).
        simpl in *.
        match_option
        ; rewrite eqq in H
        ; simpl in *; match_option_in H; [|tauto|].
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_forall_some_f H); intros; simpl in H1.
          match_option; symmetry.
          * apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H3 i).
            specialize (apply vectoro_to_ovector_forall_some_f H3); intros; simpl in H4.
            apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H4 i0).
            unfold lift in H4; unfold lift.
            match_option_in H4.
            unfold lift in H0.
            rewrite eqq1 in H0.
            generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq2 (s, DTfloat))
            ;intros.
            specialize (H5 vin).
            specialize (H0 d2 H5 H2).
            match_option_in H0.
            symmetry in H0.
            specialize (apply vectoro_to_ovector_forall_some_f H0); intros; simpl in H6.
            specialize (H6 i).
            specialize (apply vectoro_to_ovector_forall_some_f H6); intros; simpl in H7.
            specialize (H7 i0).
            destruct i; destruct i0;  simpl; simpl in eqq2; simpl in H7.
            rewrite eqq2.
            generalize (backprop_deriv_fully_closed_not_none 
                          σ r d2
                          (UnitMatrix n m (exist (fun n' : nat => n' < n) x l0)
                                      (exist (fun n' : nat => n' < m) x0 l1)))
            ; intros;  specialize (H8 H2).

            generalize (scalarMult_backprop_grad_scalar 
                          σ r s d2 d2
                          (UnitMatrix n  m (exist (fun n' : nat => n' < n) x l0)
                                      (exist (fun n' : nat => n' < m) x0 l1))
                          (-1)%R ); intros.
            specialize (H9 H5 H5).
            generalize (backprop_deriv_fully_closed_not_none 
                          σ r d2
                           (scalarMult (DTMatrix n m) (-1)%R
                                       (UnitMatrix n m (exist (fun n' : nat => n' < n) x l0)
                                                   (exist (fun n' : nat => n' < m) x0 l1))))
            ; intros;  specialize (H10 H2).
            specialize (H9 H10 H8).
            unfold df_eval_backprop_delta in H9; simpl in H9.
            rewrite eqq3 in H9.
            unfold lift in H9; simpl in H9.
            replace
              (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                 (-
                  (@UnitMatrix floatish_R n m (exist (fun n' : nat => (n' < n)%nat) x l0)
                             (exist (fun n' : nat => (n' < m)%nat) x0 l1)) i j)%R)
              with
                (fun (i : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                   (-1 *
                     UnitMatrix n m (exist (fun n' : nat => (n' < n)%nat) x l0)
                                (exist (fun n' : nat => (n' < m)%nat) x0 l1) i j)%R).
            match_option; [|tauto]; f_equal.
            rewrite eqq4 in H9.
            rewrite (split_subvar d2 d4 d0 d3); trivial.
            rewrite H7 in H9.
            inversion H9.
            rewrite H12.
            inversion H4; lra.
            apply FunctionalExtensionality.functional_extensionality; intros.
            apply FunctionalExtensionality.functional_extensionality; intros.             
            lra.
          * generalize (eval_deriv_genvar_fully_closed_not_none σ r [mk_env_entry (s, DTfloat) 1%R]); intros.
            now specialize (H4 H2).
        + specialize (H H1).
          symmetry in H.
          specialize (apply vectoro_to_ovector_exists_None H); intros.
          destruct H3.
          specialize (apply vectoro_to_ovector_exists_None e); intros.
          destruct H3.
          unfold lift in e0.
          match_option_in e0.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l grad_env
                         (coerce
              (df_eval_backward_gen_top_obligation_3 UnitAnn (DTMatrix n m) l n m eq_refl x
                 x0) (UnitMatrix n m x x0))); intros.
          specialize (H3 H1); tauto.
      - Case "VectorScalMult"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        generalize (eval_fully_closed_not_none σ x); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H5 H2).
        case_eq (df_eval σ l); [intros|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        case_eq (df_eval_backprop_deriv σ x grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
        match_option; unfold lift; symmetry.
        apply vectoro_to_ovector_forall_some_b_strong; intros.
        replace (@vsum 
                   floatish_R n
                   (fun j : @sig nat (fun n' : nat => lt n' n) =>
                      Rmult (d1 j)
                            (@coerce (Vector R n) (Vector R n)
                                     (@df_eval_backward_gen_top_obligation_2 
                                        floatish_R UnitAnn 
                                        (DTVector n) 
                                        (@VectorScalMult floatish_R UnitAnn n ann x l) n
                                        (@eq_refl definition_function_types (DTVector n)) i)
                                     (@UnitVector floatish_R n i) j)))
                with (d1 i).
        generalize (scalarMult_backprop_grad_scalar 
                      σ x s grad_env grad_env 1%R (d1 i)); intros; simpl in H7.
        unfold df_eval_backprop_delta in H7.
        rewrite eqq1 in H7; simpl in H7.
        specialize (H7 vin vin).
        rewrite eqq0 in H7.
        generalize (backprop_deriv_fully_closed_not_none 
                      σ x grad_env (d1 i * 1)%R ); intros.
        specialize (H8 H1); specialize (H7 H8).
        cut_to H7; try discriminate.
        invcs H.
        { specialize (H0 d3).
          cut_to H0;
            [| now apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
             | apply H2].
           unfold lift in H7; simpl in H7.
           match_option_in H7.
           replace (d1 i) with (d1 i * 1)%R  by lra.
           rewrite eqq3.
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat)); intros.
           specialize (H vin).
           case_eq (vartlookup d3 (s, DTfloat)); [intros | congruence].
           rewrite H9 in H0.
           unfold lift; simpl.
           unfold lift in H0.
           rewrite eqq2 in H0.
           generalize (scalarMult_backprop_grad_scalar σ l s d2 d3 (UnitVector n i) d)
           ; intros; simpl in H10.
           unfold df_eval_backprop_delta in H10; simpl in H10.
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq3 (s, DTfloat));intros.
           specialize (H11 vin).
           case_eq (vartlookup d2 (s, DTfloat)); [intros | congruence].
           specialize (H10 H11 H).
           rewrite H9, H12 in H10.
           symmetry in H0.
           specialize (apply vectoro_to_ovector_forall_some_f H0); intros.
           specialize (H13 i); simpl in H13.
           generalize (backprop_deriv_fully_closed_not_none 
                           σ l d2
                           (fun i0 : {n' : nat | n' < n} => (d * UnitVector n i i0)%R)); intros.                                   
           specialize (H14 H2); specialize (H10 H14).
           generalize (backprop_deriv_fully_closed_not_none 
                           σ l d3 (UnitVector n i)); intros.
           specialize (H15 H2); specialize (H10 H15).
           unfold lift in H10.
           match_option_in H10; [|congruence]; f_equal.
           replace
               (fun j : @sig nat (fun n' : nat => lt n' n) =>
                  Rmult d
                        (@coerce (Vector R n) (Vector R n)
                                 (@df_eval_backward_gen_top_obligation_2 
                                    floatish_R UnitAnn 
                                    (DTVector n) (@VectorScalMult floatish_R UnitAnn n ann x l) n
                                    (@eq_refl definition_function_types (DTVector n)) i)
                                 (@UnitVector floatish_R n i) j))
               with 
               (fun i0 : {n' : nat | n' < n} => (d * UnitVector n i i0)%R).
           rewrite eqq4.
           rewrite (split_subvar d2 d7 d0 d6); trivial; f_equal.
           match_option_in H10; inversion H10.
           match_option_in H13.
           invcs H7; invcs H13.
           rewrite H17.
           destruct i; simpl in eqq6.
           rewrite eqq6 in eqq5.
           invcs eqq5.
           lra.
           apply FunctionalExtensionality.functional_extensionality; intros.             
           now destruct i; simpl.
        }   
        + symmetry.
          destruct i; simpl.
          apply vsum_unitvector.
        + specialize (H0 d3).
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat)); intros.
          specialize (H7 vin).
          specialize (H0 H7 H2).
          rewrite eqq2 in H0.
          unfold lift in H0.
          symmetry in H0.
          case_eq (vartlookup d3 (s, DTfloat)); [intros | congruence].
          rewrite H8 in H0; simpl in H0.
          specialize (apply vectoro_to_ovector_exists_None H0); intros.
          destruct H9.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l d3
                        (coerce
                           (df_eval_backward_gen_top_obligation_2 
                              UnitAnn (DTVector n) l n eq_refl x0)
                           (UnitVector n x0))); intros.
          specialize (H9 H2).
          match_option_in e.
          tauto.
        + unfold lift in H.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ x grad_env 1%R); intros.
          specialize (H7 H1).
          match_option_in H.
          tauto.
      - Case "MatrixScalMult"%string.
        destruct closed.
        specialize (H grad_env vin H1).
        simpl in *.
        generalize (eval_fully_closed_not_none σ x); intros.
        specialize (H3 H1).
        match_case; [intros|tauto].
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d0 eqq0|tauto].
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H5 H2).
        case_eq (df_eval σ l); [intros|tauto].
        match_option
        ; rewrite eqq in H
        ; simpl in *; rewrite eqq0 in H.
        case_eq (df_eval_backprop_deriv σ x grad_env 1%R)
          ; [intros ? eqq1 | intros eqq1]
          ; rewrite eqq1 in H
          ; simpl in *
          ; try discriminate.
        match_option; unfold lift; symmetry.
        apply vectoro_to_ovector_forall_some_b_strong; intros.
        apply vectoro_to_ovector_forall_some_b_strong; intros.        
        replace
          (@msum floatish_R n m
             (fun (i1 : @sig nat (fun n' : nat => lt n' n))
                (j : @sig nat (fun m' : nat => lt m' m)) =>
              Rmult (d1 i1 j)
                (@coerce (Matrix R n m) (Matrix R n m)
                   (@df_eval_backward_gen_top_obligation_3 floatish_R UnitAnn 
                      (DTMatrix n m) (@MatrixScalMult floatish_R UnitAnn n m ann x l) n m
                      (@eq_refl definition_function_types (DTMatrix n m)) i i0)
                   (@UnitMatrix floatish_R n m i i0) i1 j)))
          with (d1 i i0).
        generalize (scalarMult_backprop_grad_scalar 
                      σ x s grad_env grad_env 1%R (d1 i i0)); intros; simpl in H7.
        unfold df_eval_backprop_delta in H7.

        rewrite eqq1 in H7; simpl in H7.
        specialize (H7 vin vin).
        rewrite eqq0 in H7.
        generalize (backprop_deriv_fully_closed_not_none 
                      σ x grad_env (d1 i i0 * 1)%R ); intros.
        specialize (H8 H1); specialize (H7 H8).
        cut_to H7; try discriminate.
        invcs H.
        { specialize (H0 d3).
          cut_to H0;
            [| now apply (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat))
             | apply H2].
           unfold lift in H7; simpl in H7.
           match_option_in H7.
           replace (d1 i i0) with (d1 i i0 * 1)%R  by lra.
           rewrite eqq3.
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat)); intros.
           specialize (H vin).
           case_eq (vartlookup d3 (s, DTfloat)); [intros | congruence].
           rewrite H9 in H0.
           unfold lift in H0.
           rewrite eqq2 in H0.
           generalize (scalarMult_backprop_grad_scalar σ l s d2 d3 (UnitMatrix n m i i0) d)
           ; intros; simpl in H10.
           unfold df_eval_backprop_delta in H10; simpl in H10.
           generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq3 (s, DTfloat));intros.
           specialize (H11 vin).
           case_eq (vartlookup d2 (s, DTfloat)); [intros | congruence].
           specialize (H10 H11 H).
           rewrite H9, H12 in H10.
           symmetry in H0.
           specialize (apply vectoro_to_ovector_forall_some_f H0); intros.
           specialize (H13 i); simpl in H13.
           specialize (apply vectoro_to_ovector_forall_some_f H13); intros.           
           specialize (H14 i0); simpl in H14.
           generalize (backprop_deriv_fully_closed_not_none 
                         σ l d2
                         (fun (i1 : {n' : nat | n' < n}) (j : {m' : nat | m' < m}) =>
                            (d * UnitMatrix n m i i0 i1 j)%R)); intros.
           specialize (H15 H2); specialize (H10 H15).
           generalize (backprop_deriv_fully_closed_not_none 
                           σ l d3 (UnitMatrix n m i i0)); intros.
           specialize (H16 H2); specialize (H10 H16).
           unfold lift in H10.
           match_option_in H10; [|congruence]; f_equal.
           replace
             (fun (i1 : @sig nat (fun n' : nat => lt n' n))
                  (j : @sig nat (fun m' : nat => lt m' m)) =>
                Rmult
                  (@coerce (Matrix R n m) (Matrix R n m)
                           (@df_eval_backward_gen_top_obligation_3 
                              floatish_R UnitAnn 
                              (DTMatrix n m) (@MatrixScalMult floatish_R UnitAnn n m ann x l) n m
                              (@eq_refl definition_function_types (DTMatrix n m)) i i0)
                           (@UnitMatrix floatish_R n m i i0) i1 j) d)
               with 
               (fun i1 j => (d * UnitMatrix n m i i0 i1 j)%R).
           rewrite eqq4.
           rewrite (split_subvar d2 d7 d0 d6); trivial; f_equal.
           match_option_in H10; inversion H10.
           match_option_in H14.
           rewrite H18.
           invcs H7; invcs H14.
           destruct i; destruct i0; simpl in eqq6.
           rewrite eqq6 in eqq5.
           invcs eqq5.
           rewrite H17.
           lra.
           apply FunctionalExtensionality.functional_extensionality; intros.
           apply FunctionalExtensionality.functional_extensionality; intros.
           destruct i; destruct i0; simpl.
           lra.
        }   
        + symmetry.
          destruct i; destruct i0; simpl.
          apply msum_unitmatrix.
        + specialize (H0 d3).
          generalize (df_eval_backprop_deriv_preserves_lookup_not_none eqq1 (s, DTfloat)); intros.
          specialize (H7 vin).
          specialize (H0 H7 H2).
          rewrite eqq2 in H0.
          unfold lift in H0.
          symmetry in H0.
          case_eq (vartlookup d3 (s, DTfloat)); [intros | congruence].
          rewrite H8 in H0; simpl in H0.
          specialize (apply vectoro_to_ovector_exists_None H0); intros.
          destruct H9.
          specialize (apply vectoro_to_ovector_exists_None e); intros.
          destruct H9.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ l d3
                        (coerce
                           (df_eval_backward_gen_top_obligation_3 
                              UnitAnn (DTMatrix n m) l n m eq_refl x0 x1) 
                           (UnitMatrix n m x0 x1))); intros.
          specialize (H9 H2).
          match_option_in e0.
          tauto.
        + unfold lift in H.
          generalize (backprop_deriv_fully_closed_not_none 
                        σ x grad_env 1%R); intros.
          specialize (H7 H1).
          match_option_in H.
          tauto.
      - Case "VectorApply"%string.
        destruct closed.
        generalize (eval_fully_closed_not_none (mk_env_entry (v, DTfloat) (0%R) :: nil) s0); intros.
        specialize (H4 H2).
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H5 H3).
        match_case; [intros|tauto].
        specialize (H1 grad_env vin H3).
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d1 eqq1 | tauto].
        rewrite eqq1 in H1; simpl in H1.
        match_option
        ; rewrite eqq in H1; unfold lift in H1; symmetry in H1.
        + specialize (apply vectoro_to_ovector_forall_some_f H1); intros; simpl in H7.
          unfold lift; simpl.
          match_option.
          * specialize (vectoro_to_ovector_forall_some_f eqq0); intros; simpl in H8.
            symmetry.
            apply vectoro_to_ovector_forall_some_b_strong; intros.
            specialize (H8 i).
            specialize (H7 i).
            destruct i.
            simpl.
            match_nested_case.
            -- assert ( df_eval_backprop_deriv σ l grad_env v1 <> None).
               apply backprop_deriv_fully_closed_not_none; trivial.
               match_option; [|tauto].
               f_equal.
               simpl in H7.
               match_option_in H8.
               specialize (vectoro_to_ovector_forall_some_f eqq2); intros.
               assert (H10c := H10).
               specialize (H10 (exist _ x l0)).
               rewrite vmap_nth in H10; simpl in H10.
               match_option_in H10; simpl in H10.
               unfold UnitVector in H10; simpl in H10.
               destruct (equiv_dec x x); [|congruence].
               invcs H8; rewrite H12.
               assert (v1 = 
                       scalarMult (DTVector n) d4
                                  (UnitVector n (exist (fun n' : nat => n' < n) x l0))).
               ++ unfold scalarMult; simpl.
                  apply FunctionalExtensionality.functional_extensionality; intros.
                  specialize (H10c x0); simpl in H10c.
                  rewrite vmap_nth in H10c; simpl in H10c.
                  match_option_in H10c.
                  invcs H10c.
                  destruct x0.
                  unfold UnitVector; simpl.
                  destruct (equiv_dec x0 x).
                  ** red in e0.
                     subst.
                     erewrite index_pf_irrel in eqq6.
                     rewrite eqq5 in eqq6.
                     invcs eqq6; lra.
                  ** lra.
               ++ replace (1 * d4)%R with d4 in H10 by lra.
                  generalize (scalarMult_backprop_grad_scalar 
                                σ l s grad_env grad_env
                                (UnitVector n (exist (fun n' : nat => n' < n) x l0)) d4)
                  ; intros.
                  simpl in H11; cut_to H11; trivial; try congruence.
                  ** unfold df_eval_backprop_delta in H11.
                     rewrite eqq1 in H11.
                     unfold lift in H11; simpl in H11.
                     rewrite H8 in eqq3.
                     unfold scalarMult in eqq3; simpl in eqq3.
                     match_option_in H7.
                     rewrite eqq3, eqq6 in H11.
                     invcs H11; rewrite H14.
                     invcs H7; rewrite H11.
                     generalize 
                       (df_eval_deriv_genvar_same
                          [mk_env_entry (v, DTfloat)
                                        (d (exist (fun n' : nat => n' < n) x l0) )]
                          s0 v); simpl; intros.
                     specialize (H7 H H2).
                     unfold lift, df_eval_deriv_gen_top in H7; simpl in H7.
                     rewrite <- H12.
                     unfold mk_genvar_env in eqq4; simpl in eqq4.
                     rewrite eqq4, eqq5 in H7.
                     invcs H7; lra.
                  ** apply backprop_deriv_fully_closed_not_none; trivial.
                  ** apply backprop_deriv_fully_closed_not_none; trivial.               
            -- apply vectoro_to_ovector_exists_None in eqq2; destruct eqq2.
               rewrite vmap_nth in e; simpl in e.
               assert (df_eval [mk_env_entry (v, DTfloat) (d x0)] 
                               (df_deriv s0 (v, DTfloat)) <> None).
               apply eval_fully_closed_not_none.
               apply fully_closed_deriv; trivial.
               match_option_in e; tauto.
          * apply vectoro_to_ovector_exists_None in eqq0; destruct eqq0.
            assert (df_eval_deriv_genvar [mk_env_entry (v, DTfloat) (d x)] s0
                                         [mk_env_entry (v, DTfloat) 1%R] <> None).
            apply eval_deriv_genvar_fully_closed_not_none; trivial.
            match_option_in e; tauto.
        + assert (df_eval_deriv_genvar σ l [mk_env_entry (s, DTfloat) 1%R] <> None).
          apply eval_deriv_genvar_fully_closed_not_none; trivial.          
          tauto.
      - Case "MatrixApply"%string.
        destruct closed.
        generalize (eval_fully_closed_not_none (mk_env_entry (v, DTfloat) (0%R) :: nil) s0); intros.
        specialize (H4 H2).
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H5 H3).
        match_case; [intros|tauto].
        specialize (H1 grad_env vin H3).
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d1 eqq1 | tauto].
        rewrite eqq1 in H1; simpl in H1.
        match_option
        ; rewrite eqq in H1; unfold lift in H1; symmetry in H1.
        + specialize (apply vectoro_to_ovector_forall_some_f H1); intros; simpl in H7.
          unfold lift; simpl.
          match_option.
          * specialize (apply vectoro_to_ovector_forall_some_f eqq0); intros; simpl in H8.
            symmetry.
            apply vectoro_to_ovector_forall_some_b_strong; intros.
            apply vectoro_to_ovector_forall_some_b_strong; intros.            
            specialize (H8 i).
            specialize (H7 i).
            match_nested_case.
            -- assert ( df_eval_backprop_deriv σ l grad_env m1 <> None).
               apply backprop_deriv_fully_closed_not_none; trivial.
               match_option; [|tauto].
               f_equal.
               simpl in H7.               
               specialize (vectoro_to_ovector_forall_some_f H8); intros.
               specialize (vectoro_to_ovector_forall_some_f H7); intros.               
               specialize (H10 i0); simpl in H10.
               match_option_in H10.
               specialize (vectoro_to_ovector_forall_some_f eqq2); intros.
               assert (H12c := H12).
               specialize (H12 i); simpl in H12.
               specialize (vectoro_to_ovector_forall_some_f H12); intros.               
               specialize (H13 i0); simpl in H13; unfold mmap in H13.
               rewrite vmap_nth in H13; simpl in H13.
               rewrite vmap_nth in H13; simpl in H13.
               destruct i; destruct i0; simpl in H13.
               simpl in *.
               unfold matrix_zip in H13.
               rewrite vmap_nth in H13; simpl in H13.
               match_option_in H13; simpl in H13.
               unfold UnitMatrix in H13; simpl in H13.
               destruct (equiv_dec x x); [|congruence].
               destruct (equiv_dec x0 x0); [|congruence].               
               invcs H13; invcs H10.
               assert (m1 = 
                       scalarMult (DTMatrix m n) d4
                                  (UnitMatrix m n 
                                              (exist (fun n' : nat => n' < m) x l0)
                                              (exist (fun n' : nat => n' < n) x0 l1))).
               ++ unfold scalarMult; simpl.
                  apply FunctionalExtensionality.functional_extensionality; intros.
                  apply FunctionalExtensionality.functional_extensionality; intros.
                  specialize (H12c x1); simpl in H12c.
                  specialize (vectoro_to_ovector_forall_some_f H12c); intros.               
                  specialize (H10 x2); simpl in H10; unfold mmap in H10.

                  rewrite vmap_nth in H10; simpl in H10.
                  rewrite vmap_nth in H10; simpl in H10.
                  unfold matrix_zip in H10.
                  rewrite vmap_nth in H10; simpl in H10.
                  match_option_in H10.
                  invcs H10.
                  destruct x1; destruct x2.
                  unfold UnitMatrix; simpl.
                  destruct (equiv_dec x1 x).
                  ** red in e1; subst.
                     destruct (equiv_dec x2 x0).
                     --- red in e1; subst.
                         rewrite index_pf_irrel with (pf2 := l0) in eqq6.
                         rewrite index_pf_irrel with (pf1 := l3) (pf2 := l1) in eqq6.
                         rewrite eqq5 in eqq6.
                         invcs eqq6; lra.
                     --- lra.
                  ** lra.
               ++ replace (1 * d4)%R with d4 in H15 by lra.
                  generalize (scalarMult_backprop_grad_scalar 
                                σ l s grad_env grad_env
                                (UnitMatrix m n (exist (fun n' : nat => n' < m) x l0)
                                            (exist (fun n' : nat => n' < n) x0 l1)) d4)
                  ; intros.
                  simpl in H13; cut_to H13; trivial; try congruence.
                  ** unfold df_eval_backprop_delta in H13.
                     rewrite eqq1 in H13.
                     unfold lift in H13; simpl in H13.
                     rewrite H10 in eqq3.
                     unfold scalarMult in eqq3; simpl in eqq3.
                     specialize (H11  (exist (fun n' : nat => n' < n) x0 l1)).
                     simpl in H11.
                     match_option_in H11.
                     rewrite eqq3, eqq6 in H13.
                     
                     generalize 
                       (df_eval_deriv_genvar_same
                          [mk_env_entry (v, DTfloat)
                                        (d (exist (fun n' : nat => n' < m) x l0) 
                                           (exist (fun n' : nat => n' < n) x0 l1))]
                          s0 v).
                     simpl; intros.
                     specialize (H16 H H2).
                     unfold lift, df_eval_deriv_gen_top in H16; simpl in H16.
                     unfold mk_genvar_env in eqq4; simpl in eqq4.
                     rewrite eqq4, eqq5 in H16.
                     invcs H13; rewrite H18.
                     invcs H16.
                     invcs H11; rewrite H15; lra.
                  ** apply backprop_deriv_fully_closed_not_none; trivial.
                  ** apply backprop_deriv_fully_closed_not_none; trivial.               
            -- unfold matrixo_to_omatrix in eqq2.
               apply vectoro_to_ovector_exists_None in eqq2; destruct eqq2.
               apply vectoro_to_ovector_exists_None in e; destruct e.
               unfold mmap in e.
               rewrite vmap_nth in e; simpl in e.
               rewrite vmap_nth in e; simpl in e.
               rewrite matrix_zip_m_n in e.
               destruct i; destruct i0.
               simpl in e.
               assert (df_eval [mk_env_entry (v, DTfloat) 
                                             (d x x0)] 
                               (df_deriv s0 (v, DTfloat)) <> None).
               apply eval_fully_closed_not_none.
               apply fully_closed_deriv; trivial.
               match_option_in e; tauto.
          * unfold matrixo_to_omatrix in eqq0.
            apply vectoro_to_ovector_exists_None in eqq0; destruct eqq0.
            apply vectoro_to_ovector_exists_None in e; destruct e.            
            assert (df_eval_deriv_genvar [mk_env_entry (v, DTfloat) (d x x0)] s0
                                         [mk_env_entry (v, DTfloat) 1%R] <> None).
            apply eval_deriv_genvar_fully_closed_not_none; trivial.
            match_option_in e; tauto.
        + assert (df_eval_deriv_genvar σ l [mk_env_entry (s, DTfloat) 1%R] <> None).
          apply eval_deriv_genvar_fully_closed_not_none; trivial.          
          tauto.
      - Case "VLossfun"%string.
        destruct closed.
        generalize (eval_fully_closed_not_none 
                      (mk_env_entry (v1, DTfloat) (0%R) :: 
                                    (mk_env_entry (v2, DTfloat) (0%R) :: nil)) s0); intros.
        specialize (H4 H2).
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H5 H3).
        match_case; [intros|tauto].
        specialize (H1 grad_env vin H3).
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d1 eqq1 | tauto].
        rewrite eqq1 in H1; simpl in H1.
        match_option
        ; rewrite eqq in H1; unfold lift in H1; symmetry in H1.
        + specialize (vectoro_to_ovector_forall_some_f H1); intros; simpl in H7.
          unfold lift; simpl.
          match_nested_case.
          * specialize (vectoro_to_ovector_forall_some_f eqq0); intros; simpl in H8.
            symmetry.
            match_nested_case.
            -- specialize (vectoro_to_ovector_forall_some_f eqq2); intros; simpl in H9.
               assert ( df_eval_backprop_deriv σ l grad_env v0 <> None).
               apply backprop_deriv_fully_closed_not_none; trivial.
               match_option; [|tauto].
               unfold snd in d1; simpl in d1.
               assert (forall i : {n' : nat | n' < n},
                          df_eval [mk_env_entry (v1, DTfloat) (d i); mk_env_entry (v2, DTfloat) (r i)]
                                  (df_deriv s0 (v1, DTfloat))
                          = Some (v0 i)).
               intros ; specialize (H9 i)
               ; rewrite vmap_nth in H9
               ; simpl in H9
               ; match_option_in H9
               ;inversion H9 ;f_equal; lra.
               generalize (df_eval_backprop_delta_by_unit_partvec σ l s grad_env v0 v).
               intros.
               specialize (H12 H3 vin).
               cut_to H12.
               ++ unfold df_eval_backprop_delta, lift in H12.
                  now rewrite eqq1, eqq3 in H12.
               ++ intros.
                  replace (@scaleUnitVector (@float floatish_R) n i (v0 i) (IZR Z0)) with 
                      (scalarMult (DTVector n) (v0 i) (UnitVector n i)) by 
                      (unfold scalarMult, scaleUnitVector, UnitVector;
                       apply FunctionalExtensionality.functional_extensionality; intros; 
                       simpl; destruct (equiv_dec (` x) (` i)); lra).
                  rewrite scalarMult_backprop_grad_scalar with (grad_env2 := grad_env); trivial.
                  ** unfold df_eval_backprop_delta.
                     rewrite eqq1.
                     specialize (H7 i); simpl in H7.
                     specialize (H8 i); simpl in H8.
                     specialize (H9 i); simpl in H9.
                     generalize 
                       (df_eval_deriv_genvar_same
                          [mk_env_entry (v1, DTfloat) (d i); mk_env_entry (v2, DTfloat) (r i)]
                          s0 v1); simpl; intros.
                     specialize (H13 H H2).
                     unfold df_eval_deriv_gen_top in H13; simpl in H13.
                     unfold lift in H13; simpl in H13.
                     match_option_in H13.
                     --- unfold mk_genvar_env in H8; simpl in H8.
                         rewrite eqq4 in H8.
                         specialize (H11 i).
                         destruct i; simpl in H7.
                         match_option_in H7.
                         unfold lift; f_equal.
                         unfold scalarMult; simpl.
                         invcs H8.
                         invcs H7.
                         rewrite H14.
                         rewrite <- H13 in H11.
                         invcs H11.
                         lra.
                     --- assert (df_eval_deriv_genvar
                                   [mk_env_entry (v1, DTfloat) (d i); 
                                    mk_env_entry (v2, DTfloat) (r i)] s0
                                   [mk_env_entry (v1, DTfloat) 1%R] <> None).
                         apply eval_deriv_genvar_fully_closed_not_none; trivial.          
                         tauto.
                  ** apply backprop_deriv_fully_closed_not_none; trivial.
                  ** apply backprop_deriv_fully_closed_not_none; trivial.
            -- apply vectoro_to_ovector_exists_None in eqq2.
               destruct eqq2.
               rewrite vmap_nth in e; simpl in e.
               match_option_in e.
               assert (df_eval [mk_env_entry (v1, DTfloat) (d x); 
                                mk_env_entry (v2, DTfloat) (r x)]
                               (df_deriv s0 (v1, DTfloat)) <> None).
               apply eval_fully_closed_not_none; simpl.
               apply fully_closed_deriv; trivial.
               tauto.
          * apply vectoro_to_ovector_exists_None in eqq0.
            destruct eqq0.
            match_option_in e.
            assert (df_eval_deriv_genvar
                      [mk_env_entry (v1, DTfloat) (d x); 
                       mk_env_entry (v2, DTfloat) (r x)] s0
                      [mk_env_entry (v1, DTfloat) 1%R] <> None).
            apply eval_deriv_genvar_fully_closed_not_none; trivial.
            tauto.
        + assert (df_eval_deriv_genvar σ l [mk_env_entry (s, DTfloat) 1%R] <> None).
          apply eval_deriv_genvar_fully_closed_not_none; trivial.          
          tauto.
      - Case "MLossfun"%string.
        destruct closed.
        generalize (eval_fully_closed_not_none 
                      (mk_env_entry (v1, DTfloat) (0%R) :: 
                                    (mk_env_entry (v2, DTfloat) (0%R) :: nil)) s0); intros.
        specialize (H4 H2).
        generalize (eval_fully_closed_not_none σ l); intros.
        specialize (H5 H3).
        match_case; [intros|tauto].
        specialize (H1 grad_env vin H3).
        case_eq (vartlookup grad_env (s, DTfloat)); [intros d1 eqq1 | tauto].
        rewrite eqq1 in H1; simpl in H1.
        match_option
        ; rewrite eqq in H1; unfold lift in H1; symmetry in H1.
        + specialize (vectoro_to_ovector_forall_some_f H1); intros; simpl in H7.
          unfold lift; simpl.
          match_nested_case.
          * specialize (vectoro_to_ovector_forall_some_f eqq0); intros; simpl in H8.
            symmetry.
            match_nested_case.
            -- specialize (vectoro_to_ovector_forall_some_f eqq2); intros; simpl in H9.
               assert ( df_eval_backprop_deriv σ l grad_env m1 <> None).
               apply backprop_deriv_fully_closed_not_none; trivial.
               match_option; [|tauto].
               unfold snd in d1; simpl in d1.
               assert (forall (i : {n' : nat | n' < m}) (j : {m' : nat | m' < n}),
                           match
                             df_eval [mk_env_entry (v1, DTfloat) (d i j); 
                                      mk_env_entry (v2, DTfloat) (r i j)]
                                     (df_deriv s0 (v1, DTfloat))
                           with
                           | Some se => Some (1 * se / IZR (Z.of_nat n))%R
                           | None => None
                           end = Some (m1 i j)); intros.
               ++ specialize (H9 i).
                  specialize (vectoro_to_ovector_forall_some_f H9); intros.
                  specialize (H11 j); simpl in H11; unfold mmap in H11.
                  do 2 rewrite vmap_nth in H11; simpl in H11.
                  unfold matrix_zip, vector_zip in H11; simpl in H11.
                  rewrite vmap_nth in H11; simpl in H11.
                  match_option; rewrite eqq4 in H11; apply H11.
               ++ generalize (df_eval_backprop_delta_by_unit_partmat 
                                σ l s grad_env m1 
                                (mmap (fun u => u / IZR (Z.of_nat n))%R m0)); intros.
                  specialize (H12 H3 vin).
                  cut_to H12.
                  ** unfold df_eval_backprop_delta, lift in H12.
                     rewrite eqq1, eqq3 in H12.
                     replace ((@msum floatish_R m n m0) / IZR (Z.of_nat n))%R with 
                         (msum (mmap (fun u : R => (u / IZR (Z.of_nat n))%R) m0)).
                     --- apply H12.
                     --- now rewrite msum_mmap_div_denom.
                  ** intros.
                     rewrite scalarMult_backprop_grad_scalar with (grad_env2 := grad_env)
                     ; trivial.
                     --- unfold df_eval_backprop_delta.
                         rewrite eqq1.
                         specialize (H7 i); simpl in H7.
                         specialize (H8 i); simpl in H8.
                         specialize (H11 i j); simpl in H11.
                         specialize (vectoro_to_ovector_forall_some_f H7); intros.
                         specialize (H13 j); simpl in H13.
                         specialize (vectoro_to_ovector_forall_some_f H8); intros.
                         specialize (H14 j); simpl in H14.
                         generalize 
                           (df_eval_deriv_genvar_same
                              [mk_env_entry (v1, DTfloat) (d i j); 
                               mk_env_entry (v2, DTfloat) (r i j)]
                              s0 v1); simpl; intros.
                         specialize (H15 H H2).
                         unfold df_eval_deriv_gen_top in H15; simpl in H15.
                         unfold lift in H15; simpl in H15.
                         match_option_in H15.
                         +++ unfold mk_genvar_env in H14; simpl in H14.
                             rewrite eqq4 in H14.
                             destruct i; destruct j; simpl in H13.
                             match_option_in H13.
                             unfold lift; f_equal.
                             invcs H13.
                             invcs H14.
                             rewrite H17.
                             unfold mmap.
                             rewrite vmap_nth.
                             rewrite vmap_nth.
                             rewrite <- H16.
                             rewrite <- H15 in H11.
                             invcs H11.
                             lra.
                         +++ assert (df_eval_deriv_genvar
                                       [mk_env_entry (v1, DTfloat) (d i j); 
                                        mk_env_entry (v2, DTfloat) (r i j)] s0
                                       [mk_env_entry (v1, DTfloat) 1%R] <> None).
                             apply eval_deriv_genvar_fully_closed_not_none; trivial.          
                             tauto.
                     --- apply backprop_deriv_fully_closed_not_none; trivial.
                     --- apply backprop_deriv_fully_closed_not_none; trivial.
            -- unfold matrixo_to_omatrix in eqq2.
               apply vectoro_to_ovector_exists_None in eqq2.
               destruct eqq2.
               apply vectoro_to_ovector_exists_None in e.
               destruct e.
               unfold mmap in e.
               rewrite vmap_nth in e; simpl in e.
               rewrite vmap_nth in e; simpl in e.
               unfold matrix_zip,vector_zip in e; simpl in e.
               rewrite vmap_nth in e.
               match_option_in e.
               assert (df_eval [mk_env_entry (v1, DTfloat) (d x x0); 
                                mk_env_entry (v2, DTfloat) (r x x0)]
                               (df_deriv s0 (v1, DTfloat)) <> None).
               apply eval_fully_closed_not_none; simpl.
               apply fully_closed_deriv; trivial.
               tauto.
          * unfold matrixo_to_omatrix in eqq0.
            apply vectoro_to_ovector_exists_None in eqq0.
            destruct eqq0.
            apply vectoro_to_ovector_exists_None in e.
            destruct e.
            match_option_in e.
            assert (df_eval_deriv_genvar
                      [mk_env_entry (v1, DTfloat) (d x x0); 
                       mk_env_entry (v2, DTfloat) (r x x0)] s0
                      [mk_env_entry (v1, DTfloat) 1%R] <> None).
            apply eval_deriv_genvar_fully_closed_not_none; trivial.
            tauto.
        + assert (df_eval_deriv_genvar σ l [mk_env_entry (s, DTfloat) 1%R] <> None).
          apply eval_deriv_genvar_fully_closed_not_none; trivial.          
          tauto.
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


 Lemma tree_backpropeq_complete_gen {T} (env gradenv : df_env) 
       (dfexpr : DefinedFunction EvalAnn T) (grad : definition_function_types_interp T) : 
   forall (x : SubVar), 
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
     DefinedFunction_cases (induction T, df using DefinedFunction_ind_simpl) Case.

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
    (* We need to open the string scope in order to use "a" as a string. *)
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
