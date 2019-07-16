Require Import String.
Require Import RelationClasses.
Require Import List.
Require Import Rbase Rtrigo Rpower Rbasic_fun.
Require Import DefinedFunctions.
Require Import Lra.

Require Import BasicTactics.
Require Import ListAdd Assoc.

Record FullNN : Set := mkNN { ldims : list nat; param_var : SubVar; 
                              f_activ : DefinedFunction ; f_loss : DefinedFunction }.

Definition mkRvector (lr : list R) : list DefinedFunction :=
    map (fun r => Number r) lr.

Definition mkVector (v : SubVar) (n : nat) : list DefinedFunction :=
    map (fun n => Var (Sub v n)) (seq 1 n).

Definition mkMatrix (v : SubVar) (n m : nat) : list (list DefinedFunction) :=
    map (fun n =>  mkVector (Sub v n) m) (seq 1 n).

Definition vecprod (vec1 vec2 : list DefinedFunction) : DefinedFunction :=
  fold_right (fun x y => Plus x y) (Number 0) (map (fun '(x,y) => Times x y) (combine vec1 vec2)).

Definition mul_mat_vec (mat : list (list DefinedFunction)) (vec : list DefinedFunction) : list DefinedFunction :=
  map (fun row => vecprod row vec) mat.

Definition unique_var (df : DefinedFunction) : option SubVar :=
  let fv := nodup var_dec (df_free_variables df) in
  match fv with
  | nil => None
  | v :: nil => Some v
  | _ => None
  end.   

Definition activation (df : DefinedFunction) (vec : list DefinedFunction) : option (list DefinedFunction) :=
    match unique_var df with
    | Some v => Some (map (fun dfj => df_subst df v dfj) vec)
    | None => None
    end.

Definition mkNN2 (n1 n2 n3 : nat) (ivar wvar : SubVar) (f_activ : DefinedFunction) : option (list DefinedFunction) :=
  let mat1 := mkMatrix (Sub wvar 1) n1 n2 in
  let mat2 := mkMatrix (Sub wvar 2) n2 n3 in
  let ivec := mkVector ivar n1 in
  let N1 := activation f_activ (mul_mat_vec mat1 ivec) in 
  match N1 with
  | Some vec => activation f_activ (mul_mat_vec mat2 vec)
  | None => None
  end.



  





  
