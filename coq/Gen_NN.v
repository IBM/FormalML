Require Import String.
Require Import RelationClasses.
Require Import List.
Require Import Rbase Rtrigo Rpower Rbasic_fun.
Require Import DefinedFunctions.
Require Import Lra.

Require Import BasicTactics.
Require Import ListAdd Assoc.

Record FullNN : Type := mkNN { ldims : list nat; param_var : SubVar; 
                              f_activ : DefinedFunction ; f_loss : DefinedFunction }.

Definition mkRvector (lr : list R) : list DefinedFunction :=
    map (fun r => Number r) lr.

Definition mkSubVarVector (v : SubVar) (n : nat) : list DefinedFunction :=
    map (fun n => Var (Sub v n)) (seq 1 n).

Definition mkSubVarMatrix (v : SubVar) (n m : nat) : list (list DefinedFunction) :=
    map (fun n =>  mkSubVarVector (Sub v n) m) (seq 1 n).

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
  let mat1 := mkSubVarMatrix (Sub wvar 1) n1 n2 in
  let mat2 := mkSubVarMatrix (Sub wvar 2) n2 n3 in
  let ivec := mkSubVarVector ivar n1 in
  let N1 := activation f_activ (mul_mat_vec mat1 ivec) in 
  match N1 with
  | Some vec => activation f_activ (mul_mat_vec mat2 vec)
  | None => None
  end.

Record testcases : Type := mkTest {ninput: nat; noutput: nat; ntest: nat; 
                                   data : list ((list R) * (list R))}.

Definition deltalosses (df : DefinedFunction) (losses : list DefinedFunction) : option DefinedFunction :=
  let losslist : option (list DefinedFunction) :=
      match unique_var df with
      | Some v => Some (map (fun dfj => df_subst df v dfj) losses)
      | None => None
      end 
  in
  match losslist with
  | Some l => Some (fold_right Plus (Number R0) l)
  | None => None
  end.

Definition NNinstance (n1 n2 n3 : nat) (ivar : SubVar) (f_loss : DefinedFunction) 
           (NN2 : list DefinedFunction) (inputs : (list R)) 
           (outputs : (list R)): option DefinedFunction :=
  let ipairs := (list_prod (map (fun n => (Sub ivar n)) (seq 1 n1))
                           (map Number inputs)) in
  let inputFunctions := (map (fun df => df_subst_list df ipairs) NN2) in
  let losses := (map (fun '(df,outval) =>  (Minus df (Number outval)))
                     (list_prod inputFunctions outputs)) in
     deltalosses f_loss losses.


  


  





  
