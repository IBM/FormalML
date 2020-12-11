Require Import List.
Require Import BinInt.
Require Import Lia.
Require Import LibUtils.

Require Import VectorDef.
Require Vector.

Section Vector.
  
Definition vector (T:Type) (n:nat) := Vector.t T n.

Definition vnil {T} : vector T 0 := nil T.

Definition vcons {T} (n:nat) (c:T) (v:vector T n) : vector T (S n) :=
  cons T c n v.

Definition vappend {T} (n1 n2:nat) (v1:vector T n1) (v2:vector T n2) : vector T (n1 + n2) 
  := append v1 v2.

Definition vmap {A B} {n} (f:A->B) (v : vector A n) : vector B n :=  map f v.

Definition vhd {T} {n:nat} (v : vector T (S n)):T := hd v.

Definition vtl {T} {n:nat} (v : vector T (S n)) : vector T n := tl v.

Definition vlast {T} {n:nat} (v : vector T (S n)) := last v.

Definition vnth {T} {n:nat}  (v : vector T n) (i:nat | i<n) : T
  := nth v (Fin.of_nat_lt (proj2_sig i)).

Definition vec_fun {T} {n:nat} (v:vector T n) : {i:nat | i<n} -> T :=
  fun i => vnth v i.

Program Definition ConstVector {T} (n:nat) (c:T) : vector T n
  := of_list (repeat c n).
Next Obligation.
  now rewrite repeat_length.
Qed.  

Program Definition build_vector {T} {n:nat} (v:{n':nat | n' < n}%nat -> T) : vector T n
  := of_list (Vector.vector_to_list v).
Next Obligation.
  apply Vector.vector_to_list_length.
Qed.

Lemma to_list_length {T} {n:nat} (v : vector T n) : length (to_list v) = n.
  induction v; simpl; trivial.
  now f_equal.
Qed.

Program Definition vcombine {T1 T2} {n:nat} (v1:vector T1 n) (v2:vector T2 n): vector (T1*T2) n :=
  of_list (combine (to_list v1) (to_list v2)).
Next Obligation.
  rewrite combine_length.
  rewrite to_list_length, to_list_length.
  apply PeanoNat.Nat.min_id.
Qed.

Definition vector_zip {T1 T2} {n:nat} (v1:vector T1 n) (v2:vector T2 n): vector (T1*T2) n :=
  vcombine v1 v2.

Definition vmap2 {A B C} {n} (f:A->B->C) (v1 : vector A n) (v2 : vector B n) : vector C n
  :=  Vector.map2 f v1 v2.

Definition vmap4 {A B} {n} (f:A->A->A->A->B) (v1 v2 v3 v4 : vector A n) : vector B n :=
  vmap2 (fun '(a1,a2) '(a3,a4) => f a1 a2 a3 a4) (vcombine v1 v2) (vcombine v3 v4).

Program Definition vectoro_to_ovector {T} {n} (v:vector (option T) n) : option (vector T n) 
  := match listo_to_olist (to_list v) with
     | None => None
     | Some l => Some (of_list l)
     end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply listo_to_olist_some in Heq_anonymous.
  rewrite <- map_length with (f := Some).
  rewrite <- Heq_anonymous.
  now apply to_list_length.
Qed.

Definition vforall {A} {m:nat} (P: A -> Prop) (v:vector A m) : Prop
  := Vector.Forall P v.

End Vector.

Section Matrix.
  
Definition matrix (T:Type) (n m : nat) := vector (vector T m) n.

Definition mat_fun {T:Type} (n m : nat) (mat : matrix T n m ) :
  {n':nat | n' < n}%nat -> {m':nat | m' < m}%nat -> T :=
  fun i => fun j => vnth (vnth mat i) j.

Definition mmap {A B} {n m} (f:A->B) (mat : matrix A n m) : matrix B n m :=
  vmap (vmap f) mat.

Definition mnth {T} {n m :nat}  (v : matrix T n m) (i:nat | i<n) (j:nat | j<m) : T
  := vnth (vnth v i) j.

Definition mcombine {T1 T2} {n m : nat} (mat1 : matrix T1 n m) (mat2 : matrix T2 n m) : matrix (T1*T2) n m :=
  vmap (fun '(a,b) => vcombine a b) (vcombine mat1 mat2).

Definition matrix_zip {T1 T2} {n m : nat} (mat1 : matrix T1 n m) (mat2 : matrix T2 n m) : matrix (T1*T2) n m := mcombine mat1 mat2.

Definition build_matrix {T} {n m:nat} 
        (mat:{n':nat | n' < n}%nat -> {m':nat | m' < m}%nat -> T) : matrix T n m
  := vmap build_vector (build_vector mat).

Definition transpose {T} {m n : nat} (mat:matrix T m n) : matrix T n m
  := build_matrix (fun i j => mnth mat j i).

Definition ConstMatrix {T} (n m : nat) (c:T) : matrix T n m := 
  ConstVector n (ConstVector m c).

Definition matrixo_to_omatrix {T} {m n} (v:matrix (option T) m n) : option (matrix T m n)
  := vectoro_to_ovector (vmap vectoro_to_ovector v).

Definition mmap2 {A B C} {n m} (f:A->B->C) (v1 : matrix A n m) (v2 : matrix B n m) : matrix C n m :=  vmap2 (fun r1 r2 => vmap2 f r1 r2) v1 v2.

Definition mforall {A} {m n:nat} (P: A -> Prop) (m:matrix A m n) : Prop
  := vforall (fun x => vforall P x) m.

End Matrix.

Section Tensor.
Fixpoint tensor T (l:list nat) : Type
  := match l with
     | List.nil => T
     | x::l' => vector (tensor T l') x
     end.

Lemma tensor0 T : tensor T List.nil = T.
Proof.
  reflexivity.
Qed.

Lemma tensor1 T n : tensor T (n::List.nil) = vector T n.
Proof.
  reflexivity.
Qed.

Lemma tensor_app T l1 l2 : tensor (tensor T l1) l2 = tensor T (l2++l1).
Proof.
  revert l1.
  induction l2; intros l1; simpl; trivial.
  now rewrite IHl2.
Qed.

Fixpoint ConstTensor {T} (l : list nat) (c:T) : (tensor T l) := 
  match l with 
  | List.nil => c
  | x::l' => ConstVector x (ConstTensor l' c)
  end.

Fixpoint Tensor_map {A B} {dims:list nat} (f:A->B) : tensor A dims -> tensor B dims
  := match dims with
     | List.nil => fun x => f x
     | x::l' => vmap (Tensor_map f)
     end.

Definition scalar {T} (c:T) : tensor T List.nil := c.

End Tensor.

Inductive NumericType
  := FloatType
   | IntTYpe.


Definition ntype_interp (n:NumericType) : Type
  := match n with
     | FloatType => nat
     | IntType => Z
     end.

  Structure BigArray (ln : list nat) (T : NumericType) : Type := 
    Tensor { tdata :> list (ntype_interp T); _ : length tdata = List.fold_right Nat.mul 1%nat ln }.

  Structure Array1 (n : nat) (T : NumericType) : Type := 
    array1 { a1data :> list (ntype_interp T); _ : length a1data = n}.

  Structure Array2 (n m : nat) (T : NumericType) : Type := 
    array2 { a2data :> list (ntype_interp T); _ : length a2data = n * m}.

Definition tensor_abs_type  (T:NumericType) (dims:list nat) := tensor (ntype_interp T) dims.

Class TensorDef :=
  {
  tensor_t (T:NumericType) (dims:list nat) : Type
  ; tensor_repr {T:NumericType} {dims:list nat} : tensor_t T dims -> tensor_abs_type T dims -> Prop

  ; tensor_const {T} (dims : list nat) (c:ntype_interp T) : tensor_t T dims
  ; tensor_const_p {T} (dims : list nat) (c:ntype_interp T) : tensor_repr (tensor_const dims c) (ConstTensor dims c)

  ; tensor_map {A B} {dims : list nat} (f:ntype_interp A-> ntype_interp B) (t:tensor_t A dims) : tensor_t B dims
  ; tensor_map_p {A B} {dims : list nat} (f:ntype_interp A-> ntype_interp B)  (t:tensor_t A dims) :
      forall r, tensor_repr t r ->
           tensor_repr (tensor_map f t) (Tensor_map f r)

  (* ; tensor_nth {A} {dims : list nat} (indices:list nat) (indices_in_range:True) (t:tensor A dims) : A *)
  (* ; tensor_nth_p {A:Type} {dims : list nat} (indices:list nat) (indices_in_range:True) (t:tensor_t A dims) : *)
  (*   forall r, tensor_repr t r -> *)
  (*          tensor_repr (tensor_nth indices indices_in_range t) (tensor_nth indices indices_in_range r) *)
  }.

(*
Class TensorDefExt {base:TensorDef} :=
  {
  tensor_transpose;
  }.
*)
  (* ; tensor_nth {A} {dims : list nat} (indices:list nat) (indices_in_range:True) (t:tensor A dims) : A *)
  (* ; tensor_nth_p {A:Type} {dims : list nat} (indices:list nat) (indices_in_range:True) (t:tensor_t A dims) : *)
  (*   forall r, tensor_repr t r -> *)
  (*          tensor_repr (tensor_nth indices indices_in_range t) (tensor_nth indices indices_in_range r) *)

(* Instance trivial_TensorDef : TensorDef := *)
(*   { *)
(*   tensor_t := tensor; *)
(*   tensor_repr _ _ a b := a = b *)
(*   }. *)
(*
Fixpoint flat_list_represent_tensor {T} {dims} (l:list A) (t:tensor T dims) : Prop
  := 
         
Instance BigArray_TensorDef : TensorDef
  := {
  tensor_t A dims := list A;
  tensor_repr T dims (l:list A) (tensor T dims)
  := fix 
    }.
*)

Require Import Floatish.
Section float_ops.
  Context {floatish_impl:floatish}.
  Local Open Scope float.

  Definition vsum {m:nat} (v:vector float m) : float
      := List.fold_right Fplus 0 (to_list v).

  Definition msum {m n:nat} (v:matrix float m n) : float :=
    vsum (vmap vsum v).

  Definition vdot {m:nat} (v1 v2 : vector float m) : float :=
    List.fold_right Fplus 0
               (List.map (fun '(a,b) => a * b) 
                    (combine (to_list v1) (to_list v2))).

  Definition vadd {m:nat} (v1 v2 : vector float m) :=
    vmap (fun '(a,b) => a+b) (vcombine v1 v2).

  Definition madd {m n:nat} (mat1 mat2 : matrix float m n) :=
    mmap (fun '(a,b) => a+b) (mcombine mat1 mat2).

  Definition matrix_vector_mult {n m} (l : matrix float n m)(r : vector float m) : vector float n :=
    vmap (fun l1 => vdot l1 r) l.

  Definition matrix_vector_add {n m} (l : matrix float n m) (r : vector float n) : matrix float n m := 
    build_matrix (fun i j => (vnth (vnth l i) j) + (vnth r i)).
    
(*
    transpose (vmap (fun l1 => vadd l1 r) (transpose l)).
 *)
  
  Definition matrix_mult {n m p} (l : matrix float n m)(r : matrix float m p) : matrix float n p :=
      build_matrix (fun i k => vsum (build_vector 
                                       (fun j => (vnth (vnth l i) j) * 
                                                 (vnth (vnth r j) k)))).

(*
    transpose (vmap (fun r1 => matrix_vector_mult l r1) (transpose r)).
*)

End float_ops.

  
  

  

