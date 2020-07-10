Require Import List.
Require Import Omega.
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

Definition vnth {T} {n:nat} (i:nat | i<n) (v : vector T n) : T
  := nth v (Fin.of_nat_lt (proj2_sig i)).

Definition vec_fun {T} {n:nat} (v:vector T n) : {i:nat | i<n} -> T :=
  fun i => vnth i v.

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

Program Definition vcombine {T} {n:nat} (v1 v2:vector T n) : vector (T*T) n :=
  of_list (combine (to_list v1) (to_list v2)).
Next Obligation.
  rewrite combine_length.
  rewrite to_list_length, to_list_length.
  apply Nat.min_id.
Qed.

End Vector.

Section Matrix.
  
Definition matrix (T:Type) (n m : nat) := vector (vector T m) n.

Definition mat_fun {T:Type} (n m : nat) (mat : matrix T n m ) :
  {n':nat | n' < n}%nat -> {m':nat | m' < m}%nat -> T :=
  fun i => fun j => vnth j (vnth i mat).

Definition mmap {A B} {n m} (f:A->B) (mat : matrix A n m) : matrix B n m :=
  vmap (vmap f) mat.

Definition mcombine {T} {n m : nat} (mat1 mat2 : matrix T n m) : matrix (T*T) n m :=
  vmap (fun '(a,b) => vcombine a b) (vcombine mat1 mat2).


Definition build_matrix {T} {n m:nat} 
        (mat:{n':nat | n' < n}%nat -> {m':nat | m' < m}%nat -> T) : matrix T n m
  := vmap build_vector (build_vector mat).

Definition transpose {T} {m n : nat} (mat:matrix T m n) : matrix T n m
  := build_matrix (fun i j => vnth i (vnth j mat)).

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

Fixpoint tensor_map {A B} {dims:list nat} (f:A->B) : tensor A dims -> tensor B dims
  := match dims with
     | List.nil => fun x => f x
     | x::l' => vmap (tensor_map f)
     end.

Definition scalar {T} (c:T) : tensor T List.nil := c.

End Tensor.

Class TensorDef :=
  {
  tensor_t (T:Type) (dims:list nat) : Type
  ; tensor_repr {T:Type} {dims:list nat} : tensor_t T dims -> tensor T dims -> Prop

  ; tensor_const {T} (dims : list nat) (c:T) : tensor_t T dims
  ; tensor_const_p {T} (dims : list nat) (c:T) : tensor_repr (tensor_const dims c) (ConstTensor dims c)

  ; vector_map {A B} {dims : list nat} (f:A->B) (t:tensor_t A dims) : tensor_t B dims
  ; vector_map_prop {A B} {dims : list nat} (f:A->B) (t:tensor_t A dims) :
      forall r, tensor_repr t r ->
           tensor_repr (vector_map f t) (tensor_map f r)
  }.



Section float_ops.

Require Import Floatish.

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
    build_matrix (fun i j => (vnth j (vnth i l)) + (vnth i r)).
    
(*
    transpose (vmap (fun l1 => vadd l1 r) (transpose l)).
 *)
  
  Definition matrix_mult {n m p} (l : matrix float n m)(r : matrix float m p) : matrix float n p :=
      build_matrix (fun i k => vsum (build_vector 
                                       (fun j => (vnth j (vnth i l)) * (vnth k (vnth j r))))).

(*
    transpose (vmap (fun r1 => matrix_vector_mult l r1) (transpose r)).
*)

End float_ops.

