Require Import List.
Require Import Omega.
Require Vector.

Section Vector.
  
Definition vector (T:Type) (n:nat) := { l : list T | length l = n }.

Program Definition vnil {T} : vector T 0 := exist _ nil _.

Program Definition vcons {T} (n:nat) (c:T) (v:vector T n) : vector T (S n) :=
  exist _ (c::proj1_sig v) _.
Next Obligation.
  destruct v; simpl.
  now rewrite e.
Qed.

Program Definition vappend {T} (n1 n2:nat) (v1:vector T n1) (v2:vector T n2) : vector T (n1 + n2) :=
  exist _ (proj1_sig v1 ++ proj1_sig v2) _ .
Next Obligation.
  destruct v1.
  destruct v2.
  simpl.
  now rewrite app_length, e, e0.
Qed.

Program Definition vmap {A B} {n} (f:A->B) (v : vector A n) : vector B n :=
  exist _ (map f (proj1_sig v)) _.
Next Obligation.
  destruct v; simpl.
  now rewrite map_length.
Qed.

Program Definition vhd {T} {n:nat} (v : vector T (S n)):T := 
  match proj1_sig v with
  | c :: l => c
  | nil => _
  end.
Next Obligation.
  destruct v; simpl in *.
  subst; simpl in *.
  congruence.
Qed.

Program Definition vtl {T} {n:nat} (v : vector T (S n)) : vector T n :=
  exist _ (tl (proj1_sig v)) _.
Next Obligation.
  destruct v; simpl.
  destruct x; simpl in *.
  omega.
  now inversion e.
Qed.

Program Definition vnth {T} {n:nat} (i:nat | i<n) (v : vector T n) : T
  := match nth_error v i with
     | None => _
     | Some t => t
     end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply nth_error_None in Heq_anonymous.
  destruct v; simpl in *.
  omega.
Qed.

Program Definition vlast {T} {n:nat} (v : vector T (S n)) := 
  vnth (exist _ n _) v.

Definition ConstVector {T} (n:nat) (c:T) : vector T n
  := exist _ (repeat c n) (repeat_length _ _).

Definition vec_fun {T} {n:nat} (v:vector T n) : {i:nat | i<n} -> T :=
  fun i => vnth i v.

Program Definition vcombine {T} {n:nat} (v1 v2:vector T n) : vector (T*T) n :=
  exist _ (combine (proj1_sig v1) (proj1_sig v2)) _.
Next Obligation.
  destruct v1.
  destruct v2.
  simpl.
  rewrite combine_length.
  rewrite e, e0.
  apply Nat.min_id.
Qed.

Program Definition build_vector {T} {n:nat} (v:{n':nat | n' < n}%nat -> T) : vector T n
  := Vector.vector_to_list v.
Next Obligation.
  apply Vector.vector_to_list_length.
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
     | nil => T
     | x::l' => vector (tensor T l') x
     end.

Lemma tensor0 T : tensor T nil = T.
Proof.
  reflexivity.
Qed.

Lemma tensor1 T n : tensor T (n::nil) = vector T n.
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
  | nil => c
  | x::l' => ConstVector x (ConstTensor l' c)
  end.

Definition scalar {T} (c:T) : tensor T nil := c.

End Tensor.

Section float_ops.

Require Import Floatish.

  Context {floatish_impl:floatish}.
  Local Open Scope float.

  Definition vsum {m:nat} (v:vector float m) : float
      := fold_right Fplus 0 (proj1_sig v).

  Definition msum {m n:nat} (v:matrix float m n) : float :=
    vsum (vmap vsum v).

  Definition vdot {m:nat} (v1 v2 : vector float m) : float :=
    fold_right Fplus 0
               (map (fun '(a,b) => a * b) 
                    (combine (proj1_sig v1) (proj1_sig v2))).

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

