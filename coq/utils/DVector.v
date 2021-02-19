Require Import List Lia.

Import ListNotations.

Definition vector (T:Type) (n:nat)
  := { l : list T | length l = n}.

Program Lemma vector_length {T:Type} {n:nat} (v:vector T n)
  : length v = n.
Proof.
  now destruct v; simpl.
Qed.

Program Fixpoint vector_create
           {T:Type}
           (n:nat)
           (f:forall m, (m < n)%nat -> T) : vector T n
  := match n with
     | 0 => []
     | S m => f m _ :: vector_create m (fun x pf => f x _)
     end.

Program Definition vector_nth
        {T:Type}
        {n:nat}
        (i:nat)
        (pf:(i<n)%nat)
        (v:vector T n)
        : T
  := match nth_error v i with
     | Some x => x
     | None => _
     end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply nth_error_None in Heq_anonymous.
  rewrite vector_length in Heq_anonymous.
  lia.
Qed.

Program Definition vector_map {A B:Type}
           {n:nat} (f:A->B) (v:vector A n) : vector B n
  := map f v.
Next Obligation.
  rewrite map_length.
  now destruct v; simpl.
Qed.

Program Definition vector_zip {A B:Type}
           {n:nat} (v1:vector A n) (v2:vector B n) : vector (A*B) n
  := combine v1 v2.
Next Obligation.
  rewrite combine_length.
  repeat rewrite vector_length.
  now rewrite Min.min_idempotent.
Qed.

