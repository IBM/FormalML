Definition coerce {A B:Type} (pf:A=B) : A -> B.
Proof.
  destruct pf.
  intro a; exact a.
Defined.
