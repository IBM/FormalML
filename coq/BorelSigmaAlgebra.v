Require Import Rbase Ranalysis.
Require Import ProbSpace SigmaAlgebras.

(* specialized for R *)

Instance open_borel_sa : SigmaAlgebra R
  := generated_sa open_set.

Instance borel_sa : SigmaAlgebra R
  := generated_sa (fun (s:R->Prop) => exists r, forall m, m <= r <-> s m)%R.

Lemma borel_sa_preimage
      {Ts:Type}
      {dom: SigmaAlgebra Ts}
      (rvx: Ts -> R)
      (pf_pre: forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r)%R) :
  (forall B: event R, sa_sigma B -> sa_sigma (event_preimage rvx B)).
Proof.
Admitted.


Lemma borel_sa_preimage2 
      {Ts:Type}
      {dom: SigmaAlgebra Ts}
      (rvx: Ts -> R):
  (forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r)%R) <-> 
  (forall B: event R, sa_sigma B -> (sa_sigma (event_preimage rvx B))).
Proof.
  split; intros.
  - now apply borel_sa_preimage.
  - unfold event_preimage in *.
    simpl in H.
    apply (H (fun x => x <= r)%R).
    apply generated_sa_sub.
    exists r; intuition.
Qed.
