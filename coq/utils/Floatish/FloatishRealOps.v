Require Import BinInt Reals Lra.
Require Import FloatishDef FloatishReal FloatishOps.

Section real_pfs.

  Local Existing Instance floatish_R.
  Lemma Fmax_Rmax x y : Fmax x y = Rmax x y.
  Proof.
    vm_compute.
    destruct (Rlt_dec x y); destruct (Rle_dec); lra.
  Qed.

  Lemma Fmin_Rmin x y : Fmin x y = Rmin x y.
  Proof.
    vm_compute.
    destruct (Rgt_dec x y); destruct (Rle_dec); lra.
  Qed.

End real_pfs.

Hint Rewrite Fmax_Rmax Fmin_Rmin : Rarith.
