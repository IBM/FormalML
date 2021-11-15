Require Import Flocq.IEEE754.BinarySingleNaN.
Require Import BinInt.

Require Import FloatishDef.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.


Definition IEEE_float := binary64.
Definition IEEE_zero : IEEE_float := B754_zero 53 1024 false.
Definition IEEE_opp := b64_opp.
Definition IEEE_plus := b64_plus mode_NE.
Definition IEEE_minus := b64_minus mode_NE.
Definition IEEE_mult := b64_mult mode_NE.
Definition IEEE_div := b64_div mode_NE.
Definition IEEE_sqrt := b64_sqrt mode_NE.
Definition IEEE_abs := b64_abs.

Definition IEEE_fromZ i := binary_normalize 53 1024 (eq_refl _) (eq_refl _) mode_NE i 0 false.

Definition IEEE_eq (x y:IEEE_float)
  := (match b64_compare x y with
      | Some Eq => true
      | _ => false
      end).      

Definition IEEE_neq (x y:IEEE_float)
  := (match b64_compare x y with
      | Some Eq => false
      | Some _ => true
      | _ => false
      end).      

Definition IEEE_lt (x y:IEEE_float)
  := (match b64_compare x y with
      | Some Lt => true
      | _ => false
      end).                               

Definition IEEE_le (x y:IEEE_float)
  := (match b64_compare x y with
      | Some Lt => true
      | Some Eq => true                         
      | _ => false
      end).                               


Definition IEEE_gt (x y:IEEE_float)
  := (match b64_compare x y with
      | Some Gt => true
      | _ => false
      end).                               


Definition IEEE_ge (x y:IEEE_float)
  := (match b64_compare x y with
      | Some Gt => true
      | Some Eq => true                         
      | _ => false
      end).                               

(* following function will be defined only via extraction *)
Axiom IEEE_exp : IEEE_float -> IEEE_float.
Axiom IEEE_ln : IEEE_float -> IEEE_float.
Axiom IEEE_pi : IEEE_float.
Axiom IEEE_sin : IEEE_float -> IEEE_float.
Axiom IEEE_cos : IEEE_float -> IEEE_float.  

Local Instance floatish_IEEE : floatish :=
  {
    float := IEEE_float
    ; Fzero := IEEE_zero
    ; Fopp := IEEE_opp
    ; Fplus := IEEE_plus
    ; Fminus := IEEE_minus
    ; Fmult := IEEE_mult
    ; Fdiv := IEEE_div
    ; Fsqrt := IEEE_sqrt
    ; Fabs := IEEE_abs 

    ; Fexp := IEEE_exp
    ; Fln  := IEEE_ln

    ; Fpi := IEEE_pi
    ; Fsin := IEEE_sin
    ; Fcos := IEEE_cos

    ; FfromZ := IEEE_fromZ


    ; Feq  := IEEE_eq
    ; Fneq := IEEE_neq
    ; Flt  := IEEE_lt
    ; Fle  := IEEE_le
    ; Fgt  := IEEE_gt
    ; Fge  := IEEE_ge
  }.
