Require Import BinInt.

Require Import Interval.Real.Xreal.

Require Import Interval.Interval.Transcend.
Require Import Interval.Float.Specific_ops.
Require Import Interval.Float.Specific_stdz.
Require Import Interval.Float.Basic.

Require Import FloatishDef.

Module F := SpecificFloat StdZRadix2.
Module A := TranscendentalFloatFast F.

Local Instance floatish_interval_gen (prec:Z) : floatish :=
  {
    float := F.type
    ; Fzero := F.zero
                 
    ; Fopp := F.neg
                
    ; Fplus := F.add_slow rnd_NE prec
    ; Fminus x y := F.add_slow rnd_NE prec x (F.neg y)
    ; Fmult := F.mul rnd_NE prec
    ; Fdiv := F.div rnd_NE prec

    ; Fsqrt := F.sqrt rnd_NE prec
    ; Fabs := F.abs

    ; Fexp x := A.I.midpoint(A.exp_fast prec x)
    ; Fln x  := A.I.midpoint(A.ln_fast prec x)

    ; Fsin x := A.I.midpoint(A.sin_fast prec x)
    ; Fcos x := A.I.midpoint(A.cos_fast prec x)
    ; Fpi := F.mul rnd_NE prec (F.fromZ 4) (A.I.midpoint (A.pi4 prec))

    ; FfromZ := F.fromZ

    ; Feq (x y:F.type) 
      := (match F.cmp x y with
          | Xeq => true
          | _ => false
          end)

    ; Fneq (x y:F.type)
      := (match F.cmp x y with
          | Xeq => false
          | _ => true
          end)

    ; Flt (x y:F.type)
      := (match F.cmp x y with
          | Xlt => true
          | _ => false
          end)

    ; Fle (x y:F.type)
      := (match F.cmp x y with
          | Xlt => true
          | Xeq => true                         
          | _ => false
          end)

    ; Fgt (x y:F.type)
      := (match F.cmp x y with
          | Xgt => true
          | _ => false
          end)

    ; Fge (x y:F.type)
      := (match F.cmp x y with
          | Xgt => true
          | Xeq => true                         
          | _ => false
          end)
  }.


Local Instance floatish_interval : floatish := floatish_interval_gen 53.

Definition FZF (r:float) := F.nearbyint rnd_NE r.
Definition FZFscale (n:Z) (r:float) := FZF (Fmult (FfromZ n) r).
