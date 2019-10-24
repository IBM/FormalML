Require Import BinInt Reals Lra.

Require Import FloatishDef.

Local Instance floatish_R : floatish :=
  {
    float := R
    ; Fzero := 0%R
    ; Fopp := Ropp
    ; Fplus := Rplus
    ; Fminus := Rminus
    ; Fmult := Rmult
    ; Fdiv := Rdiv
    ; Fsqrt := sqrt
    ; Fabs := Rabs

    ; Fexp := exp
    ; Fln  := ln

    ; Fpi := PI
    ; Fsin := sin
    ; Fcos := cos

    ; FfromZ := IZR

                  
    ; Feq x y := if Req_EM_T x y then true else false
    ; Fneq x y := if Req_EM_T x y then false else true
    ; Flt x y := if Rlt_dec x y then true else false
    ; Fle x y := if Rle_dec x y then true else false
    ; Fgt x y := if Rgt_dec x y then true else false
    ; Fge x y := if Rge_dec x y then true else false
  }.
