Require Import BinInt.

Declare Scope float.

Class floatish : Type :=
  {
    float : Type
    ; Fzero : float
                
    ; Fopp : float -> float
                        
    ; Fplus : float -> float -> float
    ; Fminus : float -> float -> float
    ; Fmult : float -> float -> float
    ; Fdiv : float -> float -> float
                                 
    ; Fsqrt : float -> float
    ; Fabs : float -> float
                        
    ; Fexp : float -> float
    ; Fln : float -> float
                       
    ; Fsin : float -> float
    ; Fcos : float -> float
    ; Fpi : float
                        
    ; FfromZ : Z -> float

    ; Feq : float -> float -> bool
    ; Fneq : float -> float -> bool
    ; Flt : float -> float -> bool
    ; Fle : float -> float -> bool
    ; Fgt : float -> float -> bool
    ; Fge : float -> float -> bool
  }.
                                   
Notation "0" := (Fzero) : float.
Notation "1" := (FfromZ 1) : float.
Notation "2" := (FfromZ 2) : float.
Notation "- x" := (Fopp x) (at level 35, right associativity) : float.
Notation "x + y" := (Fplus x y) (at level 50, left associativity) : float.
Notation "x - y" := (Fminus x y) (at level 50, left associativity) : float.
Notation "x * y" := (Fmult x y) (at level 40, left associativity) : float.
Notation "x / y" := (Fdiv x y) (at level 40, left associativity) : float.


Notation "x ==b y" := (Feq x y) (at level 70, no associativity) : float.
Notation "x != y" := (Fneq x y) (at level 70, no associativity) : float.
Notation "x < y" := (Flt x y)  (at level 70, no associativity) : float.
Notation "x <= y" := (Fle x y) (at level 70, no associativity) : float.
Notation "x > y" := (Fgt x y)  (at level 70, no associativity) : float.
Notation "x >= y" := (Fge x y) (at level 70, no associativity) : float.
