Require Import FloatishDef.

Section floatish_ops.

  Context {floatish_impl:floatish}.
  Local Open Scope float.

  Definition pos_sign (e:float)
    := if e >= 0 then 1 else Fopp 1.

  Definition neg_sign (e:float)
    := if e <= 0 then Fopp 1 else 1.

  Definition sign (e:float)
    := if e < 0 then Fopp 1
       else if e > 0 then 1
            else 0.

  Definition Fmax (x y:float)
    := if x < y then y else x.

  Definition Fmin (x y:float)
    := if x > y then y else x.
  
End floatish_ops.
