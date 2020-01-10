Require Import Extraction.
Require Import FloatishIEEE.

(* This is assumed by fromZ *)
Require Import ExtrOcamlZInt.

Extract Constant IEEE_float => "float".

Extract Inlined Constant IEEE_zero => "0.".
Extract Inlined Constant IEEE_opp => "Float.neg".
Extract Inlined Constant IEEE_plus => "Float.add".
Extract Inlined Constant IEEE_minus => "Float.sub".
Extract Inlined Constant IEEE_mult  => "Float.mul".
Extract Inlined Constant IEEE_div   => "Float.div".
Extract Inlined Constant IEEE_sqrt  => "Float.sqrt".
Extract Inlined Constant IEEE_abs   => "Float.abs".


Extract Inlined Constant IEEE_exp   => "Float.exp".
Extract Inlined Constant IEEE_ln    => "Float.log".

Extract Inlined Constant IEEE_pi    => "Float.pi".
Extract Inlined Constant IEEE_sin   => "Float.sin".
Extract Inlined Constant IEEE_cos   => "Float.cos".

Extract Inlined Constant IEEE_fromZ => "Float.of_int".

Extract Inlined Constant IEEE_eq    => "Float.equal".
Extract Inlined Constant IEEE_neq   => "(fun x y -> x = y)".
Extract Inlined Constant IEEE_lt    => "(fun x y -> x < y)".
Extract Inlined Constant IEEE_le    => "(fun x y -> x <= y)".
Extract Inlined Constant IEEE_gt    => "(fun x y -> x > y)".
Extract Inlined Constant IEEE_ge    => "(fun x y -> x >= y)".
