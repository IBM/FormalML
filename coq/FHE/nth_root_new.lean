import Mathlib.RingTheory.RootsOfUnity.Complex

open Classical Nat Real Complex

noncomputable section

def nth_root (j n : Nat) :=
  (exp (2 * ↑Real.pi * I * (↑j / ↑n)))

theorem nth_root_0 n :
  nth_root 0 (succ n) = 1  := by
     unfold nth_root
     simp

theorem  nth_root_2PI_1 n  :
  nth_root (succ n) (succ n) = 1 := by
     unfold nth_root
     rw [div_eq_mul_inv]
     rw [Complex.mul_inv_cancel]
     . rw [mul_one]
       rw [Complex.exp_eq_one_iff]
       exists 1
       simp
     . rw [cast_ne_zero]
       apply succ_ne_zero


theorem  nth_root_2PI j n  :
  nth_root (j * (succ n)) (succ n) = 1 := by
     unfold nth_root
     rw [Complex.exp_eq_one_iff]
     exists j
     rw [div_eq_mul_inv]
     rw [cast_mul]
     rw [mul_assoc]
     rw [mul_assoc]
     rw [mul_assoc]
     rw [Complex.mul_inv_cancel]
     . rw [mul_one]
       simp; ring
     . rw [cast_ne_zero]
       apply succ_ne_zero


 theorem nth_root_2PI_plus n j k :
  nth_root (j + k * (succ n)) (succ n) = nth_root j (succ n) := by
    unfold nth_root
    rw [Complex.exp_eq_exp_iff_exists_int]
    exists k
    rw [div_eq_mul_inv]
    rw [mul_assoc]
    rw [mul_assoc]
    rw [cast_add]
    rw [add_mul]
    rw [mul_assoc]
    rw [cast_mul]
    rw [mul_assoc]
    rw [Complex.mul_inv_cancel]
    . simp; ring
    . rw [cast_ne_zero]
      apply succ_ne_zero 

    
theorem pow_nth_root j n e :
  (nth_root j (succ n)) ^ e = nth_root (e * j) (succ n) := by
    unfold nth_root
    rw [← Complex.exp_nat_mul]
    rw [Complex.exp_eq_exp_iff_exists_int]
    exists 0
    rw [Int.cast_zero]
    rw [zero_mul]
    rw [add_zero]
    simp; ring

theorem pow_nth_root_comm j n e :
  (nth_root j (succ n)) ^ e = (nth_root e (succ n)) ^ j := by
    rw [pow_nth_root]
    rw [pow_nth_root]
    rw [mul_comm]

theorem nth_root_npow j n :
  (nth_root j (succ n)) ^ (succ n) = 1 := by
   rw [pow_nth_root, mul_comm, nth_root_2PI]


theorem prim_nth_root j n :
  nth_root j (succ n) = (nth_root 1 (succ n)) ^ j := by
  rw [pow_nth_root]
  simp










