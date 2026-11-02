import Mathlib

-- SCRATCH (never ships): minimal repro of the calc + rw parse failure.

-- Variant A: the exact broken shape
example (h : ℕ) (hm : h ^ 101 ≤ 5) : h ^ 1010 ≤ 5 ^ 10 :=
  calc h ^ 1010 = (h ^ 101) ^ 10 := by
      rw [(by norm_num : (1010 : ℕ) = 101 * 10), pow_mul]
    _ ≤ 5 ^ 10 := Nat.pow_le_pow_left hm _

-- Variant B: show-form instead of parenthesized by
example (h : ℕ) (hm : h ^ 101 ≤ 5) : h ^ 1010 ≤ 5 ^ 10 :=
  calc h ^ 1010 = (h ^ 101) ^ 10 := by
      rw [show (1010 : ℕ) = 101 * 10 from by norm_num, pow_mul]
    _ ≤ 5 ^ 10 := Nat.pow_le_pow_left hm _

-- Variant C: single-line by
example (h : ℕ) (hm : h ^ 101 ≤ 5) : h ^ 1010 ≤ 5 ^ 10 :=
  calc h ^ 1010 = (h ^ 101) ^ 10 := by rw [(by norm_num : (1010 : ℕ) = 101 * 10), pow_mul]
    _ ≤ 5 ^ 10 := Nat.pow_le_pow_left hm _
