import Mathlib

-- SCRATCH: variant D — calc on own line, tree style, multiline by first step.
example (h : ℕ) (hm : h ^ 101 ≤ 5) : h ^ 1010 ≤ 5 ^ 10 :=
  calc
    h ^ 1010 = (h ^ 101) ^ 10 := by
      rw [(by norm_num : (1010 : ℕ) = 101 * 10), pow_mul]
    _ ≤ 5 ^ 10 := Nat.pow_le_pow_left hm _

-- Variant E: does the rw chain itself close the goal? (term-mode check)
example (h : ℕ) : h ^ 1010 = (h ^ 101) ^ 10 := by
  rw [(by norm_num : (1010 : ℕ) = 101 * 10), pow_mul]
