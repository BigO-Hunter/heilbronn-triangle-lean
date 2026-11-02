import Submission.Bridge.Cardinality

-- SCRATCH B13: verify the SAFE replacement shapes kernel-check quickly.

namespace OAI.Problem355.Bridge

noncomputable section

set_option maxRecDepth 4000

open Problem355

-- S-a: ℝ-side positivity of ↑(200·K²) via cast rewrites + literal exponent
example : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow]
  exact mul_pos (by norm_num) (pow_pos (by exact_mod_cast heilbronnK_pos) 2)

-- S-b: pow_pos with K-headed NAT exponent, but ℝ base (syntactic instance match)
example : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) ^ (heilbronnK * 3029 + 1) := by
  have hb : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    exact mul_pos (by norm_num) (pow_pos (by exact_mod_cast heilbronnK_pos) 2)
  exact pow_pos hb (heilbronnK * 3029 + 1)

-- S-c: full cubeTauConst positivity
example : (0 : ℝ) < cubeTauConst heilbronnK := by
  unfold cubeTauConst
  have hb : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    exact mul_pos (by norm_num) (pow_pos (by exact_mod_cast heilbronnK_pos) 2)
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 2 ^ 30)) (pow_pos hb (heilbronnK * 3029 + 1))

-- S-d: mul_pow with K-headed exponent (hsC shape)
example (m : ℝ) : (2 * m) ^ (heilbronnK * 45435 + 16) =
    (2 : ℝ) ^ (heilbronnK * 45435 + 16) * m ^ (heilbronnK * 45435 + 16) :=
  mul_pow _ _ _

-- S-e: div_pos chain (hCpos shape) with C'
example : (0 : ℝ) < Real.sqrt (cubeTauConst heilbronnK) *
    (4 : ℝ) ^ (heilbronnK * 45435 + 16) * 2 / Real.sqrt 2 := by
  have hc : (0 : ℝ) < cubeTauConst heilbronnK := by
    unfold cubeTauConst
    have hb : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      exact mul_pos (by norm_num) (pow_pos (by exact_mod_cast heilbronnK_pos) 2)
    exact mul_pos (mul_pos (by norm_num) (by norm_num))
      (pow_pos hb (heilbronnK * 3029 + 1))
  exact div_pos
    (mul_pos (mul_pos (Real.sqrt_pos.mpr hc)
        (pow_pos (by norm_num : (0 : ℝ) < 4) _)) (by norm_num))
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))

end

end OAI.Problem355.Bridge
