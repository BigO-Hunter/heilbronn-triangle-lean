import Submission.Bridge.Cardinality

-- SCRATCH B9: isolate which preamble have poisons the kernel check.

namespace OAI.Problem355.Bridge

noncomputable section

set_option maxRecDepth 4000

open Problem355

-- G1: hbN via Nat.mul_pos/Nat.pow_pos
example : (0 : ℕ) < 200 * heilbronnK ^ 2 :=
  Nat.mul_pos (by norm_num) (Nat.pow_pos (n := 2) heilbronnK_pos)

-- G2: hCcube with exact_mod_cast for hb (the shipped shape)
example : (0 : ℝ) < cubeTauConst heilbronnK := by
  unfold cubeTauConst
  have hb : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by norm_num) (Nat.pow_pos (n := 2) heilbronnK_pos))
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 2 ^ 30)) (pow_pos hb _)

-- G3: hCcube with Nat.cast_pos.mpr instead of exact_mod_cast
example : (0 : ℝ) < cubeTauConst heilbronnK := by
  unfold cubeTauConst
  have hb : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (by norm_num) (Nat.pow_pos (n := 2) heilbronnK_pos))
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 2 ^ 30)) (pow_pos hb _)

end

end OAI.Problem355.Bridge
