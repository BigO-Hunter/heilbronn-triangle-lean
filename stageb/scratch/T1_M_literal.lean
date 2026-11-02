import Submission.OAI.Geometry.HeilbronnTriangle.Parameters

-- SCRATCH (never ships): can we pin heilbronnM to its 39-digit literal?
-- Route: choose_eq_factorial_div_factorial + norm_num on factorials.

namespace OAI.Problem355

example : heilbronnM = 606759748397114245242771031375422128400 := by
  show Nat.choose (4 * 41 - 1) 41 = 606759748397114245242771031375422128400
  rw [Nat.choose_eq_factorial_div_factorial (by decide : 41 ≤ 4 * 41 - 1)]
  norm_num

-- The numeric side of K ≤ 10^232: (M₀:ℝ)^6/36 + 1 ≤ 10^232.
example : (606759748397114245242771031375422128400 : ℝ) ^ 6 / 36 + 1 ≤ (10 : ℝ) ^ 232 := by
  norm_num

-- Same but in ℕ shape (fallback if the ℝ norm_num struggles).
example : 606759748397114245242771031375422128400 ^ 6 ≤ 36 * 10 ^ 232 := by
  norm_num

end OAI.Problem355
