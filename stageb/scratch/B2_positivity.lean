import Submission.OAI.Geometry.HeilbronnTriangle.Parameters

-- SCRATCH: which tactic+expression recurses deeply with the opaque huge Nat?

namespace OAI.Problem355

noncomputable section

set_option maxRecDepth 4000

-- P1: positivity on real pow with flipped-exponent Nat
example : (0 : ℝ) < (4 : ℝ) ^ (heilbronnK * 45435 + 16) := by positivity

-- P2: positivity on 1/α
example : (0 : ℝ) < 1 / (↑(heilbronnK * 45435 + 16) : ℝ) := by positivity

-- P3: one_le_rpow application shape
example : (1 : ℝ) ≤ Real.rpow 2 (1 / (↑(heilbronnK * 45435 + 16) : ℝ)) := by
  apply Real.one_le_rpow _ (by positivity)
  norm_num

-- P4: nlinarith with 200*K^2 (Nat)
example : (0 : ℕ) < 200 * heilbronnK ^ 2 := by
  have := heilbronnK_ge_two
  nlinarith

-- P5: exact_mod_cast chain
example : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) := by
  exact_mod_cast (show (0 : ℕ) < 200 * heilbronnK ^ 2 from by
    have := heilbronnK_ge_two
    nlinarith)

-- P6: nlinarith with sqrt and Nat var (hy1 shape)
example (n : ℕ) (hn : (3 : ℝ) ≤ n) : Real.sqrt 2 ≤ (n + 1 : ℝ) := by
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hn]

end

end OAI.Problem355
