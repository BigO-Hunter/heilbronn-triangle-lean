import Submission.OAI.Geometry.HeilbronnTriangle.Parameters

namespace OAI.Problem355

noncomputable section

set_option maxRecDepth 4000

example : 0 < heilbronnK := heilbronnK_pos

example : 0 < heilbronnK ^ 2 := Nat.pow_pos heilbronnK_pos 2

example : 0 < 200 * heilbronnK ^ 2 :=
  Nat.mul_pos (by norm_num) (Nat.pow_pos heilbronnK_pos 2)

example : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) :=
  Nat.cast_pos.mpr (Nat.mul_pos (by norm_num) (Nat.pow_pos heilbronnK_pos 2))

example : (0 : ℝ) < (3 : ℝ) * 2 ^ 30 := by norm_num

example : (200 * heilbronnK ^ 2 : ℕ) = 200 * heilbronnK ^ 2 := rfl

end

end OAI.Problem355
