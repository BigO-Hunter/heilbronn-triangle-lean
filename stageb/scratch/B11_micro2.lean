import Submission.OAI.Geometry.HeilbronnTriangle.Parameters
import Submission.Bridge.Cardinality

namespace OAI.Problem355.Bridge

noncomputable section

set_option maxRecDepth 4000

open Problem355

-- P1
example : 0 < heilbronnK ^ 2 := Nat.pow_pos heilbronnK_pos

-- P2
example : 0 < 200 * heilbronnK ^ 2 :=
  Nat.mul_pos (by norm_num) (Nat.pow_pos heilbronnK_pos)

-- P3: the B9-G1 shape with (n := 2) named arg — the suspect form
example : 0 < 200 * heilbronnK ^ 2 :=
  Nat.mul_pos (by norm_num) (Nat.pow_pos (n := 2) heilbronnK_pos)

-- P4
example : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) :=
  Nat.cast_pos.mpr (Nat.mul_pos (by norm_num) (Nat.pow_pos heilbronnK_pos))

-- P5: pow with the flipped K-headed exponent
example : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) ^ (heilbronnK * 3029 + 1) :=
  pow_pos (Nat.cast_pos.mpr (Nat.mul_pos (by norm_num) (Nat.pow_pos heilbronnK_pos)))
    (heilbronnK * 3029 + 1)

-- P6: full cubeTauConst positivity, pure terms
example : (0 : ℝ) < cubeTauConst heilbronnK := by
  unfold cubeTauConst
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (0 : ℝ) < 2 ^ 30))
    (pow_pos (Nat.cast_pos.mpr (Nat.mul_pos (by norm_num) (Nat.pow_pos heilbronnK_pos))) _)

end

end OAI.Problem355.Bridge
