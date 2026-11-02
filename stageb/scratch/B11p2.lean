import Submission.OAI.Geometry.HeilbronnTriangle.Parameters
import Submission.Bridge.Cardinality

namespace OAI.Problem355.Bridge

noncomputable section

set_option maxRecDepth 4000

open Problem355

example : 0 < 200 * heilbronnK ^ 2 :=
  Nat.mul_pos (by norm_num) (Nat.pow_pos heilbronnK_pos)
end

end OAI.Problem355.Bridge
