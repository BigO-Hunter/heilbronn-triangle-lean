import Submission.OAI.Geometry.HeilbronnTriangle.Parameters
import Submission.Bridge.Cardinality

namespace OAI.Problem355.Bridge

noncomputable section

set_option maxRecDepth 4000

open Problem355

example : 0 < heilbronnK ^ 2 := Nat.pow_pos heilbronnK_pos
end

end OAI.Problem355.Bridge
