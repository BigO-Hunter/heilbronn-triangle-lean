import Submission.OAI.Geometry.HeilbronnTriangle.Parameters

-- SCRATCH B5: which certificate shape makes the KERNEL whnf a K-headed term?

namespace OAI.Problem355

noncomputable section

set_option maxRecDepth 4000

-- B5a: hypothesis mentioning the cast form, syntactic pass-through
example : (31620 * heilbronnK + 1 : ℝ) < 5 → (31620 * heilbronnK + 1 : ℝ) < 5 := fun h => h

-- B5b: max-wrapped
example : max ((31620 * heilbronnK + 1 : ℝ) ^ 2) 64 < 5 → True := fun _ => trivial

-- B5c: linarith over such atoms
example
    (h1 : 4 * (8 : ℝ) + (31620 * heilbronnK + 1 : ℝ) ^ 2 ≤
      max (4 * (8 : ℝ) + (31620 * heilbronnK + 1 : ℝ) ^ 2) 64)
    (h2 : max (4 * (8 : ℝ) + (31620 * heilbronnK + 1 : ℝ) ^ 2) 64 < (7 : ℝ)) :
    4 * (8 : ℝ) + (31620 * heilbronnK + 1 : ℝ) ^ 2 < (7 : ℝ) := by linarith

-- B5d: exact_mod_cast stripping a 400*K^2 Nat cast
example (h : ((400 * heilbronnK ^ 2 : ℕ) : ℝ) < (5 : ℝ)) : 400 * heilbronnK ^ 2 < 5 := by
  exact_mod_cast h

-- B5e: omega s ≠ 0 shape
example (n s : ℕ) (h3 : 3 ≤ n) (h4 : n ≤ s) : s ≠ 0 := by omega

-- B5f: linarith mixing an atom that CONTAINS a let-bound flipped exponent
example (K2 : ℕ) (hK2 : (2 : ℝ) ≤ (3 : ℝ)) : True := trivial

-- B5g: exact_mod_cast through ↑(400·K²) ≤ A-shaped term with max
example (r : ℕ)
    (h1 : ((400 * heilbronnK ^ 2 : ℕ) : ℝ) ≤
      max (max ((400 * heilbronnK ^ 2 : ℕ) : ℝ) (4 * (8 : ℝ))) 64)
    (h2 : max (max ((400 * heilbronnK ^ 2 : ℕ) : ℝ) (4 * (8 : ℝ))) 64 < (r : ℝ)) :
    400 * heilbronnK ^ 2 ≤ r := by
  exact_mod_cast (le_of_lt (lt_of_le_of_lt h1 h2))

end

end OAI.Problem355
