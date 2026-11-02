import Submission.VacuityCheck

/-!
Provenance: new file, local pre-build (R2125607854), 2026-11-01.
`docs/targets.md` writes rational targets as `((p : ℚ) / q)` and integer-valued
bounds with `q = 1` (Catalan: `((1091 : ℚ) / 1)`), so the Heilbronn target
generator may emit `Bound ((0 : ℚ) / 1)` rather than `Bound 0` for η = 0.
The root `Submission.lean` declares the mandated `Bound 0` form; this module
pre-compiles the divided form so filing can swap one line within hours if the
controller binds that shape. Both are defeq; Rat literals do not kernel-reduce
(subset-sum filing lesson), so the FILED type must match the generator's shape.
-/

namespace BigOSpeedrun.HeilbronnTriangle

/-- η = 0 in the `((p : ℚ) / q)` generator shape, `q = 1`. Rat literal forms do
not kernel-reduce (subset-sum #94 filing lesson), so bridge by `norm_num`. -/
theorem bound_zero_div_form : Bound ((0 : ℚ) / 1) := by
  have h : ((0 : ℚ) / 1) = (0 : ℚ) := by norm_num
  rw [h]
  exact bound_zero

end BigOSpeedrun.HeilbronnTriangle
