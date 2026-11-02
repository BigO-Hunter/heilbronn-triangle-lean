import Submission.Bridge.Assembly
import Submission.Statement

/-!
# Stage B dry-run entry (R2125607854 bridge mission) — NOT the filed Submission.lean

Re-exports the §8 interpolation `OAI.Problem355.Bridge.bound_stageB` under the
house entry name for the immunization quartet. The rational is
`η₀ = (1:ℚ)/10^237 = 1/(100000·10^232)` with `10^232 ≥ heilbronnK` proven
symbolically (K opaque; `Bridge/KBound.lean`). Rat-literal discipline per the
Stage A ZeroForms lesson: the ℝ-side identity is bridged with `norm_num` + an
explicit `rw`, never defeq/`▸`.

Provenance of the proof tree: `Submission/Bridge/{Cardinality,KBound,Assembly}.lean`
(new) on top of the ported openai/math@1581d4cb HeilbronnTriangle comparator
tree (Apache-2.0; see LICENSE, PORT_MANIFEST.json, BRIDGE_EDITS.md). Packaging
into the filed `Submission.lean` happens at gate open, in the shape the live
target generator binds.
-/

theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound (1 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) := by
  have hcast : ((1 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) =
      (1 : ℝ) / (100000 * (10 ^ 232 : ℝ)) := by
    norm_num
  obtain ⟨c, hc, N, hN⟩ := OAI.Problem355.Bridge.bound_stageB
  refine ⟨c, hc, N, fun n hn => ?_⟩
  obtain ⟨P, hcard, hsq, harea⟩ := hN n hn
  refine ⟨P, hcard, hsq, ?_⟩
  rw [hcast]
  exact harea
