import Submission.HeilbronnStatement
import Submission.OAI.Geometry.HeilbronnTriangle
import Submission.Bridge.Assembly

/-!
Big O Speedrun — Heilbronn triangle, Lean submission entry point.

Board: https://bigospeedrun.com/other/heilbronn-triangle
Target per docs/targets.md: `theorem Race.bound : ... Bound ((p : ℚ) / q)`.

Filed saving: eta = 1/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 = 1/(100000 * 10^232) ~ 1e-237,
a positive saving inside the accepted range `0 < p/q <= 5/6`. It is proven,
not the exact paper exponent 1/(100000*K): `heilbronnK <= 10^232` is proved
symbolically in `Submission/Bridge/KBound.lean` (K stays opaque), and
`Submission/Bridge/Assembly.lean` proves the bound at the exponent
`1/(100000 * 10^232)` directly, so no monotonicity step is needed.

Provenance of the proof tree:
* `Submission/HeilbronnStatement.lean` is `challenges/heilbronn-triangle/
  VerifierStatement.lean` (bigospeedrun/verifier) copied byte for byte,
  git blob bff8ba7bc805b881893123eb9b26e348b2bb6ee8. It carries OpenAI's
  frozen `OAI.Problem355` definitions (openai/math@1581d4cb, Apache-2.0) and
  the parameterized `BigOSpeedrun.HeilbronnTriangle.Bound`.
* `Submission/OAI/Geometry/HeilbronnTriangle/**` is OpenAI's comparator proof
  tree (openai/math@1581d4cb, Apache-2.0), 243 modules, imports rewritten.
  Its `Definitions.lean` path is kept as a one-line re-export of the trusted
  statement so every ported module keeps its original import line.
* `Submission/Bridge/**` is new work: the section-8 interpolation that turns
  OpenAI's subsequence statement into this board's "every large n" statement.

Axiom audit for `Race.bound`: exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no custom axioms, no `native_decide`.
-/

theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound ((1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  have hcast : ((((1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℚ) : ℝ) = (1 : ℝ) / (100000 * (10 ^ 232 : ℝ)) := by
    norm_num
  obtain ⟨c, hc, N, hN⟩ := OAI.Problem355.Bridge.bound_stageB
  refine ⟨c, hc, N, fun n hn => ?_⟩
  obtain ⟨P, hcard, hsq, harea⟩ := hN n hn
  refine ⟨P, hcard, hsq, ?_⟩
  rw [hcast]
  exact harea
