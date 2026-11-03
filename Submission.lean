import Submission.HeilbronnStatement
import Submission.OAI.Geometry.HeilbronnTriangle
import Submission.VacuityCheck
import Submission.Bridge.Assembly

/-!
# Heilbronn-triangle submission — `Race.bound`

Entry for the Big O Speedrun heilbronn-triangle board (issue route opened
2026-11-03; filing instructions in bigospeedrun/verifier#105).

`Race.bound` proves `BigOSpeedrun.HeilbronnTriangle.Bound η` at
`η = 1/10^237`, filed as the literal 238-digit reduced fraction below.
This is slightly below the paper-exact saving `η₀ = 1/(100000·K)` of
OpenAI's preprint: the proof establishes `K ≤ 10^232` symbolically with
`heilbronnK` kept opaque (`Submission/Bridge/KBound.lean`), hence
`1/10^237 = 1/(100000·10^232) ≤ η₀`, and the board bound holds at the
filed value directly. No `bound_mono` transport and no equality bridge are
needed: the filed rational is exactly the proven one.

Proof structure: `Submission/Bridge/` (three new files) interpolates the
ported OpenAI comparator tree (`Submission/OAI/`, openai/math@1581d4cb,
Apache-2.0, only import lines rewritten) from its subsequence form to the
board's "every sufficiently large `n`" form: Bertrand prime choice per `n`,
two-sided `sampleCard` bounds, `Finset` deletion to exact `n`, and `rpow`
algebra. Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.
Zero `sorry`.

Trusted statement: `Submission/HeilbronnStatement.lean` is a byte-for-byte
copy of `challenges/heilbronn-triangle/VerifierStatement.lean` at
bigospeedrun/verifier main (commit be0eb9436df5adf2502fa7bba41672ce6ff0df15,
sha256 efc9772011b2104ba2cb51bd672e1bb974ab1a29f2384922e1c62f54307e32cb).
-/

theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound ((1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  have hcast : ((((1 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) : ℚ) : ℝ) =
      (1 : ℝ) / (100000 * (10 ^ 232 : ℝ)) := by
    norm_num
  obtain ⟨c, hc, N, hN⟩ := OAI.Problem355.Bridge.bound_stageB
  refine ⟨c, hc, N, fun n hn => ?_⟩
  obtain ⟨P, hcard, hsq, harea⟩ := hN n hn
  refine ⟨P, hcard, hsq, ?_⟩
  rw [hcast]
  exact harea
