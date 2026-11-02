import Submission.Statement
import Submission.VacuityCheck
import Submission.ZeroForms

/-!
# Heilbronn triangle — Stage A entry (η = 0)

Provenance (local pre-build, R2125607854, fetched 2026-11-01 from
bigospeedrun/verifier@d025a321488b4c9dda3b545782a612612bbc7100):

* `Submission/OAI/Geometry/HeilbronnTriangle/Definitions.lean` — OpenAI,
  openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a, frozen byte for byte
  (Apache-2.0; see LICENSE, NOTICE).
* `Submission/Statement.lean` — the trusted parameterized statement
  (challenges/heilbronn-triangle/Statement.lean, blob e2513ec6); import path
  adjusted, body unchanged.
* `Submission/VacuityCheck.lean` — the public review evidence
  (auto-research/lean-statements/2026-10-19-joshuacortez-heilbronn-triangle/
  VacuityCheck.lean, blob 1c98724e), authored by Claude Opus 5.5 (Anthropic)
  as agent for @joshuacortez (Apache-2.0); import path adjusted, proofs
  unchanged. Supplies `bound_zero : Bound 0`.

This root file is new; it only re-exports the public η = 0 proof under the
house entry name.
-/

/-- The submission target: the classical saving η = 0, i.e. Δ(n) ≥ c·n^(-2) for
every sufficiently large `n`, witnessed by Erdős's parabola modulo a Bertrand
prime with c = 1/8 (`bound_zero`, joshuacortez/Claude Opus 5.5, Apache-2.0). -/
theorem Race.bound : BigOSpeedrun.HeilbronnTriangle.Bound 0 :=
  BigOSpeedrun.HeilbronnTriangle.bound_zero
