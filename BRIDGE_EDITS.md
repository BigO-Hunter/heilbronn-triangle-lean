# BRIDGE_EDITS.md — Stage B §8 interpolation bridge (R2125607854, 2026-11-02)

Record of every file touched by the bridge mission, per the attach-point
report's rule ("Do NOT modify ported upstream files except at the documented
attach points — record every edit").

## Ported upstream files (openai/math@1581d4cb → Submission/OAI/**)

**ZERO edits.** All 243 ported modules are byte-identical to the port-milestone
commit (17cb9b8); `git diff 17cb9b8..HEAD -- stageb/Submission/OAI` is empty.
The bridge attaches purely by import:

* `ParameterSampling.configuration_of_law` — called (not modified) from
  `Bridge/Assembly.lean` at the Bertrand-chosen prime.
* `Main.lean` r0=0 point-law instantiation — copied verbatim into
  `Bridge/Assembly.lean::point_law_at_prime` (Cp = 8,
  Ct = (128/7)·`UniformFixedFiberCount.countConstant`, `Fact r.Prime` /
  `Fact D.q.Prime` lets). Main.lean itself untouched.
* `ParameterConclusion.sampleCard_le_power`, `ParameterSequence.real_bounds` /
  `exists_primeParameterData` / `ratio_bound` / structure fields,
  `FinalScalingBridge.triangleAreasAtLeast_of_scaled`,
  `FinalScaling.sample_size_scaled_area`,
  `AlterationAsymptotics.sample_half_le_nat_floor`,
  `Parameters.heilbronnK_eq` / `heilbronnM_ge_three` / `heilbronnK_pos` /
  `heilbronnExponent_le` — all consumed as-is.

## New files (all bridge-authored)

| File | Content |
|---|---|
| `Submission/Bridge/Cardinality.lean` | THE new lemma: two-sided `sampleCard` bounds `√2·r^(k·45435+16) − 1 < sampleCard ≤ √(cubeTauConst k)·r^(k·45435+16)`, `cubeTauConst k = 3·2³⁰·(200k²)^(k·3029+1)`, via `N³/tau ∈ (2·r^(k·90870+30), C_k·r^(…)]` from structure fields only. |
| `Submission/Bridge/KBound.lean` | `heilbronnM = 606759748397114245242771031375422128400` (factorial route + norm_num), `6T = M(M−1)(M−2)`, **`heilbronnT_val` (116-digit T literal), `heilbronnK_val` (232-digit K = T²+1 literal, via in-tree `heilbronnK_eq` + cast injectivity — K never whnf'd), `eta_eq_heilbronnExponent : (1:ℝ)/(100000·K_literal) = heilbronnExponent`** (an equality since rung 1; the earlier `heilbronnK ≤ 10^232` floor and its `T² ≤ M⁶/36` support are deleted). |
| `Submission/Bridge/Assembly.lean` | Subset-restriction lemmas; `point_law_at_prime`; `config_at_prime`; **`bound_stageB`**: ∃c>0 ∃N ∀n≥N ∃P (card n, in square, areas ≥ c·n^(−2+heilbronnExponent)) — stated AT the symbolic exponent since rung 1, so no exponent-monotonicity step remains. |
| `AxCheck.lean` (workspace root) | The axiom audit: `#print axioms` for `Race.bound`, `bound_stageB`, `heilbronnT_val`, `heilbronnK_val`, `eta_eq_heilbronnExponent`. A root file, not a `Submission` library module, so it is not a build target. (`EntryDryRun.lean` and `scratch/` from the port phase were removed before submission.) |
| `scratch/` (never ships) | T1–T3, B1–B13, C_*/D_*/E_* bisect probes + `axcheck_dryrun.lean`. |

## Pre-existing non-upstream files edited

| File | Edit |
|---|---|
| `Submission.lean` (root hub, workspace-local provisional file — NOT upstream) | Added `import Submission.VacuityCheck` + `import Submission.Bridge.Assembly`; docstring updated. Reason: this lakefile's `lean_lib` builds **roots + import closure, not a directory glob** — the booked "glob-cache silently skips new modules" gotcha is exactly this (probe-verified: even a `False` theorem under Submission/Bridge/ was invisible to bare `lake build Submission`). With the imports, one `lake build Submission` = 9173 jobs covers the whole tree. |
| `lakefile.toml` | Byte-identical (a rescan-marker comment was added mid-mission and reverted; the trace file `.lake/build/lib/lean/Submission.trace` deletion is build-artifact-only). |

## Verification (rung 1, 2026-11-07 — `1f36158`, supersedes the 2026-11-02 notes)

* `lake build Submission`: **9172 jobs, GREEN, EXIT=0** (~41 s warm; a re-run
  after the commit is a 7 s no-op, so the committed tree is the built tree).
  Assembly alone rebuilds in 65 s.
* `#print axioms` for `Race.bound`, `bound_stageB`, `heilbronnT_val`,
  `heilbronnK_val`, `eta_eq_heilbronnExponent` — each exactly
  `[propext, Classical.choice, Quot.sound]`. (`heilbronnK_le` no longer
  exists: the crude floor is gone, replaced by the exact-K equality.)
* Zero `sorry` / `axiom` / `native_decide` in `Submission/`, `Submission.lean`.
* Filed value: `Bound ((1:ℚ)/(100000·K))`, K the exact 232-digit literal
  (denominator 237 digits) ⇒ η ≈ 7.2144e-237.

### Port-phase notes (2026-11-02, historical)

* Immunization quartet: (1) `^theorem Race.bound` at `EntryDryRun.lean:21`;
  (2) `#print axioms` for `Race.bound`, `bound_stageB`, `sampleCard_gt`,
  `heilbronnK_le` — each exactly `[propext, Classical.choice, Quot.sound]`;
  (3) zero `sorry` / `axiom` / `native_decide` in Submission/, Submission.lean,
  EntryDryRun.lean; (4) `lake env lean -DautoImplicit=false EntryDryRun.lean`
  exit 0, zero diagnostics.
