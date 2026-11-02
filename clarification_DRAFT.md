# Clarification issue DRAFT — OWNER REVIEW REQUIRED BEFORE ANY POSTING

Status: DRAFT ONLY (R2125607854 Task C). Nothing here has been posted anywhere.
Target: one GitHub issue on bigospeedrun/verifier, phrased as a prospective
submitter's pre-build questions on the merged Heilbronn-triangle statement
(PR #20, trusted at 079ac7b). Refines probe-report §e candidates #1–#3 into a
single tight issue. Rationale for asking all three at once: they are the three
unknowns that change WHAT we pre-build (target η, tree layout, rational form),
and one well-scoped issue is cheaper for the maintainer than three.

Suggested labels/title per repo conventions; body below the line.

---

**Title:** Heilbronn-triangle: three pre-build questions (profile range & stepping stones, comparator layout for a ~240-file proof tree, huge-rational target form)

**Body:**

I'm preparing Lean submissions for the Heilbronn-triangle board against the
trusted statement from #20 (`BigOSpeedrun.HeilbronnTriangle.Bound`, frozen OAI
`Problem355` definitions), and I'd like to pre-build against the right targets
before the profile lands. Three questions:

**1. Profile range and stepping-stone rows.** The README argues the meaningful
range is `0 ≤ η ≤ 5/6`. Will the profile's range be that (or wider)? And per
the 2026-11-02 records ruling (8cf5db18) — with no Lean Verified row yet, every
bound in the profile range runs, and the best Lean Verified row is listed even
when it is worse than the classic bound — can I confirm that a Lean Verified row
*below* the OpenAI baseline exponent is listed as a stepping stone? Concretely:
η = 0 (the statement package's own `bound_zero`), and later the comparator
exponent η₀ = 1/(100000·K) ≈ 7·10⁻²³⁷ obtained by extending OpenAI's existing
proof tree with the §8 interpolation argument (Bertrand prime choice +
deletion to exact n). Both are below the Claimed baseline 2/(45435K+16); both
would be Lean Verified. Is that the intended reading?

**2. Comparator layout binding + a ~240-file submission tree.** The statement
README leaves it to the maintainer whether submissions copy
`Statement.lean`/`Definitions.lean` under `Submission/` (imports adjusted) or
the profile stages `challenges/heilbronn-triangle/` next to the submission.
Which will the target generator bind? Submitters must pre-build import paths
now. (I've pre-built the copy-into-`Submission/` variant, and also keep a
byte-exact `OAI/Geometry/HeilbronnTriangle/Definitions.lean` at the original
module path so either layout is a packaging-time choice.) Related: a full port
of openai/math's `lean/OAI/Geometry/HeilbronnTriangle/` tree is 243 modules
(~1.6 MB of Lean, Mathlib-only external imports, on exactly the board pins
v4.34.1 + d13f23b — verified, builds green locally in ~5 minutes warm-cached).
Will a tree of that size pass the Comparator kernel check, nanoda, and the
axiom audit within CI budget, or should large submissions be pre-trimmed to
the modules reachable from the entry theorem? Catalan's split-build note in
docs/targets.md suggests large proofs are anticipated — does Heilbronn get the
same treatment?

**3. Huge-rational target form.** Has the rational target generator been
exercised with a ~237-digit denominator like 100000·K (K = T²+1, 232 digits)?
Two sub-questions: (a) exact form the controller substitutes for such an η —
`Bound ((1 : ℚ) / <literal>)` reduced, per the targets.md `((p : ℚ) / q)`
convention? (b) since upstream marks `heilbronnK` `@[irreducible]`, a proof
can't unfold K to a numeral; the sane route is bounding K symbolically
(K ≤ L for an explicit literal L, via `heilbronnT = choose heilbronnM 3 ≤
heilbronnM³`) and filing η₀ = 1/(100000·L) ≤ heilbronnExponent — i.e. the
filed rational is slightly below the paper's exact exponent. Is a
symbolic-bound η₀ acceptable for the row (it's the same ~10⁻²³⁷ scale), or do
you expect the exact 1/(100000·K) value with K's numeral computed out-of-band
and certified? For what it's worth, local timing shows 237-digit literals add
<1s to elaboration and norm_num reduction, so the mechanics look fine either
way.

Happy to file the η = 0 vacuity-row smoke first (analogous to the subset-sum
#94 pattern) the moment the profile exists. Thanks for the statement work —
the frozen-definitions + parameterized-adapter split is a pleasure to build
against.

---

## Owner-review notes (not part of the issue body)

- Tone: prospective submitter, homework visible, zero entitlement; mirrors the
  #94 smoke-test precedent which OPENED the subset-sum gate (trust-building).
- Q1 quotes ruling 8cf5db18 back to them — cheap confirmation, and it
  establishes the stepping-stone reading on the record before we file η₀.
- Q2 discloses the port exists and builds green (credibility) and asks the
  CI-budget question the probe ranked as risk #3; also offers the trimmed-tree
  fallback so the answer can't be a flat "no".
- Q3 pre-solves their likely worry (irreducible K) and offers the symbolic
  route as the default, asking only for acceptance — hardest to answer
  tersely, so it's last.
- RISKS OF POSTING: reveals lane strategy (η=0 first, η₀ second) to any
  competitor reading the issue (Blinov iterates fast, though toolchain-
  stranded on v4.11.0). Mitigation: the strategy is already inferable from
  the public bound_zero + openai/math tree; nothing here reveals the bridge
  analysis. Owner may prefer posting Q2/Q3 only, or none until the profile
  lands. AWAIT OWNER DECISION — do not post without explicit go.
