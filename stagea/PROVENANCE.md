# Stage A provenance (R2125607854 pre-build, 2026-11-01)

All upstream content fetched read-only via `gh api` from
`bigospeedrun/verifier@main = d025a321488b4c9dda3b545782a612612bbc7100` on 2026-11-01; every copy
below was sha256-verified against the GitHub blob listing AND, where listed,
against upstream's own `MANIFEST.json` (all matched).

| Local path | Upstream path | blob sha1 | sha256 (prefix) | Treatment |
|---|---|---|---|---|
| Submission/OAI/Geometry/HeilbronnTriangle/Definitions.lean | challenges/heilbronn-triangle/OAI/Geometry/HeilbronnTriangle/Definitions.lean | 6dd76ecf | e0d75ecc | byte-exact (frozen, OpenAI, Apache-2.0) |
| OAI/Geometry/HeilbronnTriangle/Definitions.lean | (same) | 6dd76ecf | e0d75ecc | byte-exact; insurance copy for the profile-stages-challenge-folder layout |
| Submission/Statement.lean | challenges/heilbronn-triangle/Statement.lean | e2513ec6 | 512410d5 | import path adjusted + provenance comment; body unchanged |
| Submission/VacuityCheck.lean | auto-research/lean-statements/2026-10-19-joshuacortez-heilbronn-triangle/VacuityCheck.lean | 1c98724e | 517f5e8f | import path adjusted + provenance comment; proofs & header unchanged |
| VerifierChallenge.lean | challenges/heilbronn-triangle/Statement.lean | e2513ec6 | 512410d5 | byte-exact; LOCAL DRY-RUN replica of the pipeline-generated root, never shipped |
| LICENSE | challenges/heilbronn-triangle/LICENSE | 261eeb9e | c71d239d | byte-exact (Apache-2.0) |
| lake-manifest.json | profiles/lake-manifest.json | (see git) | (see git) | byte-exact (Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612) |
| Submission.lean, Submission/ZeroForms.lean, VerifierAudit.lean, lakefile.toml, lean-toolchain | — | — | — | new (local pre-build); lakefile mirrors scripts/verifier.py lakefile() |

Attribution: Definitions.lean © OpenAI (Apache-2.0). Statement.lean and
VacuityCheck.lean: prepared by Claude Opus 5.5 (Anthropic) as agent for
@joshuacortez (Apache-2.0), per upstream NOTICE files — headers preserved
verbatim in every copy.
