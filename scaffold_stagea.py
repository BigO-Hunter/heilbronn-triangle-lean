#!/usr/bin/env python3
"""Scaffold the Stage A submission tree (R2125607854).

Layout mirrors the verifier's staged build (scripts/verifier.py prepare()):
  - Submission lib: root Submission.lean + Submission/ modules (house contract,
    docs/targets.md; the copy-into-Submission layout option from the challenge
    README).
  - OAI lib: byte-exact frozen Definitions at the original module path — the
    insurance copy for the alternative layout where the profile stages the
    challenge folder (VerifierChallenge.lean imports OAI.Geometry...).
  - VerifierChallenge.lean / VerifierAudit.lean: LOCAL DRY-RUN replicas of the
    pipeline-generated roots (never shipped in the submission repo).

Every derived file carries a provenance comment; byte-exact copies are
sha256-verified against the upstream MANIFEST.json values.
"""
import hashlib
import shutil
from pathlib import Path

WS = Path("/Volumes/Substrate-1/bigo/heilbronn-lane")
F = WS / "_fetched"
S = WS / "stagea"

VERIFIER_COMMIT = "d025a321488b4c9dda3b545782a612612bbc7100"
FETCH_DATE = "2026-11-01"

# Upstream MANIFEST.json sha256 values (cross-checked against GitHub blob shas
# at fetch time — all matched).
EXPECTED = {
    "Statement.lean": "512410d50823a099599f662fe5e15462ed6d89df36e7363799ec4a3e14aebfcb",
    "Definitions.lean": "e0d75ecc36327321392b4d3c8f08cc7ecfcf678cdc47ccfde314fb8dd9c9196d",
    "VacuityCheck.lean": "517f5e8fc44b4603884c83fdde97b2dad566dbcd4558676aa36c7cdaf6d42864",
    "LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "NOTICE": "0dbe4f972c8df52dd4dea42329b54c5b33da48ce261d071f12c1673e4faacdf0",
}


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check(src: Path, name: str) -> None:
    got = sha256(src)
    assert got == EXPECTED[name], f"{name}: {got} != {EXPECTED[name]}"


def w(p: Path, text: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


# --- byte-exact copies -------------------------------------------------------
for name, src in [
    ("Statement.lean", F / "challenge/Statement.lean"),
    ("Definitions.lean", F / "challenge/OAI/Geometry/HeilbronnTriangle/Definitions.lean"),
    ("VacuityCheck.lean", F / "autoresearch/VacuityCheck.lean"),
    ("LICENSE", F / "challenge/LICENSE"),
    ("NOTICE", F / "challenge/NOTICE"),
]:
    check(src, name)

defs_rel = "OAI/Geometry/HeilbronnTriangle/Definitions.lean"
# frozen definitions at BOTH module paths (Submission.* copy + original OAI.* root)
(S / "Submission" / defs_rel).parent.mkdir(parents=True, exist_ok=True)
(S / defs_rel).parent.mkdir(parents=True, exist_ok=True)
shutil.copyfile(F / "challenge/OAI/Geometry/HeilbronnTriangle/Definitions.lean",
                S / "Submission" / defs_rel)
shutil.copyfile(F / "challenge/OAI/Geometry/HeilbronnTriangle/Definitions.lean",
                S / defs_rel)
shutil.copyfile(F / "challenge/LICENSE", S / "LICENSE")
shutil.copyfile(F / "profiles/lake-manifest.json", S / "lake-manifest.json")
# local dry-run replica of the pipeline-generated challenge root (byte-exact
# original Statement.lean, original import path -> resolves via the OAI lib)
shutil.copyfile(F / "challenge/Statement.lean", S / "VerifierChallenge.lean")

for p, name in [
    (S / "Submission" / defs_rel, "Definitions.lean"),
    (S / defs_rel, "Definitions.lean"),
    (S / "VerifierChallenge.lean", "Statement.lean"),
    (S / "LICENSE", "LICENSE"),
]:
    assert sha256(p) == EXPECTED[name], f"copy mismatch: {p}"

# --- toolchain + lakefile (mirror verifier.py lakefile(), roots per profile) --
w(S / "lean-toolchain", "leanprover/lean4:v4.34.1\n")

w(S / "lakefile.toml", '''name = "Verifier"
version = "0.1.0"
[leanOptions]
autoImplicit = false
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"

[[lean_lib]]
name = "Submission"

[[lean_lib]]
name = "OAI"

[[lean_lib]]
name = "VerifierChallenge"

[[lean_lib]]
name = "VerifierAudit"
''')

# --- derived files: import rewrite + provenance ------------------------------
PROV = (
    "-- Provenance: copied from bigospeedrun/verifier@{commit}\n"
    "--   file: {path} (blob {blob}, sha256 {sha}), fetched {date}.\n"
    "--   ONLY the import path(s) below were adjusted to the Submission/ layout\n"
    "--   (challenge README's copy-into-Submission option); body unchanged.\n"
)

stmt = (F / "challenge/Statement.lean").read_text()
assert stmt.startswith("import OAI.Geometry.HeilbronnTriangle.Definitions\n")
stmt_out = ("import Submission.OAI.Geometry.HeilbronnTriangle.Definitions\n"
            + PROV.format(commit=VERIFIER_COMMIT,
                          path="challenges/heilbronn-triangle/Statement.lean",
                          blob="e2513ec608abcc958d9bb2b9f44e0da98c62ebe5",
                          sha=EXPECTED["Statement.lean"], date=FETCH_DATE)
            + stmt.split("\n", 1)[1])
w(S / "Submission/Statement.lean", stmt_out)

vac = (F / "autoresearch/VacuityCheck.lean").read_text()
assert vac.startswith("import Statement\n")
vac_out = ("import Submission.Statement\n"
           + PROV.format(commit=VERIFIER_COMMIT,
                         path="auto-research/lean-statements/2026-10-19-joshuacortez-"
                              "heilbronn-triangle/VacuityCheck.lean",
                         blob="1c98724e2000e2e3a6593a208108e2055f9dbe5b",
                         sha=EXPECTED["VacuityCheck.lean"], date=FETCH_DATE)
           + "--   Authorship (upstream NOTICE.md): Claude Opus 5.5 (Anthropic) as agent\n"
           + "--   for @joshuacortez, who reviewed and submitted it. Apache-2.0; header below\n"
           + "--   preserved verbatim.\n"
           + vac.split("\n", 1)[1])
w(S / "Submission/VacuityCheck.lean", vac_out)

# --- alternate target forms (generator-shape insurance) -----------------------
w(S / "Submission/ZeroForms.lean", '''import Submission.Statement

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

/-- η = 0 in the `((p : ℚ) / q)` generator shape, `q = 1`. -/
theorem bound_zero_div_form : Bound ((0 : ℚ) / 1) := bound_zero

end BigOSpeedrun.HeilbronnTriangle
''')

# --- root entry ----------------------------------------------------------------
w(S / "Submission.lean", '''import Submission.Statement
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
''')

# --- local dry-run audit root (replica of the pipeline's VerifierAudit) --------
w(S / "VerifierAudit.lean", '''import Submission
#print axioms Race.bound
''')

# --- provenance + housekeeping --------------------------------------------------
w(S / "PROVENANCE.md", f"""# Stage A provenance (R2125607854 pre-build, {FETCH_DATE})

All upstream content fetched read-only via `gh api` from
`bigospeedrun/verifier@main = {VERIFIER_COMMIT}` on {FETCH_DATE}; every copy
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
""")

w(S / ".gitignore", ".lake/\n")

print("scaffold OK")
for p in sorted(S.rglob("*")):
    if p.is_file() and ".lake" not in p.parts and p.name != ".gitignore":
        print(f"  {p.relative_to(S)}  sha256={sha256(p)[:16]}")
