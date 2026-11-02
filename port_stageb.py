#!/usr/bin/env python3
"""Port openai/math's HeilbronnTriangle tree into stageb/ (R2125607854).

Mechanical port ONLY (per mission): copy every file, rewrite import roots
OAI.Geometry.HeilbronnTriangle* -> Submission.OAI.Geometry.HeilbronnTriangle*,
keep everything else byte-identical. NO bridge proofs here (next mission).

Verifications performed:
  - source pin: git rev-parse HEAD == 1581d4cbdd69a0faf34b2089614fe2a814316a6a
  - every ported file differs from its source ONLY on `import OAI...` lines
  - Definitions.lean (and any file with no internal imports) stays byte-exact
  - file counts: 242 dir files + 1 hub module = 243
  - writes stageb/PORT_MANIFEST.json with per-file sha256 (source + ported)
"""
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

WS = Path("/Volumes/Substrate-1/bigo/heilbronn-lane")
SRC = WS / "openai-math-src"
PIN = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
TREE_SRC = SRC / "lean/OAI/Geometry/HeilbronnTriangle"
HUB_SRC = SRC / "lean/OAI/Geometry/HeilbronnTriangle.lean"
B = WS / "stageb"
TREE_DST = B / "Submission/OAI/Geometry/HeilbronnTriangle"
HUB_DST = B / "Submission/OAI/Geometry/HeilbronnTriangle.lean"

OLD = "import OAI.Geometry.HeilbronnTriangle"
NEW = "import Submission.OAI.Geometry.HeilbronnTriangle"


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


head = subprocess.check_output(["/usr/bin/git", "-C", str(SRC), "rev-parse", "HEAD"],
                               text=True).strip()
assert head == PIN, f"source pin mismatch: {head}"

sources = sorted(TREE_SRC.glob("*.lean"))
assert len(sources) == 242, f"expected 242 dir files, got {len(sources)}"
assert HUB_SRC.exists()

TREE_DST.mkdir(parents=True, exist_ok=True)
manifest = {"source_repo": "https://github.com/openai/math", "source_commit": PIN,
            "source_path": "lean/OAI/Geometry/HeilbronnTriangle/",
            "rewrite": f"'{OLD}*' -> '{NEW}*'; all other lines byte-identical",
            "files": {}}

rewritten = byte_exact = 0
for src in sources + [HUB_SRC]:
    rel = src.relative_to(SRC / "lean")  # OAI/Geometry/HeilbronnTriangle[.lean]/X.lean
    dst = B / "Submission" / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    text = src.read_text()
    out_lines = []
    changed = 0
    for line in text.split("\n"):
        if line.startswith(OLD):
            out_lines.append(NEW + line[len(OLD):])
            changed += 1
        else:
            out_lines.append(line)
    out = "\n".join(out_lines)
    dst.write_text(out)
    # verify: only import lines differ
    a, b = text.split("\n"), out.split("\n")
    assert len(a) == len(b)
    for x, y in zip(a, b):
        assert x == y or (x.startswith(OLD) and y == NEW + x[len(OLD):]), \
            f"non-import line changed in {rel}"
    if changed:
        rewritten += 1
    else:
        byte_exact += 1
        assert sha256(dst) == sha256(src)
    manifest["files"][str(rel)] = {"source_sha256": sha256(src),
                                   "ported_sha256": sha256(dst),
                                   "imports_rewritten": changed}

# Definitions.lean must be byte-exact (frozen upstream file, only 'import Mathlib')
defs = TREE_DST / "Definitions.lean"
assert sha256(defs) == "e0d75ecc36327321392b4d3c8f08cc7ecfcf678cdc47ccfde314fb8dd9c9196d"

# LICENSE (Apache-2.0, repo root) + toolchain/manifest/lakefile
shutil.copyfile(SRC / "LICENSE", B / "LICENSE")
(B / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
shutil.copyfile(WS / "_fetched/profiles/lake-manifest.json", B / "lake-manifest.json")
(B / "lakefile.toml").write_text('''name = "Verifier"
version = "0.1.0"
[leanOptions]
autoImplicit = false
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"

[[lean_lib]]
name = "Submission"
''')
(B / ".gitignore").write_text(".lake/\n")

# Statement copy (same derived file as stagea: frozen statement, import adjusted)
shutil.copyfile(WS / "stagea/Submission/Statement.lean", B / "Submission/Statement.lean")

# Provisional root hub (replaced by the Race.bound entry when the bridge lands)
(B / "Submission.lean").write_text('''import Submission.OAI.Geometry.HeilbronnTriangle
import Submission.Statement

/-!
Provisional root hub for the Stage B port (R2125607854 pre-build, 2026-11-02).
Imports the full ported comparator tree so `lake build Submission` elaborates
every file. When the §8 bridge lands (next mission), this file becomes the
entry point declaring `theorem Race.bound :
BigOSpeedrun.HeilbronnTriangle.Bound <eta-zero-rational>`.

Ported tree: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/Geometry/HeilbronnTriangle/ (242 files) + the HeilbronnTriangle.lean
hub module; Apache-2.0 (LICENSE); import roots rewritten to Submission.*, all
other lines byte-identical (see PORT_MANIFEST.json).
-/
''')

manifest["counts"] = {"dir_files": len(sources), "hub": 1,
                      "files_with_rewritten_imports": rewritten,
                      "byte_exact_files": byte_exact}
(B / "PORT_MANIFEST.json").write_text(json.dumps(manifest, indent=1) + "\n")

print(f"port OK: {rewritten} files import-rewritten, {byte_exact} byte-exact "
      f"(incl. Definitions.lean), total {len(sources) + 1} modules")
