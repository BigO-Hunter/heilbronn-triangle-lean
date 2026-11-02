#!/usr/bin/env python3
"""Generate stageb/scratch/ huge-rational smoke files (Task B.3, R2125607854).

SCRATCH ONLY — nothing here ships. Tests elaboration/kernel mechanics of the
237-digit rational η₀ = 1/(100000·K) the controller would substitute, to
de-risk probe-report risk #4. Timings: run smoke_time.sh (each file timed via
`lake env lean`, S0 baseline subtracts import overhead).
"""
import json
from pathlib import Path

WS = Path("/Volumes/Substrate-1/bigo/heilbronn-lane")
D = json.loads((WS / "_riders/k_digits.json").read_text())["D"]  # 100000·K, 237 digits
D2 = str(2 * int(D))  # 238 digits
SCR = WS / "stageb/scratch"
SCR.mkdir(parents=True, exist_ok=True)

HDR = """-- SCRATCH smoke test (R2125607854 pre-build) — NOT part of any submission.
-- η₀ literal: 1/{D} (D = 100000·K, K = T²+1 has 232 digits; D has {nd} digits).
import Submission.Statement

open BigOSpeedrun.HeilbronnTriangle
"""


def w(name: str, body: str) -> None:
    (SCR / name).write_text(HDR.format(D=D, nd=len(D)) + body)


w("S0_baseline.lean", """
-- import-overhead baseline: no huge literals
#check @Bound
""")

w("S1_elab_huge.lean", f"""
-- Statement-shape elaboration with the full 237-digit literal (sorry: SCRATCH ONLY)
theorem huge_shape : Bound (1 / {D} : ℚ) := by sorry
#check @huge_shape
""")

w("S2_kernel_rfl.lean", f"""
-- Kernel-side handling of the huge literal: defeq + numeral ascription
example : ℚ := (1 : ℚ) / {D}
example : (1 : ℚ) / {D} = (1 : ℚ) / {D} := rfl
theorem huge_shape' : Bound ((1 : ℚ) / {D}) := by sorry
example : Bound ((1 : ℚ) / {D}) := huge_shape'
""")

w("S3_norm_num_reduce.lean", f"""
-- Reduced-rational mechanics the filing path needs (subset-sum #94 lesson:
-- Rat literal forms do NOT defeq-reduce; bridges go through norm_num + rw).
example : ((2 : ℚ) / {D2}) = ((1 : ℚ) / {D}) := by norm_num
example : (({D} : ℚ) / {D}) = (1 : ℚ) := by norm_num
example : ((1 : ℚ) / {D}) > 0 := by norm_num
""")

w("S4_rpow_elab.lean", f"""
-- rpow algebra shape with the huge exponent (elaboration only; proofs next mission)
example (n : ℕ) : ℝ := (n : ℝ) ^ (-2 + ((1 : ℚ) / {D} : ℝ))
-- literal η vs symbolic heilbronnExponent (heilbronnK is @[irreducible] upstream):
-- the statement must ELABORATE with K opaque; proving it is the bridge mission.
example : ((1 : ℚ) / {D} : ℝ) ≤ 1 / (100000 * (OAI.Problem355.heilbronnK : ℝ)) := by sorry
example : ((1 : ℚ) / {D} : ℝ) < (0 : ℝ) + 1 := by norm_num
""")

w("S5_div_one_form.lean", f"""
-- targets.md generator shape `((p : ℚ) / q)` with the huge q, plus the
-- bound_mono-style transport shape (η' ≤ η → Bound η' given Bound η)
theorem huge_shape_div : Bound ((1 : ℚ) / {D}) := by sorry
theorem bound_one_scratch : Bound (1 : ℚ) := by sorry  -- SCRATCH placeholder
example : Bound ((1 : ℚ) / {D}) :=
  bound_mono bound_one_scratch (by norm_num)
""")

# S5 uses bound_mono from VacuityCheck — needs that import too
p = SCR / "S5_div_one_form.lean"
p.write_text(p.read_text().replace("import Submission.Statement",
           "import Submission.Statement\nimport Submission.VacuityCheck"))

print("smoke files written:")
for f in sorted(SCR.glob("S*.lean")):
    print(f"  {f.name} ({f.stat().st_size} bytes)")
