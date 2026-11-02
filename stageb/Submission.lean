import Submission.OAI.Geometry.HeilbronnTriangle
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
