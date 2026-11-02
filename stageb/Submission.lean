import Submission.OAI.Geometry.HeilbronnTriangle
import Submission.Statement
import Submission.VacuityCheck
import Submission.Bridge.Assembly

/-!
Provisional root hub for the Stage B port (R2125607854 pre-build, 2026-11-02).
Imports the full ported comparator tree so `lake build Submission` elaborates
every file. The §8 bridge has now landed (Submission/Bridge/); it is imported
here so the default lib build covers the Bridge modules too (this lakefile's
lean_lib builds roots + import closure, NOT a directory glob — the booked
"glob-cache skip" gotcha is exactly this). The filed entry
`theorem Race.bound : BigOSpeedrun.HeilbronnTriangle.Bound (1/10^237 : ℚ)`
currently lives in the workspace-root `EntryDryRun.lean` (dry-run per mission
spec); packaging into the filed Submission.lean shape happens at gate open,
per the shape the live target generator binds.

Ported tree: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/OAI/Geometry/HeilbronnTriangle/ (242 files) + the HeilbronnTriangle.lean
hub module; Apache-2.0 (LICENSE); import roots rewritten to Submission.*, all
other lines byte-identical (see PORT_MANIFEST.json).
-/
