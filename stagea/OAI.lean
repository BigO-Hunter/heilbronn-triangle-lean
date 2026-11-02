import OAI.Geometry.HeilbronnTriangle.Definitions

/-!
Minimal root hub for the local `OAI` lean_lib (Lake's default glob requires the
root module file to exist). This root exists ONLY for the insurance layout in
which a future heilbronn profile stages the challenge folder's frozen
`OAI/Geometry/HeilbronnTriangle/Definitions.lean` at its original module path
next to the submission (challenge README: "the profile can stage this folder
next to the submission"); `VerifierChallenge.lean` (the byte-exact original
Statement.lean) imports it under that name. The shipped Stage A submission tree
is self-contained under `Submission/` and does not need this file.

Provenance: Definitions.lean byte-exact from bigospeedrun/verifier@d025a32
(challenges/heilbronn-triangle/OAI/Geometry/HeilbronnTriangle/Definitions.lean,
blob 6dd76ecf, sha256 e0d75ecc...; © OpenAI, Apache-2.0, openai/math@1581d4cb).
This hub file is new (local pre-build R2125607854, 2026-11-02).
-/
