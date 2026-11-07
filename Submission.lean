import Submission.HeilbronnStatement
import Submission.OAI.Geometry.HeilbronnTriangle
import Submission.Bridge.Assembly

/-!
Big O Speedrun — Heilbronn triangle, Lean submission entry point.

Board: https://bigospeedrun.com/other/heilbronn-triangle
Target per docs/targets.md: `theorem Race.bound : ... Bound ((p : ℚ) / q)`.

Filed saving: eta = 1/(100000·K) with the EXACT K = heilbronnT² + 1 computed
in `Submission/Bridge/KBound.lean` (`heilbronnK_val`: 232-digit literal via
the factorial route — M literal → 6T = M(M−1)(M−2) → K = T²+1), so

  eta = 1/1386111206301928454498485019847624895039491801209725212873
        0425919908971829698657583967280364458651602109006309282023968
        540550722705409312459754149245805196259647487531313292805515
        3805949190893429472432269634916029759500562026384000100000

(237-digit denominator, numerator 1 ⇒ reduced) ≈ 7.2144·10⁻²³⁷ — the exact
symbolic exponent `heilbronnExponent = 1/(100000·K)` the OpenAI comparator
tree proves (`Submission/Bridge/Assembly.lean::bound_stageB` is stated AT
`heilbronnExponent`; the earlier crude floor `heilbronnK ≤ 10^232` and the
≤-monotonicity step are gone — the literal IS the exponent now).

Provenance of the proof tree:
* `Submission/HeilbronnStatement.lean` is `challenges/heilbronn-triangle/
  VerifierStatement.lean` (bigospeedrun/verifier) copied byte for byte,
  git blob bff8ba7bc805b881893123eb9b26e348b2bb6ee8. It carries OpenAI's
  frozen `OAI.Problem355` definitions (openai/math@1581d4cb, Apache-2.0) and
  the parameterized `BigOSpeedrun.HeilbronnTriangle.Bound`.
* `Submission/OAI/Geometry/HeilbronnTriangle/**` is OpenAI's comparator proof
  tree (openai/math@1581d4cb, Apache-2.0), 243 modules, imports rewritten.
  Its `Definitions.lean` path is kept as a one-line re-export of the trusted
  statement so every ported module keeps its original import line.
* `Submission/Bridge/**` is new work: the section-8 interpolation that turns
  OpenAI's subsequence statement into this board's "every large n" statement.

Axiom audit for `Race.bound`: exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no custom axioms, no `native_decide`.
-/

theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound ((1 : ℚ) /
      138611120630192845449848501984762489503949180120972521287304259199089718296986575839672803644586516021090063092820239685405507227054093124597541492458051962596474875313132928055153805949190893429472432269634916029759500562026384000100000) := by
  have hcast : ((((1 : ℚ) /
      138611120630192845449848501984762489503949180120972521287304259199089718296986575839672803644586516021090063092820239685405507227054093124597541492458051962596474875313132928055153805949190893429472432269634916029759500562026384000100000) : ℚ) : ℝ)
      = (1 : ℝ) /
      (100000 *
        1386111206301928454498485019847624895039491801209725212873042591990897182969865758396728036445865160210900630928202396854055072270540931245975414924580519625964748753131329280551538059491908934294724322696349160297595005620263840001) := by
    norm_num
  have heta : (1 : ℝ) /
      (100000 *
        1386111206301928454498485019847624895039491801209725212873042591990897182969865758396728036445865160210900630928202396854055072270540931245975414924580519625964748753131329280551538059491908934294724322696349160297595005620263840001)
      = OAI.Problem355.heilbronnExponent :=
    OAI.Problem355.Bridge.eta_eq_heilbronnExponent
  obtain ⟨c, hc, N, hN⟩ := OAI.Problem355.Bridge.bound_stageB
  refine ⟨c, hc, N, fun n hn => ?_⟩
  obtain ⟨P, hcard, hsq, harea⟩ := hN n hn
  refine ⟨P, hcard, hsq, ?_⟩
  rw [hcast, heta]
  exact harea
