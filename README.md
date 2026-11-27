# Heilbronn triangle — Lean submission (Big O Speedrun)

Entry point for the [Big O Speedrun Heilbronn triangle board](https://bigospeedrun.com/other/heilbronn-triangle),
issue route.

```lean
import Submission.HeilbronnStatement

theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound
      ((1 : ℚ) / 138611120630192845449848501984762489503949180120972521287304259199089718296986575839672803644586516021090063092820239685405507227054093124597541492458051962596474875313132928055153805949190893429472432269634916029759500562026384000100000) := …
```

Filed saving: `η = 1/(100000·K) = 1/138611120630192845449848501984762489503949180120972521287304259199089718296986575839672803644586516021090063092820239685405507227054093124597541492458051962596474875313132928055153805949190893429472432269634916029759500562026384000100000`
(237-digit denominator, numerator 1 ⇒ one reduced fraction, as the
submission form requires).

**Filing status:** verifier#184 — Lean Verified for commit `6189ae97` (run 42435729355). η ≈ 7.2144×10⁻²³⁷ ≈ 7.2× the 1/10²³⁷ bar.

## Build

Lean `leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
(the board pins), `autoImplicit = false`:

```
lake exe cache get
lake build Submission
```

Warm-cached this is ~9172 jobs. Cold, budget well inside the verifier's
320-minute one-job deadline (measured locally: port-only tree builds in ~7 min
warm on 12 cores).

## What the proof does

`Submission/HeilbronnStatement.lean` is the board's trusted
`VerifierStatement.lean`, copied byte for byte (git blob
`bff8ba7bc805b881893123eb9b26e348b2bb6ee8`). Everything else is either
OpenAI's comparator proof tree from [openai/math](https://github.com/openai/math)
at `1581d4cb` (imports rewritten only) or the new bridge in `Submission/Bridge/`
that turns that tree's subsequence statement into the board's "every large `n`"
statement. See `PROVENANCE.md` and `BRIDGE_EDITS.md`.

The saving is proven at the exact comparator exponent `1/(100000·K)`:
`K = C(C(163,41),3)² + 1` is computed in Lean as a 232-digit numeral via the
factorial route (`Submission/Bridge/KBound.lean`), reached only through the
in-tree `heilbronnK_eq`, never by unfolding the `@[irreducible]` definition.

Axiom audit (`#print axioms Race.bound`):

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no custom axioms.

## Credit

The frozen definitions and the entire comparator proof tree are OpenAI's
(Apache-2.0, `LICENSE`). The parameterized board statement is from the
bigospeedrun statement-review contribution. This repository's contribution is
the interpolation bridge plus packaging.

## License

Licensed under the CFSF License — see `LICENSE` ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf)). The vendored maintainer statement keeps its upstream license — see `NOTICE`.

## Next steps

Independent rebuilds of the pinned package (verified pin: `6189ae976a538f309232e73ad147c351dc2410f2`, closed 2026-11-08; commits after the pin are docs/license only). The next positive-power improvement lives in the [heilbronn-bar](https://github.com/BigO-Hunter/heilbronn-bar) lane (private). The 1/10²³⁷ bar is held by [heilbronn-triangle-ten237](https://github.com/BigO-Hunter/heilbronn-triangle-ten237) ([verifier#126](https://github.com/bigospeedrun/verifier/issues/126)).

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for [Big O Speedrun](https://bigospeedrun.com) contributions · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).
