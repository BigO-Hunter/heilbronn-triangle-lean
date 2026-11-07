# Heilbronn triangle — Lean submission (Big O Speedrun)

Entry point for the [Big O Speedrun Heilbronn triangle board](https://bigospeedrun.com/other/heilbronn-triangle),
issue route.

```lean
import Submission.HeilbronnStatement

theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound ((1 : ℚ) / 10^237) := …
```

Filed saving: `η = 1/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000`
= `10^-237` (238-digit denominator, one reduced fraction of digits, as the
submission form requires).

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

The saving is proven at `1/(100000·10^232)`, slightly below the exact
comparator exponent `1/(100000·K)`: `heilbronnK ≤ 10^232` is proved with `K`
kept opaque, so nothing unfolds the 232-digit numeral `K`.

Axiom audit (`#print axioms Race.bound`):

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no `native_decide`, no custom axioms.

## Credit

The frozen definitions and the entire comparator proof tree are OpenAI's
(Apache-2.0, `LICENSE`). The parameterized board statement is from the
bigospeedrun statement-review contribution. This repository's contribution is
the interpolation bridge plus packaging. It does not improve the mathematical
record; the claimed frontier on this board is orders of magnitude better.

## License

Apache-2.0. See `LICENSE` and `NOTICE`.
