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
the interpolation bridge plus packaging. It does not improve the mathematical
record; the claimed frontier on this board is orders of magnitude better.

## License

Apache-2.0. See `LICENSE` and `NOTICE`.

---

## Why this repo is up

Reproducible verified bounds: this package backs the org's Heilbronn triangle filing (bound 1/10²³⁷, verifier#126 verified) so anyone can rebuild and recheck it against the board's issue route.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

The filed bound is verified (verifier#126). Open work: independent rebuilds of the pinned package; the next positive-power improvement (see the heilbronn-bar lane for the live bar).

