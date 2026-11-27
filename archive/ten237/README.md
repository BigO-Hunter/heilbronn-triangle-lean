# heilbronn-triangle-ten237

Lean Verified submission for the [Big O Speedrun heilbronn-triangle board](https://bigospeedrun.com/other/heilbronn-triangle) — the first machine-checked positive power improvement on the board's issue route (opened 2026-11-03, [verifier#105](https://github.com/bigospeedrun/verifier/issues/105)).

> Board (Nov 26 2026): this repo verifies η = 1/10²³⁷ (Lean); the open race is currently led by Qiuyu Chen (Euler)'s claimed η > 1.98·10⁻⁸ (Oct 19) — see [bigospeedrun.com](https://bigospeedrun.com).

## The result

```lean
theorem Race.bound :
    BigOSpeedrun.HeilbronnTriangle.Bound ((1 : ℚ) / 1000...0)  -- 1/10^237, 238-digit literal
```

The filed saving is `η = 1/10^237 = 1/(100000·10^232)`, written in the entry as one reduced fraction of literal digits. It is slightly below the paper-exact `η₀ = 1/(100000·K)` of OpenAI's preprint *A power improvement in the Heilbronn triangle lower bound* (Sep 25, 2026): the proof establishes `K ≤ 10^232` symbolically with `heilbronnK` kept `@[irreducible]`-opaque, so the board's bound holds at the filed value directly — `Race.bound` proves exactly the filed rational, with no monotonicity transport.

- **Axioms:** exactly `propext`, `Classical.choice`, `Quot.sound`.
- **Zero** `sorry`, `axiom`, `native_decide`.
- **Pins:** Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (`profiles/lake-manifest.json` on the verifier) — the same pins the frozen definitions were authored under.

## Layout

| Path | What |
|---|---|
| `Submission.lean` | root entry: `theorem Race.bound` |
| `Submission/HeilbronnStatement.lean` | **byte-for-byte** copy of [`challenges/heilbronn-triangle/VerifierStatement.lean`](https://github.com/bigospeedrun/verifier/blob/main/challenges/heilbronn-triangle/VerifierStatement.lean) at verifier main `be0eb9436df5adf2502fa7bba41672ce6ff0df15` (sha256 `efc9772011b2104ba2cb51bd672e1bb974ab1a29f2384922e1c62f54307e32cb`) |
| `Submission/OAI/Geometry/HeilbronnTriangle/**` | port of [`openai/math`](https://github.com/openai/math) at `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, `lean/OAI/Geometry/HeilbronnTriangle/` (242 files + hub). **Only import lines differ** from upstream (`OAI.*` → `Submission.OAI.*`, and the frozen `Definitions` import → `Submission.HeilbronnStatement`, since the verifier does not stage that module next to submissions); every other line is byte-identical. Apache-2.0. |
| `Submission/Bridge/{Cardinality,KBound,Assembly}.lean` | new: the §8 interpolation from the comparator's subsequence form to the board's "every sufficiently large `n`" form — per-`n` Bertrand prime choice, two-sided `sampleCard` cardinality bounds (`α = 45435k+16`), opaque-`K` bound `K ≤ 10^232`, `Finset.exists_subset_card_eq` deletion to exact `n`, `rpow` exponent algebra |
| `Submission/VacuityCheck.lean` | the challenge package's vacuity checks (`bound_mono`, `bound_zero`, `not_bound_of_two_lt`), import path adjusted only |

## Build

```bash
lake exe cache get   # Mathlib oleans
lake build Submission
```

## License and provenance

Licensed under the CFSF License (see `LICENSE`, ([github.com/darkhipo/cfsf](https://github.com/darkhipo/cfsf))). Definitions and the comparator proof tree: Copyright OpenAI (see `NOTICE`, `LICENSE`). Vacuity checks: prepared with assistance from Claude (Anthropic) for @joshuacortez. Bridge, port rewiring and this entry: prepared by darkhipo's agent. The Heilbronn statement files come from [bigospeedrun/verifier](https://github.com/bigospeedrun/verifier), which credits the sources above.

## Status and next steps

Lean Verified via [verifier#126](https://github.com/bigospeedrun/verifier/issues/126) (run 41623930086); the board pins this repo @ `236a3233`. Open work: independent reruns. The exact-K rung above this bar — η = 1/(100000·K) ≈ 7.2144×10⁻²³⁷, `K = C(C(163,41),3)²+1` computed in Lean, Lean Verified as [verifier#184](https://github.com/bigospeedrun/verifier/issues/184) @ `6189ae97` — is in [BigO-Hunter/heilbronn-triangle-lean](https://github.com/BigO-Hunter/heilbronn-triangle-lean). Heilbronn board history: [heilbronn-bar](https://github.com/BigO-Hunter/heilbronn-bar).

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for [Big O Speedrun](https://bigospeedrun.com) contributions · [org profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).
