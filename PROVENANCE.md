# Provenance

Three layers, all credited.

## 1. Trusted statement (copied byte for byte)

`Submission/HeilbronnStatement.lean`
= `challenges/heilbronn-triangle/VerifierStatement.lean` from
[bigospeedrun/verifier](https://github.com/bigospeedrun/verifier).

* Git blob: `bff8ba7bc805b881893123eb9b26e348b2bb6ee8`, 2751 bytes.
* Verified locally with `git hash-object -t blob` against the GitHub blob sha.
* Not modified. Every definition Comparator matches (`Point`, `triangleArea`,
  `pointInUnitSquare`, `pointsInUnitSquare`, `triangleAreasAtLeast`,
  `heilbronnD`, `heilbronnM`, `heilbronnT`, `heilbronnK`,
  `heilbronnExponent`, `eventualAlmostUpperBound`) and `Bound` itself come
  from this file.
* Authors: OpenAI (the frozen `OAI.Problem355` definitions) plus the statement
  review contribution by @joshuacortez with Claude (Anthropic) as agent for the
  parameterized adapter. Apache-2.0.

## 2. Proof tree (OpenAI)

`Submission/OAI/Geometry/HeilbronnTriangle/**`, 243 modules, is the comparator
proof tree from [openai/math](https://github.com/openai/math) at commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, path
`lean/OAI/Geometry/HeilbronnTriangle/`.

* Authors: OpenAI. Apache-2.0 (`LICENSE`).
* Change made by us: **import paths only** — `import OAI.Geometry.HeilbronnTriangle*`
  became `import Submission.OAI.Geometry.HeilbronnTriangle*`. Every other line is
  byte-identical; `PORT_MANIFEST.json` records source and ported SHA-256 per file.
* `Submission/OAI/Geometry/HeilbronnTriangle/Definitions.lean` is kept at its
  original module path but is now a one-line re-export of
  `Submission.HeilbronnStatement`, because the trusted statement already
  carries those definitions verbatim and the verifier does not stage the
  original module. This is the only file whose body we replaced, and the body
  it used to carry is present unchanged inside `Submission/HeilbronnStatement.lean`.

The upstream tree proves a *subsequence* statement at the fixed exponent
`η₀ = 1/(100000·K)`. It is used here only as a library; every theorem proved in
this repository is new.

## 3. New work (this repository)

| File | Content |
|---|---|
| `Submission/Bridge/Cardinality.lean` | Two-sided `sampleCard` bounds: `√2·r^(k·45435+16) − 1 < sampleCard ≤ √(3·2³⁰·(200k²)^(k·3029+1))·r^(k·45435+16)`. The `α = 45435k+16` exponent matches the board baseline `2/(45435K+16)`. |
| `Submission/Bridge/KBound.lean` | `heilbronnK ≤ 10^232` with `K` kept opaque (`K = T²+1`, `T = choose M 3`, `M = choose 163 41`), plus `1/(100000·10^232) ≤ heilbronnExponent`. |
| `Submission/Bridge/Assembly.lean` | Section-8 interpolation: Bertrand prime choice, `m = ⌈((n+1)/√2)^(1/α)⌉`, `s ∈ [n, C′·n]`, deletion to exactly `n` points, and `bound_stageB : ∃ c > 0, ∃ N, ∀ n ≥ N, ∃ P, …` at exponent `1/(100000·10^232)`. |
| `Submission.lean` | Entry point: `theorem Race.bound : BigOSpeedrun.HeilbronnTriangle.Bound ((1 : ℚ) / 10^237)`. |

`BRIDGE_EDITS.md` records every file the bridge touched, including the zero
edits to the ported tree.

## What is proven and what is not

Proven: `Δ(n) ≥ c·n^(-2+η)` for every `n ≥ N`, with `η = 10^-237`.

Not proven here: the exact paper exponent `η₀ = 1/(100000·K) ≈ 7.2·10^-237`.
The filed value is smaller, which implies the same shape at a slightly weaker
saving; no monotonicity lemma is needed because the interpolation is carried
out directly at `1/(100000·10^232)`.

Nothing here improves the state of the art. The value of the row is that it is
the first machine-verified *positive* saving on this board: it checks that the
`Bound η` target is attainable at all, and that OpenAI's comparator tree
extends from a subsequence statement to the board's "every large `n`" form.
