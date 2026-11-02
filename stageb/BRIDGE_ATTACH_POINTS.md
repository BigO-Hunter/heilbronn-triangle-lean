# Stage B — bridge attach points (port kickoff report, R2125607854)

Date: 2026-11-02. Port of `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`
`lean/OAI/Geometry/HeilbronnTriangle/` (242 dir files + `HeilbronnTriangle.lean` hub =
**243 modules**) into `stageb/Submission/OAI/Geometry/HeilbronnTriangle*`, import roots
rewritten `OAI.Geometry.HeilbronnTriangle*` → `Submission.OAI.Geometry.HeilbronnTriangle*`
(177 files rewritten, 66 byte-exact incl. frozen `Definitions.lean`; per-file sha256 in
`PORT_MANIFEST.json`). **Build GREEN on exact board pins** (v4.34.1 + Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612, byte-exact `profiles/lake-manifest.json`):
9169 jobs, **5m01s wall** (16-core M4 Max, warm Mathlib cache), zero sorry/axiom/native_decide
tree-wide. Import closure verified EXHAUSTIVELY self-contained: 519 internal imports +
67 `import Mathlib`, nothing else. Upstream dependency pins (aesop/Qq/batteries/plausible/
LeanSearchClient/importGraph/proofwidgets/Cli) are ALL identical to the board manifest —
one cache serves both stages.

## What the tree proves vs what the board wants

- Tree (Main.lean `heilbronn_power_lower_bound`): `0 < heilbronnExponent ∧ ∃ n : ℕ → ℕ,
  ∃ P : ℕ → Finset Point, Tendsto n atTop atTop ∧ ∀ j, 3 ≤ n j ∧ (P j).card = n j ∧
  pointsInUnitSquare (P j) ∧ triangleAreasAtLeast (P j) (rpow (n j) (-2 + heilbronnExponent))`
  — SUBSEQUENCE form, constant 1, exponent `heilbronnExponent = 1/(100000·(K:ℝ))` with
  `@[irreducible] heilbronnK`.
- Board (`BigOSpeedrun.HeilbronnTriangle.Bound η`, η : ℚ literal): `∃ c > 0, ∃ N, ∀ n ≥ N,
  ∃ P, P.card = n ∧ pointsInUnitSquare P ∧ triangleAreasAtLeast P (c · n^(-2+η))` — EVERY
  large n, unspecified c, literal rational η.
- Gaps (all elementary, per probe §1): (i) subsequence → ∀n via per-prime uniformity +
  Bertrand + deletion; (ii) symbolic exponent → literal η₀ ≤ heilbronnExponent with K
  OPAQUE; (iii) constant-1 → ∃c (free: c absorbs the bounded cardinality ratio factor).

## Attach points (all signatures verified against the checked-out pin)

1. **`ParameterSampling.lean:73` — `configuration_of_law {k r : ℕ} (D : PrimeParameterData k r)
   (L : PointLaw) {Cp Ct : ℝ} (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
   (hlarge : 4*Cp + 24*Ct*(31620*k+1 : ℝ)^2 < r)
   (hpair : L.pairProbability ≤ Cp*(D.M:ℝ)^6/(D.N:ℝ)^3)
   (htriple : L.tripleProbability (D.tau/(16*(D.N:ℝ)^3)) ≤ Ct*(log(2*(D.N:ℝ)))^2*D.h/((D.N:ℝ)^3*(r:ℝ)^41)) :
   ∃ P : Finset Point, P.card = D.sampleCard ∧ pointsInUnitSquare P ∧
   triangleAreasAtLeast P (D.tau/(16*(D.N:ℝ)^3))`** — the per-prime configuration machine.
   This is THE attach point: call it at the Bertrand-chosen prime r for each large n.

2. **`Main.lean:17-31` — the r0=0 instantiation**: `heilbronn_power_lower_bound` applies
   `ParameterSampling.heilbronn_power_lower_bound_of_point_laws` (ParameterSampling.lean:91)
   with `Cp := 8`, `Ct := (128/7)·UniformFixedFiberCount.countConstant`, and
   `refine ⟨0, ?_⟩` — i.e. the point-law hypothesis holds for EVERY prime r: given
   `hr : r.Prime` it builds `Fact r.Prime`, `Fact D.q.Prime` and supplies
   `ActualPointLaw.pointLaw D`, `ActualPointLaw.pairProbability_le D`,
   `ActualPointLaw.tripleProbability_le_of_count D ... UniformFixedFiberCount.matrix_fiber_le`.
   The bridge copies this instantiation verbatim per n (no sequence needed).

3. **`ParameterConclusion.lean:16,19` — `sampleCard` + its UPPER bound**:
   `def sampleCard (P : PrimeParameterData k r) : ℕ := ⌊(r:ℝ)·Real.sqrt((P.N:ℝ)³/(P.tau:ℝ))⌋₊`;
   `lemma sampleCard_le_power (P) : (P.sampleCard : ℝ) ≤ Real.rpow (r:ℝ) (100000*(k:ℝ))`
   (via `SampleUpper.lean:34 sample_size_le_real_power {n r N tau : ℝ} {k : ℕ} (hr : 1 ≤ r)
   (hN : 1 ≤ N) (htau : 1 ≤ tau) (hk : 1 ≤ k) (hbox : N ≤ r^(31620*k))
   (hsample : n ≤ r·sqrt(N³/tau)) : n ≤ rpow r (100000*(k:ℝ))`).
   **THE MISSING LEMMA is its mirror**: a LOWER bound `A·r^α ≤ sampleCard` with the SAME α
   (paper §8's two-sided `A_k r^α ≤ n_r ≤ D_k r^α`). Ingredients, all in-tree:
   - `ParameterSequence.lean:161 real_bounds : 1 ≤ (P.N:ℝ) ∧ 1 ≤ (P.tau:ℝ) ∧ (P.tau:ℝ) ≤ (P.N:ℝ)³
     ∧ (r:ℝ) ≤ (P.M:ℝ) ∧ (P.N:ℝ) ≤ (r:ℝ)^(31620*k)` (components 3–5 feed the lower estimate);
   - `Parameters.lean:56 def threshold (B k : ℕ) : ℕ := B^(k-1)/2` — so `P.tau = B^(k-1)/2`
     and with `base_upper : B ≤ 200k²r³⁰` / `base_polynomial : B ≤ r^31` an upper bound
     `tau ≤ r^(31(k-1))` is immediate; `N = M^10 = (h·q)^10`, `h = B^k`
     (ParameterSequence.lean:39-41) with `base_lower : 100k²r³⁰ < B` gives `N ≥ r^(300k·…)`;
   - `ParameterSampling.lean:36 r_le_sampleCard : r ≤ D.sampleCard` (the trivial α=1 lower
     bound — NOT sufficient alone: the deletion ratio must be bounded, see "the arithmetic"
     below).

4. **`PrimeParameters.lean:58` — `exists_prime_parameters (k r : ℕ) (hk : 0 < k)
   (hr : 200*k^2 ≤ r) : ∃ B q, B.Prime ∧ q.Prime ∧ 100k²r³⁰ < B ∧ B ≤ 200k²r³⁰ ∧ B ≤ r³¹ ∧
   (B^k)^100 < q ∧ q ≤ 2(B^k)^100 ∧ q ≤ (B^k)^101 ∧ (B^k).Coprime q ∧ 2000((B^k)²)² ≤ q`** —
   works for ANY r ≥ 200k². Cleaner wrapper already in-tree:
   **`ParameterSequence.lean:28 exists_primeParameterData (hk : 2 ≤ k) (hr : 400*k^2 ≤ r) :
   Nonempty (PrimeParameterData k r)`** — THIS is the constructor to call at the
   Bertrand-chosen r (structure `PrimeParameterData` at ParameterSequence.lean:11; k := heilbronnK
   with `heilbronnK_ge_two`; note `large_for_moment : 400k² ≤ r` is a field, hence the 400 threshold).

5. **Exponent algebra to per-n form**: `FinalScalingBridge.lean:61
   heilbronn_power_lower_bound_of_floor_configurations (r N τ : ℕ → ℝ) (hr : Tendsto r atTop atTop)
   (hscale : ∀ᶠ j, 0 < N j ∧ 0 < τ j ∧ τ j ≤ N j³) (hsize : ∀ᶠ j, (⌊r j·sqrt(N j³/τ j)⌋₊ : ℝ) ≤
   rpow (r j) (100000·(heilbronnK:ℝ))) (hconfig : ∀ᶠ j, ∃ P, P.card = ⌊…⌋₊ ∧ pointsInUnitSquare P ∧
   triangleAreasAtLeast P (τ j/(16·N j³))) : [subsequence conclusion]` — its internals
   (`FinalScalingBridge.lean:32 heilbronn_power_lower_bound_of_scaled_configurations`,
   `ExponentScaling.lean:10 exponent_scaling {n r a k : ℝ}`, `floor_sample_properties`,
   `sample_size_scaled_area`) carry the `area ≥ n_j^(-2+η₀)` algebra per j. The bridge either
   generalizes those steps to a FIXED r (most of them are pointwise already) or restates the
   per-j chain at the chosen r. `heilbronn_power_lower_bound_of_parameter_configurations`
   (ParameterConclusion.lean:33) shows the assembly pattern (sampleCard_le_power + real_bounds
   + configurations → conclusion).

6. **Deletion to exact n** (Mathlib, present at pins): `Finset.exists_subset_card_eq`
   (n ≤ s.card → ∃ t ⊆ s, t.card = n) + two 3-line restriction lemmas (both target props are
   ∀-over-membership): `t ⊆ s → triangleAreasAtLeast s a → triangleAreasAtLeast t a`,
   `t ⊆ s → pointsInUnitSquare s → pointsInUnitSquare t`. **Bertrand**:
   `Nat.exists_prime_lt_and_le_two_mul` (already exercised at these pins by Stage A's bound_zero).

7. **Symbolic-K rational side**: `Submission/VacuityCheck.lean bound_mono {η η' : ℚ}
   (h : Bound η) (hle : η' ≤ η) : Bound η'` (rpow_le_rpow_of_exponent_le machinery) — but its
   type is ℚ-indexed while the tree's exponent is `heilbronnExponent : ℝ`. The bridge proves
   the ℝ-variant directly: from per-n `area ≥ c·n^(-2+heilbronnExponent)` and
   `(η₀:ℝ) ≤ heilbronnExponent` conclude `Bound η₀` (for n ≥ N ≥ 1, rpow monotone in the
   exponent gives n^(-2+heiExp) ≥ n^(-2+η₀) — the GIVEN bound is the larger value, so the
   direction is free). The only place irreducibility bites: proving `(η₀:ℝ) ≤ 1/(100000·(K:ℝ))`
   with K opaque = proving `K ≤ L` for the literal L in η₀ = 1/(100000·L). Route: only
   `heilbronnK` is `@[irreducible]`; `heilbronnT = Nat.choose heilbronnM 3` and
   `heilbronnM = Nat.choose 163 41` are ordinary defs. `M` kernel-reduces to a 39-digit literal
   (choose on 163 — cheap); `T` does NOT (choose on a 39-digit argument). So bound symbolically:
   `T = choose M 3 ≤ M³` (prove via Nat.choose recursion or a Mathlib choose≤pow lemma),
   `K = T²+1 ≤ M⁶+1 =: L` (literal, ~232-233 digits). Then η₀ = 1/(100000·L) ≤ heilbronnExponent.
   NOTE: this yields a filed η₀ slightly BELOW the paper's exact 1/(100000K) (L ≥ K) — legal and
   still ~1e-236-scale, astronomically above nothing; alternatively prove K = literal by the same
   symbolic squeeze if maintainers want the exact exponent (both bounds → K pinned between
   literals; equality needs the exact T value — likely infeasible, and unnecessary: any η' ≤ η
   is listable, and a cleaner η₀ like 1/L' with L' = 10^233 > K also works and is prettier).

## The arithmetic the bridge must line up (why the LOWER bound is the real work)

Given large n: pick m := ⌈(n/A)^{1/α}⌉ (α = the cardinality exponent from the two-sided
bound, A its lower constant), Bertrand prime r ∈ (m, 2m] (needs r ≥ 400K² — true for large n),
`D := exists_primeParameterData (k := heilbronnK) …`, `P₀ := configuration_of_law D (pointLaw D) …`
(hlarge holds for r large), `s := D.sampleCard ∈ [A·r^α, D_k·r^α]` ⇒ `s ≥ n` and
`s ≤ C·n` with C = D_k·2^α/A^{…} CONSTANT in n. Delete to exactly n
(`Finset.exists_subset_card_eq`), area ≥ s^(-2+η₀)-ish ≥ (C·n)^(-2+η₀) = C^(-2+η₀)·n^(-2+η₀)
— board's `∃ c > 0` absorbs C^(-2+η₀) (never needs to be explicit). With ONLY `r ≤ sampleCard`
(α=1 lower) and `sampleCard ≤ r^(100000K)` upper, choosing r ∈ (n, 2n] gives s ≥ n but
s ≤ (2n)^(100000K) — ratio s/n unbounded ⇒ no constant c: this is precisely why the missing
sampleCard lower bound at matching α is the one genuine lemma of the bridge.

## Surprises / gotchas found during the port (booked for the bridge mission)

1. **Lake glob caching**: adding `Submission/VacuityCheck.lean` to the existing lib was NOT
   picked up by a bare `lake build Submission` (identical job count, module silently skipped);
   explicit `lake build Submission.VacuityCheck` built it (32s). After adding bridge files,
   build explicit targets once (or touch lakefile.toml).
2. **`/-! -/` docstring BEFORE imports is rejected** by v4.34.1 ("invalid 'import' command,
   it must be used in the beginning of the file") — keep `import` lines first (upstream style
   agrees; Stage A derived files preserved it; only scratch files hit this).
3. **Rat literal forms do NOT defeq-reduce** — `((0:ℚ)/1) ≠ defeq 0` at elaboration (Stage A
   ZeroForms, empirically; matches subset-sum #94 filing lesson) and `▸` picks the wrong
   direction easily: every rational-form bridge goes through `norm_num` + explicit `rw`.
4. **No per-file license headers upstream** — Apache-2.0 lives in the repo-root `LICENSE`
   (copied to `stageb/LICENSE`) and the directory has no LICENSE of its own; attribution is
   handled via stageb/NOTICE + PORT_MANIFEST.json.
5. **Upstream comparator target** (`lean/ComparatorChallenges/HeilbronnTriangle.lean`, fetched
   to `_reference/`) = the same frozen Definitions + two `sorry`ed statements
   (`heilbronn_power_lower_bound`, `almost_n_minus_two_refuted`) with
   `attribute [local irreducible] heilbronnT heilbronnM` — Main.lean carries the same local
   irreducibles; the bridge should replicate them where T/M appear in inequalities.
6. **Digits, exact** (computed from Definitions' recursion): M = C(163,41) has 39 digits,
   T = C(M,3) has 116, K = T²+1 has **232**, D = 100000·K has **237**, η₀ = 1/D ≈ 7.2e-237
   (probe's ≈7e-237 ✓; the mission's "233-digit" ≈ K's 232). Full literals: `_riders/k_digits.json`.

## Huge-rational smoke results (scratch/, NOT shipped; timings logs/smoke_timings.txt)

Warm-cache wall times, `lake env lean -DautoImplicit=false`, 16-core M4 Max; baseline
S0 (import Submission.Statement only) = 4.61s:

| file | shape tested | warm real | Δ vs baseline |
|---|---|---|---|
| S1_elab_huge | `theorem … : Bound (1 / <237-digit> : ℚ) := by sorry` | 4.89s | +0.28s |
| S2_kernel_rfl | ℚ ascription of huge literal + `rfl` equality + `((1:ℚ)/D)` div-form theorem | 4.52s | +0.00s |
| S3_norm_num_reduce | `norm_num`: (2/(2D)) = (1/D) [238-digit gcd], D/D = 1, 1/D > 0 | 5.39s | +0.78s |
| S4_rpow_elab | `#check` of `(n:ℝ)^(-2+((1:ℚ)/D:ℝ))`; `(1/D:ℝ) ≤ 1/(100000·(heilbronnK:ℝ))` ELABORATES with K irreducible (sorry proof) | 4.48s | +0.00s |
| S5_div_one_form | `bound_mono` transport with `norm_num` side-condition `(1:ℚ)/D ≤ 1` | 5.21s | +0.60s |

**Verdict: probe risk #4 (huge-rational mechanics) is DEAD on the elaboration/kernel side.**
237-digit literals cost ≤0.8s over baseline in every shape the filing needs; the only
`sorry`s are the intentional scratch placeholders. (Cold-cache first runs measured up to
32s — that is import/page-cache cost, not literal cost; the warm second S0 re-run confirms.)
