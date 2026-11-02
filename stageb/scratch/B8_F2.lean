import Mathlib
import Submission.Bridge.Cardinality
import Submission.Bridge.KBound
import Submission.OAI.Geometry.HeilbronnTriangle.Main
import Submission.OAI.Geometry.HeilbronnTriangle.ParameterSampling
import Submission.OAI.Geometry.HeilbronnTriangle.FinalScalingBridge

/-!
# §8 bridge, step 3: assembly — subsequence form ⇒ every-large-`n` form

Given `n ≥ N`: `m := ⌈((n+1)/√2)^(1/α)⌉₊` (α = 45435K+16, the cardinality
exponent of `Bridge/Cardinality.lean`), Bertrand prime `r ∈ (m, 2m]`
(`Nat.exists_prime_lt_and_le_two_mul`, the invocation pattern Stage A's
`bound_zero` already exercised at these pins), parameters
`D : PrimeParameterData heilbronnK r` (`exists_primeParameterData`, valid
since `r > m ≥ R0 > 400K²`), configuration `P₀` of size `s = D.sampleCard`
(`ParameterSampling.configuration_of_law` with Main.lean's r0=0 point-law
instantiation copied verbatim per prime), scaled to
`area ≥ s^(-2+heilbronnExponent)` (`triangleAreasAtLeast_of_scaled` +
`sample_size_scaled_area` + `sample_half_le_nat_floor`), deleted to exactly
`n` points (`Finset.exists_subset_card_eq`; deletion cannot lower the min
triangle area — the min is over fewer triples).

The two-sided cardinality bound makes `s ∈ [n, C'·n]` with
`C' = √(cubeTauConst K)·4^α·2/√2` CONSTANT in `n`, so
`area ≥ s^(-2+η_exp) ≥ (C'n)^(-2+η_exp) = C'^(-2+η_exp)·n^(-2+η_exp)
≥ c·n^(-2+η₀)` with `c = C'^(-2+η_exp) > 0` and
`η₀ = 1/(100000·10^232) ≤ heilbronnExponent` (`Bridge/KBound.lean`).
The board's `∃ c > 0` never needs `c` explicit.
-/

namespace OAI

noncomputable section

set_option maxRecDepth 4000

namespace Problem355.Bridge

open Problem355 Parameters Parameters.PrimeParameterData ParameterSampling

/-- Deletion preserves `pointsInUnitSquare` (a ∀-over-membership property). -/
theorem pointsInUnitSquare_of_subset {s t : Finset Point} (hts : t ⊆ s)
    (hs : pointsInUnitSquare s) : pointsInUnitSquare t := by
  intro p hp
  exact hs p (hts hp)

/-- Deletion preserves `triangleAreasAtLeast`: the minimum after deletion is
over FEWER triples, so it cannot drop. -/
theorem triangleAreasAtLeast_of_subset {s t : Finset Point} {a : ℝ} (hts : t ⊆ s)
    (hs : triangleAreasAtLeast s a) : triangleAreasAtLeast t a := by
  intro p hp q hq u hu hpq hpu hqu
  exact hs p (hts hp) q (hts hq) u (hts hu) hpq hpu hqu

/-- Main.lean's r0=0 point-law instantiation, restated for a single prime.
Copied verbatim from the ported `Main.lean` (Cp = 8,
Ct = (128/7)·`UniformFixedFiberCount.countConstant`). -/
theorem point_law_at_prime (r : ℕ) (hr : r.Prime) (D : PrimeParameterData heilbronnK r) :
    ∃ L : PointLaw,
      L.pairProbability ≤ 8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 ∧
      L.tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
        ((128 / 7 : ℝ) * UniformFixedFiberCount.countConstant) *
          (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h / ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
  let : Fact r.Prime := ⟨hr⟩
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  refine ⟨ActualPointLaw.pointLaw D, ActualPointLaw.pairProbability_le D, ?_⟩
  exact ActualPointLaw.tripleProbability_le_of_count D
    UniformFixedFiberCount.countConstant_nonneg
    (fun A => ActualPointLaw.weightedFiberBound_of_matrix_count
      UniformFixedFiberCount.countConstant
      @UniformFixedFiberCount.matrix_fiber_le D A)

/-- Per-prime configuration with the area already in `sampleCard`-power form
`s^(-2+heilbronnExponent)` (the tree carries it only as `tau/(16N³)`). -/
theorem config_at_prime (r : ℕ) (hr : r.Prime) (D : PrimeParameterData heilbronnK r)
    (hlarge : 4 * (8 : ℝ) + 24 * ((128 / 7 : ℝ) * UniformFixedFiberCount.countConstant) *
        (31620 * heilbronnK + 1 : ℝ) ^ 2 < (r : ℝ))
    (hr64 : (64 : ℝ) ≤ (r : ℝ)) :
    ∃ P : Finset Point, P.card = D.sampleCard ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P (Real.rpow (D.sampleCard : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨L, hpair, htriple⟩ := point_law_at_prime r hr D
  obtain ⟨P, hcard, hsq, harea⟩ :=
    configuration_of_law D L (by norm_num)
      (mul_nonneg (by norm_num) UniformFixedFiberCount.countConstant_nonneg)
      hlarge hpair htriple
  refine ⟨P, hcard, hsq, ?_⟩
  apply triangleAreasAtLeast_of_scaled
  · exact (show 3 ≤ r from
      le_trans (by norm_num : (3 : ℕ) ≤ 64) (by exact_mod_cast hr64)).trans
      (r_le_sampleCard D)
  · exact hr64
  · exact D.sampleCard_le_power
  · intro p hp q hq u hu hpq hpu hqu
    have hN : (0 : ℝ) < D.N := by exact_mod_cast D.N_pos
    have htau : (0 : ℝ) < D.tau := by exact_mod_cast D.tau_pos
    have hrR : (0 : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt D.r_pos
    obtain ⟨_, _, htaule, _, _⟩ := D.real_bounds
    have hratio : (1 : ℝ) ≤ (D.N : ℝ) ^ 3 / D.tau :=
      (le_div_iff₀ htau).2 (by simpa using htaule)
    have hsqrt : (1 : ℝ) ≤ Real.sqrt ((D.N : ℝ) ^ 3 / D.tau) := by
      simpa using Real.sqrt_le_sqrt hratio
    have hx2 : (2 : ℝ) ≤ (r : ℝ) * Real.sqrt ((D.N : ℝ) ^ 3 / D.tau) :=
      calc (2 : ℝ) ≤ 64 := by norm_num
        _ ≤ (r : ℝ) := hr64
        _ ≤ (r : ℝ) * Real.sqrt ((D.N : ℝ) ^ 3 / D.tau) :=
          le_mul_of_one_le_right (by positivity) hsqrt
    have hhalf : (r : ℝ) * Real.sqrt ((D.N : ℝ) ^ 3 / D.tau) / 2 ≤
        (D.sampleCard : ℝ) :=
      sample_half_le_nat_floor hx2
    exact sample_size_scaled_area hrR hN htau hhalf
      (harea p hp q hq u hu hpq hpu hqu)

/-- THE §8 INTERPOLATION, real-exponent form: for `η₀ℝ = 1/(100000·10^232)`,
every sufficiently large `n` carries an `n`-point configuration with
`min area ≥ c·n^(-2+η₀ℝ)`, `c > 0`. -/
theorem bound_stageB :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧
        triangleAreasAtLeast P
          (c * Real.rpow (n : ℝ)
            (-2 + (1 : ℝ) / (100000 * (10 ^ 232 : ℝ)))) := by
  classical
  let αN : ℕ := heilbronnK * 45435 + 16
  let α : ℝ := (αN : ℝ)
  have hαN1 : (1 : ℕ) ≤ αN := by
    show (1 : ℕ) ≤ heilbronnK * 45435 + 16
    exact le_trans (by norm_num : (1 : ℕ) ≤ 16) (Nat.le_add_left 16 _)
  have hαpos : (0 : ℝ) < α := by
    show (0 : ℝ) < (αN : ℝ)
    exact_mod_cast Nat.lt_of_succ_le hαN1
  let Ct : ℝ := (128 / 7 : ℝ) * UniformFixedFiberCount.countConstant
  -- One real threshold A dominating every largeness condition on the prime r.
  let A : ℝ := max (max ((400 * heilbronnK ^ 2 : ℕ) : ℝ)
    (4 * (8 : ℝ) + 24 * Ct * (31620 * heilbronnK + 1 : ℝ) ^ 2)) 64
  sorry

end Problem355.Bridge

end

end OAI
