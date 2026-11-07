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
= c·n^(-2+η_exp)` with `c = C'^(-2+η_exp) > 0` (exact-K restatement: the
filed exponent equals `heilbronnExponent`, see `Bridge/KBound.lean`).
`η₀ = 1/(100000·10^232) ≤ heilbronnExponent` — replaced by the exact-K
equality `eta_eq_heilbronnExponent` (`Bridge/KBound.lean`, rung-1).
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

/-- THE §8 INTERPOLATION, real-exponent form at the exact symbolic exponent
`heilbronnExponent = 1/(100000·K)` (K computed exactly in `Bridge/KBound.lean`):
every sufficiently large `n` carries an `n`-point configuration with
`min area ≥ c·n^(-2+η_exp)`, `c > 0`. -/
theorem bound_stageB :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧
        triangleAreasAtLeast P
          (c * Real.rpow (n : ℝ) (-2 + heilbronnExponent)) := by
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
  obtain ⟨R0, hR0⟩ := exists_nat_gt A
  obtain ⟨N1, hN1⟩ := exists_nat_gt (Real.sqrt 2 * Real.rpow (R0 : ℝ) α)
  let N : ℕ := max N1 3
  -- The deletion-ratio constant C' (depends on K only, NOT on n).
  -- NOTE (kernel hygiene, scratch B9-B13): NO Nat.pow_pos / nlinarith /
  -- exact_mod_cast certificates over K-headed NAT expressions — their
  -- elaborated pow form mismatches `Nat.pow` and the kernel's whnf fallback
  -- unfolds the @[irreducible] K into the Nat.choose Pascal recursion
  -- (deterministic timeout, measured). ℝ-side rewrites (Nat.cast_mul/pow)
  -- with literal-exponent pow_pos are the safe shape (B13 S-a..S-e).
  have hCcube : (0 : ℝ) < cubeTauConst heilbronnK := by
    unfold cubeTauConst
    have hb : (0 : ℝ) < ((200 * heilbronnK ^ 2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      exact mul_pos (by norm_num) (pow_pos (by exact_mod_cast heilbronnK_pos) 2)
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (0 : ℝ) < 2 ^ 30)) (pow_pos hb (heilbronnK * 3029 + 1))
  let C' : ℝ :=
    Real.sqrt (cubeTauConst heilbronnK) * (4 : ℝ) ^ αN * 2 / Real.sqrt 2
  have hCpos : (0 : ℝ) < C' := by
    unfold C'
    exact div_pos
      (mul_pos (mul_pos (Real.sqrt_pos.mpr hCcube) (pow_pos (by norm_num : (0 : ℝ) < 4) _))
        (by norm_num))
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  refine ⟨Real.rpow C' (-2 + heilbronnExponent), Real.rpow_pos_of_pos hCpos _, N,
    fun n hn => ?_⟩
  have hn3 : 3 ≤ n := (le_max_right N1 3).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn3)
  have hnR3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  -- y = ((n+1)/√2)^(1/α), m = ⌈y⌉₊
  set y : ℝ := Real.rpow ((n + 1 : ℝ) / Real.sqrt 2) (1 / α) with hy
  set m : ℕ := Nat.ceil y with hm
  have hypos : (0 : ℝ) < y := by
    rw [hy]
    exact Real.rpow_pos_of_pos
      (div_pos (by exact_mod_cast (Nat.succ_pos n))
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))) _
  have hy1 : (1 : ℝ) ≤ y := by
    rw [hy]
    apply Real.one_le_rpow _ (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by norm_num⟩
    have hcast : (n + 1 : ℝ) = (n : ℝ) + 1 := by ring
    have hle : Real.sqrt 2 ≤ (n + 1 : ℝ) := by
      have h4 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num) hn3)
      linarith [hcast]
    exact (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
      (by rw [one_mul]; exact hle)
  have hym : y ≤ (m : ℝ) := by exact_mod_cast Nat.le_ceil y
  have hym1 : (m : ℝ) < y + 1 := Nat.ceil_lt_add_one (le_of_lt hypos)
  -- y^α = (n+1)/√2
  have hyα : Real.rpow y α = (n + 1 : ℝ) / Real.sqrt 2 := by
    have hb : (0 : ℝ) ≤ (n + 1 : ℝ) / Real.sqrt 2 :=
      div_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one) (Real.sqrt_nonneg 2)
    calc Real.rpow y α
        = Real.rpow (Real.rpow ((n + 1 : ℝ) / Real.sqrt 2) (1 / α)) α := by rw [hy]
      _ = Real.rpow ((n + 1 : ℝ) / Real.sqrt 2) ((1 / α) * α) :=
          (Real.rpow_mul hb (1 / α) α).symm
      _ = Real.rpow ((n + 1 : ℝ) / Real.sqrt 2) 1 := by
          congr 1
          exact div_mul_cancel₀ (1 : ℝ) (ne_of_gt hαpos)
      _ = (n + 1 : ℝ) / Real.sqrt 2 := Real.rpow_one _
  have hyαN : (y : ℝ) ^ αN = (n + 1 : ℝ) / Real.sqrt 2 := by
    have hbridge : Real.rpow y α = (y : ℝ) ^ αN := by
      show Real.rpow y (αN : ℝ) = (y : ℝ) ^ αN
      exact Real.rpow_natCast y αN
    rw [← hbridge, hyα]
  -- y > R0, hence m > R0: because n+1 > √2·R0^α.
  have hn1' : Real.sqrt 2 * Real.rpow (R0 : ℝ) α < (n + 1 : ℝ) := by
    have h3 : (N1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_max_left N1 3).trans hn
    have h2 : (n + 1 : ℝ) = (n : ℝ) + 1 := by ring
    linarith [hN1]
  have hyR0 : (R0 : ℝ) < y := by
    by_contra h
    have hle : y ≤ (R0 : ℝ) := le_of_not_gt h
    have hpow : Real.rpow y α ≤ Real.rpow (R0 : ℝ) α :=
      Real.rpow_le_rpow (le_of_lt hypos) hle (le_of_lt hαpos)
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hmul : Real.sqrt 2 * Real.rpow y α ≤ Real.sqrt 2 * Real.rpow (R0 : ℝ) α :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt h2pos)
    have heq : Real.sqrt 2 * Real.rpow y α = (n + 1 : ℝ) := by
      rw [hyα, mul_comm,
        div_mul_cancel₀ _ (ne_of_gt h2pos)]
    linarith
  have hmR0 : (R0 : ℕ) < m := by
    have h1 : (R0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hyR0 hym
    exact_mod_cast h1
  have hR0A : (A : ℝ) < (R0 : ℝ) := by exact_mod_cast hR0
  have hR0gt1 : 1 < R0 := by
    have h2 : (64 : ℝ) ≤ A := le_max_right _ _
    have h4 : (64 : ℝ) < (R0 : ℝ) := lt_of_le_of_lt h2 hR0A
    have h5 : 64 < R0 := by exact_mod_cast h4
    exact lt_trans (by norm_num : (1 : ℕ) < 64) h5
  -- Bertrand prime r ∈ (m, 2m]
  have hm1 : 1 < m :=
    lt_of_lt_of_le (Nat.lt_succ_of_lt hR0gt1) (Nat.succ_le_of_lt hmR0)
  obtain ⟨r, hrp, hrm, hr2m⟩ :=
    Nat.exists_prime_lt_and_le_two_mul m (by omega : m ≠ 0)
  have hrR : (m : ℝ) < (r : ℝ) := by exact_mod_cast hrm
  have hr2R : (r : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hr2m
  have hrA : (A : ℝ) < (r : ℝ) := lt_of_lt_of_le hR0A (by
    exact_mod_cast (Nat.le_trans (Nat.le_of_lt hmR0) (Nat.le_of_lt hrm)))
  have hr400 : 400 * heilbronnK ^ 2 ≤ r := by
    have h1 : ((400 * heilbronnK ^ 2 : ℕ) : ℝ) ≤ A :=
      (le_max_left _ _).trans (le_max_left _ _)
    have h2 : (A : ℝ) < (r : ℝ) := hrA
    exact_mod_cast (le_of_lt (lt_of_le_of_lt h1 h2))
  have hlarge : 4 * (8 : ℝ) + 24 * Ct * (31620 * heilbronnK + 1 : ℝ) ^ 2 < (r : ℝ) := by
    have h1 : 4 * (8 : ℝ) + 24 * Ct * (31620 * heilbronnK + 1 : ℝ) ^ 2 ≤ A :=
      (le_max_right _ _).trans (le_max_left _ _)
    linarith [h1, hrA]
  have hr64 : (64 : ℝ) ≤ (r : ℝ) := by
    have h1 : (64 : ℝ) ≤ A := le_max_right _ _
    linarith [h1, hrA]
  -- Parameters and configuration at r
  obtain ⟨D⟩ := exists_primeParameterData heilbronnK_ge_two hr400
  obtain ⟨P0, hP0card, hP0sq, hP0area⟩ := config_at_prime r hrp D hlarge hr64
  let s : ℕ := D.sampleCard
  -- Two-sided cardinality bounds at r
  have hlow : Real.sqrt 2 * (r : ℝ) ^ αN - 1 < (s : ℝ) := sampleCard_gt D
  have hup : (s : ℝ) ≤ Real.sqrt (cubeTauConst heilbronnK) * (r : ℝ) ^ αN :=
    sampleCard_le_tight D
  -- s ≥ n
  have hmα : Real.sqrt 2 * (m : ℝ) ^ αN ≤ Real.sqrt 2 * (r : ℝ) ^ αN :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hrm.le) αN)
      (Real.sqrt_nonneg 2)
  have hmαy : Real.sqrt 2 * (y : ℝ) ^ αN ≤ Real.sqrt 2 * (m : ℝ) ^ αN :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_of_lt hypos) hym αN) (Real.sqrt_nonneg 2)
  have hsq2 : Real.sqrt 2 * ((n + 1 : ℝ) / Real.sqrt 2) - 1 = (n : ℝ) := by
    rw [mul_comm, div_mul_cancel₀ _
      (ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)))]
    ring
  have hysq : (y : ℝ) ^ αN = (n + 1 : ℝ) / Real.sqrt 2 := hyαN
  have hysq2 : Real.sqrt 2 * (y : ℝ) ^ αN =
      Real.sqrt 2 * ((n + 1 : ℝ) / Real.sqrt 2) := by rw [hysq]
  -- NOTE: NO linarith here (scratch C_E5: its certificate zeta-expands the
  -- K-headed exponent atoms and the kernel's whnf then unfolds K into the
  -- Nat.choose Pascal recursion -> deterministic timeout). Pure calc chain.
  have hsnR : (n : ℝ) < (s : ℝ) :=
    calc (n : ℝ)
        = Real.sqrt 2 * ((n + 1 : ℝ) / Real.sqrt 2) - 1 := hsq2.symm
      _ = Real.sqrt 2 * (y : ℝ) ^ αN - 1 := by rw [hysq]
      _ ≤ Real.sqrt 2 * (m : ℝ) ^ αN - 1 := sub_le_sub_right hmαy 1
      _ ≤ Real.sqrt 2 * (r : ℝ) ^ αN - 1 := sub_le_sub_right hmα 1
      _ < (s : ℝ) := hlow
  have hsn : n ≤ s := by
    have h1 : n < s := by exact_mod_cast hsnR
    exact Nat.le_of_lt h1
  -- s ≤ C'·n
  have hm2y : (m : ℝ) ≤ 2 * y := by linarith [hym1, hy1]
  have hfour : (2 : ℝ) ^ αN * (2 : ℝ) ^ αN = (4 : ℝ) ^ αN := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hsC : (s : ℝ) ≤ C' * (n : ℝ) := by
    have h1 : (s : ℝ) ≤ Real.sqrt (cubeTauConst heilbronnK) * (2 * (m : ℝ)) ^ αN :=
      le_trans hup (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hr2R αN) (Real.sqrt_nonneg _))
    have h2 : (2 * (m : ℝ)) ^ αN = (2 : ℝ) ^ αN * (m : ℝ) ^ αN := mul_pow _ _ _
    have h3 : (m : ℝ) ^ αN ≤ (2 * y) ^ αN :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hm2y _
    have h4 : (2 * y) ^ αN = (2 : ℝ) ^ αN * (y : ℝ) ^ αN := mul_pow _ _ _
    have h5 : (y : ℝ) ^ αN = (n + 1 : ℝ) / Real.sqrt 2 := hyαN
    have h6 : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by
      have h7 : (n + 1 : ℝ) = (n : ℝ) + 1 := by ring
      linarith [hn1]
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h8 : (2 : ℝ) ^ αN * (m : ℝ) ^ αN ≤ (2 : ℝ) ^ αN * (2 * y) ^ αN :=
      mul_le_mul_of_nonneg_left h3 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    have h9 : (n + 1 : ℝ) / Real.sqrt 2 ≤ 2 * (n : ℝ) / Real.sqrt 2 :=
      div_le_div_of_nonneg_right h6 (le_of_lt h2pos)
    calc (s : ℝ)
        ≤ Real.sqrt (cubeTauConst heilbronnK) * (2 * (m : ℝ)) ^ αN := h1
      _ = Real.sqrt (cubeTauConst heilbronnK) * ((2 : ℝ) ^ αN * (m : ℝ) ^ αN) := by rw [h2]
      _ ≤ Real.sqrt (cubeTauConst heilbronnK) * ((2 : ℝ) ^ αN * (2 * y) ^ αN) :=
          mul_le_mul_of_nonneg_left h8 (Real.sqrt_nonneg _)
      _ = Real.sqrt (cubeTauConst heilbronnK) * ((2 : ℝ) ^ αN * ((2 : ℝ) ^ αN * (y : ℝ) ^ αN)) :=
          by rw [h4]
      _ = Real.sqrt (cubeTauConst heilbronnK) * ((4 : ℝ) ^ αN * ((n + 1 : ℝ) / Real.sqrt 2)) := by
          have hstep : (2 : ℝ) ^ αN * ((2 : ℝ) ^ αN * (y : ℝ) ^ αN) =
              (4 : ℝ) ^ αN * ((n + 1 : ℝ) / Real.sqrt 2) := by
            rw [← mul_assoc, hfour, h5]
          exact congrArg (fun x => Real.sqrt (cubeTauConst heilbronnK) * x) hstep
      _ ≤ Real.sqrt (cubeTauConst heilbronnK) * ((4 : ℝ) ^ αN * (2 * (n : ℝ) / Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h9
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)) (Real.sqrt_nonneg _)
      _ = C' * (n : ℝ) := by
          unfold C'
          field_simp
  -- Delete points down to exactly n; the min area cannot drop.
  have hP0s : P0.card = s := hP0card
  have hnP0 : n ≤ P0.card := hsn.trans (Nat.le_of_eq hP0s.symm)
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hnP0
  refine ⟨P, hPcard, pointsInUnitSquare_of_subset hPsub hP0sq, ?_⟩
  have hsub := triangleAreasAtLeast_of_subset hPsub hP0area
  -- Final exponent arithmetic: c·n^(-2+η₀) ≤ s^(-2+η_exp) ≤ areas.
  have hexple : -2 + heilbronnExponent ≤ 0 := by
    have := heilbronnExponent_le
    linarith
  have hstep1 : Real.rpow (C' * (n : ℝ)) (-2 + heilbronnExponent) ≤
      Real.rpow (s : ℝ) (-2 + heilbronnExponent) :=
    Real.rpow_le_rpow_of_nonpos (by
      have h3 : (3 : ℕ) ≤ n := hn3
      have h4 : n ≤ s := hsn
      have h5 : (0 : ℕ) < s := Nat.pos_of_ne_zero (by omega)
      exact_mod_cast h5) hsC hexple
  have hstep2 : Real.rpow (C' * (n : ℝ)) (-2 + heilbronnExponent) =
      Real.rpow C' (-2 + heilbronnExponent) *
        Real.rpow (n : ℝ) (-2 + heilbronnExponent) :=
    Real.mul_rpow (le_of_lt hCpos) (by positivity)
  intro p hp q hq u hu hpq hpu hqu
  calc Real.rpow C' (-2 + heilbronnExponent) *
        Real.rpow (n : ℝ) (-2 + heilbronnExponent)
      = Real.rpow (C' * (n : ℝ)) (-2 + heilbronnExponent) := hstep2
    _ ≤ Real.rpow (s : ℝ) (-2 + heilbronnExponent) := hstep1
    _ ≤ triangleArea p q u := hsub p hp q hq u hu hpq hpu hqu

end Problem355.Bridge

end

end OAI
