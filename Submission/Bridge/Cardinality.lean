import Mathlib
import Submission.OAI.Geometry.HeilbronnTriangle.ParameterConclusion

/-!
# §8 bridge, step 1: two-sided cardinality bounds for `sampleCard`

New bridge file (R2125607854, §8 interpolation). The ported tree carries the
UPPER bound `sampleCard_le_power : (P.sampleCard : ℝ) ≤ r ^ (100000·k)`
(`ParameterConclusion.lean`). For the board's every-large-`n` form we need a
LOWER bound at a MATCHING exponent (paper §8's two-sided `A_k·r^α ≤ n_r ≤
D_k·r^α`), so that the deletion ratio `sampleCard / n` is bounded by a
constant depending only on `k` (see `BRIDGE_ATTACH_POINTS.md`, "The
arithmetic the bridge must line up").

The arithmetic, all from `PrimeParameterData` fields:
* `B ∈ (100k²r³⁰, 200k²r³⁰]`, `h = B^k`, `q ∈ (h¹⁰⁰, 2h¹⁰⁰]`
  (`base_lower`, `base_upper`, `auxiliary_lower`, `auxiliary_upper`),
* `M = h·q ∈ [h¹⁰¹, 2h¹⁰¹]`, `N = M¹⁰ ∈ [h¹⁰¹⁰, 2¹⁰h¹⁰¹⁰]`,
* `tau = B^(k-1)/2`, upper side by `Nat.cast_div_le`, lower side via the
  in-tree `ratio_bound` (`h/tau ≤ 3B`),
* hence `N³/tau ∈ (2·B^(3029k+1), 3·2³⁰·B^(3029k+1)]`, and with
  `B^(3029k+1) ∈ (r^(90870k+30), (200k²)^(3029k+1)·r^(90870k+30)]`:
  `2·r^γ < N³/tau ≤ C_k·r^γ` with `γ = 90870k+30`,
  `C_k = 3·2³⁰·(200k²)^(3029k+1)`,
* `sampleCard = ⌊r·sqrt(N³/tau)⌋₊ ∈ (√2·r^α − 1, √C_k·r^α]` with
  `α = 45435k+16 = γ/2 + 1` (the paper's cardinality exponent; the site
  baseline saving is `2/(45435K+16)` — consistency check ✓).

All exponents are natural numbers; no `rpow` appears in this file.
-/

namespace OAI

noncomputable section

namespace Problem355.Bridge

open Parameters Parameters.PrimeParameterData

variable {k r : ℕ}

/-- The upper constant `C_k` in `N³/tau ≤ C_k · r^(90870k+30)`. -/
def cubeTauConst (k : ℕ) : ℝ :=
  3 * 2 ^ 30 * ((200 * k ^ 2 : ℕ) : ℝ) ^ (k * 3029 + 1)

lemma cubeTauConst_nonneg (k : ℕ) : 0 ≤ cubeTauConst k := by
  unfold cubeTauConst
  positivity

section Facts

variable (P : PrimeParameterData k r)

include P

lemma r30_lt_B : (r : ℝ) ^ 30 < (P.B : ℝ) := by
  have hk : (0 : ℕ) < 100 * k ^ 2 := by
    have := P.two_le_k
    nlinarith
  have hle : (r ^ 30 : ℕ) ≤ 100 * k ^ 2 * r ^ 30 := Nat.le_mul_of_pos_left _ hk
  exact_mod_cast hle.trans_lt P.base_lower

lemma M_ge_h101 : P.h ^ 101 ≤ P.M :=
  calc P.h ^ 101 ≤ P.h ^ 101 + P.h := Nat.le_add_right _ _
    _ = P.h * (P.h ^ 100 + 1) := by ring
    _ ≤ P.h * P.q := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt P.auxiliary_lower)
    _ = P.M := rfl

lemma M_le_2h101 : P.M ≤ 2 * P.h ^ 101 :=
  calc P.M = P.h * P.q := rfl
    _ ≤ P.h * (2 * P.h ^ 100) := Nat.mul_le_mul_left _ P.auxiliary_upper
    _ = 2 * P.h ^ 101 := by ring

lemma N_ge_h1010 : P.h ^ 1010 ≤ P.N :=
  calc
    P.h ^ 1010 = (P.h ^ 101) ^ 10 := by
      rw [(by norm_num : (1010 : ℕ) = 101 * 10), pow_mul]
    _ ≤ P.M ^ 10 := Nat.pow_le_pow_left (M_ge_h101 P) _
    _ = P.N := rfl

lemma N_le_2pow10_h1010 : P.N ≤ 2 ^ 10 * P.h ^ 1010 :=
  calc
    P.N = P.M ^ 10 := rfl
    _ ≤ (2 * P.h ^ 101) ^ 10 := Nat.pow_le_pow_left (M_le_2h101 P) _
    _ = 2 ^ 10 * (P.h ^ 101) ^ 10 := by rw [mul_pow]
    _ = 2 ^ 10 * P.h ^ 1010 := by
      rw [(by norm_num : (1010 : ℕ) = 101 * 10), ← pow_mul]

lemma tau_eq_threshold : P.tau = P.B ^ (k - 1) / 2 := rfl

lemma tau_le_half : (P.tau : ℝ) ≤ (P.B : ℝ) ^ (k - 1) / 2 := by
  have hdef : P.tau = P.B ^ (k - 1) / 2 := rfl
  rw [hdef]
  exact (Nat.cast_div_le).trans (by rw [Nat.cast_pow, Nat.cast_ofNat])

lemma h_cast : (P.h : ℝ) = (P.B : ℝ) ^ k := by
  have : P.h = P.B ^ k := rfl
  rw [this, Nat.cast_pow]

lemma tau_ge : (P.h : ℝ) / (3 * (P.B : ℝ)) ≤ (P.tau : ℝ) := by
  have hb : (P.h : ℝ) / (P.tau : ℝ) ≤ 3 * (P.B : ℝ) :=
    ratio_bound P.base_ge_three P.two_le_k
  have hpos : (0 : ℝ) < 3 * (P.B : ℝ) := by
    have := P.base_ge_three
    positivity
  have ht : (0 : ℝ) < (P.tau : ℝ) := by exact_mod_cast P.tau_pos
  rw [div_le_iff₀ ht] at hb
  rw [div_le_iff₀ hpos]
  nlinarith

lemma B3029_le :
    (P.B : ℝ) ^ (k * 3029 + 1) ≤
      ((200 * k ^ 2 : ℕ) : ℝ) ^ (k * 3029 + 1) * (r : ℝ) ^ (k * 90870 + 30) := by
  have hb : (P.B : ℝ) ≤ ((200 * k ^ 2 : ℕ) : ℝ) * (r : ℝ) ^ 30 := by
    have : ((200 * k ^ 2 * r ^ 30 : ℕ) : ℝ) =
        ((200 * k ^ 2 : ℕ) : ℝ) * (r : ℝ) ^ 30 := by push_cast; ring
    exact_mod_cast P.base_upper
  calc (P.B : ℝ) ^ (k * 3029 + 1)
      ≤ (((200 * k ^ 2 : ℕ) : ℝ) * (r : ℝ) ^ 30) ^ (k * 3029 + 1) := by gcongr
    _ = ((200 * k ^ 2 : ℕ) : ℝ) ^ (k * 3029 + 1) * ((r : ℝ) ^ 30) ^ (k * 3029 + 1) :=
        mul_pow _ _ _
    _ = ((200 * k ^ 2 : ℕ) : ℝ) ^ (k * 3029 + 1) * (r : ℝ) ^ (k * 90870 + 30) := by
        rw [show ((r : ℝ) ^ 30) ^ (k * 3029 + 1) = (r : ℝ) ^ (30 * (k * 3029 + 1))
          by rw [pow_mul]]
        congr 1
        ring

/-- The lower two-sided ingredient: `2·r^γ < N³/tau`, `γ = 90870k+30`. -/
theorem cube_div_tau_gt :
    2 * (r : ℝ) ^ (k * 90870 + 30) < (P.N : ℝ) ^ 3 / (P.tau : ℝ) := by
  have hBpos : (0 : ℝ) < P.B := by exact_mod_cast P.base_prime.pos
  have hstep : 2 * (P.B : ℝ) ^ (k * 3029 + 1) =
      (P.B : ℝ) ^ (k * 3030) / ((P.B : ℝ) ^ (k - 1) / 2) := by
    have he : k * 3030 = k * 3029 + 1 + (k - 1) := by
      have := P.two_le_k; omega
    rw [he, pow_add]
    field_simp
    ring
  have hN3 : ((P.h ^ 1010 : ℕ) : ℝ) ^ 3 = (P.B : ℝ) ^ (k * 3030) := by
    push_cast
    calc ((P.h : ℝ) ^ 1010) ^ 3
        = (P.h : ℝ) ^ (1010 * 3) := by rw [← pow_mul]
      _ = (P.h : ℝ) ^ 3030 := by congr 1
      _ = ((P.B : ℝ) ^ k) ^ 3030 := by rw [h_cast P]
      _ = (P.B : ℝ) ^ (k * 3030) := by rw [← pow_mul]
  have hdiv : (P.B : ℝ) ^ (k * 3030) / ((P.B : ℝ) ^ (k - 1) / 2) ≤
      (P.N : ℝ) ^ 3 / (P.tau : ℝ) := by
    rw [← hN3]
    gcongr
    · exact_mod_cast P.tau_pos
    · exact_mod_cast N_ge_h1010 P
    · exact tau_le_half P
  calc 2 * (r : ℝ) ^ (k * 90870 + 30)
      = 2 * ((r : ℝ) ^ 30) ^ (k * 3029 + 1) := by
        rw [show (k * 90870 + 30 : ℕ) = 30 * (k * 3029 + 1) by ring, ← pow_mul]
    _ < 2 * (P.B : ℝ) ^ (k * 3029 + 1) := by
        refine mul_lt_mul_of_pos_left ?_ (by norm_num)
        exact pow_lt_pow_left₀ (r30_lt_B P) (by positivity) (by positivity)
    _ = (P.B : ℝ) ^ (k * 3030) / ((P.B : ℝ) ^ (k - 1) / 2) := hstep
    _ ≤ (P.N : ℝ) ^ 3 / (P.tau : ℝ) := hdiv

/-- The upper two-sided ingredient: `N³/tau ≤ C_k·r^γ`, `γ = 90870k+30`. -/
theorem cube_div_tau_le :
    (P.N : ℝ) ^ 3 / (P.tau : ℝ) ≤
      cubeTauConst k * (r : ℝ) ^ (k * 90870 + 30) := by
  have hBpos : (0 : ℝ) < P.B := by exact_mod_cast P.base_prime.pos
  have hhpos : (0 : ℝ) < P.h := by
    rw [h_cast P]
    exact pow_pos hBpos _
  have hh3030 : ((2 ^ 10 * P.h ^ 1010 : ℕ) : ℝ) ^ 3 =
      (2 : ℝ) ^ 30 * (P.h : ℝ) ^ 3030 := by
    push_cast
    rw [mul_pow]
    congr 1
    · norm_num
    · rw [← pow_mul]
  have hpow : (P.h : ℝ) ^ 3030 = (P.h : ℝ) ^ 3029 * (P.h : ℝ) := by
    rw [show (3030 : ℕ) = 3029 + 1 by norm_num, pow_add, pow_one]
  calc (P.N : ℝ) ^ 3 / (P.tau : ℝ)
      ≤ ((2 ^ 10 * P.h ^ 1010 : ℕ) : ℝ) ^ 3 / ((P.h : ℝ) / (3 * (P.B : ℝ))) := by
        gcongr
        · exact_mod_cast N_le_2pow10_h1010 P
        · exact tau_ge P
    _ = 3 * 2 ^ 30 * ((P.h : ℝ) ^ 3029 * (P.B : ℝ)) := by
        rw [hh3030, div_div_eq_mul_div, hpow]
        field_simp [ne_of_gt hhpos]
    _ = 3 * 2 ^ 30 * (P.B : ℝ) ^ (k * 3029 + 1) := by
        have h1 : ((P.B : ℝ) ^ k) ^ 3029 = (P.B : ℝ) ^ (k * 3029) := by
          rw [← pow_mul]
        rw [h_cast P, h1]
        congr 1
    _ ≤ 3 * 2 ^ 30 * (((200 * k ^ 2 : ℕ) : ℝ) ^ (k * 3029 + 1) *
        (r : ℝ) ^ (k * 90870 + 30)) := by gcongr; exact B3029_le P
    _ = cubeTauConst k * (r : ℝ) ^ (k * 90870 + 30) := by
        unfold cubeTauConst
        ring

end Facts

/-- THE two-sided cardinality bound, lower side: `√2·r^α − 1 < sampleCard`,
with `α = 45435k+16` the paper's cardinality exponent. -/
theorem sampleCard_gt (P : PrimeParameterData k r) :
    Real.sqrt 2 * (r : ℝ) ^ (k * 45435 + 16) - 1 < (P.sampleCard : ℝ) := by
  have hkey : Real.sqrt 2 * (r : ℝ) ^ (k * 45435 + 16) <
      (r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ)) := by
    have hsq : Real.sqrt 2 * (r : ℝ) ^ (k * 45435 + 15) <
        Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ)) := by
      rw [Real.lt_sqrt (by positivity)]
      have h2 : (Real.sqrt 2 * (r : ℝ) ^ (k * 45435 + 15)) ^ 2 =
          (2 : ℝ) * (r : ℝ) ^ (k * 90870 + 30) := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2), ← pow_mul]
        congr 1
        congr 1
        ring
      rw [h2]
      exact cube_div_tau_gt P
    calc Real.sqrt 2 * (r : ℝ) ^ (k * 45435 + 16)
        = (r : ℝ) * (Real.sqrt 2 * (r : ℝ) ^ (k * 45435 + 15)) := by
          rw [show (k * 45435 + 16 : ℕ) = k * 45435 + 15 + 1 by ring,
            pow_add, pow_one]
          ring
      _ < (r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ)) := by
          refine mul_lt_mul_of_pos_left hsq ?_
          exact_mod_cast P.r_pos
  have hf := Nat.lt_floor_add_one ((r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ)))
  have hdef : (⌊(r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ))⌋₊ : ℝ) =
      (P.sampleCard : ℝ) := rfl
  linarith

/-- THE two-sided cardinality bound, upper side: `sampleCard ≤ √C_k·r^α`. -/
theorem sampleCard_le_tight (P : PrimeParameterData k r) :
    (P.sampleCard : ℝ) ≤
      Real.sqrt (cubeTauConst k) * (r : ℝ) ^ (k * 45435 + 16) := by
  have hsqrt : Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ)) ≤
      Real.sqrt (cubeTauConst k) * (r : ℝ) ^ (k * 45435 + 15) := by
    have heq : Real.sqrt (cubeTauConst k * (r : ℝ) ^ (k * 90870 + 30)) =
        Real.sqrt (cubeTauConst k) * (r : ℝ) ^ (k * 45435 + 15) := by
      rw [Real.sqrt_mul (cubeTauConst_nonneg k),
        show (r : ℝ) ^ (k * 90870 + 30) = ((r : ℝ) ^ (k * 45435 + 15)) ^ 2 from by
          rw [(by ring : (k * 90870 + 30 : ℕ) = (k * 45435 + 15) * 2), pow_mul],
        Real.sqrt_sq (pow_nonneg (Nat.cast_nonneg _) _)]
    rw [← heq]
    exact Real.sqrt_le_sqrt (cube_div_tau_le P)
  calc (P.sampleCard : ℝ)
      ≤ (r : ℝ) * Real.sqrt ((P.N : ℝ) ^ 3 / (P.tau : ℝ)) :=
        Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    _ ≤ (r : ℝ) * (Real.sqrt (cubeTauConst k) * (r : ℝ) ^ (k * 45435 + 15)) := by gcongr
    _ = Real.sqrt (cubeTauConst k) * (r : ℝ) ^ (k * 45435 + 16) := by
        conv_rhs =>
          rw [(by ring : (k * 45435 + 16 : ℕ) = k * 45435 + 15 + 1), pow_add,
            pow_one]
        ring

end Problem355.Bridge

end

end OAI
