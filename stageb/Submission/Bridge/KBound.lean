import Mathlib
import Submission.OAI.Geometry.HeilbronnTriangle.Parameters

/-!
# §8 bridge, step 2: the literal rational saving, with `heilbronnK` OPAQUE

The filed saving is `η₀ = 1/(100000·L)` with the explicit literal
`L = 10^232 ≥ heilbronnK`. `heilbronnK = heilbronnT² + 1` is `@[irreducible]`
upstream, so we never evaluate it — we bound it symbolically:

* `heilbronnM = Nat.choose 163 41` reduces to its 39-digit literal through
  `Nat.choose_eq_factorial_div_factorial` + `norm_num` (Pascal recursion on a
  39-digit argument is kernel-intractable; the factorial route is not);
* `6·heilbronnT = M·(M−1)·(M−2)` via
  `Nat.choose_mul_factorial_mul_factorial` + `Nat.factorial_succ`, hence
  `(T:ℝ) ≤ (M:ℝ)³/6` and `(T:ℝ)² ≤ (M:ℝ)⁶/36`;
* `heilbronnK_eq` (in-tree, `Parameters.lean`) unfolds the irreducible `K`,
  giving `K ≤ M⁶/36 + 1 ≤ 10^232` (the last step pure `norm_num` on the
  literal: `M₀⁶ ≈ 5·10²³² < 36·10²³²`);
* reciprocals flip: `(1:ℝ)/(100000·10^232) ≤ heilbronnExponent`.

The board rational itself is `η₀ = (1:ℚ)/10^237` (238-digit denominator
literal `100000·10^232`); the cast identity to the ℝ form used in the
assembly is `norm_num` (smoke S5 precedent: 237-digit rational forms cost
≤0.8s warm).
-/

namespace OAI

noncomputable section

-- norm_num/exact_mod_cast on 232-digit literals needs deeper recursion.
set_option maxRecDepth 4000

namespace Problem355.Bridge

open Problem355

/-- `heilbronnM = Nat.choose 163 41` as an explicit 39-digit literal. -/
theorem heilbronnM_val :
    heilbronnM = 606759748397114245242771031375422128400 := by
  show Nat.choose (4 * 41 - 1) 41 = 606759748397114245242771031375422128400
  rw [Nat.choose_eq_factorial_div_factorial (by decide : 41 ≤ 4 * 41 - 1)]
  norm_num

/-- The exact factorial identity behind `T = choose M 3`, in ℝ. -/
theorem heilbronnT_mul_six :
    (heilbronnT : ℝ) * 6 =
      (heilbronnM : ℝ) * ((heilbronnM - 1 : ℕ) : ℝ) * ((heilbronnM - 2 : ℕ) : ℝ) := by
  have hM3 : 3 ≤ heilbronnM := heilbronnM_ge_three
  -- Keep `Nat.choose` syntactic: a defeq check `heilbronnT =?= choose M 3`
  -- whnf's the Pascal recursion on a 39-digit argument (maxRecDepth blowup).
  have hTdef : heilbronnT = Nat.choose heilbronnM 3 := rfl
  have hfac : Nat.choose heilbronnM 3 * Nat.factorial 3 *
      Nat.factorial (heilbronnM - 3) = Nat.factorial heilbronnM :=
    Nat.choose_mul_factorial_mul_factorial hM3
  rw [← hTdef] at hfac
  have h6 : Nat.factorial 3 = 6 := by norm_num
  rw [h6] at hfac
  have hfact3 : Nat.factorial heilbronnM =
      heilbronnM * (heilbronnM - 1) * (heilbronnM - 2) * Nat.factorial (heilbronnM - 3) := by
    -- Substitute d = M - 3 so no truncated subtraction survives into `ring`.
    obtain ⟨d, hd⟩ : ∃ e, heilbronnM = e + 3 := ⟨heilbronnM - 3, by omega⟩
    have a1 : d + 3 - 1 = d + 2 := by omega
    have a2 : d + 3 - 2 = d + 1 := by omega
    have a3 : d + 3 - 3 = d := by omega
    have a4 : d + 3 = d + 2 + 1 := by omega
    have a5 : d + 2 = d + 1 + 1 := by omega
    rw [hd, a1, a2, a3, a4, a5]
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [hfact3] at hfac
  have hnz : ((Nat.factorial (heilbronnM - 3)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hR := congrArg (fun x : ℕ => (x : ℝ)) hfac
  push_cast at hR
  exact mul_right_cancel₀ hnz hR

/-- `T ≤ M³/6` — the sharpening that makes `L = 10^232` reachable. -/
theorem heilbronnT_le : (heilbronnT : ℝ) ≤ (heilbronnM : ℝ) ^ 3 / 6 := by
  have hM0 : (0 : ℝ) ≤ heilbronnM := by positivity
  have hM1 : ((heilbronnM - 1 : ℕ) : ℝ) ≤ heilbronnM := by
    exact_mod_cast Nat.sub_le _ _
  have hM2 : ((heilbronnM - 2 : ℕ) : ℝ) ≤ heilbronnM := by
    exact_mod_cast Nat.sub_le _ _
  have hprod : (heilbronnM : ℝ) * ((heilbronnM - 1 : ℕ) : ℝ) *
      ((heilbronnM - 2 : ℕ) : ℝ) ≤ (heilbronnM : ℝ) ^ 3 := by
    calc (heilbronnM : ℝ) * ((heilbronnM - 1 : ℕ) : ℝ) * ((heilbronnM - 2 : ℕ) : ℝ)
        ≤ (heilbronnM : ℝ) * (heilbronnM : ℝ) * (heilbronnM : ℝ) := by
          gcongr
        _ = (heilbronnM : ℝ) ^ 3 := by ring
  have h6 : (6 : ℝ) * (heilbronnT : ℝ) ≤ (heilbronnM : ℝ) ^ 3 := by
    have := heilbronnT_mul_six
    linarith
  have h6pos : (0 : ℝ) < 6 := by norm_num
  rw [le_div_iff₀ h6pos]
  linarith

/-- `T² ≤ M⁶/36` — the squared form the literal `norm_num` check consumes. -/
theorem heilbronnT_sq_le : (heilbronnT : ℝ) ^ 2 ≤ (heilbronnM : ℝ) ^ 6 / 36 := by
  have hT0 : (0 : ℝ) ≤ heilbronnT := by positivity
  have h1 : (heilbronnT : ℝ) ^ 2 ≤ ((heilbronnM : ℝ) ^ 3 / 6) ^ 2 :=
    pow_le_pow_left₀ hT0 heilbronnT_le 2
  have h2 : ((heilbronnM : ℝ) ^ 3 / 6) ^ 2 = (heilbronnM : ℝ) ^ 6 / 36 := by ring
  linarith

/-- THE literal bound: `heilbronnK ≤ 10^232`, with `K` never evaluated. -/
theorem heilbronnK_le : heilbronnK ≤ 10 ^ 232 := by
  rw [heilbronnK_eq]
  exact_mod_cast (show ((heilbronnT ^ 2 + 1 : ℕ) : ℝ) ≤ (10 ^ 232 : ℝ) from by
    push_cast
    have hM : (heilbronnM : ℝ) = 606759748397114245242771031375422128400 := by
      exact_mod_cast heilbronnM_val
    have hnum : (606759748397114245242771031375422128400 : ℝ) ^ 6 / 36 + 1 ≤
        (10 ^ 232 : ℝ) := by norm_num
    have hc : (heilbronnM : ℝ) ^ 6 / 36 + 1 ≤ (10 ^ 232 : ℝ) := by
      rw [hM]
      exact hnum
    have hsq := heilbronnT_sq_le
    linarith)

/-- The filed exponent is below the tree's symbolic exponent. -/
theorem eta_le_heilbronnExponent :
    (1 : ℝ) / (100000 * (10 ^ 232 : ℝ)) ≤ heilbronnExponent := by
  have hK : (0 : ℝ) < 100000 * (heilbronnK : ℝ) := by
    have := heilbronnK_pos
    positivity
  have hden : 100000 * (heilbronnK : ℝ) ≤ 100000 * (10 ^ 232 : ℝ) := by
    gcongr
    exact_mod_cast heilbronnK_le
  exact one_div_le_one_div_of_le hK hden

end Problem355.Bridge

end

end OAI
