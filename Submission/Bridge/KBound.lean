import Mathlib
import Submission.OAI.Geometry.HeilbronnTriangle.Parameters

/-!
# §8 bridge, step 2: the literal rational saving, with `heilbronnK` EXACT

The filed saving is `η₀ = 1/(100000·K)` with `K = heilbronnK` computed exactly
(232-digit literal). `heilbronnK = heilbronnT² + 1` is `@[irreducible]`
upstream, so we never evaluate it by whnf — we compute it through the
sanctioned `heilbronnK_eq` route:

* `heilbronnM = Nat.choose 163 41` reduces to its 39-digit literal through
  `Nat.choose_eq_factorial_div_factorial` + `norm_num` (Pascal recursion on a
  39-digit argument is kernel-intractable; the factorial route is not);
* `6·heilbronnT = M·(M−1)·(M−2)` via
  `Nat.choose_mul_factorial_mul_factorial` + `Nat.factorial_succ`
  (`heilbronnT_mul_six`, unchanged), hence `heilbronnT` as its 116-digit
  literal (`heilbronnT_val`: rewrite the M literal into the identity, cancel
  the 6, `norm_num` on 39-digit arithmetic);
* `heilbronnK_eq` (in-tree, `Parameters.lean`) unfolds the irreducible `K`
  symbolically to `heilbronnT² + 1`; the ℕ equality `heilbronnT = T_literal`
  comes back by cast injectivity (no K whnf anywhere), so `heilbronnK_val`
  closes on one 232-digit `norm_num` (`T² + 1` vs the K literal);
* `eta_eq_heilbronnExponent` unfolds the plain `heilbronnExponent` def and
  rewrites the cast K — an equality, replacing the old `≤ 10^232` floor.

Kernel hygiene (Assembly scratch B9–B13, kept): NO `Nat.pow_pos` /
`nlinarith` / `exact_mod_cast` certificates over K-headed ℕ expressions
(their elaborated pow form mismatches `Nat.pow` and the kernel's whnf
fallback unfolds the `@[irreducible]` K into the `Nat.choose` Pascal
recursion — deterministic timeout, measured). K is touched only through
`heilbronnK_eq` + the M-literal route, on the ℝ side.
-/

namespace OAI

noncomputable section

-- norm_num on 232-digit literals needs deeper recursion (232-digit
-- decimal literals are new here; the ≤ 10^232 route only ever handled
-- 39-digit inputs and a sparse `10^232`).
set_option maxRecDepth 20000

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

/-- `heilbronnT` as its exact 116-digit literal: substitute the M literal into
`heilbronnT_mul_six` (all M occurrences become ℕ literals), cancel the 6,
`norm_num` on 39-digit arithmetic. -/
theorem heilbronnT_val :
    (heilbronnT : ℝ) =
      37230514451212307341579258391864337055334059182582962517976151329575965621134724577475162784520018371181237814762800 := by
  have hM : heilbronnM = 606759748397114245242771031375422128400 := heilbronnM_val
  have h6 := heilbronnT_mul_six
  rw [hM] at h6
  have hnz : (6 : ℝ) ≠ 0 := by norm_num
  refine mul_right_cancel₀ hnz ?_
  rw [h6]
  norm_num

/-- `heilbronnK` as its exact 232-digit literal. The irreducible `K` is
unfolded only through `heilbronnK_eq` (the sanctioned route); the ℕ equality
`heilbronnT = T_literal` returns by cast injectivity, never by whnf. -/
theorem heilbronnK_val :
    (heilbronnK : ℝ) =
      1386111206301928454498485019847624895039491801209725212873042591990897182969865758396728036445865160210900630928202396854055072270540931245975414924580519625964748753131329280551538059491908934294724322696349160297595005620263840001 := by
  rw [heilbronnK_eq]
  have hTnat : heilbronnT =
      37230514451212307341579258391864337055334059182582962517976151329575965621134724577475162784520018371181237814762800 := by
    exact_mod_cast heilbronnT_val
  rw [hTnat]
  norm_num

/-- The filed exponent IS the tree's symbolic exponent, exactly. -/
theorem eta_eq_heilbronnExponent :
    (1 : ℝ) /
      (100000 *
        1386111206301928454498485019847624895039491801209725212873042591990897182969865758396728036445865160210900630928202396854055072270540931245975414924580519625964748753131329280551538059491908934294724322696349160297595005620263840001) =
      heilbronnExponent := by
  unfold heilbronnExponent
  rw [heilbronnK_val]

end Problem355.Bridge

end

end OAI
