import Mathlib
import FormalConjecturesForMathlib.Analysis.SpecialFunctions.NthRoot
import FormalConjectures.Util.Answer

namespace Eval_gpt_6_astra
open scoped Real Nat Topology Polynomial

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = answer(26) := by
  change x = 26
  have hy : y ≤ 8 := by
    by_contra h
    have hy9 : 9 ≤ y := by omega
    have hx10 : 10 ≤ x := by omega
    nlinarith [mul_nonneg (show 0 ≤ x - 10 by omega)
      (show 0 ≤ y - 9 by omega)]
  interval_cases y <;> norm_num at h₂ <;> omega
end Eval_gpt_6_astra

namespace Eval_gpt_5_6_sol
open scoped Real Nat Topology Polynomial

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = answer(26) := by
  have hy : y ≤ 8 := by
    by_contra h
    have hy8 : 8 < y := lt_of_not_ge h
    have hp : 0 < (x - y) * y :=
      mul_pos (sub_pos.mpr h₁) h₀
    have hq : 0 < (y - 8) * (y + 10) :=
      mul_pos (by omega) (by omega)
    nlinarith
  interval_cases y <;> norm_num at h₂ ⊢ <;> omega
end Eval_gpt_5_6_sol

namespace Eval_gpt_5_6_terra
open scoped Real Nat Topology Polynomial

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = answer(26) := by
  have h := mul_nonneg (show 0 ≤ x - y - 1 by omega) (show 0 ≤ y + 1 by omega)
  have hy : y ≤ 7 := by
    nlinarith
  interval_cases y <;> norm_num at h₀ h₁ h₂ ⊢ <;> omega
end Eval_gpt_5_6_terra

namespace Eval_gpt_5_6_luna
open scoped Real Nat Topology Polynomial

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = answer(26) := by
  change x = 26
  have hlt : y + 1 ≤ x := by omega
  have hxy : y * (y + 1) ≤ x * y :=
    mul_le_mul_of_nonneg_right hlt (le_of_lt h₀)
  have hy7 : y ≤ 7 := by
    by_contra h
    have hy8 : 8 ≤ y := by omega
    have hs : 0 ≤ (y - 8) * (y - 8) := mul_self_nonneg _
    nlinarith [hxy, hs]
  interval_cases y <;> norm_num at * <;> omega
end Eval_gpt_5_6_luna

namespace Eval_gpt_5_5
open scoped Real Nat Topology Polynomial

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = answer(26) := by
  omega
end Eval_gpt_5_5
