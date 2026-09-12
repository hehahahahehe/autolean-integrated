import Mathlib

namespace Eval_gpt_6_astra
open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
theorem Artin_exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x * y = y * x := by
  have aux (c : G) (ha : Commute c a) (hb : Commute c b) :
      ∀ z ∈ Subgroup.closure {x : G | x = a ∨ x = b}, Commute c z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
        rcases hz with rfl | rfl
        · exact ha
        · exact hb
    | one =>
        show c * 1 = 1 * c
        simp
    | mul z w hz hw ihz ihw =>
        exact ihz.mul_right ihw
    | inv z hz ih =>
        exact ih.inv_right
  intro x y
  have hab : Commute a b := h
  have hxa : Commute (x : G) a :=
    (aux a (Commute.refl a) hab x x.property).symm
  have hxb : Commute (x : G) b :=
    (aux b hab.symm (Commute.refl b) x x.property).symm
  apply Subtype.ext
  exact (aux (x : G) hxa hxb y y.property).eq
end Eval_gpt_6_astra

namespace Eval_gpt_5_6_sol
open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
theorem Artin_exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x * y = y * x := by
  intro x y
  apply Subtype.ext
  change Commute (x : G) (y : G)
  refine Subgroup.closure_induction x.property ?_ ?_ ?_ ?_
  · intro z hz
    refine Subgroup.closure_induction y.property ?_ ?_ ?_ ?_
    · intro w hw
      rcases hz with (rfl | rfl) <;> rcases hw with (rfl | rfl)
      · exact Commute.refl _
      · exact h
      · exact h.symm
      · exact Commute.refl _
    · exact Commute.one_right _
    · intro u v hu hv
      exact hu.mul_right hv
    · intro u hu
      exact hu.inv_right
  · exact Commute.one_left _
  · intro u v hu hv
    exact hu.mul_left hv
  · intro u hu
    exact hu.inv_left
end Eval_gpt_5_6_sol

namespace Eval_gpt_5_6_terra
open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
theorem Artin_exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x * y = y * x := by
  intro x hx y hy
  have hgen : ∀ g ∈ ({x | x = a ∨ x = b} : Set G),
      ∀ z ∈ closure {x | x = a ∨ x = b}, Commute g z := by
    intro g hg z hz
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hz
    · intro w hw
      rcases hg with (rfl | rfl) <;> rcases hw with (rfl | rfl)
      · exact Commute.refl a
      · exact h
      · exact h.symm
      · exact Commute.refl b
    · exact Commute.one_right g
    · intro u v hu hv
      exact hu.mul_right hv
    · intro u hu
      exact hu.inv_right
  have hxy : Commute x y := by
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · intro g hg
      exact hgen g hg y hy
    · exact Commute.one_left y
    · intro u v hu hv
      exact hu.mul_left hv
    · intro u hu
      exact hu.inv_left
  exact hxy.eq
end Eval_gpt_5_6_terra

namespace Eval_gpt_5_6_luna
open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
theorem Artin_exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x * y = y * x := by
  let S : Set G := {z | z = a ∨ z = b}
  let K : Subgroup G := Subgroup.closure S
  have gen_comm : ∀ g, g ∈ S → ∀ y, y ∈ K → g * y = y * g := by
    intro g hg y hy
    change g = a ∨ g = b at hg
    refine Subgroup.closure_induction (p := fun z => g * z = z * g) hy ?_ ?_ ?_ ?_
    · simp
    · intro u v hu hv
      calc
        g * (u * v) = (g * u) * v := by rw [mul_assoc]
        _ = (u * g) * v := by rw [hu]
        _ = u * (g * v) := by rw [mul_assoc]
        _ = u * (v * g) := by rw [hv]
        _ = (u * v) * g := by rw [mul_assoc]
    · intro u hu
      calc
        g * u⁻¹ = u⁻¹ * (u * g) * u⁻¹ := by group
        _ = u⁻¹ * (g * u) * u⁻¹ := by rw [hu.symm]
        _ = u⁻¹ * g := by group
    · intro z hz
      change z = a ∨ z = b at hz
      rcases hg with rfl | rfl <;> rcases hz with rfl | rfl
      · rfl
      · exact h
      · exact h.symm
      · rfl
  intro x y
  change (x : G) * (y : G) = (y : G) * (x : G)
  refine Subgroup.closure_induction
    (p := fun u => ∀ z, z ∈ K → u * z = z * u) x.property ?_ ?_ ?_ ?_
  · intro z hz
    simp
  · intro u v hu hv z hz
    calc
      (u * v) * z = u * (v * z) := by rw [mul_assoc]
      _ = u * (z * v) := by rw [hv z hz]
      _ = (u * z) * v := by rw [← mul_assoc]
      _ = (z * u) * v := by rw [hu z hz]
      _ = z * (u * v) := by rw [mul_assoc]
  · intro u hu z hz
    calc
      u⁻¹ * z = u⁻¹ * (z * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * z) * u⁻¹ := by rw [← hu z hz]
      _ = z * u⁻¹ := by group
  · intro u hu z hz
    exact gen_comm u hu z hz
end Eval_gpt_5_6_luna

namespace Eval_gpt_5_5
open Function Fintype Subgroup Ideal Polynomial Submodule Zsqrtd
open scoped BigOperators
theorem Artin_exercise_2_2_9 {G : Type*} [Group G] {a b : G}
  (h : a * b = b * a) :
  ∀ x y : closure {x | x = a ∨ x = b}, x * y = y * x := by
  intro x y
  exact Subgroup.closure_induction₂ x.property y.property
    (by
      intro u hu v hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact h
      · exact h.symm
      · rfl)
    (by simp)
    (by simp)
    (by
      intro u v w _ _ huv huw
      calc
        u * (v * w) = (u * v) * w := by simp [mul_assoc]
        _ = (v * u) * w := by rw [huv]
        _ = v * (u * w) := by simp [mul_assoc]
        _ = v * (w * u) := by rw [huw]
        _ = (v * w) * u := by simp [mul_assoc])
    (by
      intro u v w _ _ huv huw
      calc
        (u * v) * w = u * (v * w) := by simp [mul_assoc]
        _ = u * (w * v) := by rw [huw]
        _ = (u * w) * v := by simp [mul_assoc]
        _ = (w * u) * v := by rw [huv]
        _ = w * (u * v) := by simp [mul_assoc])
    (by
      intro u v _ huv
      exact (Commute.eq (Commute.inv_left (Commute.mk huv)))
    )
    (by
      intro u v _ huv
      exact (Commute.eq (Commute.inv_right (Commute.mk huv)))
    )
end Eval_gpt_5_5
