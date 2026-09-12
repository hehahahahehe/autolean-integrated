import Mathlib

namespace Eval_gpt_6_astra
/--
Let $S$ be a set of rational numbers such that whenever $a$ and $b$ are members of $S$, so are $a+b$ and $ab$, and having the property that for every rational number $r$ exactly one of the following three statements is true: \[ r \in S, -r \in S, r = 0. \] Prove that $S$ is the set of all positive rational numbers.
-/
theorem putnam_1962_a6
(S : Set ℚ)
(hSadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
(hSprod : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
(hScond : ∀ r : ℚ, (r ∈ S ∨ -r ∈ S ∨ r = 0) ∧ ¬(r ∈ S ∧ -r ∈ S) ∧ ¬(r ∈ S ∧ r = 0) ∧ ¬(-r ∈ S ∧ r = 0))
: S = { r : ℚ | r > 0 } :=
by
  have hzero : (0 : ℚ) ∉ S := by
    intro h
    exact (hScond 0).2.2.1 ⟨h, rfl⟩
  have hone : (1 : ℚ) ∈ S := by
    rcases (hScond 1).1 with h | h | h
    · exact h
    · have := hSprod (-1) h (-1) h
      norm_num at this
      exact this
    · norm_num at h
  have hnat : ∀ n : ℕ, 0 < n → (n : ℚ) ∈ S := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      by_cases h : n = 0
      · subst n
        simpa using hone
      · have hn' : 0 < n := Nat.pos_of_ne_zero h
        simpa only [Nat.cast_add, Nat.cast_one] using
          hSadd (n : ℚ) (ih hn') 1 hone
  have hpos : ∀ r : ℚ, 0 < r → r ∈ S := by
    intro r hr
    have hd : (0 : ℚ) < (r.den : ℚ) := by
      exact_mod_cast r.den_pos
    have hrepr : (r.num : ℚ) / (r.den : ℚ) = r := by
      first
      | exact Rat.num_div_den r
      | exact Rat.num_den r
    have heq : (r.num : ℚ) = r * (r.den : ℚ) :=
      (div_eq_iff (ne_of_gt hd)).mp hrepr
    have hnum : (0 : ℚ) < (r.num : ℚ) := by
      rw [heq]
      exact mul_pos hr hd
    have hi : 0 ≤ r.num := by
      exact_mod_cast (le_of_lt hnum)
    have hc : (r.num.toNat : ℚ) = (r.num : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg hi)
    have hn : 0 < r.num.toNat := by
      have : (0 : ℚ) < (r.num.toNat : ℚ) := by
        rw [hc]
        exact hnum
      exact_mod_cast this
    have hnumS : (r.num : ℚ) ∈ S := by
      rw [← hc]
      exact hnat _ hn
    rcases (hScond r).1 with h | h | h
    · exact h
    · have hdS : (r.den : ℚ) ∈ S := hnat _ r.den_pos
      have hneg : -(r.num : ℚ) ∈ S := by
        have hm := hSprod (-r) h (r.den : ℚ) hdS
        simpa only [neg_mul, ← heq] using hm
      exact False.elim ((hScond (r.num : ℚ)).2.1 ⟨hnumS, hneg⟩)
    · subst r
      norm_num at hr
  apply Set.ext
  intro r
  change r ∈ S ↔ 0 < r
  constructor
  · intro hr
    by_contra h
    have hle : r ≤ 0 := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (hScond r).2.1 ⟨hr, hpos (-r) (neg_pos.mpr hlt)⟩
    · exact hzero (heq ▸ hr)
  · exact hpos r
end Eval_gpt_6_astra

namespace Eval_gpt_5_6_sol
/--
Let $S$ be a set of rational numbers such that whenever $a$ and $b$ are members of $S$, so are $a+b$ and $ab$, and having the property that for every rational number $r$ exactly one of the following three statements is true: \[ r \in S, -r \in S, r = 0. \] Prove that $S$ is the set of all positive rational numbers.
-/
theorem putnam_1962_a6
(S : Set ℚ)
(hSadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
(hSprod : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
(hScond : ∀ r : ℚ, (r ∈ S ∨ -r ∈ S ∨ r = 0) ∧ ¬(r ∈ S ∧ -r ∈ S) ∧ ¬(r ∈ S ∧ r = 0) ∧ ¬(-r ∈ S ∧ r = 0))
: S = { r : ℚ | r > 0 } :=
by
  have hone : (1 : ℚ) ∈ S := by
    rcases (hScond 1).1 with h | h | h
    · exact h
    · simpa using hSprod (-1) h (-1) h
    · norm_num at h
  have hnat : ∀ n : ℕ, 0 < n → (n : ℚ) ∈ S := by
    have hsucc : ∀ n : ℕ, ((n.succ : ℕ) : ℚ) ∈ S := by
      intro n
      induction n with
      | zero =>
          simpa using hone
      | succ n ih =>
          simpa only [Nat.cast_succ] using
            hSadd ((n.succ : ℕ) : ℚ) ih 1 hone
    intro n hn
    obtain ⟨k, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact hsucc k
  have hpositive : ∀ r : ℚ, 0 < r → r ∈ S := by
    intro r hr
    rcases (hScond r).1 with hrs | hnrs | hr0
    · exact hrs
    · have hdenpos : (0 : ℚ) < (r.den : ℚ) := by
        exact_mod_cast r.den_pos
      have hdenS : (r.den : ℚ) ∈ S :=
        hnat r.den r.den_pos
      have hmul : r * (r.den : ℚ) = (r.num : ℚ) := by
        rw [← r.num_div_den]
        field_simp [ne_of_gt hdenpos]
      have hnumQ : (0 : ℚ) < (r.num : ℚ) := by
        rw [← hmul]
        exact mul_pos hr hdenpos
      have hnum : 0 < r.num := by
        exact_mod_cast hnumQ
      have hnumeq :
          ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt hnum)
      have hnumS : (r.num : ℚ) ∈ S := by
        rw [← hnumeq]
        exact hnat _ (Int.toNat_pos.mpr hnum)
      have hnegnumS : -(r.num : ℚ) ∈ S := by
        have hp := hSprod (-r) hnrs (r.den : ℚ) hdenS
        simpa [hmul] using hp
      exact False.elim ((hScond (r.num : ℚ)).2.1 ⟨hnumS, hnegnumS⟩)
    · linarith
  ext r
  constructor
  · intro hrs
    by_contra hr
    rcases lt_or_eq_of_le (le_of_not_gt hr) with hneg | rfl
    · have hnrs : -r ∈ S := hpositive (-r) (by linarith)
      exact (hScond r).2.1 ⟨hrs, hnrs⟩
    · exact (hScond 0).2.2.1 ⟨hrs, rfl⟩
  · intro hr
    exact hpositive r hr
end Eval_gpt_5_6_sol

namespace Eval_gpt_5_6_terra
/--
Let $S$ be a set of rational numbers such that whenever $a$ and $b$ are members of $S$, so are $a+b$ and $ab$, and having the property that for every rational number $r$ exactly one of the following three statements is true: \[ r \in S, -r \in S, r = 0. \] Prove that $S$ is the set of all positive rational numbers.
-/
theorem putnam_1962_a6
(S : Set ℚ)
(hSadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
(hSprod : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
(hScond : ∀ r : ℚ, (r ∈ S ∨ -r ∈ S ∨ r = 0) ∧ ¬(r ∈ S ∧ -r ∈ S) ∧ ¬(r ∈ S ∧ r = 0) ∧ ¬(-r ∈ S ∧ r = 0))
: S = { r : ℚ | r > 0 } :=
by
  have h_one : (1 : ℚ) ∈ S := by
    rcases (hScond 1).1 with h | h | h
    · exact h
    · have h' := hSprod (-1) h (-1) h
      norm_num at h'
      exact h'
    · norm_num at h
  have h_nat : ∀ n : ℕ, 0 < n → (n : ℚ) ∈ S := by
    intro n hn
    induction n with
    | zero => simp at hn
    | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using h_one
        · simpa [Nat.cast_succ] using hSadd (n : ℚ) (ih hn) 1 h_one
  have h_inv : ∀ n : ℕ, 0 < n → ((n : ℚ)⁻¹) ∈ S := by
    intro n hn
    rcases (hScond ((n : ℚ)⁻¹)).1 with h | h | h
    · exact h
    · exfalso
      apply (hScond (1 : ℚ)).2.1
      refine ⟨h_one, ?_⟩
      have h' := hSprod (-(n : ℚ)⁻¹) h (n : ℚ) (h_nat n hn)
      convert h' using 1
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
    · have hn0 : (n : ℚ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hn
      exact (inv_ne_zero hn0 h).elim
  have hpos : ∀ r : ℚ, 0 < r → r ∈ S := by
    intro r hr
    have hdennat : 0 < r.den := Nat.pos_of_ne_zero (Rat.den_nz r)
    have hden : 0 < (r.den : ℚ) := by
      exact_mod_cast hdennat
    have hfrac : 0 < (r.num : ℚ) / (r.den : ℚ) := by
      simpa only [Rat.num_div_den] using hr
    have hnum : 0 < (r.num : ℚ) := by
      rcases (div_pos_iff.mp hfrac) with h | h
      · exact h.1
      · linarith
    have hnum_nat : 0 < r.num.toNat := Int.toNat_pos.mpr hnum
    have hcast : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by
      have hz : (↑r.num.toNat : ℤ) = r.num :=
        Int.toNat_of_nonneg (le_of_lt hnum)
      exact_mod_cast hz
    have hnum_mem : (r.num : ℚ) ∈ S := by
      rw [← hcast]
      exact h_nat r.num.toNat hnum_nat
    calc
      r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
      _ = (r.num : ℚ) * ((r.den : ℚ)⁻¹) := by rw [div_eq_mul_inv]
      _ ∈ S := hSprod _ hnum_mem _ (h_inv r.den hdennat)
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hr
    rcases lt_trichotomy r 0 with h | h | h
    · exfalso
      apply (hScond r).2.1
      refine ⟨hr, ?_⟩
      simpa using hpos (-r) (by linarith)
    · exact (hScond r).2.2.1 ⟨hr, h⟩ |> False.elim
    · exact h
  · exact hpos r
end Eval_gpt_5_6_terra

namespace Eval_gpt_5_6_luna
/--
Let $S$ be a set of rational numbers such that whenever $a$ and $b$ are members of $S$, so are $a+b$ and $ab$, and having the property that for every rational number $r$ exactly one of the following three statements is true: \[ r \in S, -r \in S, r = 0. \] Prove that $S$ is the set of all positive rational numbers.
-/
theorem putnam_1962_a6
(S : Set ℚ)
(hSadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
(hSprod : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
(hScond : ∀ r : ℚ, (r ∈ S ∨ -r ∈ S ∨ r = 0) ∧ ¬(r ∈ S ∧ -r ∈ S) ∧ ¬(r ∈ S ∧ r = 0) ∧ ¬(-r ∈ S ∧ r = 0))
: S = { r : ℚ | r > 0 } :=
by
  obtain ⟨hcase1, hnotboth1, _, _⟩ := hScond (1 : ℚ)
  have hone : (1 : ℚ) ∈ S := by
    rcases hcase1 with h | h
    · exact h
    · rcases h with h | h
      · have hs : ((-1 : ℚ) * (-1)) ∈ S := hSprod _ h _ h
        simpa using hs
      · norm_num at h
  have hnat : ∀ n : ℕ, 0 < n → (n : ℚ) ∈ S := by
    intro n
    induction n with
    | zero =>
        intro hn
        omega
    | succ n ih =>
        intro _
        by_cases hn0 : n = 0
        · subst n
          simpa using hone
        · have hprev : 0 < n := by omega
          have hs := hSadd _ (ih hprev) _ hone
          simpa [Nat.cast_succ] using hs
  have hpos : ∀ q : ℚ, 0 < q → q ∈ S := by
    intro q hq
    have hdenQ : (0 : ℚ) < (q.den : ℚ) := by
      exact_mod_cast q.den_pos
    have hnumQ : (0 : ℚ) < (q.num : ℚ) := by
      have hmul : (q.num : ℚ) = q * (q.den : ℚ) := by
        calc
          (q.num : ℚ) = ((q.num : ℚ) / (q.den : ℚ)) * (q.den : ℚ) := by
            field_simp [ne_of_gt hdenQ]
          _ = q * (q.den : ℚ) := by rw [q.num_div_den]
      nlinarith [mul_pos hq hdenQ]
    have hnumInt : 0 < q.num := by
      exact_mod_cast hnumQ
    have hnumCast : (q.num.toNat : ℚ) = (q.num : ℚ) := by
      have hz : (q.num.toNat : ℤ) = q.num :=
        Int.toNat_of_nonneg (le_of_lt hnumInt)
      exact_mod_cast hz
    have hnumS : (q.num : ℚ) ∈ S := by
      have hs := hnat q.num.toNat (by exact_mod_cast hnumQ)
      rw [hnumCast] at hs
      exact hs
    have hdenS : (q.den : ℚ) ∈ S := hnat q.den q.den_pos
    have hinvS : (q.den : ℚ)⁻¹ ∈ S := by
      let d : ℚ := q.den
      have hdpos : 0 < d := by
        exact_mod_cast q.den_pos
      have hdS : d ∈ S := by
        simpa [d] using hdenS
      have hinvne : d⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hdpos)
      rcases (hScond (d⁻¹)).1 with hi | hneg | hzero
      · simpa [d] using hi
      · have hprod : d * (-(d⁻¹)) ∈ S := hSprod _ hdS _ hneg
        have heq : d * (-(d⁻¹)) = (-1 : ℚ) := by
          field_simp [ne_of_gt hdpos]
        rw [heq] at hprod
        exact (hnotboth1 ⟨hone, hprod⟩).elim
      · exact (hinvne hzero).elim
    have heq : q = (q.num : ℚ) * (q.den : ℚ)⁻¹ := by
      rw [← q.num_div_den]
      field_simp [ne_of_gt hdenQ]
    rw [heq]
    exact hSprod _ hnumS _ hinvS
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra hnot
    have hxle : x ≤ 0 := le_of_not_gt hnot
    have hxne : x ≠ 0 := by
      intro hz
      obtain ⟨_, _, hnotzero, _⟩ := hScond x
      exact hnotzero ⟨hx, hz⟩
    have hxlt : x < 0 := lt_of_le_of_ne hxle hxne
    have hnegS := hpos (-x) (neg_pos.mpr hxlt)
    obtain ⟨_, hnotboth, _, _⟩ := hScond x
    exact hnotboth ⟨hx, hnegS⟩
  · exact hpos x)
end Eval_gpt_5_6_luna

namespace Eval_gpt_5_5
/--
Let $S$ be a set of rational numbers such that whenever $a$ and $b$ are members of $S$, so are $a+b$ and $ab$, and having the property that for every rational number $r$ exactly one of the following three statements is true: \[ r \in S, -r \in S, r = 0. \] Prove that $S$ is the set of all positive rational numbers.
-/
theorem putnam_1962_a6
(S : Set ℚ)
(hSadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S)
(hSprod : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
(hScond : ∀ r : ℚ, (r ∈ S ∨ -r ∈ S ∨ r = 0) ∧ ¬(r ∈ S ∧ -r ∈ S) ∧ ¬(r ∈ S ∧ r = 0) ∧ ¬(-r ∈ S ∧ r = 0))
: S = { r : ℚ | r > 0 } :=
by
  ext r
  constructor
  · intro hr
    by_contra h
    have hz : r = 0 ∨ r < 0 := by linarith
    rcases hz with rfl | hrneg
    · exact (hScond 0).2.2.1 ⟨hr, rfl⟩
    · have hpos : -r ∈ S := by
        have htr := (hScond (-r)).1
        rcases htr with h1 | h2 | h3
        · simpa using h1
        · exfalso
          have : r ∈ S := by simpa using h2
          exact (hScond r).2.1 ⟨hr, this⟩
        · linarith
      exact (hScond r).2.1 ⟨hr, hpos⟩
  · intro hrpos
    have hzero_not : 0 ∉ S := by
      intro h0
      exact (hScond 0).2.2.1 ⟨h0, rfl⟩
    have hOne : (1 : ℚ) ∈ S := by
      have htr := (hScond (1 : ℚ)).1
      rcases htr with h1 | hm1 | hzero
      · exact h1
      · exfalso
        have h1' : (1 : ℚ) ∈ S := by
          have := hSprod (-1) hm1 (-1) hm1
          simpa using this
        have h0 : (0 : ℚ) ∈ S := by
          have := hSadd (-1) hm1 1 h1'
          simpa using this
        exact hzero_not h0
      · norm_num at hzero
    have hnat : ∀ n : ℕ, 0 < n → ((n : ℚ) ∈ S) := by
      intro n hn
      induction' n with n ih
      · norm_num at hn
      · cases n with
        | zero =>
            simpa using hOne
        | succ n =>
            have hsucc : (0 : ℕ) < Nat.succ n := Nat.succ_pos n
            have hnS : ((Nat.succ n : ℚ) ∈ S) := ih hsucc
            have := hSadd (Nat.succ n : ℚ) hnS 1 hOne
            norm_num at this
            simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using this
    obtain ⟨m, n, hn, hmn⟩ := Rat.exists_eq_num_div_den r
    have hnpos : (0 : ℚ) < n := by exact_mod_cast n.pos
    have hnS : ((n : ℚ) ∈ S) := hnat n (Nat.pos_of_ne_zero hn)
    have hmpos : (0 : ℚ) < m := by
      rw [hmn] at hrpos
      positivity
    have hm_nat_pos : 0 < m.natAbs := Int.natAbs_pos.mpr (by linarith)
    have hmS : ((m.natAbs : ℚ) ∈ S) := hnat m.natAbs hm_nat_pos
    have hmS' : ((m : ℚ) ∈ S) := by
      have : m = (m.natAbs : ℤ) := Int.eq_natAbs_of_zero_le (by linarith)
      simpa [this] using hmS
    have htr := (hScond r).1
    rcases htr with hrS | hnrS | hz
    · exact hrS
    · exfalso
      have hprod : ((n : ℚ) * (-r) ∈ S) := hSprod (n : ℚ) hnS (-r) hnrS
      have hnegm : (-(m : ℚ) ∈ S) := by
        rw [hmn] at hprod
        field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast hn] at hprod
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
      have h0 : (0 : ℚ) ∈ S := by
        have := hSadd (m : ℚ) hmS' (-(m : ℚ)) hnegm
        simpa using this
      exact hzero_not h0
    · linarith
end Eval_gpt_5_5
