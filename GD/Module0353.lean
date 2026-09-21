import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace GD.N0104
noncomputable section

variable {k : ℕ}

theorem d005221 (α : Fin k → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hsum : ∑ i, α i = 1) (s : Finset (Fin k)) : ∑ i ∈ s, α i ≤ 1 := by
  calc
    ∑ i ∈ s, α i ≤ ∑ i, α i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => hα i)
    _ = 1 := hsum

theorem d005222 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) (hα : ∀ i, 0 ≤ 1 - ρ * a i)
    (hsum : ∑ i, (1 - ρ * a i) = 1) (s : Finset (Fin k)) (hs : s.Nonempty) :
    (s.card : ℝ) - 1 < ∑ i ∈ s, a i := by
  have hbound := _root_.GD.N0104.d005221 (fun i => 1 - ρ * a i) hα hsum s
  have hpos : 0 < ∑ i ∈ s, a i := Finset.sum_pos (fun i _ => ha i) hs
  have hmul := mul_lt_mul_of_pos_right hρ hpos
  have hid : ρ * (∑ i ∈ s, a i) = (s.card : ℝ) - ∑ i ∈ s, (1 - ρ * a i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum]
    ring
  linarith

theorem d005223 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) (hα : ∀ i, 0 ≤ 1 - ρ * a i)
    (hsum : ∑ i, (1 - ρ * a i) = 1) (i j : Fin k) (hij : i ≠ j) :
    1 < a i + a j := by
  have h := _root_.GD.N0104.d005222 a ρ ha hρ hα hsum {i, j}
    (by simp)
  norm_num [hij] at h
  exact h

theorem d005224 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 ≤ 1 - ρ * (((sizes i - 1 : ℕ) : ℝ) / 2))
    (hsum : ∑ i, (1 - ρ * (((sizes i - 1 : ℕ) : ℝ) / 2)) = 1) :
    Set.Subsingleton {i : Fin k | sizes i = 2} := by
  have ha : ∀ i, 0 < (((sizes i - 1 : ℕ) : ℝ) / 2) := by
    intro i
    exact div_pos (by exact_mod_cast (show 0 < sizes i - 1 by have := hn i; omega))
      (by norm_num)
  intro i hi j hj
  by_contra hij
  have h := _root_.GD.N0104.d005223 (fun i => (((sizes i - 1 : ℕ) : ℝ) / 2))
    ρ ha hρ hα hsum i j hij
  simp only [Set.mem_setOf_eq] at hi hj
  norm_num [hi, hj] at h

#print axioms _root_.GD.N0104.d005221
#print axioms _root_.GD.N0104.d005222
#print axioms _root_.GD.N0104.d005223
#print axioms _root_.GD.N0104.d005224

end
end GD.N0104
