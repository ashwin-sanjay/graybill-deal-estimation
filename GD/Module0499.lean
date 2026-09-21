import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace GD.N0072
noncomputable section

variable {k : ℕ}

def d007613 (p : Fin k → ℝ) : ℝ := ∑ i, max (p i) 0
def d007614 (p : Fin k → ℝ) (i : Fin k) : ℝ := max (p i) 0 / _root_.GD.N0072.d007613 p

theorem d007615 (p : Fin k → ℝ) (hp : ∑ i, p i = 1) :
    1 ≤ _root_.GD.N0072.d007613 p := by
  rw [← hp]
  exact Finset.sum_le_sum (fun i _ => le_max_left (p i) 0)

theorem d007616 (p : Fin k → ℝ) (hp : ∑ i, p i = 1) (i : Fin k) :
    0 ≤ _root_.GD.N0072.d007614 p i :=
  div_nonneg (le_max_right _ _) (zero_le_one.trans (_root_.GD.N0072.d007615 p hp))

theorem d007617 (p : Fin k → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, _root_.GD.N0072.d007614 p i = 1 := by
  simp only [_root_.GD.N0072.d007614, ← Finset.sum_div]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (_root_.GD.N0072.d007615 p hp)))

theorem d007618 (p : Fin k → ℝ) (hp : ∑ i, p i = 1) (i : Fin k) :
    _root_.GD.N0072.d007614 p i ≤ max (p i) 0 := by
  apply (div_le_iff₀ (zero_lt_one.trans_le (_root_.GD.N0072.d007615 p hp))).mpr
  exact le_mul_of_one_le_right (le_max_right _ _) (_root_.GD.N0072.d007615 p hp)

theorem d007619 (p : Fin k → ℝ) (hp : ∑ i, p i = 1) (i : Fin k) :
    _root_.GD.N0072.d007614 p i ^ 2 ≤ p i ^ 2 := by
  by_cases hi : 0 ≤ p i
  · have hle := _root_.GD.N0072.d007618 p hp i
    rw [max_eq_left hi] at hle
    exact (sq_le_sq₀ (_root_.GD.N0072.d007616 p hp i) hi).mpr hle
  · simp only [_root_.GD.N0072.d007614, max_eq_right (le_of_not_ge hi), zero_div, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

theorem d007620 (p : Fin k → ℝ) (i : Fin k) (hi : p i < 0) :
    _root_.GD.N0072.d007614 p i = 0 := by
  simp only [_root_.GD.N0072.d007614, max_eq_right hi.le, zero_div]

def d007621 (v p : Fin k → ℝ) : ℝ := ∑ i, p i ^ 2 * v i

theorem d007622 (v p : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i) : 0 ≤ _root_.GD.N0072.d007621 v p :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hv i))

theorem d007623 (v p : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hp : ∑ i, p i = 1) : _root_.GD.N0072.d007621 v (_root_.GD.N0072.d007614 p) ≤ _root_.GD.N0072.d007621 v p :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (_root_.GD.N0072.d007619 p hp i) (hv i))

theorem d007624 (v p : Fin k → ℝ) (hv : ∀ i, 0 < v i)
    (hp : ∑ i, p i = 1) (hneg : ∃ i, p i < 0) :
    _root_.GD.N0072.d007621 v (_root_.GD.N0072.d007614 p) < _root_.GD.N0072.d007621 v p := by
  obtain ⟨i, hi⟩ := hneg
  apply Finset.sum_lt_sum
  · exact fun j _ => mul_le_mul_of_nonneg_right (_root_.GD.N0072.d007619 p hp j) (hv j).le
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [_root_.GD.N0072.d007620 p i hi]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_pos (sq_pos_of_neg hi) (hv i)

@[fun_prop] theorem d007625 : Measurable (_root_.GD.N0072.d007614 (k := k)) := by
  unfold _root_.GD.N0072.d007614 _root_.GD.N0072.d007613
  fun_prop

@[fun_prop] theorem d007626 (v : Fin k → ℝ) : Measurable (_root_.GD.N0072.d007621 v) := by
  unfold _root_.GD.N0072.d007621
  fun_prop

end
end GD.N0072

#print axioms _root_.GD.N0072.d007617
#print axioms _root_.GD.N0072.d007619
#print axioms _root_.GD.N0072.d007624
#print axioms _root_.GD.N0072.d007625
