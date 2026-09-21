import GD.Module1487
import GD.Module1491

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0421
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0021

variable {k : ℕ}


theorem d023356 (sizes : Fin k → ℕ)
    (hn : ∀ i, 4 ≤ sizes i) :
    (∫ q : Fin k → ℝ, _root_.GD.N0021.d023316 q
      ∂Measure.pi (fun i => gammaMeasure (((sizes i - 1 : ℕ) : ℝ) / 2)
        (((sizes i - 1 : ℕ) : ℝ) / 2))) =
      (k : ℝ) + ((k : ℝ) - 1) *
        ∑ i, ((sizes i : ℝ) - 1) / ((sizes i : ℝ) - 3) := by
  have hcast (i : Fin k) : ((sizes i - 1 : ℕ) : ℝ) = (sizes i : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ sizes i by have := hn i; omega), Nat.cast_one]
  have hnreal (i : Fin k) : (4 : ℝ) ≤ (sizes i : ℝ) := by exact_mod_cast hn i
  have hs (i : Fin k) : 1 < ((sizes i - 1 : ℕ) : ℝ) / 2 := by
    rw [hcast]
    linarith [hnreal i]
  rw [_root_.GD.N0102.N0421.d023322 _ hs]
  apply congrArg (fun x : ℝ => (k : ℝ) + ((k : ℝ) - 1) * x)
  apply Finset.sum_congr rfl
  intro i _
  rw [hcast]
  have hden : (sizes i : ℝ) - 3 ≠ 0 := by linarith [hnreal i]
  have hden' : ((sizes i : ℝ) - 1) / 2 - 1 ≠ 0 := by linarith [hnreal i]
  apply (div_eq_div_iff hden' hden).2
  ring


theorem d023357 (sizes : Fin k → ℕ)
    (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0021.d023350 sizes = (k : ℝ) + ((k : ℝ) - 1) *
      ∑ i, ((sizes i : ℝ) - 1) / ((sizes i : ℝ) - 3) := by
  simpa only [_root_.GD.N0021.d023350, _root_.GD.N0021.d023347, _root_.GD.N0021.d023346] using
    _root_.GD.N0102.N0421.d023356 sizes hn


theorem d023358 (sizes : Fin k → ℕ)
    (hk : 0 < k) (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤
      ENNReal.ofReal ((k : ℝ) + ((k : ℝ) - 1) *
        ∑ i, ((sizes i : ℝ) - 1) / ((sizes i : ℝ) - 3)) := by
  rw [← _root_.GD.N0102.N0421.d023357 sizes hn]
  exact _root_.GD.N0021.d023354 sizes hk hn

end
end GD.N0102.N0421

#print axioms _root_.GD.N0102.N0421.d023356
#print axioms _root_.GD.N0102.N0421.d023357
#print axioms _root_.GD.N0102.N0421.d023358
