import GD.Module1720

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0094
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0939 _root_.GD.N0232.N0719.N0941
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0033 _root_.GD.N0071

variable {k : ℕ}


theorem d028726
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (i h : Fin (k + 1)) (hi : sizes i = 2) (hih : i ≠ h)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => (_root_.GD.N0232.N0719.N0941.d020687 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)))⁻¹) atTop atTop := by
    apply ENNReal.tendsto_ofReal_nhds_top.mp
    simpa only [_root_.GD.N0071.d028335 sizes hk hn] using
      _root_.GD.N0094.d028722 sizes hk hn i h hi hih e he he0
  simpa only [Function.comp_def, inv_inv] using tendsto_inv_atTop_zero.comp hlim



theorem d028727
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1))
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n))) atTop
      (𝓝 (if ∃ i, i ≠ h ∧ sizes i = 2 then 0 else
        1 / (1 + _root_.GD.N0033.d028329 sizes h))) := by
  classical
  by_cases hsmall : ∃ i, i ≠ h ∧ sizes i = 2
  · rw [if_pos hsmall]
    obtain ⟨i, hih, hi⟩ := hsmall
    exact _root_.GD.N0094.d028726 sizes hk hn i h hi hih e he he0
  · rw [if_neg hsmall]
    have hother : ∀ i, i ≠ h → 3 ≤ sizes i := by
      intro i hih
      have hi : sizes i ≠ 2 := fun hi => hsmall ⟨i, hih, hi⟩
      have := hn i
      omega
    exact _root_.GD.N0033.d028332 sizes hn h hother e he he0



theorem d028728
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1))
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n))) atTop (𝓝 1) ↔
      ∀ i, i ≠ h → 4 ≤ sizes i := by
  constructor
  · intro hsat
    have hother : ∀ i, i ≠ h → 3 ≤ sizes i := by
      intro i hih
      by_contra hi
      have hi2 : sizes i = 2 := by have := hn i; omega
      have heq := tendsto_nhds_unique
        (_root_.GD.N0094.d028726 sizes hk hn i h hi2 hih e he he0) hsat
      norm_num at heq
    exact (_root_.GD.N0033.d028333 sizes hn h hother e he he0).mp hsat
  · intro hother
    exact _root_.GD.N0232.N0719.N0939.d020711 sizes hn h hother e he he0

end
end GD.N0094

#print axioms _root_.GD.N0094.d028726
#print axioms _root_.GD.N0094.d028727
#print axioms _root_.GD.N0094.d028728
