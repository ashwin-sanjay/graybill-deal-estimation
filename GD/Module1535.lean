import GD.Module1534

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0038
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0069

variable {k : ℕ}


theorem d023861 (sizes : Fin k → ℕ) (i j : Fin k) :
    1 < _root_.GD.N0069.d022756 sizes i * _root_.GD.N0069.d022756 sizes j ↔ 4 < (sizes i - 1) * (sizes j - 1) := by
  unfold _root_.GD.N0069.d022756
  constructor
  · intro h
    have hh : (4 : ℝ) < ((sizes i - 1 : ℕ) : ℝ) * ((sizes j - 1 : ℕ) : ℝ) := by nlinarith
    exact_mod_cast hh
  · intro h
    have hh : (4 : ℝ) < ((sizes i - 1 : ℕ) : ℝ) * ((sizes j - 1 : ℕ) : ℝ) := by exact_mod_cast h
    nlinarith



theorem d023862
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hpairs : ∀ i j : Fin k, i ≠ j → 4 < (sizes i - 1) * (sizes j - 1)) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  apply _root_.GD.N0038.d023860 hk sizes hn
  intro i j hij
  exact (_root_.GD.N0038.d023861 sizes i j).mpr (hpairs i j hij)

theorem d023863
    (sizes : Fin k → ℕ) (i₀ : Fin k) (hsmall : 2 ≤ sizes i₀)
    (hlarge : ∀ i, i ≠ i₀ → 6 ≤ sizes i) :
    (∀ i, 2 ≤ sizes i) ∧
      ∀ i j : Fin k, i ≠ j → 4 < (sizes i - 1) * (sizes j - 1) := by
  have hn (i : Fin k) : 2 ≤ sizes i := by
    by_cases hi : i = i₀
    · simpa only [hi] using hsmall
    · have := hlarge i hi
      omega
  refine ⟨hn, ?_⟩
  intro i j hij
  have hi : 1 ≤ sizes i - 1 := by have := hn i; omega
  have hj : 1 ≤ sizes j - 1 := by have := hn j; omega
  by_cases hi0 : i = i₀
  · have hj0 : j ≠ i₀ := by intro h; exact hij (hi0.trans h.symm)
    have hj5 : 5 ≤ sizes j - 1 := by have := hlarge j hj0; omega
    nlinarith
  · have hi5 : 5 ≤ sizes i - 1 := by have := hlarge i hi0; omega
    nlinarith



theorem d023864
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (i₀ : Fin k)
    (hsmall : 2 ≤ sizes i₀) (hlarge : ∀ i, i ≠ i₀ → 6 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes < ⊤ := by
  obtain ⟨hn, hpairs⟩ := _root_.GD.N0038.d023863 sizes i₀ hsmall hlarge
  exact _root_.GD.N0038.d023862 hk sizes hn hpairs



theorem d023865
    (hk : 2 ≤ k) (sizes : Fin k → ℕ) (i₀ : Fin k)
    (hsmall : 2 ≤ sizes i₀) (hlarge : ∀ i, i ≠ i₀ → 6 ≤ sizes i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable d ∧ ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0232.N0719.N0962.d012186 k sizes θ d ≤ ENNReal.ofReal C := by
  obtain ⟨hn, hpairs⟩ := _root_.GD.N0038.d023863 sizes i₀ hsmall hlarge
  apply _root_.GD.N0038.d023859 hk sizes hn
  intro i j hij
  exact (_root_.GD.N0038.d023861 sizes i j).mpr (hpairs i j hij)

end
end GD.N0038

#print axioms _root_.GD.N0038.d023861
#print axioms _root_.GD.N0038.d023862
#print axioms _root_.GD.N0038.d023864
#print axioms _root_.GD.N0038.d023865
