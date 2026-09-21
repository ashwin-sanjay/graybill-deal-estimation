import GD.Module1498

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace GD.N0072
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0107

variable {k : ℕ}




theorem d023454 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, w (_root_.GD.N0232.N0719.N0900.d009103 k sizes z) i < 0}) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0072.d007614 ∘ w)) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) := by
  have hqfinite := _root_.GD.N0072.d023443 sizes hn w hw hunit
  intro θ
  by_cases hf : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) = ⊤
  · rw [hf]
    exact lt_top_iff_ne_top.mpr (hqfinite.2 θ)
  · rw [_root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0072.d007625.comp hw)
        (fun t => _root_.GD.N0072.d007617 (w t) (hunit t)),
      _root_.GD.N0072.d023297 sizes hn w hw hunit]
    have hv : ∀ i, 0 < θ.scale i ^ 2 / (sizes i : ℝ) := fun i =>
      div_pos (sq_pos_of_pos (θ.scale_pos i))
        (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hn i)))
    apply _root_.GD.N0072.d023449 _ _ hv w hw hunit
    · rw [← _root_.GD.N0072.d023297 sizes hn w hw hunit θ]
      exact hf
    · exact _root_.GD.N0072.d023450 sizes hn w hw θ₀ hneg θ




theorem d023455
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, w (fun j => _root_.GD.N0107.d009085 (z j)) i < 0}) :
    Measurable (_root_.GD.N0072.d007614 ∘ w) ∧
      (∀ t, ∑ i, (_root_.GD.N0072.d007614 ∘ w) t i = 1) ∧
      (∀ t i, 0 ≤ (_root_.GD.N0072.d007614 ∘ w) t i) ∧
      _root_.GD.N0072.d023292 sizes (_root_.GD.N0072.d007614 ∘ w) ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes (_root_.GD.N0072.d007614 ∘ w)) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  let wr : (Fin k → ℝ) → Fin k → ℝ := fun t => w (fun i => (sizes i : ℝ) * t i)
  have hwr : Measurable wr := by unfold wr; fun_prop
  have hwrunit : ∀ t, ∑ i, wr t i = 1 := fun t => hunit _
  have hraw : _root_.GD.N0072.d023291 sizes wr = _root_.GD.N0072.d023292 sizes w :=
    (_root_.GD.N0072.d023294 sizes hn0 w).symm
  have hrawq : _root_.GD.N0072.d023291 sizes (_root_.GD.N0072.d007614 ∘ wr) =
      _root_.GD.N0072.d023292 sizes (_root_.GD.N0072.d007614 ∘ w) := by
    simpa only [wr, Function.comp_def] using
      (_root_.GD.N0072.d023294 sizes hn0 (_root_.GD.N0072.d007614 ∘ w)).symm
  have hnr : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, wr (_root_.GD.N0232.N0719.N0900.d009103 k sizes z) i < 0} := by
    simpa only [wr, _root_.GD.N0072.d023293 sizes hn0] using hneg
  have hs := _root_.GD.N0072.d023454 sizes hn wr hwr hwrunit θ₀ hnr
  have hqfinite := _root_.GD.N0072.d023443 sizes hn wr hwr hwrunit
  rw [hrawq] at hqfinite
  simp only [hrawq, hraw] at hs
  exact ⟨_root_.GD.N0072.d007625.comp hw,
    fun t => _root_.GD.N0072.d007617 (w t) (hunit t),
    fun t i => _root_.GD.N0072.d007616 (w t) (hunit t) i, hqfinite, hs⟩

end
end GD.N0072

#print axioms _root_.GD.N0072.d023454
#print axioms _root_.GD.N0072.d023455
