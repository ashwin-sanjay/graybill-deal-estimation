import GD.Module1498














set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal BigOperators

namespace GD.N0072
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933


theorem d023456 {k : ℕ}
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0072.d007614 ∘ w)) ≤
        ENNReal.ofReal (∑ i, θ.scale i ^ 2 / (sizes i : ℝ)) ∧
      ENNReal.ofReal (∑ i, θ.scale i ^ 2 / (sizes i : ℝ)) < ⊤ := by
  refine ⟨?_, ENNReal.ofReal_lt_top⟩
  let v : Fin k → ℝ := fun i => θ.scale i ^ 2 / (sizes i : ℝ)
  have hv : ∀ i, 0 ≤ v i := fun i => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ.scale
  rw [_root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0072.d007625.comp hw)
    (fun t => _root_.GD.N0072.d007617 (w t) (hunit t))]
  calc
    _ ≤ ∫⁻ _t, ENNReal.ofReal (∑ i, v i) ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale :=
      lintegral_mono (fun t => ENNReal.ofReal_le_ofReal
        (_root_.GD.N0072.d023442 v (w t) hv (hunit t)))
    _ = ENNReal.ofReal (∑ i, θ.scale i ^ 2 / (sizes i : ℝ)) := by simp [v]

end
end GD.N0072

#print axioms _root_.GD.N0072.d023456
