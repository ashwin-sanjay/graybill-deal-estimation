import GD.Module0539
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0401
noncomputable section

open _root_.GD.N0225.N0539

variable {k : ℕ}

theorem d008072 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    Integrable (fun β => Real.exp (-(∑ i, β i))) (_root_.GD.N0225.N0539.d008044 α) := by
  have hm : Measurable (fun β : Fin k → ℝ => ∑ i, β i) := by fun_prop
  have hf : Measurable (fun r : ℝ => Real.exp (-r)) := by fun_prop
  apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp
  rw [_root_.GD.N0225.N0539.d008056 α hα hsum]
  exact (integrableOn_exp_neg_Ioi 0).smul_measure (_root_.GD.N0225.N0539.d008055 α hα)


theorem d008073 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    (∫ β, Real.exp (-(∑ i, β i)) ∂_root_.GD.N0225.N0539.d008044 α) =
      (_root_.GD.N0225.N0539.d008044 α {β | ∑ i, β i ≤ 1}).toReal := by
  have hm : Measurable (fun β : Fin k → ℝ => ∑ i, β i) := by fun_prop
  have hf : Measurable (fun r : ℝ => Real.exp (-r)) := by fun_prop
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,
    _root_.GD.N0225.N0539.d008056 α hα hsum, integral_smul_measure, smul_eq_mul,
    integral_exp_neg_Ioi_zero, mul_one]

theorem d008074 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    (∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0225.N0539.d008044 α) =
      _root_.GD.N0225.N0539.d008044 α {β | ∑ i, β i ≤ 1} := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0101.N0401.d008072 α hα hsum)
    (ae_of_all _ fun _ => (Real.exp_pos _).le),
    _root_.GD.N0101.N0401.d008073 α hα hsum,
    ENNReal.ofReal_toReal (_root_.GD.N0225.N0539.d008055 α hα)]

theorem d008075 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    (∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0225.N0539.d008044 α) ≠ ⊤ := by
  rw [_root_.GD.N0101.N0401.d008074 α hα hsum]
  exact _root_.GD.N0225.N0539.d008055 α hα

end
end GD.N0101.N0401

#print axioms _root_.GD.N0101.N0401.d008072
#print axioms _root_.GD.N0101.N0401.d008073
#print axioms _root_.GD.N0101.N0401.d008074
#print axioms _root_.GD.N0101.N0401.d008075
