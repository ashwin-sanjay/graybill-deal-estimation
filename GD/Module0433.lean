import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped BigOperators

namespace GD.N0101.N0352
noncomputable section

variable {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
  [∀ j, SigmaFinite (μ j)]



theorem d006732 (i : Fin (n + 1))
    (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Integrable F (Measure.pi μ)) :
    (∫ z, F z ∂Measure.pi μ) =
      ∫ y, ∫ x, F (i.insertNth x y) ∂μ i
        ∂Measure.pi (fun j => μ (i.succAbove j)) := by
  have hp := (measurePreserving_piFinSuccAbove μ i).symm
  have hi := (hp.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurableEmbedding).mpr hF
  calc
    _ = ∫ z, F ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) i).symm z)
        ∂(μ i).prod (Measure.pi (fun j => μ (i.succAbove j))) :=
      (hp.integral_comp' F).symm
    _ = _ := integral_prod_symm _ hi

end
end GD.N0101.N0352

#print axioms _root_.GD.N0101.N0352.d006732
