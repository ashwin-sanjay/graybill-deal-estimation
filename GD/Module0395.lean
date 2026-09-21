import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal BigOperators

namespace GD.N0089
noncomputable section

theorem d006087 {k : ℕ} (μ : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (f : Fin k → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin k → ℝ, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction k with
  | zero => simp [Measure.pi_empty_univ]
  | succ k ih =>
    have hm : Measurable (fun x : Fin (k + 1) → ℝ => ∏ i, f i (x i)) := by fun_prop
    rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp hm]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    have hgm : Measurable (fun x : Fin k → ℝ => ∏ i, f i.succ (x i)) := by fun_prop
    rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j => μ j.succ)
      (hf 0).aemeasurable hgm.aemeasurable, ih
      (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ)]



theorem d006088 {k : ℕ} (μ : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (f : Fin k → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    _root_.GD.N0089.d006087 _ f hf]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]

end
end GD.N0089

#print axioms _root_.GD.N0089.d006087
#print axioms _root_.GD.N0089.d006088
