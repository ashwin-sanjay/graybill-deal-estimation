import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0044
noncomputable section

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]


theorem d007609 {μ ν : ι → Measure X} (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro t _
    exact (OuterMeasure.pi_pi_le _ t).trans (Finset.prod_le_prod' fun i _ => h i (t i))
  exact ho s


theorem d007610 (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  letI (i : ι) : IsFiniteMeasure (c i • μ i) := (μ i).smul_finite (hc i)
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  exact (Finset.prod_mul_distrib).symm



theorem d007611 (μ ν : ι → Measure X)
    [∀ j, IsFiniteMeasure (μ j)] (i : ι) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hi : c • μ i ≤ ν i) (hother : ∀ j, j ≠ i → μ j ≤ ν j) :
    c • Measure.pi μ ≤ Measure.pi ν := by
  classical
  let w : ι → ℝ≥0∞ := fun j => if j = i then c else 1
  have hw (j : ι) : w j ≠ ⊤ := by
    dsimp only [w]
    split_ifs <;> simp_all
  have hp : (∏ j, w j) = c := by simp [w]
  rw [← hp, ← _root_.GD.N0044.d007610 μ w hw]
  apply _root_.GD.N0044.d007609
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [w, if_pos rfl] using hi
  · simpa only [w, if_neg hj, one_smul] using hother j hj



theorem d007612 (μ ν : ι → Measure X)
    [∀ j, IsFiniteMeasure (μ j)] (i : ι) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hi : c • μ i ≤ ν i) (hother : ∀ j, j ≠ i → μ j ≤ ν j)
    (f : (ι → X) → ℝ≥0∞) :
    c * (∫⁻ x, f x ∂Measure.pi μ) ≤ ∫⁻ x, f x ∂Measure.pi ν := by
  have h := lintegral_mono' (f := f) (_root_.GD.N0044.d007611 μ ν i hc hi hother) le_rfl
  simpa only [lintegral_smul_measure, smul_eq_mul] using h

end
end GD.N0044

#print axioms _root_.GD.N0044.d007609
#print axioms _root_.GD.N0044.d007610
#print axioms _root_.GD.N0044.d007611
#print axioms _root_.GD.N0044.d007612
