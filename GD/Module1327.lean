import GD.Module1326

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory

namespace GD.N0105
noncomputable section
open _root_.GD.N0150

variable {ι : Type*} [Fintype ι]

theorem d021633 (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (i j : ι) (hij : i ≠ j) :
    (Measure.pi μ).map (fun x => (x i, x j)) = (μ i).prod (μ j) := by
  have hind : iIndepFun (fun i (x : ι → ℝ) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => fun x : ℝ => x) (fun _ => measurable_id.aemeasurable)
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp
      (hind.indepFun hij)
  simpa only [(measurePreserving_eval μ i).map_eq,
    (measurePreserving_eval μ j).map_eq] using hpair

theorem d021634 (a r : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i)
    (i j : ι) (hij : i ≠ j) (hab : 1 < a i + a j) :
    Integrable (fun x : ι → ℝ => (x i + x j)⁻¹)
      (Measure.pi (fun l => gammaMeasure (a l) (r l))) := by
  letI (l : ι) := isProbabilityMeasure_gammaMeasure (ha l) (hr l)
  have hmap : MeasurePreserving (fun x : ι → ℝ => (x i, x j))
      (Measure.pi (fun l => gammaMeasure (a l) (r l)))
      ((gammaMeasure (a i) (r i)).prod (gammaMeasure (a j) (r j))) :=
    ⟨by fun_prop, _root_.GD.N0105.d021633 _ i j hij⟩
  exact hmap.integrable_comp_of_integrable
    (_root_.GD.N0150.d021629 (ha i) (ha j) hab (hr i) (hr j))

theorem d021635 (a r : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i)
    (i j : ι) (hij : i ≠ j) (hab : 1 < a i + a j) :
    (∫ x : ι → ℝ, (x i + x j)⁻¹ ∂Measure.pi (fun l => gammaMeasure (a l) (r l))) ≤
      max (r i) (r j) / (a i + a j - 1) := by
  letI (l : ι) := isProbabilityMeasure_gammaMeasure (ha l) (hr l)
  have h := integral_map
    (μ := Measure.pi (fun l => gammaMeasure (a l) (r l)))
    (f := _root_.GD.N0150.d021618)
    (show Measurable (fun x : ι → ℝ => (x i, x j)) by fun_prop).aemeasurable
    _root_.GD.N0150.d021620.aestronglyMeasurable
  rw [_root_.GD.N0105.d021633 _ i j hij] at h
  change (∫ x : ι → ℝ, _root_.GD.N0150.d021618 (x i, x j)
    ∂Measure.pi (fun l => gammaMeasure (a l) (r l))) ≤ _
  rw [← h]
  exact _root_.GD.N0150.d021630 (ha i) (ha j) hab (hr i) (hr j)

theorem d021636 (a r : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i)
    (i j : ι) (hij : i ≠ j) (hab : 1 < a i + a j) :
    (∫ x : ι → ℝ, (x i + x j)⁻¹ ∂Measure.pi (fun l => gammaMeasure (a l) (r l))) ≤
      (r i + r j) / (a i + a j - 1) :=
  (_root_.GD.N0105.d021635 a r ha hr i j hij hab).trans
    (div_le_div_of_nonneg_right (max_le (by linarith [hr j]) (by linarith [hr i]))
      (by linarith))

#print axioms _root_.GD.N0105.d021633
#print axioms _root_.GD.N0105.d021634
#print axioms _root_.GD.N0105.d021635
#print axioms _root_.GD.N0105.d021636

end
end GD.N0105
