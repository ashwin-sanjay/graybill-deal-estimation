import GD.Module1486





set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0421
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0877
open _root_.GD.N0021
open _root_.GD.N0023.N0257

variable {k : ℕ}


theorem d023320 (shape : Fin k → ℝ)
    (hs : ∀ i, 1 < shape i) (i j : Fin k) (hij : i ≠ j) :
    (∫ q : Fin k → ℝ, q i / q j
      ∂Measure.pi (fun l => gammaMeasure (shape l) (shape l))) =
      shape j / (shape j - 1) := by
  have hs0 (l : Fin k) : 0 < shape l := lt_trans zero_lt_one (hs l)
  let μ := fun l => gammaMeasure (shape l) (shape l)
  letI (l : Fin k) : IsProbabilityMeasure (μ l) :=
    isProbabilityMeasure_gammaMeasure (hs0 l) (hs0 l)
  have hind : IndepFun (fun q : Fin k → ℝ => q i) (fun q => (q j)⁻¹)
      (Measure.pi μ) := by
    have hb : IndepFun (fun q : Fin k → ℝ => q i) (fun q => q j)
        (Measure.pi μ) :=
      (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
    exact hb.comp measurable_id measurable_inv
  have hf := hind.integral_fun_mul_eq_mul_integral
    (measurable_pi_apply i).aestronglyMeasurable
    ((measurable_pi_apply j).inv).aestronglyMeasurable
  change (∫ q, q i * (q j)⁻¹ ∂Measure.pi μ) = _ at hf
  rw [integral_comp_eval (μ := μ) (i := i) (f := fun x : ℝ => x)
      measurable_id.aestronglyMeasurable,
    integral_comp_eval (μ := μ) (i := j) (f := fun x : ℝ => x⁻¹)
      measurable_inv.aestronglyMeasurable] at hf
  rw [_root_.GD.N0023.N0257.d021616 (hs0 i) (hs0 i),
    _root_.GD.N0023.N0257.d021615 (hs j) (hs0 j), div_self (hs0 i).ne', one_mul] at hf
  simpa only [div_eq_mul_inv, μ] using hf

theorem d023321 (shape : Fin k → ℝ)
    (hs : ∀ i, 1 < shape i) (i j : Fin k) :
    Integrable (fun q : Fin k → ℝ => q i / q j)
      (Measure.pi (fun l => gammaMeasure (shape l) (shape l))) := by
  have hs0 (l : Fin k) : 0 < shape l := lt_trans zero_lt_one (hs l)
  letI (l : Fin k) : IsProbabilityMeasure (gammaMeasure (shape l) (shape l)) :=
    isProbabilityMeasure_gammaMeasure (hs0 l) (hs0 l)
  by_cases hji : j = i
  · subst j
    apply (integrable_const (1 : ℝ)).congr
    filter_upwards [_root_.GD.N0232.N0719.N0910.d010287 hs0 hs0] with q hq
    exact (div_self (hq i).ne').symm
  · simpa only [_root_.GD.N0232.N0719.N0877.d020693, if_neg hji] using
      _root_.GD.N0232.N0719.N0877.d020695 shape shape hs0 hs0 i (fun j _ => hs j) j



theorem d023322 (shape : Fin k → ℝ)
    (hs : ∀ i, 1 < shape i) :
    (∫ q : Fin k → ℝ, _root_.GD.N0021.d023316 q
      ∂Measure.pi (fun l => gammaMeasure (shape l) (shape l))) =
      (k : ℝ) + ((k : ℝ) - 1) * ∑ j, shape j / (shape j - 1) := by
  classical
  have hs0 (l : Fin k) : 0 < shape l := lt_trans zero_lt_one (hs l)
  letI (l : Fin k) : IsProbabilityMeasure (gammaMeasure (shape l) (shape l)) :=
    isProbabilityMeasure_gammaMeasure (hs0 l) (hs0 l)
  have hentry (i j : Fin k) :
      (∫ q : Fin k → ℝ, q i / q j
        ∂Measure.pi (fun l => gammaMeasure (shape l) (shape l))) =
        if i = j then 1 else shape j / (shape j - 1) := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      calc
        _ = ∫ _ : Fin k → ℝ, (1 : ℝ)
            ∂Measure.pi (fun l => gammaMeasure (shape l) (shape l)) := by
          apply integral_congr_ae
          filter_upwards [_root_.GD.N0232.N0719.N0910.d010287 hs0 hs0] with q hq
          exact div_self (hq i).ne'
        _ = 1 := by simp
    · rw [if_neg hij]
      exact _root_.GD.N0102.N0421.d023320 shape hs i j hij
  unfold _root_.GD.N0021.d023316
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun j _ => _root_.GD.N0102.N0421.d023321 shape hs _ j),
      hentry]
    rw [Finset.sum_comm]
    have hsum (j : Fin k) :
        (∑ i : Fin k, if i = j then (1 : ℝ) else shape j / (shape j - 1)) =
          1 + ((k : ℝ) - 1) * (shape j / (shape j - 1)) := by
      calc
        _ = ∑ i : Fin k, (shape j / (shape j - 1) +
            if i = j then 1 - shape j / (shape j - 1) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> ring
        _ = _ := by simp [Finset.sum_add_distrib]; ring
    simp_rw [hsum]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  · intro i _
    exact integrable_finsetSum _ (fun j _ => _root_.GD.N0102.N0421.d023321 shape hs i j)

end
end GD.N0102.N0421

#print axioms _root_.GD.N0102.N0421.d023320
#print axioms _root_.GD.N0102.N0421.d023322
