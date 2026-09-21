import GD.Module1664

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0033
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0213.N0527
open _root_.GD.N0213.N0488 (d028223)

variable {k : ℕ}




theorem d029137
    (shape : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i)
    (i : Fin (k + 1)) (j : Fin k) (hi : shape i = 1)
    (C : (Fin k → ℝ) → ℝ) (hCm : Measurable C)
    (hC : ∀ᵐ b ∂_root_.GD.N0033.d028239 (fun l => shape (i.succAbove l)), 0 ≤ C b)
    (e : ℝ) (he : 0 < e) :
    (∫ a, _root_.GD.N0213.N0527.d028204 e (a (i.succAbove j)) (C (fun l => a (i.succAbove l))) (a i)
      ∂_root_.GD.N0033.d028239 shape) ≤ 1 := by
  let μ : Fin (k + 1) → Measure ℝ := fun l => gammaMeasure (shape l) (shape l)
  let ν := _root_.GD.N0033.d028239 (fun l => shape (i.succAbove l))
  letI (l : Fin (k + 1)) : IsProbabilityMeasure (μ l) :=
    isProbabilityMeasure_gammaMeasure (hs l) (hs l)
  letI : IsProbabilityMeasure (gammaMeasure 1 1) := isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hμ : μ i = gammaMeasure 1 1 := by simp [μ, hi]
  have hpos : ∀ᵐ b ∂ν, ∀ l, 0 < b l := _root_.GD.N0033.d028240 _ (fun l => hs (i.succAbove l))
  have hboth : ∀ᵐ b ∂ν, 0 < b j ∧ 0 ≤ C b := by
    filter_upwards [hpos, hC] with b hb hc
    exact ⟨hb j, hc⟩
  have hint : Integrable (fun b : Fin k → ℝ => b j) ν :=
    (measurePreserving_eval (fun l => μ (i.succAbove l)) j).integrable_comp_of_integrable
      (_root_.GD.N0232.N0719.N0877.d020694 (hs _) (hs _))
  have hmean : (∫ b : Fin k → ℝ, b j ∂ν) = 1 := by
    have hh := _root_.GD.N0232.N0719.N0960.d009682 (hs (i.succAbove j)) (hs (i.succAbove j))
    change (∫ x, x ∂μ (i.succAbove j)) = _ at hh
    rw [← (measurePreserving_eval (fun l => μ (i.succAbove l)) j).map_eq] at hh
    change (∫ x, id x ∂Measure.map (fun b : Fin k → ℝ => b j) ν) = _ at hh
    rw [integral_map_of_stronglyMeasurable (μ := ν)
      (φ := fun b : Fin k → ℝ => b j) (f := id) (measurable_pi_apply j)
      stronglyMeasurable_id] at hh
    simpa only [id_eq, div_self (hs (i.succAbove j)).ne'] using hh
  let g : ℝ × (Fin k → ℝ) → ℝ := fun p => _root_.GD.N0213.N0527.d028204 e (p.2 j) (C p.2) p.1
  have hg : Integrable g ((μ i).prod ν) := by
    rw [hμ]
    apply (integrable_const (1 / e)).mono'
    · exact (show Measurable g by unfold g _root_.GD.N0213.N0527.d028204; fun_prop).aestronglyMeasurable
    · filter_upwards [
        (Measure.quasiMeasurePreserving_fst (μ := gammaMeasure 1 1) (ν := ν)).ae
          (_root_.GD.N0232.N0719.N0910.d010286 (by norm_num) (by norm_num)),
        (Measure.quasiMeasurePreserving_snd (μ := gammaMeasure 1 1) (ν := ν)).ae hboth] with p hp hb
      have hnn : 0 ≤ g p := by
        unfold g _root_.GD.N0213.N0527.d028204
        exact div_nonneg (mul_nonneg he.le (sq_nonneg _)) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact _root_.GD.N0213.N0488.d028223 _ _ _ _ he hb.1 hb.2 hp.le
  have hsplit := (measurePreserving_piFinSuccAbove μ i).integral_comp' g
  change (∫ a, _root_.GD.N0213.N0527.d028204 e (a (i.succAbove j)) (C (fun l => a (i.succAbove l))) (a i)
      ∂_root_.GD.N0033.d028239 shape) = ∫ p, g p ∂((μ i).prod ν) at hsplit
  rw [hsplit, integral_prod_symm g hg, ← hmean]
  apply integral_mono_ae hg.integral_prod_right hint
  filter_upwards [hboth] with b hb
  change (∫ x, _root_.GD.N0213.N0527.d028204 e (b j) (C b) x ∂μ i) ≤ b j
  rw [hμ]
  exact _root_.GD.N0213.N0527.d028217 e (b j) (C b) he hb.1 hb.2

end
end GD.N0033

#print axioms _root_.GD.N0033.d029137
