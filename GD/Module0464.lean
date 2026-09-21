import GD.Module0463

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0213.N0489
noncomputable section
open _root_.GD.N0213.N0495

theorem d007193 (r : ℝ) :
    Monotone (fun n : ℕ => _root_.GD.N0213.N0495.d007174 ((n : ℝ) + 1) r) := by
  intro m n hmn
  unfold _root_.GD.N0213.N0495.d007174
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff, div_pow, div_pow]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  have hcast : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  nlinarith [sq_nonneg (n : ℝ), sq_nonneg (m : ℝ)]

theorem d007194 (r : ℝ) :
    Monotone (fun n : ℕ => ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 ((n : ℝ) + 1) r ^ 2)) := by
  intro m n hmn
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (_root_.GD.N0213.N0495.d007176 _ _).le (_root_.GD.N0213.N0489.d007193 r hmn) 2

theorem d007195 (r : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 ((n : ℝ) + 1) r ^ 2)) atTop (𝓝 1) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((_root_.GD.N0213.N0495.d007192 r).pow 2)
  simpa only [Function.comp_def, one_pow, ENNReal.ofReal_one] using h

theorem d007196 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → ℝ) (hR : Measurable R) (s : Set Ω) :
    Tendsto (fun n : ℕ => ∫⁻ x in s,
      ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 ((n : ℝ) + 1) (R x) ^ 2) ∂μ) atTop (𝓝 (μ s)) := by
  have h := lintegral_tendsto_of_tendsto_of_monotone
    (μ := μ.restrict s) (F := fun _ => (1 : ℝ≥0∞))
    (fun n => (show Measurable (fun x => ENNReal.ofReal
      (_root_.GD.N0213.N0495.d007174 ((n : ℝ) + 1) (R x) ^ 2)) from by dsimp only [_root_.GD.N0213.N0495.d007174]; fun_prop).aemeasurable)
    (ae_of_all _ (fun x => _root_.GD.N0213.N0489.d007194 (R x)))
    (ae_of_all _ (fun x => _root_.GD.N0213.N0489.d007195 (R x)))
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using h

end
end GD.N0213.N0489

#print axioms _root_.GD.N0213.N0489.d007194
#print axioms _root_.GD.N0213.N0489.d007196
