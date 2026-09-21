import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper












set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1605
noncomputable section

open MeasureTheory Set Complex Filter Topology
open scoped Topology ComplexConjugate

def d007560 (z : ℂ) : ℂ := conj z / (‖z‖ : ℂ)

theorem d007561 : Measurable _root_.GD.N0106.N0428.N0765.N1605.d007560 := by
  change Measurable (fun z : ℂ => conj z / (‖z‖ : ℂ))
  exact Complex.continuous_conj.measurable.div
    (Complex.continuous_ofReal.measurable.comp continuous_norm.measurable)

theorem d007562 (z : ℂ) : ‖_root_.GD.N0106.N0428.N0765.N1605.d007560 z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [_root_.GD.N0106.N0428.N0765.N1605.d007560, hz]
  · calc
      ‖_root_.GD.N0106.N0428.N0765.N1605.d007560 z‖ = 1 := by
        rw [_root_.GD.N0106.N0428.N0765.N1605.d007560, norm_div, Complex.norm_conj,
          Complex.norm_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz)]
      _ ≤ 1 := le_rfl

theorem d007563 (z : ℂ) : _root_.GD.N0106.N0428.N0765.N1605.d007560 z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [_root_.GD.N0106.N0428.N0765.N1605.d007560, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    rw [_root_.GD.N0106.N0428.N0765.N1605.d007560, div_mul_eq_mul_div₀, Complex.conj_mul', pow_two,
      mul_div_cancel_right₀ _ hn]



theorem d007564 (g : ℝ → ℂ) (T : ℝ) :
    (∫ t : ℝ in Icc (-T) T, _root_.GD.N0106.N0428.N0765.N1605.d007560 (g t) * g t) =
      ((∫ t : ℝ in Icc (-T) T, ‖g t‖) : ℂ) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1605.d007563] using
    (integral_complex_ofReal (μ := volume.restrict (Icc (-T) T))
      (f := fun t : ℝ => ‖g t‖))

theorem d007565 (g : ℝ → ℂ) (T : ℝ) :
    ‖∫ t : ℝ in Icc (-T) T, _root_.GD.N0106.N0428.N0765.N1605.d007560 (g t) * g t‖ =
      ∫ t : ℝ in Icc (-T) T, ‖g t‖ := by
  rw [_root_.GD.N0106.N0428.N0765.N1605.d007564, integral_complex_ofReal]
  have hnonneg : 0 ≤ ∫ t : ℝ in Icc (-T) T, ‖g t‖ :=
    integral_nonneg (fun t : ℝ => norm_nonneg (g t))
  exact Complex.norm_of_nonneg hnonneg



theorem d007566 {g : ℝ → ℂ} {C : ℝ}
    (hg : Continuous g)
    (hbound : ∀ T : ℝ, 0 ≤ T → (∫ t : ℝ in Icc (-T) T, ‖g t‖) ≤ C) :
    Integrable g ∧ (∫ t : ℝ, ‖g t‖) ≤ C := by
  have hcover : AECover volume (atTop : Filter ℝ) (fun T : ℝ => Icc (-T) T) :=
    aecover_Icc tendsto_neg_atTop_atBot tendsto_id
  have hevent : ∀ᶠ T : ℝ in atTop, (∫ t : ℝ in Icc (-T) T, ‖g t‖) ≤ C :=
    eventually_atTop.2 ⟨0, fun T hT => hbound T hT⟩
  have hi : Integrable g := hcover.integrable_of_integral_norm_bounded C
    (fun _ => hg.integrableOn_Icc) hevent
  exact ⟨hi, le_of_tendsto (hcover.integral_tendsto_of_countably_generated hi.norm) hevent⟩

end
end GD.N0106.N0428.N0765.N1605

#print axioms _root_.GD.N0106.N0428.N0765.N1605.d007561
#print axioms _root_.GD.N0106.N0428.N0765.N1605.d007563
#print axioms _root_.GD.N0106.N0428.N0765.N1605.d007566
