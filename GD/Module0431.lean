import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0042
noncomputable section

def d006724 (a r : ℝ) : ℝ := r ^ a / (a * Real.Gamma a)

theorem d006725 {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 < _root_.GD.N0042.d006724 a r :=
  div_pos (Real.rpow_pos_of_pos hr _) (mul_pos ha (Real.Gamma_pos_of_pos ha))

theorem d006726 {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    (∫⁻ x in Icc (0 : ℝ) u, ENNReal.ofReal (x ^ (a - 1))) =
      ENNReal.ofReal (u ^ a / a) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (a - 1)) (Icc 0 u) volume := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mp
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hn : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) u), 0 ≤ x ^ (a - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact Real.rpow_nonneg hx.1 _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hu,
    integral_rpow (Or.inl (by linarith : -1 < a - 1))]
  simp only [sub_add_cancel, Real.zero_rpow ha.ne', sub_zero]


theorem d006727 {a r u : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hu : 0 ≤ u) :
    gammaMeasure a r (Iic u) ≤ ENNReal.ofReal (_root_.GD.N0042.d006724 a r * u ^ a) := by
  let A : ℝ := r ^ a / Real.Gamma a
  have hA : 0 ≤ A := (div_pos (Real.rpow_pos_of_pos hr _) (Real.Gamma_pos_of_pos ha)).le
  have hdom : (Iic u).indicator (gammaPDF a r) ≤
      (Icc 0 u).indicator (fun x : ℝ => ENNReal.ofReal (A * x ^ (a - 1))) := by
    intro x
    by_cases hxu : x ≤ u
    · by_cases hx : 0 ≤ x
      · simp only [indicator_of_mem (show x ∈ Iic u from hxu), indicator_of_mem (show x ∈ Icc (0 : ℝ) u from ⟨hx, hxu⟩)]
        change ENNReal.ofReal (gammaPDFReal a r x) ≤ ENNReal.ofReal (A * x ^ (a - 1))
        apply ENNReal.ofReal_le_ofReal
        simp only [gammaPDFReal, if_pos hx]
        exact mul_le_of_le_one_right (mul_nonneg hA (Real.rpow_nonneg hx _))
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le hx)))
      · simp [indicator_of_mem (show x ∈ Iic u from hxu), gammaPDF, gammaPDFReal, hx,
          show x ∉ Icc (0 : ℝ) u from fun h => hx h.1]
    · simp [indicator_of_notMem (show x ∉ Iic u from hxu),
        show x ∉ Icc (0 : ℝ) u from fun h => hxu h.2]
  have hle := lintegral_mono (μ := volume) hdom
  rw [lintegral_indicator measurableSet_Iic, lintegral_indicator measurableSet_Icc] at hle
  unfold gammaMeasure
  rw [withDensity_apply _ measurableSet_Iic]
  apply hle.trans_eq
  simp_rw [ENNReal.ofReal_mul hA]
  rw [lintegral_const_mul _ (by fun_prop), _root_.GD.N0042.d006726 ha hu,
    ← ENNReal.ofReal_mul hA]
  congr 1
  dsimp [A, _root_.GD.N0042.d006724]
  ring

theorem d006728 {a u : ℝ}
    (ha : 0 < a) (hu : 0 ≤ u) :
    gammaMeasure a a (Iic u) ≤ ENNReal.ofReal (_root_.GD.N0042.d006724 a a * u ^ a) :=
  _root_.GD.N0042.d006727 ha ha hu

end
end GD.N0042

#print axioms _root_.GD.N0042.d006725
#print axioms _root_.GD.N0042.d006726
#print axioms _root_.GD.N0042.d006727
#print axioms _root_.GD.N0042.d006728
