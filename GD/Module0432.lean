import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace GD.N0043
noncomputable section


theorem d006729 {a r M : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hM : 1 ≤ M) (x : ℝ) :
    M ^ (-a) * gammaPDFReal a r x ≤ gammaPDFReal a (r / M) x := by
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  by_cases hx : 0 ≤ x
  · have hrate : r / M ≤ r := (div_le_self hr.le hM)
    have hexp : Real.exp (-(r * x)) ≤ Real.exp (-(r / M * x)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hrate hx))
    have heq : (r / M) ^ a = M ^ (-a) * r ^ a := by
      rw [Real.div_rpow hr.le hMp.le, Real.rpow_neg hMp.le]
      ring
    simp only [gammaPDFReal, if_pos hx, heq]
    calc
      M ^ (-a) * (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
          (M ^ (-a) * r ^ a / Real.Gamma a * x ^ (a - 1)) * Real.exp (-(r * x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by
        exact mul_nonneg (div_nonneg (mul_nonneg (Real.rpow_nonneg hMp.le _)
          (Real.rpow_nonneg hr.le _)) (Real.Gamma_pos_of_pos ha).le)
          (Real.rpow_nonneg hx _))
  · simp [gammaPDFReal, hx]

theorem d006730 {a r M : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hM : 1 ≤ M) :
    ENNReal.ofReal (M ^ (-a)) • gammaMeasure a r ≤ gammaMeasure a (r / M) := by
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  unfold gammaMeasure gammaPDF
  rw [← withDensity_smul _ ((measurable_gammaPDFReal a r).ennreal_ofReal)]
  apply withDensity_mono (ae_of_all _ fun x => ?_)
  change ENNReal.ofReal (M ^ (-a)) * ENNReal.ofReal (gammaPDFReal a r x) ≤
    ENNReal.ofReal (gammaPDFReal a (r / M) x)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hMp.le _)]
  exact ENNReal.ofReal_le_ofReal (_root_.GD.N0043.d006729 ha hr hM x)


theorem d006731 {a r M : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hM : 1 ≤ M) (f : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (M ^ (1 - a)) * (∫⁻ x, f x ∂gammaMeasure a r) ≤
      ENNReal.ofReal M * (∫⁻ x, f x ∂gammaMeasure a (r / M)) := by
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have h := lintegral_mono' (f := f) (_root_.GD.N0043.d006730 ha hr hM) le_rfl
  rw [lintegral_smul_measure] at h
  have hpow : M ^ (1 - a) = M * M ^ (-a) := by
    rw [sub_eq_add_neg, Real.rpow_add hMp, Real.rpow_one]
  rw [hpow, ENNReal.ofReal_mul hMp.le, mul_assoc]
  exact mul_le_mul_right h _

end
end GD.N0043

#print axioms _root_.GD.N0043.d006729
#print axioms _root_.GD.N0043.d006730
#print axioms _root_.GD.N0043.d006731
