import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0106.N0428.N0770
noncomputable section


theorem d007509 {A : ℝ} (hA : 0 < A) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-(A * t))) = (1 / A) ^ 2 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, show Real.Gamma 2 = 1 by norm_num, mul_one] using
    (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := A) (by norm_num) hA)



theorem d007510 (a : ℝ) {A : ℝ} (hA : 0 < A) :
    ENNReal.ofReal ((a / A) ^ 2) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t * a ^ 2 * Real.exp (-(A * t))) := by
  have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-(A * t))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [_root_.GD.N0106.N0428.N0770.d007509 hA]
    positivity
  simp_rw [show ∀ t : ℝ, t * a ^ 2 * Real.exp (-(A * t)) =
    a ^ 2 * (t * Real.exp (-(A * t))) by intro t; ring]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) ?_]
  · rw [integral_const_mul, _root_.GD.N0106.N0428.N0770.d007509 hA]
    congr 1
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (sq_nonneg a) (mul_nonneg (le_of_lt ht) (Real.exp_pos _).le)




theorem d007511
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {a A : Ω → ℝ} (ha : Measurable a) (hA : Measurable A)
    (hpos : ∀ᵐ ω ∂μ, 0 < A ω) :
    (∫⁻ ω, ENNReal.ofReal ((a ω / A ω) ^ 2) ∂μ) =
      ∫⁻ t : ℝ in Ioi 0,
        ∫⁻ ω, ENNReal.ofReal (t * a ω ^ 2 * Real.exp (-(A ω * t))) ∂μ := by
  calc
    _ = ∫⁻ ω, (∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (t * a ω ^ 2 * Real.exp (-(A ω * t)))) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with ω hω
      exact _root_.GD.N0106.N0428.N0770.d007510 (a ω) hω
    _ = _ := by
      apply lintegral_lintegral_swap
      exact (((measurable_snd.mul ((ha.comp measurable_fst).pow_const 2)).mul
        (((hA.comp measurable_fst).mul measurable_snd).neg.exp)).ennreal_ofReal).aemeasurable

end
end GD.N0106.N0428.N0770

#print axioms _root_.GD.N0106.N0428.N0770.d007509
#print axioms _root_.GD.N0106.N0428.N0770.d007510
#print axioms _root_.GD.N0106.N0428.N0770.d007511
