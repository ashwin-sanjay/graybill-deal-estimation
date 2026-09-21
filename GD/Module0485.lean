import GD.Module0484




set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0106.N0428.N0770
noncomputable section

theorem d007512 {A : ℝ} (hA : 0 < A) :
    (∫ t : ℝ in Ioi 0, Real.exp (-(A * t))) = 1 / A := by
  simpa using (Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1) (r := A) (by norm_num) hA)

theorem d007513 {a A : ℝ}
    (ha : 0 ≤ a) (hA : 0 < A) :
    ENNReal.ofReal (a / A) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (a * Real.exp (-(A * t))) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(A * t))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [_root_.GD.N0106.N0428.N0770.d007512 hA]
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul _) ?_]
  · rw [integral_const_mul, _root_.GD.N0106.N0428.N0770.d007512 hA]
    congr 1
    ring
  · exact ae_of_all _ fun _ => mul_nonneg ha (Real.exp_pos _).le

theorem d007514
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {a A : Ω → ℝ} (ha : Measurable a) (hA : Measurable A)
    (hapos : ∀ᵐ ω ∂μ, 0 ≤ a ω) (hpos : ∀ᵐ ω ∂μ, 0 < A ω) :
    (∫⁻ ω, ENNReal.ofReal (a ω / A ω) ∂μ) =
      ∫⁻ t : ℝ in Ioi 0,
        ∫⁻ ω, ENNReal.ofReal (a ω * Real.exp (-(A ω * t))) ∂μ := by
  calc
    _ = ∫⁻ ω, (∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (a ω * Real.exp (-(A ω * t)))) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hapos, hpos] with ω haω hω
      exact _root_.GD.N0106.N0428.N0770.d007513 haω hω
    _ = _ := by
      apply lintegral_lintegral_swap
      exact (((ha.comp measurable_fst).mul
        (((hA.comp measurable_fst).mul measurable_snd).neg.exp)).ennreal_ofReal).aemeasurable


theorem d007515 {a b A : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 < A) :
    ENNReal.ofReal ((a / A) * (b / A)) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t * a * b * Real.exp (-(A * t))) := by
  have h := _root_.GD.N0106.N0428.N0770.d007510 (Real.sqrt (a * b)) hA
  rw [div_pow, Real.sq_sqrt (mul_nonneg ha hb)] at h
  convert! h using 1 <;> congr 1
  · ring
  · funext t
    congr 1
    ring

theorem d007516
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {a b A : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) (hA : Measurable A)
    (hapos : ∀ᵐ ω ∂μ, 0 ≤ a ω) (hbpos : ∀ᵐ ω ∂μ, 0 ≤ b ω)
    (hpos : ∀ᵐ ω ∂μ, 0 < A ω) :
    (∫⁻ ω, ENNReal.ofReal ((a ω / A ω) * (b ω / A ω)) ∂μ) =
      ∫⁻ t : ℝ in Ioi 0,
        ∫⁻ ω, ENNReal.ofReal (t * a ω * b ω * Real.exp (-(A ω * t))) ∂μ := by
  calc
    _ = ∫⁻ ω, (∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (t * a ω * b ω * Real.exp (-(A ω * t)))) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hapos, hbpos, hpos] with ω haω hbω hω
      exact _root_.GD.N0106.N0428.N0770.d007515 haω hbω hω
    _ = _ := by
      apply lintegral_lintegral_swap
      exact ((((measurable_snd.mul (ha.comp measurable_fst)).mul
        (hb.comp measurable_fst)).mul
        (((hA.comp measurable_fst).mul measurable_snd).neg.exp)).ennreal_ofReal).aemeasurable

end
end GD.N0106.N0428.N0770

#print axioms _root_.GD.N0106.N0428.N0770.d007512
#print axioms _root_.GD.N0106.N0428.N0770.d007513
#print axioms _root_.GD.N0106.N0428.N0770.d007514
#print axioms _root_.GD.N0106.N0428.N0770.d007515
#print axioms _root_.GD.N0106.N0428.N0770.d007516
