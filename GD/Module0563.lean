import GD.Module0439
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set ProbabilityTheory
open scoped NNReal

namespace GD.N0106.N0428.N0770.N1702
noncomputable section

theorem d008342 (b : ℝ) : Integrable (_root_.GD.N0106.N0428.N0770.N1702.d006767 b) := by
  have hg := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  apply hg.mono' (by unfold _root_.GD.N0106.N0428.N0770.N1702.d006767; fun_prop)
  filter_upwards with x
  dsimp only [_root_.GD.N0106.N0428.N0770.N1702.d006767]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h := div_nonneg (sq_nonneg b) (sq_nonneg x)
  linarith

theorem d008343 {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) = 2 * Real.sqrt (Real.pi / 2) * Real.exp (-b) := by
  have hreflect : (∫ x in Iic (0 : ℝ), _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) =
      ∫ x in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
    simpa only [_root_.GD.N0106.N0428.N0770.N1702.d006767, neg_sq, neg_zero] using (integral_comp_neg_Ioi 0 (_root_.GD.N0106.N0428.N0770.N1702.d006767 b)).symm
  rw [← integral_add_compl measurableSet_Ioi (_root_.GD.N0106.N0428.N0770.N1702.d008342 b), compl_Ioi,
    hreflect, _root_.GD.N0106.N0428.N0770.N1702.d006781 hb]
  ring

theorem d008344 (b x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (-(b ^ 2 / (2 * x ^ 2))) =
      (Real.sqrt (2 * Real.pi))⁻¹ * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006767
  congr 2
  by_cases hx : x = 0
  · simp [hx]
  · field_simp [hx]
    ring


theorem d008345 {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-(b ^ 2 / (2 * x ^ 2))) ∂gaussianReal 0 1) =
      Real.exp (-b) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp_rw [smul_eq_mul, _root_.GD.N0106.N0428.N0770.N1702.d008344]
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0770.N1702.d008343 hb]
  have hsqrt : Real.sqrt (2 * Real.pi) = 2 * Real.sqrt (Real.pi / 2) := by
    rw [show 2 * Real.pi = 4 * (Real.pi / 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hsqrt]
  have hne : Real.sqrt (Real.pi / 2) ≠ 0 := by positivity
  field_simp [hne]


theorem d008346 {b : ℝ} (hb : 0 ≤ b) :
    (∫ x : ℝ, Real.exp (-(b ^ 2 / (2 * x ^ 2))) ∂gaussianReal 0 1) =
      Real.exp (-b) := by
  rcases eq_or_lt_of_le hb with h | h
  · simp [← h]
  · exact _root_.GD.N0106.N0428.N0770.N1702.d008345 h


theorem d008347 {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, Real.exp (-(t / x ^ 2)) ∂gaussianReal 0 1) =
      Real.exp (-Real.sqrt (2 * t)) := by
  have heq : ∀ x : ℝ, t / x ^ 2 = (Real.sqrt (2 * t)) ^ 2 / (2 * x ^ 2) := by
    intro x
    rw [Real.sq_sqrt (by positivity)]
    exact (mul_div_mul_left t (x ^ 2) (by norm_num : (2 : ℝ) ≠ 0)).symm
  simp_rw [heq]
  exact _root_.GD.N0106.N0428.N0770.N1702.d008346 (Real.sqrt_nonneg _)

end
end GD.N0106.N0428.N0770.N1702

#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008342
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008343
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008344
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008345
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008346
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008347
