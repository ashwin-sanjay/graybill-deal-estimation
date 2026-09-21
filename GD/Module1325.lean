import GD.Module1324
import GD.Module0658
import Mathlib.MeasureTheory.Integral.Prod





set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GD.N0023.N0257
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0876
open _root_.GD.N0232.N0719.N0877


theorem d021614
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    (∫ x, x ^ (-1 : ℝ) ∂gammaMeasure a r) = r / (a - 1) := by
  have ha0 : 0 < a := by linarith
  rw [_root_.GD.N0232.N0719.N0954.d009351 ha0 hr]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero
    (s := Set.Ioi 0) (f := fun x => gammaPDFReal a r x * x ^ (-1 : ℝ))]
  · have hkernel := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := a - 1) (r := r) (by linarith) hr
    have hpoint : ∀ x ∈ Set.Ioi (0 : ℝ),
        gammaPDFReal a r x * x ^ (-1 : ℝ) =
          (r ^ a / Real.Gamma a) * (x ^ (a - 2) * Real.exp (-(r * x))) := by
      intro x hx
      have hxpos : 0 < x := hx
      have hxpow : x ^ (a - 1) * x ^ (-1 : ℝ) = x ^ (a - 2) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      calc
        gammaPDFReal a r x * x ^ (-1 : ℝ) =
            (r ^ a / Real.Gamma a) * (x ^ (a - 1) * x ^ (-1 : ℝ)) * Real.exp (-(r * x)) := by
          simp only [gammaPDFReal, if_pos hxpos.le]
          ring
        _ = _ := by rw [hxpow]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul]
    have hkernel' : (∫ x in Set.Ioi (0 : ℝ), x ^ (a - 2) * Real.exp (-(r * x))) =
        (1 / r) ^ (a - 1) * Real.Gamma (a - 1) := by
      convert hkernel using 1
      ring
    rw [hkernel']
    have ha1 : 0 < a - 1 := by linarith
    have hGamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
      convert Real.Gamma_add_one ha1.ne' using 1
      ring
    rw [hGamma]
    have hpow : r ^ a * (1 / r) ^ (a - 1) = r := by
      rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
      rw [show a + -(a - 1) = 1 by ring, Real.rpow_one]
    rw [div_mul_eq_mul_div, ← mul_assoc, hpow]
    field_simp [ha1.ne', (Real.Gamma_pos_of_pos ha1).ne']
  · filter_upwards with x
    intro hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · subst x
      have hexp : a - 1 ≠ 0 := by linarith
      rw [gammaPDFReal, if_pos le_rfl, Real.zero_rpow hexp]
      ring
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]


theorem d021615
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    (∫ x, x⁻¹ ∂gammaMeasure a r) = r / (a - 1) := by
  simpa only [Real.rpow_neg_one] using _root_.GD.N0023.N0257.d021614 ha hr


theorem d021616
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x, x ∂gammaMeasure a r) = a / r := by
  rw [_root_.GD.N0232.N0719.N0954.d009351 ha hr]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero
    (s := Set.Ioi 0) (f := fun x => gammaPDFReal a r x * x)]
  · have hkernel := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := a + 1) (r := r) (by linarith) hr
    have hpoint : ∀ x ∈ Set.Ioi (0 : ℝ),
        gammaPDFReal a r x * x =
          (r ^ a / Real.Gamma a) * (x ^ a * Real.exp (-(r * x))) := by
      intro x hx
      have hxpos : 0 < x := hx
      have hxpow : x ^ (a - 1) * x = x ^ a := by
        calc
          x ^ (a - 1) * x = x ^ (a - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((a - 1) + 1) := (Real.rpow_add hxpos _ _).symm
          _ = x ^ a := by congr 1; ring
      calc
        gammaPDFReal a r x * x =
            (r ^ a / Real.Gamma a) * (x ^ (a - 1) * x) * Real.exp (-(r * x)) := by
          simp only [gammaPDFReal, if_pos hxpos.le]
          ring
        _ = _ := by rw [hxpow]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul]
    have hkernel' : (∫ x in Set.Ioi (0 : ℝ), x ^ a * Real.exp (-(r * x))) =
        (1 / r) ^ (a + 1) * Real.Gamma (a + 1) := by
      convert hkernel using 1
      ring
    rw [hkernel', Real.Gamma_add_one ha.ne']
    have hpow : r ^ a * (1 / r) ^ (a + 1) = 1 / r := by
      rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
      rw [show a + -(a + 1) = -1 by ring, Real.rpow_neg_one]
    rw [div_mul_eq_mul_div, ← mul_assoc, hpow]
    field_simp [(Real.Gamma_pos_of_pos ha).ne', hr.ne']
  · filter_upwards with x
    intro hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]



theorem d021617 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    (∫ q : ℝ × ℝ, (q.2 / q.1 + q.1 / q.2 - 2) / 4
      ∂(gammaMeasure a a).prod (gammaMeasure b b)) =
      (1 / (a - 1) + 1 / (b - 1)) / 4 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  letI := isProbabilityMeasure_gammaMeasure ha0 ha0
  letI := isProbabilityMeasure_gammaMeasure hb0 hb0
  have hi : Integrable (fun q : ℝ × ℝ => q.2 / q.1)
      ((gammaMeasure a a).prod (gammaMeasure b b)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (_root_.GD.N0232.N0719.N0876.d020682 ha ha0).mul_prod (_root_.GD.N0232.N0719.N0877.d020694 hb0 hb0)
  have hj : Integrable (fun q : ℝ × ℝ => q.1 / q.2)
      ((gammaMeasure a a).prod (gammaMeasure b b)) := by
    simpa only [div_eq_mul_inv] using
      (_root_.GD.N0232.N0719.N0877.d020694 ha0 ha0).mul_prod (_root_.GD.N0232.N0719.N0876.d020682 hb hb0)
  have hfirst : (∫ q : ℝ × ℝ, q.2 / q.1 ∂(gammaMeasure a a).prod (gammaMeasure b b)) =
      a / (a - 1) := by
    have hprod := integral_prod_mul (μ := gammaMeasure a a) (ν := gammaMeasure b b)
      (fun x : ℝ => x⁻¹) (fun y : ℝ => y)
    rw [_root_.GD.N0023.N0257.d021615 ha ha0, _root_.GD.N0023.N0257.d021616 hb0 hb0,
      div_self hb0.ne', mul_one] at hprod
    simpa only [div_eq_mul_inv, mul_comm] using hprod
  have hsecond : (∫ q : ℝ × ℝ, q.1 / q.2 ∂(gammaMeasure a a).prod (gammaMeasure b b)) =
      b / (b - 1) := by
    have hprod := integral_prod_mul (μ := gammaMeasure a a) (ν := gammaMeasure b b)
      (fun x : ℝ => x) (fun y : ℝ => y⁻¹)
    rw [_root_.GD.N0023.N0257.d021616 ha0 ha0, _root_.GD.N0023.N0257.d021615 hb hb0,
      div_self ha0.ne', one_mul] at hprod
    simpa only [div_eq_mul_inv] using hprod
  have hadd : Integrable (fun q : ℝ × ℝ => q.2 / q.1 + q.1 / q.2)
      ((gammaMeasure a a).prod (gammaMeasure b b)) := hi.add hj
  rw [integral_div, integral_sub hadd (integrable_const 2),
    integral_add hi hj, hfirst, hsecond]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have ha1 : a - 1 ≠ 0 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  field_simp [ha1, hb1]
  ring

end
end GD.N0023.N0257

#print axioms _root_.GD.N0023.N0257.d021615
#print axioms _root_.GD.N0023.N0257.d021616
#print axioms _root_.GD.N0023.N0257.d021617
