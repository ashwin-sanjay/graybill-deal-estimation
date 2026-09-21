import GD.Module0658












open MeasureTheory ProbabilityTheory Set

namespace GD.N0232.N0719.N0908

noncomputable section



theorem d009686 {x : ℝ} (hx : 0 < x) :
    x ^ (-2 : ℝ) = x⁻¹ ^ 2 := by
  rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num,
    Real.rpow_neg_natCast]
  norm_num
  rfl


theorem d009687
    {a r : ℝ} (ha : 2 < a) (hr : 0 < r) :
    (∫ x, x ^ (-2 : ℝ) ∂gammaMeasure a r) =
      r ^ 2 / ((a - 1) * (a - 2)) := by
  have ha0 : 0 < a := by linarith
  rw [_root_.GD.N0232.N0719.N0954.d009351 ha0 hr]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero
    (s := Set.Ioi 0)
    (f := fun x => gammaPDFReal a r x * x ^ (-2 : ℝ))]
  · have hkernel :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi
        (a := a - 2) (r := r) (by linarith) hr
    have hpoint :
        ∀ x ∈ Set.Ioi (0 : ℝ),
          gammaPDFReal a r x * x ^ (-2 : ℝ) =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 3) * Real.exp (-(r * x))) := by
      intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x ^ (-2 : ℝ) = x ^ (a - 3) := by
        calc
          x ^ (a - 1) * x ^ (-2 : ℝ) =
              x ^ ((a - 1) + (-2 : ℝ)) := by
                rw [Real.rpow_add hxpos]
          _ = x ^ (a - 3) := by ring_nf
      calc
        gammaPDFReal a r x * x ^ (-2 : ℝ) =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x ^ (-2 : ℝ)) *
              Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ (a - 3) * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
    rw [integral_const_mul]
    have hkernel' :
        (∫ x in Set.Ioi (0 : ℝ),
            x ^ (a - 3) * Real.exp (-(r * x))) =
          (1 / r) ^ (a - 2) * Real.Gamma (a - 2) := by
      convert hkernel using 1 <;> ring
    rw [hkernel']
    have ha2 : 0 < a - 2 := by linarith
    have ha1 : 0 < a - 1 := by linarith
    have hGamma1 :
        Real.Gamma (a - 1) = (a - 2) * Real.Gamma (a - 2) := by
      convert Real.Gamma_add_one (show a - 2 ≠ 0 by linarith) using 1 <;> ring
    have hGamma2 :
        Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
      convert Real.Gamma_add_one (show a - 1 ≠ 0 by linarith) using 1 <;> ring
    rw [hGamma2, hGamma1]
    have hpow : r ^ a * (1 / r) ^ (a - 2) = r ^ 2 := by
      rw [one_div, Real.inv_rpow hr.le,
        ← Real.rpow_neg hr.le,
        ← Real.rpow_add hr]
      rw [show a + -(a - 2) = 2 by ring]
      rw [Real.rpow_two]
    rw [div_mul_eq_mul_div, ← mul_assoc, hpow]
    field_simp [ha1.ne', ha2.ne', (Real.Gamma_pos_of_pos ha2).ne']
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


theorem d009688
    {a r : ℝ} (ha : 2 < a) (hr : 0 < r) :
    (∫ x, x⁻¹ ^ 2 ∂gammaMeasure a r) =
      r ^ 2 / ((a - 1) * (a - 2)) := by
  rw [← _root_.GD.N0232.N0719.N0908.d009687 ha hr]
  apply integral_congr_ae
  have hsupport :=
    _root_.GD.N0232.N0719.N0960.d009681 (by linarith : 0 < a) hr
  filter_upwards [hsupport] with x hx
  rcases hx.eq_or_lt with rfl | hxpos
  · rw [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
    norm_num
  · exact (_root_.GD.N0232.N0719.N0908.d009686 hxpos).symm



theorem d009689 :
    (∫ x, x⁻¹ ^ 2 ∂gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) =
      25 / 3 := by
  rw [_root_.GD.N0232.N0719.N0908.d009688 (by norm_num) (by norm_num)]
  norm_num

end

end GD.N0232.N0719.N0908

#print axioms _root_.GD.N0232.N0719.N0908.d009688
#print axioms _root_.GD.N0232.N0719.N0908.d009689
