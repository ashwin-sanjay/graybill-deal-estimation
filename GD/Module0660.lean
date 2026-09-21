import GD.Module0658
















open MeasureTheory ProbabilityTheory Set

namespace GD.N0232.N0719.N0909

noncomputable section


theorem d009690
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x, x ^ 2 ∂gammaMeasure a r) =
      a * (a + 1) / r ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0954.d009351
    ha hr]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero
    (s := Set.Ioi 0)
    (f := fun x ↦ gammaPDFReal a r x * x ^ 2)]
  · have hkernel :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi
        (a := a + 2) (r := r) (by linarith) hr
    have hpoint :
        ∀ x ∈ Set.Ioi (0 : ℝ),
          gammaPDFReal a r x * x ^ 2 =
            (r ^ a / Real.Gamma a) *
              (x ^ (a + 1) * Real.exp (-(r * x))) := by
      intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x ^ 2 = x ^ (a + 1) := by
        calc
          x ^ (a - 1) * x ^ 2 =
              x ^ (a - 1) * x ^ (2 : ℝ) := by
                rw [Real.rpow_two]
          _ = x ^ ((a - 1) + 2) := by
                rw [Real.rpow_add hxpos]
          _ = x ^ (a + 1) := by ring_nf
      calc
        gammaPDFReal a r x * x ^ 2 =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x ^ 2) *
              Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ (a + 1) * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
    rw [integral_const_mul]
    have hkernel' :
        (∫ x in Set.Ioi (0 : ℝ),
            x ^ (a + 1) * Real.exp (-(r * x))) =
          (1 / r) ^ (a + 2) * Real.Gamma (a + 2) := by
      convert hkernel using 1 <;> ring
    rw [hkernel']
    have hGamma1 :
        Real.Gamma (a + 1) = a * Real.Gamma a := by
      simpa using Real.Gamma_add_one ha.ne'
    have hGamma2 :
        Real.Gamma (a + 2) = (a + 1) * Real.Gamma (a + 1) := by
      convert Real.Gamma_add_one (show a + 1 ≠ 0 by linarith) using 1 <;> ring
    rw [hGamma2, hGamma1]
    have hpow : r ^ a * (1 / r) ^ (a + 2) = 1 / r ^ 2 := by
      rw [one_div, Real.inv_rpow hr.le,
        ← Real.rpow_neg hr.le,
        ← Real.rpow_add hr]
      rw [show a + -(a + 2) = -2 by ring]
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num,
        Real.rpow_neg_natCast]
      norm_num
      rfl
    rw [div_mul_eq_mul_div, ← mul_assoc, hpow]
    field_simp [(Real.Gamma_pos_of_pos ha).ne', hr.ne']
  · filter_upwards with x
    intro hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]



theorem d009691 :
    (∫ x, x ^ 2 ∂gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) = 3 := by
  rw [_root_.GD.N0232.N0719.N0909.d009690 (by norm_num) (by norm_num)]
  norm_num

end

end GD.N0232.N0719.N0909

#print axioms _root_.GD.N0232.N0719.N0909.d009690
#print axioms _root_.GD.N0232.N0719.N0909.d009691
