import GD.Module0232









namespace GD
namespace N0235

open MeasureTheory ProbabilityTheory


theorem d004038
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β = α / (α + β) * beta α β := by
  rw [beta, beta, Real.Gamma_add_one (ne_of_gt hα)]
  rw [show α + 1 + β = (α + β) + 1 by ring,
    Real.Gamma_add_one (ne_of_gt (add_pos hα hβ))]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
    ne_of_gt (Real.Gamma_pos_of_pos hβ),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)),
    ne_of_gt (add_pos hα hβ)]


theorem d004039
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta α (β + 1) = β / (α + β) * beta α β := by
  rw [beta, beta, Real.Gamma_add_one (ne_of_gt hβ)]
  rw [show α + (β + 1) = (α + β) + 1 by ring,
    Real.Gamma_add_one (ne_of_gt (add_pos hα hβ))]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
    ne_of_gt (Real.Gamma_pos_of_pos hβ),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)),
    ne_of_gt (add_pos hα hβ)]


theorem d004040
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  rw [betaPDFReal]
  split_ifs with hx
  · exact mul_nonneg
      (mul_nonneg (one_div_pos.mpr (beta_pos hα hβ)).le
        (Real.rpow_nonneg hx.1.le _))
      (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)
  · exact le_rfl



theorem d004041
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℝ) :
    (∫ x, g x ∂betaMeasure α β) =
      ∫ x, betaPDFReal α β x * g x := by
  rw [betaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (f := betaPDF α β)
      ((measurable_betaPDFReal α β).ennreal_ofReal)
      (by simp [betaPDF])]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, betaPDF, ENNReal.toReal_ofReal
    (_root_.GD.N0235.d004040 hα hβ x)]


theorem d004042
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∫ x, betaPDFReal α β x) = 1 := by
  letI : IsProbabilityMeasure (betaMeasure α β) :=
    isProbabilityMeasureBeta hα hβ
  have h :=
    _root_.GD.N0235.d004041 hα hβ (fun _ => (1 : ℝ))
  simpa using h.symm



theorem d004043
    {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (i j : ℕ) :
    betaPDFReal α β x * (x ^ i * (1 - x) ^ j) =
      (beta (α + i) (β + j) / beta α β) *
        betaPDFReal (α + i) (β + j) x := by
  by_cases hx : 0 < x ∧ x < 1
  · rw [betaPDFReal, if_pos hx, betaPDFReal, if_pos hx]
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1x0 : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
    have hαi : 0 < α + (i : ℝ) := add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg i)
    have hβj : 0 < β + (j : ℝ) := add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg j)
    rw [show α + (i : ℝ) - 1 = (α - 1) + (i : ℝ) by ring,
      show β + (j : ℝ) - 1 = (β - 1) + (j : ℝ) by ring,
      Real.rpow_add_natCast hx0, Real.rpow_add_natCast h1x0]
    field_simp [ne_of_gt (beta_pos hα hβ),
      ne_of_gt (beta_pos hαi hβj)]
  · rw [betaPDFReal, if_neg hx, betaPDFReal, if_neg hx]
    ring


theorem d004044
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (i j : ℕ) :
    (∫ x : ℝ, x ^ i * (1 - x) ^ j ∂betaMeasure α β) =
      beta (α + i) (β + j) / beta α β := by
  rw [_root_.GD.N0235.d004041 hα hβ]
  have hαi : 0 < α + (i : ℝ) :=
    add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg i)
  have hβj : 0 < β + (j : ℝ) :=
    add_pos_of_pos_of_nonneg hβ (Nat.cast_nonneg j)
  calc
    (∫ x, betaPDFReal α β x * (x ^ i * (1 - x) ^ j)) =
        ∫ x, (beta (α + i) (β + j) / beta α β) *
          betaPDFReal (α + i) (β + j) x := by
            apply integral_congr_ae
            filter_upwards with x
            exact _root_.GD.N0235.d004043 hα hβ i j
    _ = (beta (α + i) (β + j) / beta α β) *
        ∫ x, betaPDFReal (α + i) (β + j) x := by
          rw [integral_const_mul]
    _ = beta (α + i) (β + j) / beta α β := by
          rw [_root_.GD.N0235.d004042 hαi hβj, mul_one]

end N0235
end GD
