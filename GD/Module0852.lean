import GD.Module0837















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1310

noncomputable section

def d013058 (epsilon r : ℝ) : ℝ :=
  Real.sqrt (epsilon * r) / (1 + Real.sqrt (epsilon * r))

def d013059 (k epsilon r : ℝ) : ℝ :=
  k * epsilon * r / (1 + k * epsilon * r)

theorem d013060 {epsilon r : ℝ} (he : 0 < epsilon) (hr : 0 ≤ r) :
    _root_.GD.N0232.N0720.N1310.d013058 epsilon r ^ 2 / epsilon =
      r / (1 + Real.sqrt (epsilon * r)) ^ 2 := by
  have hd : 1 + Real.sqrt (epsilon * r) ≠ 0 := ne_of_gt (by positivity)
  unfold _root_.GD.N0232.N0720.N1310.d013058
  rw [div_pow, Real.sq_sqrt (mul_nonneg he.le hr)]
  field_simp [he.ne', hd]

theorem d013061 {epsilon r : ℝ} (he : 0 < epsilon) (hr : 0 ≤ r) :
    _root_.GD.N0232.N0720.N1310.d013058 epsilon r ^ 2 / epsilon ≤ r := by
  rw [_root_.GD.N0232.N0720.N1310.d013060 he hr]
  apply div_le_self hr
  nlinarith [Real.sqrt_nonneg (epsilon * r)]

theorem d013062 {k epsilon r : ℝ} (hk : 0 ≤ k)
    (he : 0 < epsilon) (hr : 0 ≤ r) :
    _root_.GD.N0232.N0720.N1310.d013059 k epsilon r ^ 2 / epsilon =
      k ^ 2 * epsilon * r ^ 2 / (1 + k * epsilon * r) ^ 2 := by
  have hd : 1 + k * epsilon * r ≠ 0 := ne_of_gt (by positivity)
  unfold _root_.GD.N0232.N0720.N1310.d013059
  field_simp [he.ne', hd]

theorem d013063 {k epsilon r : ℝ} (hk : 0 ≤ k)
    (he : 0 ≤ epsilon) (hr : 0 ≤ r) : _root_.GD.N0232.N0720.N1310.d013059 k epsilon r ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 ≤ k * epsilon * r := mul_nonneg (mul_nonneg hk he) hr
  have hd : 0 < 1 + k * epsilon * r := by linarith
  constructor
  · exact div_nonneg hp hd.le
  · exact (div_le_one hd).2 (by linarith)

theorem d013064 {k epsilon r : ℝ} (hk : 0 ≤ k)
    (he : 0 < epsilon) (hr : 0 ≤ r) :
    _root_.GD.N0232.N0720.N1310.d013059 k epsilon r ^ 2 / epsilon ≤ k * r := by
  have hg := _root_.GD.N0232.N0720.N1310.d013063 hk he.le hr
  have hs : _root_.GD.N0232.N0720.N1310.d013059 k epsilon r ^ 2 ≤ _root_.GD.N0232.N0720.N1310.d013059 k epsilon r := by
    nlinarith [mul_nonneg hg.1 (sub_nonneg.mpr hg.2)]
  have hupper : _root_.GD.N0232.N0720.N1310.d013059 k epsilon r ≤ k * epsilon * r := by
    exact div_le_self (mul_nonneg (mul_nonneg hk he.le) hr)
      (by linarith [mul_nonneg (mul_nonneg hk he.le) hr])
  apply (div_le_iff₀ he).2
  nlinarith [hs.trans hupper]


theorem d013065 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta) :
    ProbabilityTheory.beta (alpha + 1) (beta - 1) / ProbabilityTheory.beta alpha beta =
      alpha / (beta - 1) := by
  have hb0 : 0 < beta - 1 := sub_pos.mpr hb
  have hright : ProbabilityTheory.beta alpha beta =
      (beta - 1) / (alpha + (beta - 1)) * ProbabilityTheory.beta alpha (beta - 1) := by
    simpa only [sub_add_cancel] using _root_.GD.N0235.d004039 ha hb0
  rw [_root_.GD.N0235.d004038 ha hb0, hright]
  field_simp [(beta_pos ha hb0).ne', hb0.ne', (add_pos ha hb0).ne']



theorem d013066 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta)
    (u : ℝ) :
    betaPDFReal alpha beta u * (u / (1 - u)) =
      (alpha / (beta - 1)) * betaPDFReal (alpha + 1) (beta - 1) u := by
  have hb0 : 0 < beta := lt_trans zero_lt_one hb
  have hbm : 0 < beta - 1 := sub_pos.mpr hb
  by_cases hu : 0 < u ∧ u < 1
  · have hu0 : u ≠ 0 := hu.1.ne'
    have hu1 : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
    rw [← _root_.GD.N0232.N0720.N1310.d013065 ha hb]
    rw [betaPDFReal, if_pos hu, betaPDFReal, if_pos hu]
    simp only [add_sub_cancel_right]
    rw [Real.rpow_sub_one hu0 alpha, Real.rpow_sub_one hu1 (beta - 1)]
    field_simp [hu0, hu1, (beta_pos ha hb0).ne',
      (beta_pos (add_pos ha zero_lt_one) hbm).ne']
  · simp [betaPDFReal, hu]


theorem d013067 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta) :
    Integrable (fun u : ℝ ↦ u / (1 - u)) (betaMeasure alpha beta) := by
  have hb0 : 0 < beta := lt_trans zero_lt_one hb
  have hd :=
    (_root_.GD.N0232.N0720.N1091.d012772
      (add_pos ha zero_lt_one) (sub_pos.mpr hb)).const_mul (alpha / (beta - 1))
  have hprod : Integrable (fun u : ℝ ↦ betaPDFReal alpha beta u * (u / (1 - u))) := by
    apply hd.congr
    exact ae_of_all _ fun u ↦ (_root_.GD.N0232.N0720.N1310.d013066 ha hb u).symm
  unfold betaMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (μ := volume) (E := ℝ) (g := fun u : ℝ ↦ u / (1 - u))
    ((measurable_betaPDFReal alpha beta).ennreal_ofReal) (by simp)).2
  simpa only [betaPDF, ENNReal.toReal_ofReal (_root_.GD.N0235.d004040 ha hb0 _),
    smul_eq_mul] using hprod



theorem d013068 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 1 < beta) :
    (∫ u : ℝ, u / (1 - u) ∂betaMeasure alpha beta) = alpha / (beta - 1) := by
  rw [_root_.GD.N0235.d004041
    ha (lt_trans zero_lt_one hb)]
  simp_rw [_root_.GD.N0232.N0720.N1310.d013066 ha hb]
  rw [integral_const_mul, _root_.GD.N0235.d004042
    (add_pos ha zero_lt_one) (sub_pos.mpr hb), mul_one]

end
end GD.N0232.N0720.N1310

#print axioms _root_.GD.N0232.N0720.N1310.d013061
#print axioms _root_.GD.N0232.N0720.N1310.d013064
#print axioms _root_.GD.N0232.N0720.N1310.d013067
#print axioms _root_.GD.N0232.N0720.N1310.d013068
