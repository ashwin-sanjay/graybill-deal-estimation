import GD.Module0853
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus













open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1313

open _root_.GD.N0232.N0720.N1310 _root_.GD.N0232.N0720.N1309
open _root_.GD.N0232.N0720.N1091

noncomputable section

theorem d013083 {alpha : ℝ} (ha : 0 < alpha) :
    ProbabilityTheory.beta alpha 1 = 1 / alpha := by
  unfold ProbabilityTheory.beta
  rw [Real.Gamma_one, Real.Gamma_add_one ha.ne']
  field_simp [ha.ne', (Real.Gamma_pos_of_pos ha).ne']

theorem d013084 {alpha : ℝ} (ha : 0 < alpha) :
    ProbabilityTheory.beta alpha 2 = 1 / (alpha * (alpha + 1)) := by
  have h := _root_.GD.N0235.d004039 ha (by norm_num : (0 : ℝ) < 1)
  norm_num at h
  rw [h, _root_.GD.N0232.N0720.N1313.d013083 ha]
  field_simp [ha.ne', (by positivity : alpha + 1 ≠ 0)]

private theorem d013085 {alpha beta u : ℝ} (ha : 0 < alpha)
    (hb : 0 < beta) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ProbabilityTheory.beta alpha beta * betaPDFReal alpha beta u =
      u ^ (alpha - 1) * (1 - u) ^ (beta - 1) := by
  rw [betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu)]
  field_simp [(beta_pos ha hb).ne']

theorem d013086 {alpha beta : ℝ} (ha : 0 < alpha)
    (hb : 1 ≤ beta) (hb2 : beta ≤ 2) :
    ProbabilityTheory.beta alpha 2 ≤ ProbabilityTheory.beta alpha beta := by
  have hb0 : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have h := integral_mono
    ((_root_.GD.N0232.N0720.N1091.d012772 ha (by norm_num : (0 : ℝ) < 2)).const_mul
      (ProbabilityTheory.beta alpha 2))
    ((_root_.GD.N0232.N0720.N1091.d012772 ha hb0).const_mul (ProbabilityTheory.beta alpha beta))
    (fun u ↦ show ProbabilityTheory.beta alpha 2 * betaPDFReal alpha 2 u ≤
      ProbabilityTheory.beta alpha beta * betaPDFReal alpha beta u from by
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · rw [_root_.GD.N0232.N0720.N1313.d013085 ha (by norm_num) hu, _root_.GD.N0232.N0720.N1313.d013085 ha hb0 hu]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hu.2)
            (by linarith [hu.1]) (by linarith)) (Real.rpow_nonneg hu.1.le _)
      · simp only [betaPDFReal, if_neg (show ¬ (0 < u ∧ u < 1) from hu)]
        norm_num)
  simpa only [integral_const_mul, _root_.GD.N0235.d004042
    ha (by norm_num : (0 : ℝ) < 2), _root_.GD.N0235.d004042 ha hb0,
    mul_one] using h


theorem d013087 {alpha beta : ℝ} (ha : 0 < alpha)
    (hb : 1 ≤ beta) (hb2 : beta ≤ 2) (u : ℝ) :
    betaPDFReal alpha beta u ≤ (alpha + 1) * betaPDFReal alpha 1 u := by
  have hb0 : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · have hbnd := _root_.GD.N0232.N0720.N1313.d013086 ha hb hb2
    rw [_root_.GD.N0232.N0720.N1313.d013084 ha] at hbnd
    have hinv : 1 / ProbabilityTheory.beta alpha beta ≤ alpha * (alpha + 1) := by
      apply (div_le_iff₀ (beta_pos ha hb0)).2
      have := (div_le_iff₀ (by positivity : 0 < alpha * (alpha + 1))).1 hbnd
      nlinarith
    have hpow := Real.rpow_le_one (sub_pos.mpr hu.2).le
      (by linarith [hu.1] : 1 - u ≤ 1) (sub_nonneg.mpr hb)
    rw [betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu), betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu), _root_.GD.N0232.N0720.N1313.d013083 ha]
    simp only [sub_self, Real.rpow_zero, mul_one, one_div_div, div_one]
    calc
      1 / ProbabilityTheory.beta alpha beta * u ^ (alpha - 1) *
          (1 - u) ^ (beta - 1) ≤
          (alpha * (alpha + 1)) * u ^ (alpha - 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg hu.1.le _))
          hpow (Real.rpow_nonneg (sub_pos.mpr hu.2).le _)
          (mul_nonneg (mul_nonneg ha.le (by linarith)) (Real.rpow_nonneg hu.1.le _))
      _ = (alpha + 1) * (alpha * u ^ (alpha - 1)) := by ring
  · simp only [betaPDFReal, if_neg (show ¬ (0 < u ∧ u < 1) from hu)]
    norm_num

theorem d013088 (epsilon r : ℝ) : _root_.GD.N0232.N0720.N1310.d013058 epsilon r ∈ Icc (0 : ℝ) 1 := by
  have hd : 0 < 1 + Real.sqrt (epsilon * r) := by positivity
  exact ⟨div_nonneg (Real.sqrt_nonneg _) hd.le, (div_le_one hd).2 (by linarith)⟩

theorem d013089 {epsilon : ℝ} (he : 0 ≤ epsilon) :
    _root_.GD.N0232.N0720.N1309.d013069 epsilon ∈ Icc (0 : ℝ) 1 := by
  have hd : 0 < 1 + epsilon := by linarith
  exact ⟨div_nonneg he hd.le, (div_le_one hd).2 (by linarith)⟩

private theorem d013090 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ u ∈ Ioo (0 : ℝ) 1, ‖f u‖ ≤ 1) :
    Integrable (fun u ↦ betaPDFReal alpha beta u * f u) := by
  apply Integrable.mono' (_root_.GD.N0232.N0720.N1091.d012772 ha hb)
    ((measurable_betaPDFReal alpha beta).mul hf).aestronglyMeasurable
  filter_upwards with u
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0235.d004040 ha hb u)]
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · simpa using mul_le_mul_of_nonneg_left (hbound u hu)
      (_root_.GD.N0235.d004040 ha hb u)
  · simp only [betaPDFReal, if_neg (show ¬ (0 < u ∧ u < 1) from hu)]
    norm_num

private theorem d013091 {alpha beta epsilon : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : 0 ≤ epsilon) :
    Integrable (fun u ↦ betaPDFReal alpha beta u *
      (_root_.GD.N0232.N0720.N1310.d013058 epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2) := by
  apply _root_.GD.N0232.N0720.N1313.d013090 ha hb (by unfold _root_.GD.N0232.N0720.N1310.d013058 _root_.GD.N0232.N0720.N1309.d013069; fun_prop)
  intro u _
  have hg := _root_.GD.N0232.N0720.N1313.d013088 epsilon (u / (1 - u))
  have ht := _root_.GD.N0232.N0720.N1313.d013089 he
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_one_iff_abs_le_one _).2
  exact abs_le.mpr ⟨by linarith [hg.1, ht.2], by linarith [hg.2, ht.1]⟩

theorem d013092 {alpha beta epsilon : ℝ} (ha : 0 < alpha)
    (hb : 1 ≤ beta) (hb2 : beta ≤ 2) (he : 0 ≤ epsilon) :
    _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon ≤ (alpha + 1) * _root_.GD.N0232.N0720.N1309.d013070 alpha 1 epsilon := by
  have hb0 := lt_of_lt_of_le zero_lt_one hb
  unfold _root_.GD.N0232.N0720.N1309.d013070
  rw [_root_.GD.N0235.d004041 ha hb0,
    _root_.GD.N0235.d004041 ha zero_lt_one,
    ← integral_const_mul]
  apply integral_mono (_root_.GD.N0232.N0720.N1313.d013091 ha hb0 he)
    ((_root_.GD.N0232.N0720.N1313.d013091 ha zero_lt_one he).const_mul (alpha + 1))
  intro u
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (_root_.GD.N0232.N0720.N1313.d013087 ha hb hb2 u)
    (sq_nonneg (_root_.GD.N0232.N0720.N1310.d013058 epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon))

private def d013093 (d u : ℝ) : ℝ := 1 - u + d * u

private theorem d013094 {d u : ℝ} (hd : 0 < d) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1313.d013093 d u := by
  unfold _root_.GD.N0232.N0720.N1313.d013093
  by_cases hu0 : u = 0
  · simp [hu0]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hu.2)
      (mul_pos hd (lt_of_le_of_ne hu.1 (Ne.symm hu0)))


theorem d013095 {d : ℝ} (hd : 0 < d) :
    (∫ u in Ioo (0 : ℝ) 1, 1 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2) = 1 / d := by
  have hc : ContinuousOn (fun u : ℝ ↦ 1 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2) (Icc (0 : ℝ) 1) := by
    apply continuousOn_const.div
    · unfold _root_.GD.N0232.N0720.N1313.d013093; fun_prop
    · intro u hu; exact pow_ne_zero _ (_root_.GD.N0232.N0720.N1313.d013094 hd hu).ne'
  have hderiv (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v : ℝ ↦ v / _root_.GD.N0232.N0720.N1313.d013093 d v) (1 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    have hden : HasDerivAt (fun v : ℝ ↦ _root_.GD.N0232.N0720.N1313.d013093 d v) (-1 + d) u := by
      simpa only [_root_.GD.N0232.N0720.N1313.d013093, zero_sub, mul_one] using!
        ((hasDerivAt_const u (1 : ℝ)).fun_sub (hasDerivAt_id' u)).fun_add
          ((hasDerivAt_id' u).const_mul d)
    convert! (hasDerivAt_id' u).div hden (_root_.GD.N0232.N0720.N1313.d013094 hd hu').ne' using 1
    unfold _root_.GD.N0232.N0720.N1313.d013093
    congr 1
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hc.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo] at h
  simpa [_root_.GD.N0232.N0720.N1313.d013093] using h

private theorem d013096 {alpha epsilon u : ℝ} (ha : 0 < alpha)
    (he : 0 < epsilon) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) =
      (epsilon / alpha) * u / _root_.GD.N0232.N0720.N1313.d013093 (epsilon / alpha) u := by
  have hd := (_root_.GD.N0232.N0720.N1313.d013094 (div_pos he ha) ⟨hu.1.le, hu.2.le⟩).ne'
  have hp : 0 < 1 + 1 / alpha * epsilon * (u / (1 - u)) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (one_div_pos.mpr ha).le he.le)
        (div_nonneg hu.1.le (sub_pos.mpr hu.2).le))
  unfold _root_.GD.N0232.N0720.N1310.d013059 _root_.GD.N0232.N0720.N1313.d013093 at *
  field_simp [ha.ne', (sub_pos.mpr hu.2).ne', hd, hp.ne']

private theorem d013097 {alpha epsilon u : ℝ} (ha : 0 < alpha)
    (he : 0 < epsilon) (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal alpha 1 u * _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2 ≤
      alpha * (epsilon / alpha) ^ 2 / _root_.GD.N0232.N0720.N1313.d013093 (epsilon / alpha) u ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1313.d013096 ha he hu, betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu), _root_.GD.N0232.N0720.N1313.d013083 ha]
  simp only [sub_self, Real.rpow_zero, mul_one, one_div_div, div_one]
  have hp := Real.rpow_le_one hu.1.le hu.2.le (by linarith : 0 ≤ alpha + 1)
  have heq : u ^ (alpha - 1) * u ^ 2 = u ^ (alpha + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hu.1]
    congr 1
    ring
  have hd := (_root_.GD.N0232.N0720.N1313.d013094 (div_pos he ha) ⟨hu.1.le, hu.2.le⟩).ne'
  calc
    alpha * u ^ (alpha - 1) * ((epsilon / alpha) * u /
        _root_.GD.N0232.N0720.N1313.d013093 (epsilon / alpha) u) ^ 2 =
      (alpha * (epsilon / alpha) ^ 2 / _root_.GD.N0232.N0720.N1313.d013093 (epsilon / alpha) u ^ 2) *
        u ^ (alpha + 1) := by rw [← heq]; field_simp [hd]
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hp

theorem d013098 {alpha epsilon : ℝ} (ha : 0 < alpha)
    (he : 0 < epsilon) :
    (∫ u : ℝ, _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2
      ∂betaMeasure alpha 1) ≤ epsilon := by
  let d := epsilon / alpha
  have hd : 0 < d := div_pos he ha
  have hi : Integrable (fun u ↦ betaPDFReal alpha 1 u *
      _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2) := by
    apply _root_.GD.N0232.N0720.N1313.d013090 ha zero_lt_one (by unfold _root_.GD.N0232.N0720.N1310.d013059; fun_prop)
    intro u hu
    have hg := _root_.GD.N0232.N0720.N1310.d013063 (one_div_pos.mpr ha).le he.le
      (div_nonneg hu.1.le (sub_pos.mpr hu.2).le)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff₀ hg.1).2 hg.2
  have hc : ContinuousOn (fun u : ℝ ↦ alpha * d ^ 2 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2)
      (Icc (0 : ℝ) 1) := by
    apply continuousOn_const.div
    · unfold _root_.GD.N0232.N0720.N1313.d013093; fun_prop
    · intro u hu; exact pow_ne_zero _ (_root_.GD.N0232.N0720.N1313.d013094 hd hu).ne'
  have hj : IntegrableOn (fun u : ℝ ↦ alpha * d ^ 2 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2)
      (Ioo (0 : ℝ) 1) := (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [_root_.GD.N0235.d004041 ha zero_lt_one]
  have hbound := integral_mono hi ((integrable_indicator_iff measurableSet_Ioo).2 hj)
    (fun u ↦ show betaPDFReal alpha 1 u * _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2 ≤
      (Ioo (0 : ℝ) 1).indicator (fun u ↦ alpha * d ^ 2 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2) u from by
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem hu]; exact _root_.GD.N0232.N0720.N1313.d013097 ha he hu
      · rw [indicator_of_notMem hu]
        simp only [betaPDFReal, if_neg (show ¬ (0 < u ∧ u < 1) from hu)]
        norm_num)
  rw [integral_indicator measurableSet_Ioo] at hbound
  have heq : (∫ u in Ioo (0 : ℝ) 1, alpha * d ^ 2 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2) = epsilon := by
    have hpoint (u : ℝ) : alpha * d ^ 2 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2 =
        (alpha * d ^ 2) * (1 / _root_.GD.N0232.N0720.N1313.d013093 d u ^ 2) := by ring
    simp_rw [hpoint]
    rw [integral_const_mul, _root_.GD.N0232.N0720.N1313.d013095 hd]
    dsimp [d]
    field_simp [ha.ne', he.ne']
  exact hbound.trans_eq heq

theorem d013099 {alpha epsilon : ℝ} (ha : 0 < alpha) (he : 0 < epsilon) :
    _root_.GD.N0232.N0720.N1309.d013071 alpha 1 epsilon ≤ 4 * epsilon := by
  letI : IsProbabilityMeasure (betaMeasure alpha 1) := isProbabilityMeasureBeta ha zero_lt_one
  have hsq : Integrable (fun u : ℝ ↦ _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2)
      (betaMeasure alpha 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (show Measurable (fun u : ℝ ↦ _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2) from
        by unfold _root_.GD.N0232.N0720.N1310.d013059; fun_prop).aestronglyMeasurable
    filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha 1] with u hu
    have hg := _root_.GD.N0232.N0720.N1310.d013063 (one_div_pos.mpr ha).le he.le
      (div_nonneg hu.1.le (sub_pos.mpr hu.2).le)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff₀ hg.1).2 hg.2
  have herr : Integrable (fun u : ℝ ↦
      (_root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2)
      (betaMeasure alpha 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (show Measurable (fun u : ℝ ↦
        (_root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2) from
        by unfold _root_.GD.N0232.N0720.N1310.d013059 _root_.GD.N0232.N0720.N1309.d013069; fun_prop).aestronglyMeasurable
    filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha 1] with u hu
    have hg := _root_.GD.N0232.N0720.N1310.d013063 (one_div_pos.mpr ha).le he.le
      (div_nonneg hu.1.le (sub_pos.mpr hu.2).le)
    have ht := _root_.GD.N0232.N0720.N1313.d013089 he.le
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply (sq_le_one_iff_abs_le_one _).2
    exact abs_le.mpr ⟨by linarith [hg.1, ht.2], by linarith [hg.2, ht.1]⟩
  have h := integral_mono herr ((hsq.const_mul 2).add (integrable_const (2 * _root_.GD.N0232.N0720.N1309.d013069 epsilon ^ 2)))
    (fun u ↦ show (_root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2 ≤
      2 * _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2 + 2 * _root_.GD.N0232.N0720.N1309.d013069 epsilon ^ 2 from by
      nlinarith [sq_nonneg (_root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) + _root_.GD.N0232.N0720.N1309.d013069 epsilon)])
  change (∫ u, (_root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 epsilon) ^ 2
      ∂betaMeasure alpha 1) ≤
    ∫ u, 2 * _root_.GD.N0232.N0720.N1310.d013059 (1 / alpha) epsilon (u / (1 - u)) ^ 2 +
      2 * _root_.GD.N0232.N0720.N1309.d013069 epsilon ^ 2 ∂betaMeasure alpha 1 at h
  rw [integral_add (hsq.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const] at h
  simp only [probReal_univ, one_smul] at h
  have hs := _root_.GD.N0232.N0720.N1313.d013098 ha he
  have ht := _root_.GD.N0232.N0720.N1309.d013074 he.le
  change _root_.GD.N0232.N0720.N1309.d013071 alpha 1 epsilon ≤ _
  dsimp [_root_.GD.N0232.N0720.N1309.d013071] at *
  nlinarith


theorem d013100 {alpha : ℝ} (ha : 0 < alpha) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ _root_.GD.N0232.N0720.N1309.d013071 alpha 1 epsilon < _root_.GD.N0232.N0720.N1309.d013070 alpha 1 epsilon := by
  let beta : ℝ := 1 + alpha / (10 * (alpha + 1))
  have hb : 1 < beta := by
    have hp : 0 < alpha / (10 * (alpha + 1)) := div_pos ha (by positivity)
    dsimp [beta]
    linarith
  have hb2 : beta ≤ 2 := by
    dsimp [beta]
    have hd : 0 < 10 * (alpha + 1) := by positivity
    have : alpha / (10 * (alpha + 1)) ≤ 1 := (div_le_one hd).2 (by linarith)
    linarith
  let epsilon : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have he : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity
  have hlim := _root_.GD.N0232.N0720.N1309.d013079 ha hb he hepos
  have hlimit : alpha / (beta - 1) = 10 * (alpha + 1) := by
    dsimp [beta]
    field_simp [ha.ne', (by positivity : alpha + 1 ≠ 0)]
    ring
  rw [hlimit] at hlim
  have hlt : 5 * (alpha + 1) < 10 * (alpha + 1) := by linarith
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 (5 * (alpha + 1)) hlt).exists
  refine ⟨epsilon n, hepos n, ?_⟩
  have hroot := _root_.GD.N0232.N0720.N1313.d013092 ha hb.le hb2 (hepos n).le
  have hgd := _root_.GD.N0232.N0720.N1313.d013099 ha (hepos n)
  have hn' := (lt_div_iff₀ (hepos n)).1 hn
  have hroot5 : 5 * epsilon n < _root_.GD.N0232.N0720.N1309.d013070 alpha 1 (epsilon n) := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hnot)
      (show 0 ≤ alpha + 1 by linarith)
    nlinarith
  linarith [hepos n]

end
end GD.N0232.N0720.N1313

#print axioms _root_.GD.N0232.N0720.N1313.d013098
#print axioms _root_.GD.N0232.N0720.N1313.d013100
