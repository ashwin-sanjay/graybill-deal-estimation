import GD.Module0837
import GD.Module0274
import Mathlib.MeasureTheory.Integral.DominatedConvergence























open MeasureTheory ProbabilityTheory Filter Set

namespace GD
namespace N0232
namespace N0720
namespace N1092

noncomputable section

open _root_.GD.N0232.N0720.N1091



def d013024 (u : ℝ) : ℝ :=
  u ^ (-2 : ℝ) * (1 - u) ^ 2

theorem d013025 : Measurable _root_.GD.N0232.N0720.N1092.d013024 := by
  unfold _root_.GD.N0232.N0720.N1092.d013024
  fun_prop

theorem d013026 {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ _root_.GD.N0232.N0720.N1092.d013024 u := by
  exact mul_nonneg (Real.rpow_nonneg hu _) (sq_nonneg _)



theorem d013027
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1092.d013024 u = ((1 - u) / u) ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1092.d013024
  rw [Real.rpow_neg hu.1.le, Real.rpow_two]
  field_simp [hu.1.ne']



theorem d013028
    {alpha beta u : ℝ}
    (halpha : 2 < alpha) (hbeta : 0 < beta) :
    betaPDFReal alpha beta u * _root_.GD.N0232.N0720.N1092.d013024 u =
      (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
        ProbabilityTheory.beta alpha beta) *
          betaPDFReal (alpha - 2) (beta + 2) u := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have halphaShift : 0 < alpha - 2 := sub_pos.mpr halpha
  have hbetaShift : 0 < beta + 2 := by linarith
  by_cases hu : 0 < u ∧ u < 1
  · have h1u : 0 < 1 - u := sub_pos.mpr hu.2
    rw [betaPDFReal, if_pos hu, betaPDFReal, if_pos hu]
    unfold _root_.GD.N0232.N0720.N1092.d013024
    have hexponentLeft : alpha - 1 + (-2 : ℝ) = alpha - 2 - 1 := by ring
    have hexponentRight : beta - 1 + (2 : ℝ) = beta + 2 - 1 := by ring
    calc
      1 / ProbabilityTheory.beta alpha beta * u ^ (alpha - 1) *
            (1 - u) ^ (beta - 1) * (u ^ (-2 : ℝ) * (1 - u) ^ 2) =
          1 / ProbabilityTheory.beta alpha beta *
            (u ^ (alpha - 1) * u ^ (-2 : ℝ)) *
              ((1 - u) ^ (beta - 1) * (1 - u) ^ (2 : ℝ)) := by
        rw [Real.rpow_two]
        ring
      _ = 1 / ProbabilityTheory.beta alpha beta *
            u ^ (alpha - 2 - 1) * (1 - u) ^ (beta + 2 - 1) := by
        rw [← Real.rpow_add hu.1, ← Real.rpow_add h1u,
          hexponentLeft, hexponentRight]
      _ = (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
            ProbabilityTheory.beta alpha beta) *
              (1 / ProbabilityTheory.beta (alpha - 2) (beta + 2) *
                u ^ (alpha - 2 - 1) * (1 - u) ^ (beta + 2 - 1)) := by
        field_simp [ne_of_gt (ProbabilityTheory.beta_pos halpha0 hbeta),
          ne_of_gt (ProbabilityTheory.beta_pos halphaShift hbetaShift)]
  · rw [betaPDFReal, if_neg hu, betaPDFReal, if_neg hu]
    ring



theorem d013029
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta) :
    Integrable _root_.GD.N0232.N0720.N1092.d013024 (betaMeasure alpha beta) := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have halphaShift : 0 < alpha - 2 := sub_pos.mpr halpha
  have hbetaShift : 0 < beta + 2 := by linarith
  change Integrable _root_.GD.N0232.N0720.N1092.d013024
    (volume.withDensity (fun u => ENNReal.ofReal (betaPDFReal alpha beta u)))
  rw [integrable_withDensity_iff
    ((measurable_betaPDFReal alpha beta).ennreal_ofReal) (by simp)]
  have hshift : Integrable
      (fun u : ℝ =>
        (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
          ProbabilityTheory.beta alpha beta) *
            betaPDFReal (alpha - 2) (beta + 2) u) :=
    (_root_.GD.N0232.N0720.N1091.d012772 halphaShift hbetaShift).const_mul _
  apply hshift.congr
  filter_upwards with u
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0235.d004040 halpha0 hbeta u)]
  simpa [mul_comm] using
    (_root_.GD.N0232.N0720.N1092.d013028 (u := u) halpha hbeta).symm


theorem d013030
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta) :
    (∫ u, _root_.GD.N0232.N0720.N1092.d013024 u ∂betaMeasure alpha beta) =
      ProbabilityTheory.beta (alpha - 2) (beta + 2) /
        ProbabilityTheory.beta alpha beta := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have halphaShift : 0 < alpha - 2 := sub_pos.mpr halpha
  have hbetaShift : 0 < beta + 2 := by linarith
  rw [_root_.GD.N0235.d004041
    halpha0 hbeta]
  calc
    (∫ u, betaPDFReal alpha beta u * _root_.GD.N0232.N0720.N1092.d013024 u) =
        ∫ u,
          (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
            ProbabilityTheory.beta alpha beta) *
              betaPDFReal (alpha - 2) (beta + 2) u := by
      apply integral_congr_ae
      filter_upwards with u
      exact _root_.GD.N0232.N0720.N1092.d013028 halpha hbeta
    _ = (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
          ProbabilityTheory.beta alpha beta) *
        ∫ u, betaPDFReal (alpha - 2) (beta + 2) u := by
      rw [integral_const_mul]
    _ = ProbabilityTheory.beta (alpha - 2) (beta + 2) /
          ProbabilityTheory.beta alpha beta := by
      rw [_root_.GD.N0235.d004042
        halphaShift hbetaShift, mul_one]



theorem d013031 (alpha beta : ℝ) :
    ∀ᵐ u ∂betaMeasure alpha beta, u ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff
    ((measurable_betaPDFReal alpha beta).ennreal_ofReal)]
  filter_upwards with u
  intro hu
  by_contra hnot
  have houtside : ¬(0 < u ∧ u < 1) := by
    simpa only [mem_Ioo] using hnot
  simp [betaPDFReal, houtside] at hu



def d013032
    (alpha beta p u : ℝ) : ℝ :=
  alpha * (1 - u) /
    (beta * (1 - p) * u + alpha * p * (1 - u))

theorem d013033
    (alpha beta p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1092.d013032 alpha beta p) := by
  unfold _root_.GD.N0232.N0720.N1092.d013032
  fun_prop



theorem d013034
    {alpha beta p u : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u / p =
      _root_.GD.N0232.N0720.N1092.d013032 alpha beta p u := by
  have hcenter : 0 < _root_.GD.N0232.N0720.N1091.d012764 alpha beta p u :=
    _root_.GD.N0232.N0720.N1091.d012785 halpha hbeta hp0 hp1 hu.1 hu.2
  have hodds : 0 < _root_.GD.N0232.N0720.N1091.d012762 alpha beta p :=
    _root_.GD.N0232.N0720.N1091.d012778 halpha hbeta hp0 hp1
  have hweightDen : 0 <
      u + _root_.GD.N0232.N0720.N1091.d012762 alpha beta p * (1 - u) :=
    _root_.GD.N0232.N0720.N1091.d012779 hodds hu.1 hu.2
  unfold _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0232.N0720.N1091.d012762 _root_.GD.N0232.N0720.N1092.d013032
  field_simp [hp0.ne', hbeta.ne', (sub_pos.mpr hp1).ne',
    hcenter.ne', hweightDen.ne']


def d013035 (alpha beta u : ℝ) : ℝ :=
  alpha * (1 - u) / (beta * u)

theorem d013036
    (alpha beta : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1092.d013035 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1092.d013035
  fun_prop



theorem d013037
    {alpha beta u : ℝ} (hbeta : beta ≠ 0) (hu : u ≠ 0)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0720.N1092.d013032 alpha beta (p n) u)
      atTop (nhds (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u)) := by
  unfold _root_.GD.N0232.N0720.N1092.d013032 _root_.GD.N0232.N0720.N1092.d013035
  have hden : Tendsto
      (fun n => beta * (1 - p n) * u + alpha * p n * (1 - u))
      atTop (nhds (beta * u)) := by
    convert
      (((tendsto_const_nhds.sub hp).const_mul beta).mul_const u).add
        ((hp.const_mul alpha).mul_const (1 - u)) using 1 <;> ring
  have hnum : Tendsto (fun _ : ℕ => alpha * (1 - u))
      atTop (nhds (alpha * (1 - u))) := tendsto_const_nhds
  change Tendsto
    ((fun _ : ℕ => alpha * (1 - u)) /
      fun n => beta * (1 - p n) * u + alpha * p n * (1 - u))
    atTop (nhds (alpha * (1 - u) / (beta * u)))
  exact hnum.div hden (mul_ne_zero hbeta hu)



theorem d013038
    {alpha beta u : ℝ} (hbeta : beta ≠ 0)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2 =
      (alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u := by
  rw [_root_.GD.N0232.N0720.N1092.d013027 hu]
  unfold _root_.GD.N0232.N0720.N1092.d013035
  field_simp [hbeta, hu.1.ne']



theorem d013039
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta) :
    Integrable (fun u => (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2)
      (betaMeasure alpha beta) := by
  have hmajor : Integrable
      (fun u => (alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u)
      (betaMeasure alpha beta) :=
    (_root_.GD.N0232.N0720.N1092.d013029 halpha hbeta).const_mul _
  apply hmajor.congr
  filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 alpha beta] with u hu
  exact (_root_.GD.N0232.N0720.N1092.d013038 hbeta.ne' hu).symm


theorem d013040
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta) :
    (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2
      ∂betaMeasure alpha beta) =
      (alpha / beta) ^ 2 *
        (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
          ProbabilityTheory.beta alpha beta) := by
  calc
    (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2
        ∂betaMeasure alpha beta) =
        ∫ u, (alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u
          ∂betaMeasure alpha beta := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 alpha beta] with u hu
      exact _root_.GD.N0232.N0720.N1092.d013038 hbeta.ne' hu
    _ = (alpha / beta) ^ 2 *
        ∫ u, _root_.GD.N0232.N0720.N1092.d013024 u ∂betaMeasure alpha beta := by
      rw [integral_const_mul]
    _ = (alpha / beta) ^ 2 *
        (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
          ProbabilityTheory.beta alpha beta) := by
      rw [_root_.GD.N0232.N0720.N1092.d013030 halpha hbeta]


theorem d013041
    {alpha beta p u : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1092.d013032 alpha beta p u) ^ 2 ≤
      (2 * alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u := by
  have honep : 1 / 2 ≤ 1 - p := by linarith
  have hp1 : p < 1 := lt_of_le_of_lt hpHalf (by norm_num)
  have hnum : 0 ≤ alpha * (1 - u) :=
    mul_nonneg halpha.le (sub_nonneg.mpr hu.2.le)
  have hterm1 : 0 < beta * (1 - p) * u :=
    mul_pos (mul_pos hbeta (sub_pos.mpr hp1)) hu.1
  have hterm2 : 0 ≤ alpha * p * (1 - u) :=
    mul_nonneg (mul_nonneg halpha.le hp0.le) (sub_nonneg.mpr hu.2.le)
  have hden : 0 < beta * (1 - p) * u + alpha * p * (1 - u) :=
    add_pos_of_pos_of_nonneg hterm1 hterm2
  have hhalfden : 0 < beta * (1 / 2) * u :=
    mul_pos (mul_pos hbeta (by norm_num)) hu.1
  have hbp : beta * (1 / 2) ≤ beta * (1 - p) :=
    mul_le_mul_of_nonneg_left honep hbeta.le
  have hhalf_le_first : beta * (1 / 2) * u ≤ beta * (1 - p) * u :=
    mul_le_mul_of_nonneg_right hbp hu.1.le
  have hdenLower :
      beta * (1 / 2) * u ≤
        beta * (1 - p) * u + alpha * p * (1 - u) :=
    hhalf_le_first.trans (le_add_of_nonneg_right hterm2)
  have hratioNonneg : 0 ≤ _root_.GD.N0232.N0720.N1092.d013032 alpha beta p u :=
    div_nonneg hnum hden.le
  have hmajorNonneg : 0 ≤ (2 * alpha / beta) * ((1 - u) / u) := by
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) halpha.le) hbeta.le)
      (div_nonneg (sub_nonneg.mpr hu.2.le) hu.1.le)
  have hlinear :
      _root_.GD.N0232.N0720.N1092.d013032 alpha beta p u ≤
        (2 * alpha / beta) * ((1 - u) / u) := by
    unfold _root_.GD.N0232.N0720.N1092.d013032
    calc
      alpha * (1 - u) /
          (beta * (1 - p) * u + alpha * p * (1 - u)) ≤
          alpha * (1 - u) / (beta * (1 / 2) * u) :=
        div_le_div_of_nonneg_left hnum hhalfden hdenLower
      _ = (2 * alpha / beta) * ((1 - u) / u) := by
        field_simp [hbeta.ne', hu.1.ne']
  have hsquare :
      (_root_.GD.N0232.N0720.N1092.d013032 alpha beta p u) ^ 2 ≤
        ((2 * alpha / beta) * ((1 - u) / u)) ^ 2 :=
    (sq_le_sq₀ hratioNonneg hmajorNonneg).2 hlinear
  rw [_root_.GD.N0232.N0720.N1092.d013027 hu]
  simpa [mul_pow] using hsquare




theorem d013042
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) :
    Tendsto
      (fun n => ∫ u,
        (_root_.GD.N0232.N0720.N1092.d013032 alpha beta (p n) u) ^ 2
          ∂betaMeasure alpha beta)
      atTop
      (nhds (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2
        ∂betaMeasure alpha beta)) := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have hpHalf : ∀ᶠ n in atTop, p n ≤ 1 / 2 := by
    filter_upwards [(tendsto_order.1 hp).2 (1 / 2) (by norm_num)] with n hn
    exact hn.le
  have hsupport := _root_.GD.N0232.N0720.N1092.d013031 alpha beta
  let bound : ℝ → ℝ := fun u =>
    (2 * alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u
  have hboundInt : Integrable bound (betaMeasure alpha beta) :=
    (_root_.GD.N0232.N0720.N1092.d013029 halpha hbeta).const_mul _
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun n =>
      ((_root_.GD.N0232.N0720.N1092.d013033 alpha beta (p n)).pow_const 2)
        |>.aestronglyMeasurable
  · filter_upwards [hpHalf] with n hn
    filter_upwards [hsupport] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0232.N0720.N1092.d013041 halpha0 hbeta (hp0 n) hn hu
  · exact hboundInt
  · filter_upwards [hsupport] with u hu
    exact (_root_.GD.N0232.N0720.N1092.d013037 hbeta.ne' hu.1.ne' hp).pow 2


theorem d013043
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) :
    Tendsto
      (fun n => ∫ u,
        (_root_.GD.N0232.N0720.N1092.d013032 alpha beta (p n) u) ^ 2
          ∂betaMeasure alpha beta)
      atTop
      (nhds ((alpha / beta) ^ 2 *
        (ProbabilityTheory.beta (alpha - 2) (beta + 2) /
          ProbabilityTheory.beta alpha beta))) := by
  have h := _root_.GD.N0232.N0720.N1092.d013042 halpha hbeta hp hp0
  rw [_root_.GD.N0232.N0720.N1092.d013040 halpha hbeta] at h
  exact h



theorem d013044 {n : ℕ} :
    2 < (((n - 1 : ℕ) : ℝ) / 2) ↔ 6 ≤ n := by
  constructor
  · intro h
    have hsubReal : (4 : ℝ) < (n - 1 : ℕ) := by linarith
    have hsubNat : 4 < n - 1 := by exact_mod_cast hsubReal
    omega
  · intro hn
    have hsubNat : 5 ≤ n - 1 := by omega
    have hsubReal : (5 : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hsubNat
    linarith



theorem d013045 :
    (((5 - 1 : ℕ) : ℝ) / 2) = 2 := by
  norm_num

end

end N1092
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1092.d013029
#print axioms _root_.GD.N0232.N0720.N1092.d013034
#print axioms _root_.GD.N0232.N0720.N1092.d013037
#print axioms _root_.GD.N0232.N0720.N1092.d013041
#print axioms _root_.GD.N0232.N0720.N1092.d013042
#print axioms _root_.GD.N0232.N0720.N1092.d013043
#print axioms _root_.GD.N0232.N0720.N1092.d013044
