import GD.Module0851
import GD.Module0223
























open MeasureTheory ProbabilityTheory Filter Set

namespace GD
namespace N0232
namespace N0720
namespace N1421

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1092
open _root_.GD.N0232.N0720.N1093
open _root_.GD.N0232.N0720.N1050





def d013101 (alpha beta p u : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1092.d013032 alpha beta p u - 1


def d013102 (alpha beta u : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1092.d013035 alpha beta u - 1

theorem d013103
    (alpha beta p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1421.d013101 alpha beta p) := by
  unfold _root_.GD.N0232.N0720.N1421.d013101
  exact (_root_.GD.N0232.N0720.N1092.d013033 alpha beta p).sub measurable_const

theorem d013104
    (alpha beta : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1421.d013102 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1421.d013102
  exact (_root_.GD.N0232.N0720.N1092.d013036 alpha beta).sub measurable_const


theorem d013105
    {alpha beta p u : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p =
      p * _root_.GD.N0232.N0720.N1421.d013101 alpha beta p u := by
  have hdiv := _root_.GD.N0232.N0720.N1092.d013034
    halpha hbeta hp0 hp1 hu
  unfold _root_.GD.N0232.N0720.N1421.d013101
  calc
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p =
        p * (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u / p - 1) := by
      field_simp [hp0.ne']
    _ = p * (_root_.GD.N0232.N0720.N1092.d013032 alpha beta p u - 1) := by rw [hdiv]



theorem d013106
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 alpha beta p =
      p ^ 2 *
        ∫ u, (_root_.GD.N0232.N0720.N1421.d013101 alpha beta p u) ^ 2
          ∂betaMeasure alpha beta := by
  unfold _root_.GD.N0232.N0720.N1091.d012790
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 alpha beta] with u hu
  rw [_root_.GD.N0232.N0720.N1421.d013105
    halpha hbeta hp0 hp1 hu, mul_pow]





def d013107 (u : ℝ) : ℝ :=
  u ^ (-1 : ℝ) * (1 - u)

theorem d013108 : Measurable _root_.GD.N0232.N0720.N1421.d013107 := by
  unfold _root_.GD.N0232.N0720.N1421.d013107
  fun_prop

theorem d013109
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1421.d013107 u = (1 - u) / u := by
  unfold _root_.GD.N0232.N0720.N1421.d013107
  rw [Real.rpow_neg hu.1.le, Real.rpow_one]
  field_simp [hu.1.ne']



theorem d013110
    {alpha beta u : ℝ}
    (halpha : 1 < alpha) (hbeta : 0 < beta) :
    betaPDFReal alpha beta u * _root_.GD.N0232.N0720.N1421.d013107 u =
      (ProbabilityTheory.beta (alpha - 1) (beta + 1) /
        ProbabilityTheory.beta alpha beta) *
          betaPDFReal (alpha - 1) (beta + 1) u := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have halphaShift : 0 < alpha - 1 := sub_pos.mpr halpha
  have hbetaShift : 0 < beta + 1 := by linarith
  by_cases hu : 0 < u ∧ u < 1
  · have h1u : 0 < 1 - u := sub_pos.mpr hu.2
    rw [betaPDFReal, if_pos hu, betaPDFReal, if_pos hu]
    unfold _root_.GD.N0232.N0720.N1421.d013107
    have hexponentLeft : alpha - 1 + (-1 : ℝ) = alpha - 1 - 1 := by ring
    have hexponentRight : beta - 1 + (1 : ℝ) = beta + 1 - 1 := by ring
    calc
      1 / ProbabilityTheory.beta alpha beta * u ^ (alpha - 1) *
            (1 - u) ^ (beta - 1) * (u ^ (-1 : ℝ) * (1 - u)) =
          1 / ProbabilityTheory.beta alpha beta *
            (u ^ (alpha - 1) * u ^ (-1 : ℝ)) *
              ((1 - u) ^ (beta - 1) * (1 - u) ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
        ring
      _ = 1 / ProbabilityTheory.beta alpha beta *
            u ^ (alpha - 1 - 1) * (1 - u) ^ (beta + 1 - 1) := by
        rw [← Real.rpow_add hu.1, ← Real.rpow_add h1u,
          hexponentLeft, hexponentRight]
      _ = (ProbabilityTheory.beta (alpha - 1) (beta + 1) /
            ProbabilityTheory.beta alpha beta) *
              (1 / ProbabilityTheory.beta (alpha - 1) (beta + 1) *
                u ^ (alpha - 1 - 1) * (1 - u) ^ (beta + 1 - 1)) := by
        field_simp [ne_of_gt (ProbabilityTheory.beta_pos halpha0 hbeta),
          ne_of_gt (ProbabilityTheory.beta_pos halphaShift hbetaShift)]
  · rw [betaPDFReal, if_neg hu, betaPDFReal, if_neg hu]
    ring

theorem d013111
    {alpha beta : ℝ} (halpha : 1 < alpha) (hbeta : 0 < beta) :
    Integrable _root_.GD.N0232.N0720.N1421.d013107 (betaMeasure alpha beta) := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have halphaShift : 0 < alpha - 1 := sub_pos.mpr halpha
  have hbetaShift : 0 < beta + 1 := by linarith
  change Integrable _root_.GD.N0232.N0720.N1421.d013107
    (volume.withDensity (fun u => ENNReal.ofReal (betaPDFReal alpha beta u)))
  rw [integrable_withDensity_iff
    ((measurable_betaPDFReal alpha beta).ennreal_ofReal) (by simp)]
  have hshift : Integrable
      (fun u : ℝ =>
        (ProbabilityTheory.beta (alpha - 1) (beta + 1) /
          ProbabilityTheory.beta alpha beta) *
            betaPDFReal (alpha - 1) (beta + 1) u) :=
    (_root_.GD.N0232.N0720.N1091.d012772 halphaShift hbetaShift).const_mul _
  apply hshift.congr
  filter_upwards with u
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0235.d004040 halpha0 hbeta u)]
  simpa [mul_comm] using
    (_root_.GD.N0232.N0720.N1421.d013110 (u := u) halpha hbeta).symm

theorem d013112
    {alpha beta : ℝ} (halpha : 1 < alpha) (hbeta : 0 < beta) :
    (∫ u, _root_.GD.N0232.N0720.N1421.d013107 u ∂betaMeasure alpha beta) =
      ProbabilityTheory.beta (alpha - 1) (beta + 1) /
        ProbabilityTheory.beta alpha beta := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have halphaShift : 0 < alpha - 1 := sub_pos.mpr halpha
  have hbetaShift : 0 < beta + 1 := by linarith
  rw [_root_.GD.N0235.d004041
    halpha0 hbeta]
  calc
    (∫ u, betaPDFReal alpha beta u * _root_.GD.N0232.N0720.N1421.d013107 u) =
        ∫ u,
          (ProbabilityTheory.beta (alpha - 1) (beta + 1) /
            ProbabilityTheory.beta alpha beta) *
              betaPDFReal (alpha - 1) (beta + 1) u := by
      apply integral_congr_ae
      filter_upwards with u
      exact _root_.GD.N0232.N0720.N1421.d013110 halpha hbeta
    _ = (ProbabilityTheory.beta (alpha - 1) (beta + 1) /
          ProbabilityTheory.beta alpha beta) *
        ∫ u, betaPDFReal (alpha - 1) (beta + 1) u := by
      rw [integral_const_mul]
    _ = ProbabilityTheory.beta (alpha - 1) (beta + 1) /
          ProbabilityTheory.beta alpha beta := by
      rw [_root_.GD.N0235.d004042
        halphaShift hbetaShift, mul_one]

theorem d013113
    {alpha beta : ℝ} (halpha : 1 < alpha) (hbeta : 0 < beta) :
    ProbabilityTheory.beta (alpha - 1) (beta + 1) /
        ProbabilityTheory.beta alpha beta =
      beta / (alpha - 1) := by
  have ha1 : 0 < alpha - 1 := sub_pos.mpr halpha
  have hL : ProbabilityTheory.beta alpha beta =
      (alpha - 1) / (alpha - 1 + beta) *
        ProbabilityTheory.beta (alpha - 1) beta := by
    convert _root_.GD.N0235.d004038 ha1 hbeta using 1 <;> ring
  have hR : ProbabilityTheory.beta (alpha - 1) (beta + 1) =
      beta / (alpha - 1 + beta) *
        ProbabilityTheory.beta (alpha - 1) beta := by
    exact _root_.GD.N0235.d004039 ha1 hbeta
  rw [hR, hL]
  field_simp [ne_of_gt ha1, ne_of_gt hbeta,
    ne_of_gt (ProbabilityTheory.beta_pos ha1 hbeta),
    ne_of_gt (add_pos ha1 hbeta)]

theorem d013114
    {alpha beta u : ℝ} (hbeta : beta ≠ 0)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1092.d013035 alpha beta u =
      (alpha / beta) * _root_.GD.N0232.N0720.N1421.d013107 u := by
  rw [_root_.GD.N0232.N0720.N1421.d013109 hu]
  unfold _root_.GD.N0232.N0720.N1092.d013035
  field_simp [hbeta, hu.1.ne']

theorem d013115
    {alpha beta : ℝ} (halpha : 1 < alpha) (hbeta : 0 < beta) :
    Integrable (_root_.GD.N0232.N0720.N1092.d013035 alpha beta)
      (betaMeasure alpha beta) := by
  have hscaled := (_root_.GD.N0232.N0720.N1421.d013111 halpha hbeta).const_mul
    (alpha / beta)
  apply hscaled.congr
  filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 alpha beta] with u hu
  exact (_root_.GD.N0232.N0720.N1421.d013114 hbeta.ne' hu).symm

theorem d013116
    {alpha beta : ℝ} (halpha : 1 < alpha) (hbeta : 0 < beta) :
    (∫ u, _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
      ∂betaMeasure alpha beta) = alpha / (alpha - 1) := by
  calc
    (∫ u, _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
        ∂betaMeasure alpha beta) =
        ∫ u, (alpha / beta) * _root_.GD.N0232.N0720.N1421.d013107 u
          ∂betaMeasure alpha beta := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 alpha beta] with u hu
      exact _root_.GD.N0232.N0720.N1421.d013114 hbeta.ne' hu
    _ = (alpha / beta) *
        ∫ u, _root_.GD.N0232.N0720.N1421.d013107 u ∂betaMeasure alpha beta := by
      rw [integral_const_mul]
    _ = alpha / (alpha - 1) := by
      rw [_root_.GD.N0232.N0720.N1421.d013112 halpha hbeta,
        _root_.GD.N0232.N0720.N1421.d013113 halpha hbeta]
      field_simp [hbeta.ne', (sub_pos.mpr halpha).ne']



theorem d013117
    {alpha beta u : ℝ} (hbeta : beta ≠ 0) (hu : u ≠ 0)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0720.N1421.d013101 alpha beta (p n) u)
      atTop (nhds (_root_.GD.N0232.N0720.N1421.d013102 alpha beta u)) := by
  exact (_root_.GD.N0232.N0720.N1092.d013037 hbeta hu hp).sub tendsto_const_nhds

theorem d013118
    {alpha beta p u : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1421.d013101 alpha beta p u) ^ 2 ≤
      2 * ((2 * alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u) + 2 := by
  have hjet := _root_.GD.N0232.N0720.N1092.d013041
    halpha hbeta hp0 hpHalf hu
  unfold _root_.GD.N0232.N0720.N1421.d013101
  nlinarith [sq_nonneg (_root_.GD.N0232.N0720.N1092.d013032 alpha beta p u + 1)]


theorem d013119
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) :
    Tendsto
      (fun n => ∫ u,
        (_root_.GD.N0232.N0720.N1421.d013101 alpha beta (p n) u) ^ 2
          ∂betaMeasure alpha beta)
      atTop
      (nhds (∫ u, (_root_.GD.N0232.N0720.N1421.d013102 alpha beta u) ^ 2
        ∂betaMeasure alpha beta)) := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  letI : IsProbabilityMeasure (betaMeasure alpha beta) :=
    isProbabilityMeasureBeta halpha0 hbeta
  have hpHalf : ∀ᶠ n in atTop, p n ≤ 1 / 2 := by
    filter_upwards [(tendsto_order.1 hp).2 (1 / 2) (by norm_num)] with n hn
    exact hn.le
  have hsupport := _root_.GD.N0232.N0720.N1092.d013031 alpha beta
  let bound : ℝ → ℝ := fun u =>
    2 * ((2 * alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u) + 2
  have hboundInt : Integrable bound (betaMeasure alpha beta) := by
    exact ((_root_.GD.N0232.N0720.N1092.d013029 halpha hbeta).const_mul
      ((2 * alpha / beta) ^ 2) |>.const_mul 2).add (integrable_const 2)
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun n =>
      ((_root_.GD.N0232.N0720.N1421.d013103 alpha beta (p n)).pow_const 2)
        |>.aestronglyMeasurable
  · filter_upwards [hpHalf] with n hn
    filter_upwards [hsupport] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0232.N0720.N1421.d013118 halpha0 hbeta (hp0 n) hn hu
  · exact hboundInt
  · filter_upwards [hsupport] with u hu
    exact (_root_.GD.N0232.N0720.N1421.d013117 hbeta.ne' hu.1.ne' hp).pow 2


theorem d013120
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta) :
    (∫ u, (_root_.GD.N0232.N0720.N1421.d013102 alpha beta u) ^ 2
      ∂betaMeasure alpha beta) =
      (alpha ^ 2 + alpha * beta + 2 * beta) /
        (beta * (alpha - 1) * (alpha - 2)) := by
  have hjetSq := _root_.GD.N0232.N0720.N1092.d013039 halpha hbeta
  have hjet := _root_.GD.N0232.N0720.N1421.d013115
    (lt_trans (by norm_num) halpha) hbeta
  letI : IsProbabilityMeasure (betaMeasure alpha beta) :=
    isProbabilityMeasureBeta (lt_trans (by norm_num) halpha) hbeta
  calc
    (∫ u, (_root_.GD.N0232.N0720.N1421.d013102 alpha beta u) ^ 2
        ∂betaMeasure alpha beta) =
        ∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2 -
          2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u + 1
            ∂betaMeasure alpha beta := by
      apply integral_congr_ae
      filter_upwards with u
      unfold _root_.GD.N0232.N0720.N1421.d013102
      ring
    _ = (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2
          ∂betaMeasure alpha beta) -
        2 * (∫ u, _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
          ∂betaMeasure alpha beta) + 1 := by
      have hdiff : Integrable
          (fun u => (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2 -
            2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u)
          (betaMeasure alpha beta) := by
        have hraw := hjetSq.sub (hjet.const_mul 2)
        apply hraw.congr
        filter_upwards with u
        rfl
      have hadd :
          (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2 -
              2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u + 1
              ∂betaMeasure alpha beta) =
            (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2 -
                2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
                ∂betaMeasure alpha beta) +
              ∫ _ : ℝ, 1 ∂betaMeasure alpha beta := by
        exact integral_add hdiff (integrable_const 1)
      have hsub :
          (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2 -
              2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
              ∂betaMeasure alpha beta) =
            (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2
                ∂betaMeasure alpha beta) -
              ∫ u, 2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
                ∂betaMeasure alpha beta := by
        exact integral_sub hjetSq (hjet.const_mul 2)
      calc
        _ = (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2 -
              2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
              ∂betaMeasure alpha beta) +
            ∫ _ : ℝ, 1 ∂betaMeasure alpha beta := hadd
        _ = ((∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2
                ∂betaMeasure alpha beta) -
              ∫ u, 2 * _root_.GD.N0232.N0720.N1092.d013035 alpha beta u
                ∂betaMeasure alpha beta) + 1 := by
          rw [hsub, integral_const]
          simp
        _ = _ := by rw [integral_const_mul]
    _ = _ := by
      rw [_root_.GD.N0232.N0720.N1093.d013051 halpha hbeta,
        _root_.GD.N0232.N0720.N1421.d013116
          (lt_trans (by norm_num) halpha) hbeta]
      field_simp [hbeta.ne', (sub_pos.mpr halpha).ne',
        (by linarith : alpha - 1 ≠ 0)]
      ring


theorem d013121
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n) / (p n) ^ 2)
      atTop
      (nhds ((alpha ^ 2 + alpha * beta + 2 * beta) /
        (beta * (alpha - 1) * (alpha - 2)))) := by
  have h := _root_.GD.N0232.N0720.N1421.d013119
    halpha hbeta hp hp0
  rw [_root_.GD.N0232.N0720.N1421.d013120 halpha hbeta] at h
  convert h using 1
  funext n
  rw [_root_.GD.N0232.N0720.N1421.d013106
    (lt_trans (by norm_num) halpha) hbeta (hp0 n) (hp1 n)]
  field_simp [(hp0 n).ne']





noncomputable def d013122
    (alpha beta z : ℝ) : ℝ :=
  (1 / ProbabilityTheory.beta alpha beta) *
    z ^ (alpha - 1) * (alpha / (alpha + beta * z)) ^ 2

theorem d013123
    {alpha beta z : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hz : 0 < z) :
    _root_.GD.N0232.N0720.N1421.d013122 alpha beta ((alpha / beta) * z) =
      (1 / ProbabilityTheory.beta alpha beta) *
        (alpha / beta) ^ (alpha - 1) *
          (z ^ (alpha - 1) * (1 + z) ^ (-2 : ℝ)) := by
  have hscale : 0 < alpha / beta := div_pos halpha hbeta
  have hden : 0 < alpha * (1 + z) := by positivity
  unfold _root_.GD.N0232.N0720.N1421.d013122
  rw [Real.mul_rpow hscale.le hz.le]
  have hdenEq :
      alpha + beta * ((alpha / beta) * z) = alpha * (1 + z) := by
    field_simp [hbeta.ne']
  rw [hdenEq]
  have hratio :
      (alpha / (alpha * (1 + z))) ^ 2 = (1 + z) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + z), Real.rpow_two]
    field_simp [halpha.ne', hden.ne']
  rw [hratio]
  ring


theorem d013124
    {alpha beta : ℝ}
    (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta) :
    (∫ z in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1421.d013122 alpha beta z) =
      (alpha / beta) ^ alpha *
        (ProbabilityTheory.beta alpha (2 - alpha) /
          ProbabilityTheory.beta alpha beta) := by
  have htwo : 0 < 2 - alpha := sub_pos.mpr halphaTwo
  have hscale : 0 < alpha / beta := div_pos halpha hbeta
  have hcov := MeasureTheory.integral_comp_mul_left_Ioi
    (g := _root_.GD.N0232.N0720.N1421.d013122 alpha beta) 0 hscale
  simp only [mul_zero, smul_eq_mul] at hcov
  have hscaled :
      (∫ z in Ioi (0 : ℝ),
        _root_.GD.N0232.N0720.N1421.d013122 alpha beta ((alpha / beta) * z)) =
        (1 / ProbabilityTheory.beta alpha beta) *
          (alpha / beta) ^ (alpha - 1) *
            ProbabilityTheory.beta alpha (2 - alpha) := by
    calc
      _ = ∫ z in Ioi (0 : ℝ),
          ((1 / ProbabilityTheory.beta alpha beta) *
            (alpha / beta) ^ (alpha - 1)) *
              (z ^ (alpha - 1) * (1 + z) ^ (-2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro z hz
        change _root_.GD.N0232.N0720.N1421.d013122 alpha beta ((alpha / beta) * z) = _
        exact _root_.GD.N0232.N0720.N1421.d013123 halpha hbeta hz
      _ = ((1 / ProbabilityTheory.beta alpha beta) *
            (alpha / beta) ^ (alpha - 1)) *
          ∫ z in Ioi (0 : ℝ),
            z ^ (alpha - 1) * (1 + z) ^ (-2 : ℝ) := by
        rw [integral_const_mul]
      _ = _ := by
        have hprime :
            (∫ z in Ioi (0 : ℝ),
              z ^ (alpha - 1) * (1 + z) ^ (-2 : ℝ)) =
              ProbabilityTheory.beta alpha (2 - alpha) := by
          convert _root_.GD.N0232.N0720.N1050.d003164 alpha (2 - alpha) halpha htwo using 1 <;>
            ring
        rw [hprime]
  have hrecover :
      (∫ z in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1421.d013122 alpha beta z) =
        (alpha / beta) *
          ∫ z in Ioi (0 : ℝ),
            _root_.GD.N0232.N0720.N1421.d013122 alpha beta ((alpha / beta) * z) := by
    rw [hcov]
    field_simp [hscale.ne']
  rw [hrecover, hscaled]
  have hcollect :
      (alpha / beta) * (alpha / beta) ^ (alpha - 1) =
        (alpha / beta) ^ alpha := by
    calc
      _ = (alpha / beta) ^ (1 : ℝ) *
          (alpha / beta) ^ (alpha - 1) := by rw [Real.rpow_one]
      _ = (alpha / beta) ^ (1 + (alpha - 1)) :=
        (Real.rpow_add hscale 1 (alpha - 1)).symm
      _ = _ := by ring_nf
  calc
    (alpha / beta) *
        (1 / ProbabilityTheory.beta alpha beta *
          (alpha / beta) ^ (alpha - 1) *
            ProbabilityTheory.beta alpha (2 - alpha)) =
        (1 / ProbabilityTheory.beta alpha beta) *
          ((alpha / beta) * (alpha / beta) ^ (alpha - 1)) *
            ProbabilityTheory.beta alpha (2 - alpha) := by ring
    _ = (1 / ProbabilityTheory.beta alpha beta) *
          (alpha / beta) ^ alpha *
            ProbabilityTheory.beta alpha (2 - alpha) := by rw [hcollect]
    _ = _ := by ring


theorem d013125
    {alpha beta : ℝ}
    (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta) :
    (∫ z in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1421.d013122 alpha beta z) =
      (alpha / beta) ^ alpha *
        Real.Gamma (alpha + beta) * Real.Gamma (2 - alpha) /
          Real.Gamma beta := by
  rw [_root_.GD.N0232.N0720.N1421.d013124 halpha halphaTwo hbeta]
  unfold ProbabilityTheory.beta
  have hga : Real.Gamma alpha ≠ 0 :=
    (Real.Gamma_pos_of_pos halpha).ne'
  have hgb : Real.Gamma beta ≠ 0 :=
    (Real.Gamma_pos_of_pos hbeta).ne'
  have hgab : Real.Gamma (alpha + beta) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos halpha hbeta)).ne'
  have hg2a : Real.Gamma (2 - alpha) ≠ 0 :=
    (Real.Gamma_pos_of_pos (sub_pos.mpr halphaTwo)).ne'
  have htwo : Real.Gamma (alpha + (2 - alpha)) = 1 := by
    convert Real.Gamma_two using 1 <;> ring
  rw [htwo]
  field_simp [hga, hgb, hgab, hg2a]





def d013126 : ℝ → ℝ :=
  (fun _ => 1) - id

@[simp] theorem d013127 (u : ℝ) :
    _root_.GD.N0232.N0720.N1421.d013126 u = 1 - u := by
  rfl





def d013128 (p u : ℝ) : ℝ :=
  p ^ _root_.GD.N0232.N0720.N1421.d013126 u

theorem d013129 (p : ℝ) :
    _root_.GD.N0232.N0720.N1421.d013128 p 0 = p := by
  simp [_root_.GD.N0232.N0720.N1421.d013128]

theorem d013130 (p : ℝ) :
    _root_.GD.N0232.N0720.N1421.d013128 p 1 = 1 := by
  simp [_root_.GD.N0232.N0720.N1421.d013128]

theorem d013131
    {p u : ℝ} (hp : 0 < p) :
    HasDerivAt (_root_.GD.N0232.N0720.N1421.d013128 p)
      (-Real.log p * _root_.GD.N0232.N0720.N1421.d013128 p u) u := by
  have hbase : HasDerivAt _root_.GD.N0232.N0720.N1421.d013126 (0 - 1) u :=
    (hasDerivAt_const u 1).sub (hasDerivAt_id u)
  have hpow := hbase.const_rpow hp
  unfold _root_.GD.N0232.N0720.N1421.d013128
  convert hpow using 1
  ring

theorem d013132
    {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    |(-Real.log p) * _root_.GD.N0232.N0720.N1421.d013128 p u| =
      Real.log (1 / p) * _root_.GD.N0232.N0720.N1421.d013128 p u := by
  have hlog : Real.log p < 0 := Real.log_neg hp0 hp1
  have hratio : 0 < _root_.GD.N0232.N0720.N1421.d013128 p u := by
    exact Real.rpow_pos_of_pos hp0 _
  rw [abs_of_pos (mul_pos (neg_pos.mpr hlog) hratio)]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hp0.ne', Real.log_one]
  ring

end

end N1421
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1421.d013106
#print axioms _root_.GD.N0232.N0720.N1421.d013121
#print axioms _root_.GD.N0232.N0720.N1421.d013125
#print axioms _root_.GD.N0232.N0720.N1421.d013131
