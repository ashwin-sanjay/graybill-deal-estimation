import GD.Module0858
import GD.Module0223
import GD.Module0274













open Filter MeasureTheory ProbabilityTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1426

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1050
open _root_.GD.N0232.N0720.N1428
open _root_.GD.N0232.N0720.N1427
open _root_.GD.N0232.N0720.N1429


def d013187 (beta u : ℝ) : ℝ :=
  (beta / 2) * _root_.GD.N0232.N0720.N1050.d003157 u


def d013188 (beta u : ℝ) : ℝ :=
  (beta / 2) * _root_.GD.N0232.N0720.N1050.d003158 u

theorem d013189
    {beta : ℝ} (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1426.d013187 beta '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext X
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact mul_pos (div_pos hbeta (by norm_num))
      (div_pos hu.1 (sub_pos.mpr hu.2))
  · intro hX
    have hX0 : 0 < X := hX
    let u := 2 * X / (beta + 2 * X)
    have hden : 0 < beta + 2 * X := by nlinarith
    have hu0 : 0 < u := by
      dsimp [u]
      exact div_pos (mul_pos (by norm_num) hX0) hden
    have hu1 : u < 1 := by
      dsimp [u]
      rw [div_lt_one hden]
      linarith
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    unfold _root_.GD.N0232.N0720.N1426.d013187 _root_.GD.N0232.N0720.N1050.d003157
    dsimp [u]
    field_simp [hbeta.ne', hden.ne']
    ring

theorem d013190
    {beta u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (_root_.GD.N0232.N0720.N1426.d013187 beta)
      (_root_.GD.N0232.N0720.N1426.d013188 beta u) (Ioo 0 1) u := by
  convert! (_root_.GD.N0232.N0720.N1050.d003160 u hu).const_mul (beta / 2) using 1

theorem d013191
    {beta : ℝ} (hbeta : 0 < beta) :
    InjOn (_root_.GD.N0232.N0720.N1426.d013187 beta) (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  have hscale : beta / 2 ≠ 0 := (div_pos hbeta (by norm_num)).ne'
  unfold _root_.GD.N0232.N0720.N1426.d013187 at huv
  apply _root_.GD.N0232.N0720.N1050.d003161 hu hv
  exact mul_left_cancel₀ hscale huv

theorem d013192
    {beta u : ℝ} (hbeta : 0 < beta) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1426.d013187 beta u := by
  unfold _root_.GD.N0232.N0720.N1426.d013187 _root_.GD.N0232.N0720.N1050.d003157
  exact mul_pos (div_pos hbeta (by norm_num))
    (div_pos hu.1 (sub_pos.mpr hu.2))

theorem d013193
    {beta u : ℝ} (hbeta : 0 < beta) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1426.d013188 beta u := by
  unfold _root_.GD.N0232.N0720.N1426.d013188 _root_.GD.N0232.N0720.N1050.d003158
  exact mul_pos (div_pos hbeta (by norm_num))
    (one_div_pos.mpr (sq_pos_of_pos (sub_pos.mpr hu.2)))



theorem d013194
    {beta p u : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u =
      p / ((1 - p) * _root_.GD.N0232.N0720.N1426.d013187 beta u + p) := by
  have h1u : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
  have hbeta0 : beta ≠ 0 := hbeta.ne'
  have h1p : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have hleftDen :
      u + _root_.GD.N0232.N0720.N1091.d012762 2 beta p * (1 - u) ≠ 0 :=
    (_root_.GD.N0232.N0720.N1091.d012779
      (_root_.GD.N0232.N0720.N1091.d012778 (by norm_num) hbeta hp0 hp1) hu.1 hu.2).ne'
  have hrightDen :
      (1 - p) * _root_.GD.N0232.N0720.N1426.d013187 beta u + p ≠ 0 :=
    (add_pos
      (mul_pos (sub_pos.mpr hp1) (_root_.GD.N0232.N0720.N1426.d013192 hbeta hu)) hp0).ne'
  unfold _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0232.N0720.N1091.d012762 _root_.GD.N0232.N0720.N1426.d013187 _root_.GD.N0232.N0720.N1050.d003157
  field_simp [h1u, hbeta0, h1p, hleftDen, hrightDen]



theorem d013195
    {beta p u : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u - p =
      p * _root_.GD.N0232.N0720.N1428.d013136 p (_root_.GD.N0232.N0720.N1426.d013187 beta u) := by
  have hrightDen :
      (1 - p) * _root_.GD.N0232.N0720.N1426.d013187 beta u + p ≠ 0 := by
    exact (add_pos
      (mul_pos (sub_pos.mpr hp1)
        (_root_.GD.N0232.N0720.N1426.d013192 hbeta hu)) hp0).ne'
  rw [_root_.GD.N0232.N0720.N1426.d013194 hbeta hp0 hp1 hu]
  unfold _root_.GD.N0232.N0720.N1428.d013136
  field_simp [hrightDen]
  ring


theorem d013196
    {beta : ℝ} (hbeta : 0 < beta) :
    1 / ProbabilityTheory.beta 2 beta = beta * (beta + 1) := by
  unfold ProbabilityTheory.beta
  rw [show (2 : ℝ) + beta = (beta + 1) + 1 by ring,
    Real.Gamma_add_one (by linarith : beta + 1 ≠ 0),
    Real.Gamma_add_one hbeta.ne', Real.Gamma_two]
  field_simp [(Real.Gamma_pos_of_pos hbeta).ne']


theorem d013197
    {beta u : ℝ} (hbeta : 0 < beta) (hu : u ∈ Ioo (0 : ℝ) 1) :
    beta / (beta + 2 * _root_.GD.N0232.N0720.N1426.d013187 beta u) = 1 - u := by
  have h1u : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
  unfold _root_.GD.N0232.N0720.N1426.d013187 _root_.GD.N0232.N0720.N1050.d003157
  field_simp [hbeta.ne', h1u]
  ring



theorem d013198
    {beta u : ℝ} (hbeta : 0 < beta) (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal 2 beta u =
      |_root_.GD.N0232.N0720.N1426.d013188 beta u| *
        _root_.GD.N0232.N0720.N1428.d013135 beta (_root_.GD.N0232.N0720.N1426.d013187 beta u) := by
  have hu0 : 0 < u := hu.1
  have h1u : 0 < 1 - u := sub_pos.mpr hu.2
  have hderiv : 0 < _root_.GD.N0232.N0720.N1426.d013188 beta u :=
    _root_.GD.N0232.N0720.N1426.d013193 hbeta hu
  have hratio := _root_.GD.N0232.N0720.N1426.d013197 hbeta hu
  have hcollect :
      (1 - u) ^ (beta + 2) =
        (1 - u) ^ (3 : ℝ) * (1 - u) ^ (beta - 1) := by
    calc
      (1 - u) ^ (beta + 2) =
          (1 - u) ^ ((3 : ℝ) + (beta - 1)) := by
            congr 1
            ring
      _ = (1 - u) ^ (3 : ℝ) * (1 - u) ^ (beta - 1) :=
        Real.rpow_add h1u 3 (beta - 1)
  rw [betaPDFReal, if_pos ⟨hu.1, hu.2⟩, _root_.GD.N0232.N0720.N1426.d013196 hbeta,
    abs_of_pos hderiv]
  unfold _root_.GD.N0232.N0720.N1428.d013135 _root_.GD.N0232.N0720.N1428.d013133
  rw [hratio, hcollect]
  unfold _root_.GD.N0232.N0720.N1426.d013187 _root_.GD.N0232.N0720.N1426.d013188 _root_.GD.N0232.N0720.N1050.d003157
    _root_.GD.N0232.N0720.N1050.d003158
  rw [show u ^ ((2 : ℝ) - 1) = u by norm_num [Real.rpow_one],
    show (1 - u) ^ (3 : ℝ) = (1 - u) ^ (3 : ℕ) by norm_num]
  field_simp [hbeta.ne', h1u.ne']
  ring



theorem d013199
    {beta p u : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal 2 beta u *
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u - p) ^ 2 =
      p ^ 2 *
        (|_root_.GD.N0232.N0720.N1426.d013188 beta u| *
          _root_.GD.N0232.N0720.N1427.d013155 beta p (_root_.GD.N0232.N0720.N1426.d013187 beta u)) := by
  rw [_root_.GD.N0232.N0720.N1426.d013198 hbeta hu,
    _root_.GD.N0232.N0720.N1426.d013195
      hbeta hp0 hp1 hu]
  unfold _root_.GD.N0232.N0720.N1427.d013155
  ring



theorem d013200
    {beta p : ℝ} (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1429.d013174 beta p =
      ∫ u : ℝ in Ioo (0 : ℝ) 1,
        |_root_.GD.N0232.N0720.N1426.d013188 beta u| *
          _root_.GD.N0232.N0720.N1427.d013155 beta p (_root_.GD.N0232.N0720.N1426.d013187 beta u) := by
  unfold _root_.GD.N0232.N0720.N1429.d013174
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo
    (fun u hu => _root_.GD.N0232.N0720.N1426.d013190 (beta := beta) hu)
    (_root_.GD.N0232.N0720.N1426.d013191 hbeta)
    (_root_.GD.N0232.N0720.N1427.d013155 beta p)
  rw [_root_.GD.N0232.N0720.N1426.d013189 hbeta] at hcov
  simpa only [smul_eq_mul] using hcov





theorem d013201
    {beta p : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    IntegrableOn (_root_.GD.N0232.N0720.N1427.d013155 beta p) (Ioi (0 : ℝ)) := by
  have hsource : Integrable
      (fun u : ℝ => betaPDFReal (2 : ℝ) beta u *
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 (2 : ℝ) beta p) u - p) ^ 2) := by
    have hmeas : AEStronglyMeasurable
        (fun u : ℝ => betaPDFReal (2 : ℝ) beta u *
          (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 (2 : ℝ) beta p) u - p) ^ 2) :=
      ((measurable_betaPDFReal (2 : ℝ) beta).mul
        (((_root_.GD.N0232.N0720.N1091.d012771 (_root_.GD.N0232.N0720.N1091.d012762 (2 : ℝ) beta p)).sub
          measurable_const).pow_const 2)).aestronglyMeasurable
    apply (_root_.GD.N0232.N0720.N1091.d012772
      (show (0 : ℝ) < 2 by norm_num) hbeta).mono' hmeas
    filter_upwards with u
    have hpdf0 := _root_.GD.N0235.d004040
      (by norm_num : (0 : ℝ) < 2) hbeta u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · have hw := _root_.GD.N0232.N0720.N1091.d012780
        (_root_.GD.N0232.N0720.N1091.d012778 (alpha := (2 : ℝ)) (beta := beta) (p := p)
          (by norm_num) hbeta hp0 hp1) hu.1 hu.2
      have herrAbs :
          |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u - p| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hw.1, hw.2]
      have herrSq :
          |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u - p| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg
          (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u - p)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpdf0, abs_pow]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left herrSq hpdf0
    · have houtside : ¬(0 < u ∧ u < 1) := by
        simpa only [Set.mem_Ioo] using hu
      simp [betaPDFReal, houtside]
  have hchart : IntegrableOn
      (fun u : ℝ => |_root_.GD.N0232.N0720.N1426.d013188 beta u| *
        _root_.GD.N0232.N0720.N1427.d013155 beta p (_root_.GD.N0232.N0720.N1426.d013187 beta u))
      (Ioo (0 : ℝ) 1) := by
    have hscaled : IntegrableOn
        (fun u : ℝ => (p ^ 2)⁻¹ *
          (betaPDFReal (2 : ℝ) beta u *
            (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 (2 : ℝ) beta p) u - p) ^ 2))
        (Ioo (0 : ℝ) 1) :=
      (hsource.const_mul (p ^ 2)⁻¹).integrableOn
    apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioo
    intro u hu
    dsimp only
    rw [_root_.GD.N0232.N0720.N1426.d013199
      hbeta hp0 hp1 hu]
    field_simp [hp0.ne']
  rw [← _root_.GD.N0232.N0720.N1426.d013189 hbeta]
  apply (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo
    (fun u hu => _root_.GD.N0232.N0720.N1426.d013190 (beta := beta) hu)
    (_root_.GD.N0232.N0720.N1426.d013191 hbeta)
    (_root_.GD.N0232.N0720.N1427.d013155 beta p)).2
  simpa only [smul_eq_mul] using hchart





theorem d013202
    {beta p : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1429.d013174 beta p =
      _root_.GD.N0232.N0720.N1429.d013175 beta p := by
  let f : ℝ → ℝ := _root_.GD.N0232.N0720.N1427.d013155 beta p
  have hglob : IntegrableOn f (Ioi (0 : ℝ)) :=
    _root_.GD.N0232.N0720.N1426.d013201 hbeta hp0 hp1
  have hright : IntegrableOn f (Ioi (1 : ℝ)) :=
    hglob.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hzeroP : IntervalIntegrable f volume (0 : ℝ) p :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hp0.le).2
      (hglob.mono_set fun _ hx => hx.1)
  have hpOne : IntervalIntegrable f volume p 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hp1.le).2
      (hglob.mono_set fun _ hx => lt_trans hp0 hx.1)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hzeroP hpOne
  have htail := intervalIntegral.integral_interval_add_Ioi hglob hright
  unfold _root_.GD.N0232.N0720.N1429.d013174 _root_.GD.N0232.N0720.N1429.d013175
    _root_.GD.N0232.N0720.N1427.d013156 _root_.GD.N0232.N0720.N1429.d013173 _root_.GD.N0232.N0720.N1427.d013157
  change (∫ X : ℝ in Ioi (0 : ℝ), f X) =
    (∫ X : ℝ in (0 : ℝ)..p, f X) +
      (∫ X : ℝ in p..1, f X) +
        ∫ X : ℝ in Ioi (1 : ℝ), f X
  rw [hsplit]
  exact htail.symm



theorem d013203
    {beta p : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 2 beta p =
      p ^ 2 * _root_.GD.N0232.N0720.N1429.d013174 beta p := by
  unfold _root_.GD.N0232.N0720.N1091.d012790
  rw [_root_.GD.N0235.d004041
    (by norm_num : (0 : ℝ) < 2) hbeta]
  calc
    (∫ u : ℝ, betaPDFReal 2 beta u *
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u - p) ^ 2) =
        ∫ u : ℝ in Ioo (0 : ℝ) 1,
          betaPDFReal 2 beta u *
            (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 2 beta p) u - p) ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards with u hu
      have houtside : ¬(0 < u ∧ u < 1) := by
        simpa only [Set.mem_Ioo] using hu
      simp [betaPDFReal, houtside]
    _ = ∫ u : ℝ in Ioo (0 : ℝ) 1,
          p ^ 2 *
            (|_root_.GD.N0232.N0720.N1426.d013188 beta u| *
              _root_.GD.N0232.N0720.N1427.d013155 beta p
                (_root_.GD.N0232.N0720.N1426.d013187 beta u)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact
        _root_.GD.N0232.N0720.N1426.d013199
          hbeta hp0 hp1 hu
    _ = p ^ 2 *
        (∫ u : ℝ in Ioo (0 : ℝ) 1,
          |_root_.GD.N0232.N0720.N1426.d013188 beta u| *
            _root_.GD.N0232.N0720.N1427.d013155 beta p
              (_root_.GD.N0232.N0720.N1426.d013187 beta u)) := by
      rw [integral_const_mul]
    _ = p ^ 2 * _root_.GD.N0232.N0720.N1429.d013174 beta p := by
      rw [_root_.GD.N0232.N0720.N1426.d013200 hbeta]


theorem d013204
    {beta p : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 2 beta p / p ^ 2 =
      _root_.GD.N0232.N0720.N1429.d013174 beta p := by
  rw [_root_.GD.N0232.N0720.N1426.d013203
    hbeta hp0 hp1]
  field_simp [hp0.ne']



theorem d013205
    {beta p : ℝ} (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 2 beta p =
      p ^ 2 * _root_.GD.N0232.N0720.N1429.d013175 beta p := by
  rw [_root_.GD.N0232.N0720.N1426.d013203
    hbeta hp0 hp1,
    _root_.GD.N0232.N0720.N1426.d013202 hbeta hp0 hp1]



theorem d013206
    {beta : ℝ} (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1091.d012790 2 beta (p n) /
        ((p n) ^ 2 * Real.log (1 / p n)))
      atTop (nhds (_root_.GD.N0232.N0720.N1428.d013133 beta)) := by
  have hfull := _root_.GD.N0232.N0720.N1429.d013186
    hbeta hp hp0 hp1
  convert hfull using 1
  funext n
  rw [_root_.GD.N0232.N0720.N1426.d013205
    hbeta (hp0 n) (hp1 n)]
  field_simp [(hp0 n).ne']

end

end N1426
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1426.d013189
#print axioms _root_.GD.N0232.N0720.N1426.d013198
#print axioms _root_.GD.N0232.N0720.N1426.d013200
#print axioms _root_.GD.N0232.N0720.N1426.d013201
#print axioms _root_.GD.N0232.N0720.N1426.d013202
#print axioms _root_.GD.N0232.N0720.N1426.d013203
#print axioms _root_.GD.N0232.N0720.N1426.d013205
#print axioms _root_.GD.N0232.N0720.N1426.d013206
