import GD.Module0162
import GD.Module0223
import GD.Module0924
















open MeasureTheory ProbabilityTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1045

noncomputable section

open _root_.GD.N0232.N0720.N1044
open _root_.GD.N0232.N0720.N1050
open _root_.GD.N0232.N0720.N1071
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0107
open _root_.GD.N0232.N0720.N1080

private theorem d014432 :
    ProbabilityTheory.beta (1 / 2 : ℝ) (1 / 2) = Real.pi := by
  unfold ProbabilityTheory.beta
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsqrt : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    Real.Gamma_one_half_eq, Real.Gamma_one]
  field_simp [hpi, hsqrt]
  exact Real.sq_sqrt Real.pi_pos.le

private theorem d014433 :
    ProbabilityTheory.beta (1 / 2 : ℝ) (3 / 2) = Real.pi / 2 := by
  have hGammaThreeHalves :
      Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
      Real.Gamma_one_half_eq]
    ring
  unfold ProbabilityTheory.beta
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsqrt : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  rw [show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num,
    Real.Gamma_one_half_eq, hGammaThreeHalves, Real.Gamma_two]
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

private theorem d014434 :
    ProbabilityTheory.beta (1 / 2 : ℝ) (5 / 2) = 3 * Real.pi / 8 := by
  have hrec := _root_.GD.N0235.d004039
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 3 / 2 by norm_num)
  norm_num at hrec ⊢
  rw [_root_.GD.N0232.N0720.N1045.d014433] at hrec
  linarith


def d014435 (x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-1 : ℝ)

private theorem d014436
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1050.d003158 u| *
        _root_.GD.N0232.N0720.N1045.d014435 (_root_.GD.N0232.N0720.N1050.d003157 u) =
      u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (-(1 / 2 : ℝ)) := by
  have hu0 : 0 < u := hu.1
  have h1u : 0 < 1 - u := sub_pos.mpr hu.2
  have hone : 1 + _root_.GD.N0232.N0720.N1050.d003157 u = (1 - u)⁻¹ := by
    dsimp [_root_.GD.N0232.N0720.N1050.d003157]
    field_simp [ne_of_gt h1u]
    ring
  have hderiv : 0 < _root_.GD.N0232.N0720.N1050.d003158 u := by
    dsimp [_root_.GD.N0232.N0720.N1050.d003158]
    positivity
  rw [abs_of_pos hderiv]
  unfold _root_.GD.N0232.N0720.N1045.d014435
  rw [hone]
  dsimp [_root_.GD.N0232.N0720.N1050.d003157, _root_.GD.N0232.N0720.N1050.d003158]
  rw [Real.div_rpow hu0.le h1u.le,
    Real.inv_rpow h1u.le, ← Real.rpow_neg h1u.le]
  rw [div_eq_mul_inv]
  have hsquare : ((1 - u) ^ 2 : ℝ)⁻¹ = (1 - u) ^ (-2 : ℝ) := by
    simpa only [Real.rpow_two] using
      (Real.rpow_neg h1u.le (2 : ℝ)).symm
  rw [hsquare, div_eq_mul_inv, ← Real.rpow_neg h1u.le]
  have hcollect :
      (1 - u) ^ (-2 : ℝ) * (1 - u) ^ (-(-(1 / 2 : ℝ))) *
          (1 - u) ^ (-(-1 : ℝ)) =
        (1 - u) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add h1u, ← Real.rpow_add h1u]
    congr 1
    ring
  calc
    _ = u ^ (-(1 / 2 : ℝ)) *
        ((1 - u) ^ (-2 : ℝ) *
          (1 - u) ^ (-(-(1 / 2 : ℝ))) *
            (1 - u) ^ (-(-1 : ℝ))) := by ring
    _ = _ := by rw [hcollect]

private theorem d014437
    {c u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 c u = c / (_root_.GD.N0232.N0720.N1050.d003157 u + c) := by
  have h1u : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
  unfold _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0232.N0720.N1050.d003157
  field_simp [h1u]

private theorem d014438
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal (1 / 2 : ℝ) (1 / 2) u =
      (1 / Real.pi) *
        (u ^ (-(1 / 2 : ℝ)) *
          (1 - u) ^ (-(1 / 2 : ℝ))) := by
  rw [betaPDFReal, if_pos (by simpa only [mem_Ioo] using hu), _root_.GD.N0232.N0720.N1045.d014432]
  norm_num
  ring



theorem d014439
    (c : ℝ) (k : ℕ) :
    (∫ u, _root_.GD.N0232.N0720.N1091.d012763 c u ^ k ∂betaMeasure (1 / 2) (1 / 2)) =
      (1 / Real.pi) *
        ∫ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1045.d014435 x * (c / (x + c)) ^ k := by
  rw [_root_.GD.N0235.d004041
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)]
  have hrestrict :
      (∫ u, betaPDFReal (1 / 2 : ℝ) (1 / 2) u * _root_.GD.N0232.N0720.N1091.d012763 c u ^ k) =
        ∫ u in Ioo (0 : ℝ) 1,
          betaPDFReal (1 / 2 : ℝ) (1 / 2) u * _root_.GD.N0232.N0720.N1091.d012763 c u ^ k := by
    rw [← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simp only [Set.indicator, hu, if_true]
    · simp only [Set.indicator, hu, if_false]
      rw [betaPDFReal, if_neg (by simpa only [mem_Ioo] using hu)]
      simp
  rw [hrestrict]
  let g : ℝ → ℝ := fun x ↦
    _root_.GD.N0232.N0720.N1045.d014435 x * (c / (x + c)) ^ k
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo _root_.GD.N0232.N0720.N1050.d003160
      _root_.GD.N0232.N0720.N1050.d003161 g
  rw [_root_.GD.N0232.N0720.N1050.d003159] at hcov
  calc
    (∫ u in Ioo (0 : ℝ) 1,
        betaPDFReal (1 / 2 : ℝ) (1 / 2) u * _root_.GD.N0232.N0720.N1091.d012763 c u ^ k) =
        ∫ u in Ioo (0 : ℝ) 1,
          (1 / Real.pi) *
            (|_root_.GD.N0232.N0720.N1050.d003158 u| * g (_root_.GD.N0232.N0720.N1050.d003157 u)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      change betaPDFReal (1 / 2 : ℝ) (1 / 2) u * _root_.GD.N0232.N0720.N1091.d012763 c u ^ k =
        (1 / Real.pi) *
          (|_root_.GD.N0232.N0720.N1050.d003158 u| * g (_root_.GD.N0232.N0720.N1050.d003157 u))
      rw [_root_.GD.N0232.N0720.N1045.d014438 hu,
        _root_.GD.N0232.N0720.N1045.d014437 hu]
      dsimp only [g]
      rw [← _root_.GD.N0232.N0720.N1045.d014436 u hu]
      ring
    _ = (1 / Real.pi) *
        ∫ u in Ioo (0 : ℝ) 1,
          |_root_.GD.N0232.N0720.N1050.d003158 u| * g (_root_.GD.N0232.N0720.N1050.d003157 u) := by
      rw [integral_const_mul]
    _ = (1 / Real.pi) * ∫ x in Ioi (0 : ℝ), g x := by
      rw [hcov]
      rfl
    _ = _ := rfl



def d014440 (c x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) * (x + c) ^ (-1 : ℝ)

def d014441 (c x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) * (x + c) ^ (-2 : ℝ)

private theorem d014442
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1045.d014440 c (c * x) =
      c ^ (-(3 / 2 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-1 : ℝ)) := by
  have h1x : 0 ≤ 1 + x := by positivity
  have hfactor : c * x + c = c * (1 + x) := by ring
  unfold _root_.GD.N0232.N0720.N1045.d014440
  rw [hfactor, Real.mul_rpow hc.le hx.le,
    Real.mul_rpow hc.le h1x]
  have hcollect :
      c ^ (-(1 / 2 : ℝ)) * c ^ (-1 : ℝ) =
        c ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hc]
    congr 1
    ring
  calc
    _ = (c ^ (-(1 / 2 : ℝ)) * c ^ (-1 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-1 : ℝ)) := by ring
    _ = _ := by rw [hcollect]

private theorem d014443
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1045.d014441 c (c * x) =
      c ^ (-(5 / 2 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-2 : ℝ)) := by
  have h1x : 0 ≤ 1 + x := by positivity
  have hfactor : c * x + c = c * (1 + x) := by ring
  unfold _root_.GD.N0232.N0720.N1045.d014441
  rw [hfactor, Real.mul_rpow hc.le hx.le,
    Real.mul_rpow hc.le h1x]
  have hcollect :
      c ^ (-(1 / 2 : ℝ)) * c ^ (-2 : ℝ) =
        c ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_add hc]
    congr 1
    ring
  calc
    _ = (c ^ (-(1 / 2 : ℝ)) * c ^ (-2 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-2 : ℝ)) := by ring
    _ = _ := by rw [hcollect]

theorem d014444
    {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 c x) =
      c ^ (-(1 / 2 : ℝ)) * Real.pi := by
  have hscaled :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 c (c * x)) =
        c ^ (-(3 / 2 : ℝ)) * Real.pi := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          c ^ (-(3 / 2 : ℝ)) *
            (x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-1 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact _root_.GD.N0232.N0720.N1045.d014442 hc hx
      _ = c ^ (-(3 / 2 : ℝ)) *
          ∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-1 : ℝ) := by
        rw [integral_const_mul]
      _ = c ^ (-(3 / 2 : ℝ)) *
          ProbabilityTheory.beta (1 / 2) (1 / 2) := by
        congr 1
        convert _root_.GD.N0232.N0720.N1050.d003164 (1 / 2 : ℝ) (1 / 2)
          (by norm_num) (by norm_num) using 1
        all_goals norm_num
      _ = _ := by rw [_root_.GD.N0232.N0720.N1045.d014432]
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (_root_.GD.N0232.N0720.N1045.d014440 c) 0 hc
  simp only [mul_zero, smul_eq_mul] at hscale
  have hrecover :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 c x) =
        c * ∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 c (c * x) := by
    rw [hscale]
    field_simp [hc.ne']
  rw [hrecover, hscaled]
  have hcollect :
      c * c ^ (-(3 / 2 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
    calc
      c * c ^ (-(3 / 2 : ℝ)) =
          c ^ (1 : ℝ) * c ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = c ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := by
        rw [Real.rpow_add hc]
      _ = _ := by congr 1; ring
  calc
    c * (c ^ (-(3 / 2 : ℝ)) * Real.pi) =
        (c * c ^ (-(3 / 2 : ℝ))) * Real.pi := by ring
    _ = _ := by rw [hcollect]

theorem d014445
    {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014441 c x) =
      c ^ (-(3 / 2 : ℝ)) * (Real.pi / 2) := by
  have hscaled :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014441 c (c * x)) =
        c ^ (-(5 / 2 : ℝ)) * (Real.pi / 2) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          c ^ (-(5 / 2 : ℝ)) *
            (x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact _root_.GD.N0232.N0720.N1045.d014443 hc hx
      _ = c ^ (-(5 / 2 : ℝ)) *
          ∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * (1 + x) ^ (-2 : ℝ) := by
        rw [integral_const_mul]
      _ = c ^ (-(5 / 2 : ℝ)) *
          ProbabilityTheory.beta (1 / 2) (3 / 2) := by
        congr 1
        convert _root_.GD.N0232.N0720.N1050.d003164 (1 / 2 : ℝ) (3 / 2)
          (by norm_num) (by norm_num) using 1
        all_goals norm_num
      _ = _ := by rw [_root_.GD.N0232.N0720.N1045.d014433]
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (_root_.GD.N0232.N0720.N1045.d014441 c) 0 hc
  simp only [mul_zero, smul_eq_mul] at hscale
  have hrecover :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014441 c x) =
        c * ∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014441 c (c * x) := by
    rw [hscale]
    field_simp [hc.ne']
  rw [hrecover, hscaled]
  have hcollect :
      c * c ^ (-(5 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) := by
    calc
      c * c ^ (-(5 / 2 : ℝ)) =
          c ^ (1 : ℝ) * c ^ (-(5 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = c ^ ((1 : ℝ) + -(5 / 2 : ℝ)) := by
        rw [Real.rpow_add hc]
      _ = _ := by congr 1; ring
  calc
    c * (c ^ (-(5 / 2 : ℝ)) * (Real.pi / 2)) =
        (c * c ^ (-(5 / 2 : ℝ))) * (Real.pi / 2) := by ring
    _ = _ := by rw [hcollect]

theorem d014446
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (_root_.GD.N0232.N0720.N1045.d014440 c) (Ioi (0 : ℝ)) := by
  by_contra hnot
  have hzero :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 c x) = 0 :=
    integral_undef hnot
  rw [_root_.GD.N0232.N0720.N1045.d014444 hc] at hzero
  exact (mul_pos (Real.rpow_pos_of_pos hc _) Real.pi_pos).ne' hzero

theorem d014447
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (_root_.GD.N0232.N0720.N1045.d014441 c) (Ioi (0 : ℝ)) := by
  by_contra hnot
  have hzero :
      (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014441 c x) = 0 :=
    integral_undef hnot
  rw [_root_.GD.N0232.N0720.N1045.d014445 hc] at hzero
  exact (mul_pos (Real.rpow_pos_of_pos hc _) (half_pos Real.pi_pos)).ne' hzero

private theorem d014448
    {rho : ℝ} (hrho : 0 < rho) :
    (rho ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / rho := by
  rw [Real.rpow_neg (sq_nonneg rho), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq_eq_abs, abs_of_pos hrho]
  simp only [one_div]

private theorem d014449
    {rho : ℝ} (hrho : 0 < rho) :
    (rho ^ 2) ^ (-(3 / 2 : ℝ)) = 1 / rho ^ 3 := by
  rw [Real.rpow_neg (sq_nonneg rho),
    show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add (sq_pos_of_pos hrho), Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hrho]
  field_simp [hrho.ne']

private theorem d014450
    {c x : ℝ} (hc : 0 < c) (hc1 : c ≠ 1) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1045.d014435 x * (c / (x + c)) =
      (c / (c - 1)) *
        (_root_.GD.N0232.N0720.N1045.d014440 1 x - _root_.GD.N0232.N0720.N1045.d014440 c x) := by
  have hx1 : x + 1 ≠ 0 := by linarith
  have hxc : x + c ≠ 0 := by linarith
  have hcsub : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  unfold _root_.GD.N0232.N0720.N1045.d014435 _root_.GD.N0232.N0720.N1045.d014440
  simp only [Real.rpow_neg_one]
  field_simp [hx1, hxc, hcsub]
  ring

private theorem d014451
    {c x : ℝ} (hc : 0 < c) (hc1 : c ≠ 1) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1045.d014435 x * (c / (x + c)) ^ 2 =
      (c ^ 2 / (c - 1) ^ 2) * _root_.GD.N0232.N0720.N1045.d014440 1 x -
        (c ^ 2 / (c - 1) ^ 2) * _root_.GD.N0232.N0720.N1045.d014440 c x -
          (c ^ 2 / (c - 1)) * _root_.GD.N0232.N0720.N1045.d014441 c x := by
  have hx1 : x + 1 ≠ 0 := by linarith
  have hxc : x + c ≠ 0 := by linarith
  have hcsub : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  unfold _root_.GD.N0232.N0720.N1045.d014435 _root_.GD.N0232.N0720.N1045.d014440 _root_.GD.N0232.N0720.N1045.d014441
  simp only [Real.rpow_neg_one]
  rw [Real.rpow_neg (by positivity : 0 ≤ x + c), Real.rpow_two]
  field_simp [hx1, hxc, hcsub]
  ring



private theorem d014452 :
    (∫ u, _root_.GD.N0232.N0720.N1091.d012763 1 u ∂betaMeasure (1 / 2) (1 / 2)) = 1 / 2 := by
  have hmoment := _root_.GD.N0235.d004044
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) 0 1
  calc
    (∫ u, _root_.GD.N0232.N0720.N1091.d012763 1 u ∂betaMeasure (1 / 2) (1 / 2)) =
        ∫ u, u ^ 0 * (1 - u) ^ 1
          ∂betaMeasure (1 / 2) (1 / 2) := by
      apply integral_congr_ae
      filter_upwards with u
      simp [_root_.GD.N0232.N0720.N1091.d012763]
    _ = ProbabilityTheory.beta (1 / 2 + 0) (1 / 2 + 1) /
          ProbabilityTheory.beta (1 / 2) (1 / 2) := by
      simpa using hmoment
    _ = _ := by
      norm_num
      rw [_root_.GD.N0232.N0720.N1045.d014433, _root_.GD.N0232.N0720.N1045.d014432]
      field_simp [Real.pi_ne_zero]

private theorem d014453 :
    (∫ u, _root_.GD.N0232.N0720.N1091.d012763 1 u ^ 2 ∂betaMeasure (1 / 2) (1 / 2)) = 3 / 8 := by
  have hmoment := _root_.GD.N0235.d004044
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) 0 2
  calc
    (∫ u, _root_.GD.N0232.N0720.N1091.d012763 1 u ^ 2 ∂betaMeasure (1 / 2) (1 / 2)) =
        ∫ u, u ^ 0 * (1 - u) ^ 2
          ∂betaMeasure (1 / 2) (1 / 2) := by
      apply integral_congr_ae
      filter_upwards with u
      simp [_root_.GD.N0232.N0720.N1091.d012763]
    _ = ProbabilityTheory.beta (1 / 2 + 0) (1 / 2 + 2) /
          ProbabilityTheory.beta (1 / 2) (1 / 2) := by
      simpa using hmoment
    _ = _ := by
      norm_num
      rw [_root_.GD.N0232.N0720.N1045.d014434, _root_.GD.N0232.N0720.N1045.d014432]
      field_simp [Real.pi_ne_zero]


theorem d014454
    {rho : ℝ} (hrho : 0 < rho) :
    (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u
      ∂betaMeasure (1 / 2) (1 / 2)) = rho / (1 + rho) := by
  by_cases hrhoOne : rho = 1
  · subst rho
    norm_num
    exact _root_.GD.N0232.N0720.N1045.d014452
  have hc : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hc1 : rho ^ 2 ≠ 1 := by
    intro h
    have hsqrt := congrArg Real.sqrt h
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrho] at hsqrt
    norm_num at hsqrt
    exact hrhoOne hsqrt
  have htransfer :=
    _root_.GD.N0232.N0720.N1045.d014439 (rho ^ 2) 1
  simp only [pow_one] at htransfer
  rw [htransfer]
  have htarget :
      (∫ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1045.d014435 x * (rho ^ 2 / (x + rho ^ 2))) =
        (rho ^ 2 / (rho ^ 2 - 1)) *
          ((∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 1 x) -
            ∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 (rho ^ 2) x) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          (rho ^ 2 / (rho ^ 2 - 1)) *
            (_root_.GD.N0232.N0720.N1045.d014440 1 x - _root_.GD.N0232.N0720.N1045.d014440 (rho ^ 2) x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact _root_.GD.N0232.N0720.N1045.d014450 hc hc1 hx
      _ = _ := by
        rw [integral_const_mul,
          integral_sub (_root_.GD.N0232.N0720.N1045.d014446 (by norm_num))
            (_root_.GD.N0232.N0720.N1045.d014446 hc)]
  rw [htarget, _root_.GD.N0232.N0720.N1045.d014444 (by norm_num),
    _root_.GD.N0232.N0720.N1045.d014444 hc, _root_.GD.N0232.N0720.N1045.d014448 hrho]
  field_simp [Real.pi_ne_zero, hrho.ne', hc1,
    show 1 + rho ≠ 0 by linarith]
  ring


theorem d014455
    {rho : ℝ} (hrho : 0 < rho) :
    (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2
      ∂betaMeasure (1 / 2) (1 / 2)) =
      rho * (2 * rho + 1) / (2 * (1 + rho) ^ 2) := by
  by_cases hrhoOne : rho = 1
  · subst rho
    norm_num
    exact _root_.GD.N0232.N0720.N1045.d014453
  have hc : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hc1 : rho ^ 2 ≠ 1 := by
    intro h
    have hsqrt := congrArg Real.sqrt h
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrho] at hsqrt
    norm_num at hsqrt
    exact hrhoOne hsqrt
  rw [_root_.GD.N0232.N0720.N1045.d014439 (rho ^ 2) 2]
  let A : ℝ := rho ^ 4 / (rho ^ 2 - 1) ^ 2
  let C : ℝ := rho ^ 4 / (rho ^ 2 - 1)
  have hA1 : IntegrableOn (fun x ↦ A * _root_.GD.N0232.N0720.N1045.d014440 1 x)
      (Ioi (0 : ℝ)) :=
    (_root_.GD.N0232.N0720.N1045.d014446 (by norm_num)).const_mul A
  have hAc : IntegrableOn (fun x ↦ A * _root_.GD.N0232.N0720.N1045.d014440 (rho ^ 2) x)
      (Ioi (0 : ℝ)) :=
    (_root_.GD.N0232.N0720.N1045.d014446 hc).const_mul A
  have hCc : IntegrableOn (fun x ↦ C * _root_.GD.N0232.N0720.N1045.d014441 (rho ^ 2) x)
      (Ioi (0 : ℝ)) :=
    (_root_.GD.N0232.N0720.N1045.d014447 hc).const_mul C
  have htarget :
      (∫ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1045.d014435 x * (rho ^ 2 / (x + rho ^ 2)) ^ 2) =
        A * (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 1 x) -
          A * (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014440 (rho ^ 2) x) -
            C * (∫ x in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1045.d014441 (rho ^ 2) x) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          A * _root_.GD.N0232.N0720.N1045.d014440 1 x - A * _root_.GD.N0232.N0720.N1045.d014440 (rho ^ 2) x -
            C * _root_.GD.N0232.N0720.N1045.d014441 (rho ^ 2) x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only [A, C]
        convert _root_.GD.N0232.N0720.N1045.d014451 hc hc1 hx using 1
        all_goals ring
      _ = _ := by
        calc
          _ = (∫ x in Ioi (0 : ℝ),
                A * _root_.GD.N0232.N0720.N1045.d014440 1 x -
                  A * _root_.GD.N0232.N0720.N1045.d014440 (rho ^ 2) x) -
              ∫ x in Ioi (0 : ℝ),
                C * _root_.GD.N0232.N0720.N1045.d014441 (rho ^ 2) x := by
            simpa using integral_sub (hA1.sub hAc) hCc
          _ = ((∫ x in Ioi (0 : ℝ), A * _root_.GD.N0232.N0720.N1045.d014440 1 x) -
                ∫ x in Ioi (0 : ℝ),
                  A * _root_.GD.N0232.N0720.N1045.d014440 (rho ^ 2) x) -
              ∫ x in Ioi (0 : ℝ),
                C * _root_.GD.N0232.N0720.N1045.d014441 (rho ^ 2) x := by
            rw [integral_sub hA1 hAc]
          _ = _ := by
            rw [integral_const_mul, integral_const_mul,
              integral_const_mul]
  rw [htarget, _root_.GD.N0232.N0720.N1045.d014444 (by norm_num),
    _root_.GD.N0232.N0720.N1045.d014444 hc, _root_.GD.N0232.N0720.N1045.d014445 hc,
    _root_.GD.N0232.N0720.N1045.d014448 hrho, _root_.GD.N0232.N0720.N1045.d014449 hrho]
  dsimp only [A, C]
  field_simp [Real.pi_ne_zero, hrho.ne', hc1,
    show 1 + rho ≠ 0 by linarith]
  ring

theorem d014456
    {rho : ℝ} (hrho : 0 < rho) :
    Integrable (fun u ↦ _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u)
      (betaMeasure (1 / 2) (1 / 2)) := by
  by_contra hnot
  have hzero :
      (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u
        ∂betaMeasure (1 / 2) (1 / 2)) = 0 := integral_undef hnot
  rw [_root_.GD.N0232.N0720.N1045.d014454 hrho] at hzero
  exact (div_pos hrho (by linarith)).ne' hzero

theorem d014457
    {rho : ℝ} (hrho : 0 < rho) :
    Integrable (fun u ↦ _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2)
      (betaMeasure (1 / 2) (1 / 2)) := by
  by_contra hnot
  have hzero :
      (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2
        ∂betaMeasure (1 / 2) (1 / 2)) = 0 := integral_undef hnot
  rw [_root_.GD.N0232.N0720.N1045.d014455 hrho] at hzero
  exact (div_pos (mul_pos hrho (by linarith)) (by positivity)).ne' hzero

private theorem d014458
    {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2)
        (rho ^ 2 / (1 + rho ^ 2)) = rho ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1091.d012762
  field_simp [show 1 + rho ^ 2 ≠ 0 by positivity,
    show (1 / 2 : ℝ) ≠ 0 by norm_num]
  ring



theorem d014459
    {rho : ℝ} (hrho : 0 < rho) :
    _root_.GD.N0232.N0720.N1091.d012790 (1 / 2) (1 / 2)
        (rho ^ 2 / (1 + rho ^ 2)) =
      rho * (rho ^ 4 + 2 * rho ^ 3 - 2 * rho ^ 2 + 2 * rho + 1) /
        (2 * (rho + 1) ^ 2 * (rho ^ 2 + 1) ^ 2) := by
  let p : ℝ := rho ^ 2 / (1 + rho ^ 2)
  letI : IsProbabilityMeasure (betaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  have hW := _root_.GD.N0232.N0720.N1045.d014456 hrho
  have hW2 := _root_.GD.N0232.N0720.N1045.d014457 hrho
  have hpoint (u : ℝ) :
      (_root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u - p) ^ 2 =
        _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2 -
          (2 * p) * _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u + p ^ 2 := by ring
  unfold _root_.GD.N0232.N0720.N1091.d012790
  rw [_root_.GD.N0232.N0720.N1045.d014458 hrho]
  change (∫ u, (_root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u - p) ^ 2
    ∂betaMeasure (1 / 2) (1 / 2)) = _
  simp_rw [hpoint]
  have hdecomp :
      (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2 -
          (2 * p) * _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u + p ^ 2
        ∂betaMeasure (1 / 2) (1 / 2)) =
        (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2
          ∂betaMeasure (1 / 2) (1 / 2)) -
          (2 * p) * (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u
            ∂betaMeasure (1 / 2) (1 / 2)) + p ^ 2 := by
    calc
      _ = (∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2 -
              (2 * p) * _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u
            ∂betaMeasure (1 / 2) (1 / 2)) +
          ∫ _u, p ^ 2 ∂betaMeasure (1 / 2) (1 / 2) := by
        simpa using integral_add (hW2.sub (hW.const_mul (2 * p)))
          (integrable_const (p ^ 2))
      _ = ((∫ u, _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u ^ 2
              ∂betaMeasure (1 / 2) (1 / 2)) -
            ∫ u, (2 * p) * _root_.GD.N0232.N0720.N1091.d012763 (rho ^ 2) u
              ∂betaMeasure (1 / 2) (1 / 2)) +
          ∫ _u, p ^ 2 ∂betaMeasure (1 / 2) (1 / 2) := by
        rw [integral_sub hW2 (hW.const_mul (2 * p))]
      _ = _ := by
        rw [integral_const_mul, integral_const, probReal_univ]
        simp
  rw [hdecomp, _root_.GD.N0232.N0720.N1045.d014454 hrho,
    _root_.GD.N0232.N0720.N1045.d014455 hrho]
  dsimp only [p]
  field_simp [show 1 + rho ≠ 0 by linarith,
    show rho ^ 2 + 1 ≠ 0 by positivity]
  ring



def d014460 (mu rho : ℝ) (hrho : 0 < rho) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := mu
  scale₁ := 1
  scale₂ := rho
  scale₁_pos := zero_lt_one
  scale₂_pos := hrho






theorem d014461
    (mu rho : ℝ) (hrho : 0 < rho) :
    (_root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega)
      (_root_.GD.N0232.N0720.N1045.d014460 mu rho hrho)).toReal =
        rho * (rho ^ 2 + 4 * rho + 1) /
          (4 * (rho + 1) ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1071.d014427]
  change _root_.GD.N0107.d009045 2 2 1 rho *
      _root_.GD.N0232.N0720.N1442.d013867
        (_root_.GD.N0232.N0720.N1433.d014024 2) (_root_.GD.N0232.N0720.N1433.d014025 2)
        (_root_.GD.N0232.N0720.N1067.d014408 2 2
          (_root_.GD.N0232.N0720.N1045.d014460 mu rho hrho)) = _
  have hSigma : _root_.GD.N0107.d009045 2 2 1 rho = (rho ^ 2 + 1) / 2 := by
    norm_num [_root_.GD.N0107.d009045, _root_.GD.N0107.d009043, _root_.GD.N0107.d009044]
    ring
  have hp : _root_.GD.N0232.N0720.N1067.d014408 2 2
      (_root_.GD.N0232.N0720.N1045.d014460 mu rho hrho) = rho ^ 2 / (rho ^ 2 + 1) := by
    norm_num [_root_.GD.N0232.N0720.N1067.d014408, _root_.GD.N0232.N0720.N1045.d014460,
      _root_.GD.N0107.d009046, _root_.GD.N0107.d009045, _root_.GD.N0107.d009043,
      _root_.GD.N0107.d009044]
    field_simp [show rho ^ 2 + 1 ≠ 0 by positivity]
    ring
  rw [hSigma, hp]
  norm_num [_root_.GD.N0232.N0720.N1433.d014024, _root_.GD.N0232.N0720.N1433.d014025]
  unfold _root_.GD.N0232.N0720.N1442.d013867 _root_.GD.N0232.N0720.N1442.d013866
  rw [show rho ^ 2 / (rho ^ 2 + 1) =
      rho ^ 2 / (1 + rho ^ 2) by ring,
    _root_.GD.N0232.N0720.N1045.d014459 hrho]
  field_simp [show rho ^ 2 + 1 ≠ 0 by positivity,
    show rho + 1 ≠ 0 by linarith]
  ring

end

end N1045
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1045.d014454
#print axioms _root_.GD.N0232.N0720.N1045.d014455
#print axioms _root_.GD.N0232.N0720.N1045.d014459
#print axioms _root_.GD.N0232.N0720.N1045.d014461
