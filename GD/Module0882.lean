import GD.Module0859
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic






























open Filter MeasureTheory ProbabilityTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1439

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1050
open _root_.GD.N0232.N0720.N1421
open _root_.GD.N0232.N0720.N1428
open _root_.GD.N0232.N0720.N1427




def d013613 (alpha beta u : ℝ) : ℝ :=
  (beta / alpha) * _root_.GD.N0232.N0720.N1050.d003157 u


def d013614 (alpha beta u : ℝ) : ℝ :=
  (beta / alpha) * _root_.GD.N0232.N0720.N1050.d003158 u


def d013615 (alpha beta : ℝ) : ℝ :=
  (alpha / beta) ^ alpha / ProbabilityTheory.beta alpha beta


def d013616 (alpha beta X : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1439.d013615 alpha beta * X ^ (alpha - 1) *
    (beta / (beta + alpha * X)) ^ (alpha + beta)


def d013617 (alpha beta p X : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1439.d013616 alpha beta X *
    _root_.GD.N0232.N0720.N1428.d013136 p X ^ 2

theorem d013618
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1439.d013613 alpha beta '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  have hscale : 0 < beta / alpha := div_pos hbeta halpha
  ext X
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact mul_pos hscale (div_pos hu.1 (sub_pos.mpr hu.2))
  · intro hX
    have hX0 : 0 < X := hX
    let u := alpha * X / (beta + alpha * X)
    have hden : 0 < beta + alpha * X := by positivity
    have hu0 : 0 < u := by
      dsimp [u]
      exact div_pos (mul_pos halpha hX0) hden
    have hu1 : u < 1 := by
      dsimp [u]
      rw [div_lt_one hden]
      linarith
    refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
    unfold _root_.GD.N0232.N0720.N1439.d013613 _root_.GD.N0232.N0720.N1050.d003157
    dsimp [u]
    field_simp [halpha.ne', hbeta.ne', hden.ne']
    ring

theorem d013619
    {alpha beta u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (_root_.GD.N0232.N0720.N1439.d013613 alpha beta)
      (_root_.GD.N0232.N0720.N1439.d013614 alpha beta u) (Ioo 0 1) u := by
  convert! (_root_.GD.N0232.N0720.N1050.d003160 u hu).const_mul
    (beta / alpha) using 1

theorem d013620
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    InjOn (_root_.GD.N0232.N0720.N1439.d013613 alpha beta) (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  have hscale : beta / alpha ≠ 0 := (div_pos hbeta halpha).ne'
  unfold _root_.GD.N0232.N0720.N1439.d013613 at huv
  apply _root_.GD.N0232.N0720.N1050.d003161 hu hv
  exact mul_left_cancel₀ hscale huv

theorem d013621
    {alpha beta u : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1439.d013613 alpha beta u := by
  unfold _root_.GD.N0232.N0720.N1439.d013613 _root_.GD.N0232.N0720.N1050.d003157
  exact mul_pos (div_pos hbeta halpha)
    (div_pos hu.1 (sub_pos.mpr hu.2))

theorem d013622
    {alpha beta u : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1439.d013614 alpha beta u := by
  unfold _root_.GD.N0232.N0720.N1439.d013614 _root_.GD.N0232.N0720.N1050.d003158
  exact mul_pos (div_pos hbeta halpha)
    (one_div_pos.mpr (sq_pos_of_pos (sub_pos.mpr hu.2)))



theorem d013623
    {alpha beta p u : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u =
      p / ((1 - p) * _root_.GD.N0232.N0720.N1439.d013613 alpha beta u + p) := by
  have h1u : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
  have h1p : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have hleftDen :
      u + _root_.GD.N0232.N0720.N1091.d012762 alpha beta p * (1 - u) ≠ 0 :=
    (_root_.GD.N0232.N0720.N1091.d012779
      (_root_.GD.N0232.N0720.N1091.d012778 halpha hbeta hp0 hp1) hu.1 hu.2).ne'
  have hrightDen :
      (1 - p) * _root_.GD.N0232.N0720.N1439.d013613 alpha beta u + p ≠ 0 :=
    (add_pos
      (mul_pos (sub_pos.mpr hp1)
        (_root_.GD.N0232.N0720.N1439.d013621 halpha hbeta hu)) hp0).ne'
  unfold _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0232.N0720.N1091.d012762 _root_.GD.N0232.N0720.N1439.d013613 _root_.GD.N0232.N0720.N1050.d003157
  field_simp [halpha.ne', hbeta.ne', h1u, h1p, hleftDen, hrightDen]

theorem d013624
    {alpha beta p u : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p =
      p * _root_.GD.N0232.N0720.N1428.d013136 p
        (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u) := by
  have hrightDen :
      (1 - p) * _root_.GD.N0232.N0720.N1439.d013613 alpha beta u + p ≠ 0 :=
    (add_pos
      (mul_pos (sub_pos.mpr hp1)
        (_root_.GD.N0232.N0720.N1439.d013621 halpha hbeta hu)) hp0).ne'
  rw [_root_.GD.N0232.N0720.N1439.d013623
    halpha hbeta hp0 hp1 hu]
  unfold _root_.GD.N0232.N0720.N1428.d013136
  field_simp [hrightDen]
  ring


theorem d013625
    {alpha beta u : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    beta / (beta + alpha * _root_.GD.N0232.N0720.N1439.d013613 alpha beta u) = 1 - u := by
  have h1u : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
  unfold _root_.GD.N0232.N0720.N1439.d013613 _root_.GD.N0232.N0720.N1050.d003157
  field_simp [halpha.ne', hbeta.ne', h1u]
  ring



theorem d013626
    {alpha beta u : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal alpha beta u =
      |_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
        _root_.GD.N0232.N0720.N1439.d013616 alpha beta
          (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u) := by
  have hu0 : 0 < u := hu.1
  have h1u : 0 < 1 - u := sub_pos.mpr hu.2
  have hderiv : 0 < _root_.GD.N0232.N0720.N1439.d013614 alpha beta u :=
    _root_.GD.N0232.N0720.N1439.d013622 halpha hbeta hu
  have hratio := _root_.GD.N0232.N0720.N1439.d013625 halpha hbeta hu
  have hscale : 0 < beta / alpha := div_pos hbeta halpha
  have hscaleInv : 0 < alpha / beta := div_pos halpha hbeta
  have hcollect :
      (1 - u) ^ (alpha + beta) =
        (1 - u) ^ (alpha + 1) * (1 - u) ^ (beta - 1) := by
    rw [← Real.rpow_add h1u]
    congr 1
    ring
  rw [betaPDFReal, if_pos ⟨hu.1, hu.2⟩, abs_of_pos hderiv]
  unfold _root_.GD.N0232.N0720.N1439.d013616 _root_.GD.N0232.N0720.N1439.d013615
  rw [hratio, hcollect]
  unfold _root_.GD.N0232.N0720.N1439.d013613 _root_.GD.N0232.N0720.N1439.d013614 _root_.GD.N0232.N0720.N1050.d003157
    _root_.GD.N0232.N0720.N1050.d003158
  rw [Real.mul_rpow hscale.le (div_nonneg hu0.le h1u.le),
    Real.div_rpow hu0.le h1u.le]
  have hpowScale :
      (alpha / beta) ^ alpha * (beta / alpha) ^ (alpha - 1) =
        alpha / beta := by
    rw [show beta / alpha = (alpha / beta)⁻¹ by
      field_simp [halpha.ne', hbeta.ne']]
    rw [Real.inv_rpow hscaleInv.le, ← Real.rpow_neg hscaleInv.le,
      ← Real.rpow_add hscaleInv]
    convert Real.rpow_one (alpha / beta) using 1 <;> ring
  have hpowScale' :
      (alpha * beta⁻¹) ^ alpha * (beta * alpha⁻¹) ^ (alpha - 1) =
        alpha * beta⁻¹ := by
    simpa only [div_eq_mul_inv] using hpowScale
  have hcoeff :
      beta * (alpha * beta⁻¹) ^ alpha *
          (beta * alpha⁻¹) ^ (alpha - 1) = alpha := by
    rw [mul_assoc, hpowScale']
    field_simp [hbeta.ne']
  have hpowStep :
      (1 - u) ^ (alpha + 1) =
        (1 - u) ^ (alpha - 1) * (1 - u) ^ (2 : ℝ) := by
    rw [← Real.rpow_add h1u]
    congr 1
    ring
  field_simp [halpha.ne', hbeta.ne', h1u.ne',
    (ProbabilityTheory.beta_pos halpha hbeta).ne']
  ring_nf
  rw [show -1 + alpha = alpha - 1 by ring, hcoeff,
    show 1 + alpha = alpha + 1 by ring, hpowStep, Real.rpow_two]
  ring



theorem d013627
    {alpha beta p u : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal alpha beta u *
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2 =
      p ^ 2 *
        (|_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
          _root_.GD.N0232.N0720.N1439.d013617 alpha beta p
            (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u)) := by
  rw [_root_.GD.N0232.N0720.N1439.d013626
      halpha hbeta hu,
    _root_.GD.N0232.N0720.N1439.d013624
      halpha hbeta hp0 hp1 hu]
  unfold _root_.GD.N0232.N0720.N1439.d013617
  ring

theorem d013628 (alpha beta : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1439.d013616 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1439.d013616 _root_.GD.N0232.N0720.N1439.d013615
  fun_prop

theorem d013629 (alpha beta p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1439.d013617 alpha beta p) := by
  unfold _root_.GD.N0232.N0720.N1439.d013617 _root_.GD.N0232.N0720.N1428.d013136
  exact (_root_.GD.N0232.N0720.N1439.d013628 alpha beta).mul
    ((by fun_prop : Measurable
      (fun X : ℝ => (1 - p) * (1 - X) / ((1 - p) * X + p))).pow_const 2)

theorem d013630
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1439.d013615 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1439.d013615
  exact div_pos (Real.rpow_pos_of_pos (div_pos halpha hbeta) _)
    (ProbabilityTheory.beta_pos halpha hbeta)

theorem d013631
    {alpha beta X : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hX : 0 ≤ X) :
    0 ≤ _root_.GD.N0232.N0720.N1439.d013616 alpha beta X := by
  have hden : 0 < beta + alpha * X := by positivity
  unfold _root_.GD.N0232.N0720.N1439.d013616
  exact mul_nonneg
    (mul_nonneg (_root_.GD.N0232.N0720.N1439.d013630 halpha hbeta).le
      (Real.rpow_nonneg hX _))
    (Real.rpow_nonneg (div_nonneg hbeta.le hden.le) _)

theorem d013632
    {alpha beta p X : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hX : 0 ≤ X) :
    0 ≤ _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X := by
  unfold _root_.GD.N0232.N0720.N1439.d013617
  exact mul_nonneg
    (_root_.GD.N0232.N0720.N1439.d013631 halpha hbeta hX) (sq_nonneg _)



theorem d013633
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ X : ℝ in Ioi (0 : ℝ),
        _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X) =
      ∫ u : ℝ in Ioo (0 : ℝ) 1,
        |_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
          _root_.GD.N0232.N0720.N1439.d013617 alpha beta p
            (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u) := by
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo
    (fun u hu => _root_.GD.N0232.N0720.N1439.d013619
      (alpha := alpha) (beta := beta) hu)
    (_root_.GD.N0232.N0720.N1439.d013620 halpha hbeta)
    (_root_.GD.N0232.N0720.N1439.d013617 alpha beta p)
  rw [_root_.GD.N0232.N0720.N1439.d013618 halpha hbeta] at hcov
  simpa only [smul_eq_mul] using hcov

theorem d013634
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ X : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1439.d013616 alpha beta X) =
      ∫ u : ℝ in Ioo (0 : ℝ) 1,
        |_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
          _root_.GD.N0232.N0720.N1439.d013616 alpha beta
            (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u) := by
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo
    (fun u hu => _root_.GD.N0232.N0720.N1439.d013619
      (alpha := alpha) (beta := beta) hu)
    (_root_.GD.N0232.N0720.N1439.d013620 halpha hbeta)
    (_root_.GD.N0232.N0720.N1439.d013616 alpha beta)
  rw [_root_.GD.N0232.N0720.N1439.d013618 halpha hbeta] at hcov
  simpa only [smul_eq_mul] using hcov

theorem d013635
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IntegrableOn (_root_.GD.N0232.N0720.N1439.d013616 alpha beta) (Ioi (0 : ℝ)) := by
  have hsource : Integrable (betaPDFReal alpha beta) :=
    _root_.GD.N0232.N0720.N1091.d012772 halpha hbeta
  have hchart : IntegrableOn
      (fun u : ℝ => |_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
        _root_.GD.N0232.N0720.N1439.d013616 alpha beta
          (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u))
      (Ioo (0 : ℝ) 1) := by
    apply IntegrableOn.congr_fun hsource.integrableOn _ measurableSet_Ioo
    intro u hu
    exact _root_.GD.N0232.N0720.N1439.d013626
      halpha hbeta hu
  rw [← _root_.GD.N0232.N0720.N1439.d013618 halpha hbeta]
  apply (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo
    (fun u hu => _root_.GD.N0232.N0720.N1439.d013619
      (alpha := alpha) (beta := beta) hu)
    (_root_.GD.N0232.N0720.N1439.d013620 halpha hbeta)
    (_root_.GD.N0232.N0720.N1439.d013616 alpha beta)).2
  simpa only [smul_eq_mul] using hchart


theorem d013636
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ X : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1439.d013616 alpha beta X) = 1 := by
  rw [_root_.GD.N0232.N0720.N1439.d013634 halpha hbeta]
  calc
    (∫ u : ℝ in Ioo (0 : ℝ) 1,
        |_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
          _root_.GD.N0232.N0720.N1439.d013616 alpha beta
            (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u)) =
        ∫ u : ℝ in Ioo (0 : ℝ) 1, betaPDFReal alpha beta u := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact (_root_.GD.N0232.N0720.N1439.d013626
        halpha hbeta hu).symm
    _ = ∫ u : ℝ, betaPDFReal alpha beta u := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards with u hu
      have houtside : ¬(0 < u ∧ u < 1) := by
        simpa only [Set.mem_Ioo] using hu
      simp [betaPDFReal, houtside]
    _ = 1 := _root_.GD.N0235.d004042 halpha hbeta

theorem d013637
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    IntegrableOn (_root_.GD.N0232.N0720.N1439.d013617 alpha beta p) (Ioi (0 : ℝ)) := by
  have hsource : Integrable
      (fun u : ℝ => betaPDFReal alpha beta u *
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2) := by
    have hmeas : AEStronglyMeasurable
        (fun u : ℝ => betaPDFReal alpha beta u *
          (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2) :=
      ((measurable_betaPDFReal alpha beta).mul
        (((_root_.GD.N0232.N0720.N1091.d012771 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p)).sub
          measurable_const).pow_const 2)).aestronglyMeasurable
    apply (_root_.GD.N0232.N0720.N1091.d012772 halpha hbeta).mono' hmeas
    filter_upwards with u
    have hpdf0 := _root_.GD.N0235.d004040 halpha hbeta u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · have hw := _root_.GD.N0232.N0720.N1091.d012780
        (_root_.GD.N0232.N0720.N1091.d012778 halpha hbeta hp0 hp1) hu.1 hu.2
      have herrAbs :
          |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hw.1, hw.2]
      have herrSq :
          |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg
          (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpdf0, abs_pow]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left herrSq hpdf0
    · have houtside : ¬(0 < u ∧ u < 1) := by
        simpa only [Set.mem_Ioo] using hu
      simp [betaPDFReal, houtside]
  have hchart : IntegrableOn
      (fun u : ℝ => |_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
        _root_.GD.N0232.N0720.N1439.d013617 alpha beta p
          (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u))
      (Ioo (0 : ℝ) 1) := by
    have hscaled : IntegrableOn
        (fun u : ℝ => (p ^ 2)⁻¹ *
          (betaPDFReal alpha beta u *
            (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2))
        (Ioo (0 : ℝ) 1) :=
      (hsource.const_mul (p ^ 2)⁻¹).integrableOn
    apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioo
    intro u hu
    dsimp only
    rw [_root_.GD.N0232.N0720.N1439.d013627
      halpha hbeta hp0 hp1 hu]
    field_simp [hp0.ne']
  rw [← _root_.GD.N0232.N0720.N1439.d013618 halpha hbeta]
  apply (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo
    (fun u hu => _root_.GD.N0232.N0720.N1439.d013619
      (alpha := alpha) (beta := beta) hu)
    (_root_.GD.N0232.N0720.N1439.d013620 halpha hbeta)
    (_root_.GD.N0232.N0720.N1439.d013617 alpha beta p)).2
  simpa only [smul_eq_mul] using hchart


theorem d013638
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 alpha beta p =
      p ^ 2 *
        ∫ X : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X := by
  unfold _root_.GD.N0232.N0720.N1091.d012790
  rw [_root_.GD.N0235.d004041
    halpha hbeta]
  calc
    (∫ u : ℝ, betaPDFReal alpha beta u *
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2) =
        ∫ u : ℝ in Ioo (0 : ℝ) 1,
          betaPDFReal alpha beta u *
            (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards with u hu
      have houtside : ¬(0 < u ∧ u < 1) := by
        simpa only [Set.mem_Ioo] using hu
      simp [betaPDFReal, houtside]
    _ = ∫ u : ℝ in Ioo (0 : ℝ) 1,
          p ^ 2 *
            (|_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
              _root_.GD.N0232.N0720.N1439.d013617 alpha beta p
                (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact
        _root_.GD.N0232.N0720.N1439.d013627
          halpha hbeta hp0 hp1 hu
    _ = p ^ 2 *
        (∫ u : ℝ in Ioo (0 : ℝ) 1,
          |_root_.GD.N0232.N0720.N1439.d013614 alpha beta u| *
            _root_.GD.N0232.N0720.N1439.d013617 alpha beta p
              (_root_.GD.N0232.N0720.N1439.d013613 alpha beta u)) := by
      rw [integral_const_mul]
    _ = p ^ 2 *
        ∫ X : ℝ in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X := by
      rw [_root_.GD.N0232.N0720.N1439.d013633 halpha hbeta]




def d013639 (alpha beta z : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1439.d013615 alpha beta * z ^ (alpha - 1) *
    (1 + z) ^ (-2 : ℝ)



def d013640 (alpha beta p z : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1439.d013615 alpha beta * z ^ (alpha - 1) *
    (beta / (beta + alpha * p * z)) ^ (alpha + beta) *
      (((1 - p) * (1 - p * z)) / (1 + (1 - p) * z)) ^ 2


def d013641 (alpha beta p z : ℝ) : ℝ :=
  if z ∈ Ioc (0 : ℝ) (1 / p) then
    _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z
  else 0


def d013642 (alpha beta z : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1439.d013615 alpha beta *
    ((Ioc (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (alpha - 1)) z +
      4 * (Ioi (1 : ℝ)).indicator (fun x : ℝ => x ^ (alpha - 3)) z)

theorem d013643 (alpha beta : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1439.d013639 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1439.d013639 _root_.GD.N0232.N0720.N1439.d013615
  fun_prop

theorem d013644 (alpha beta p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1439.d013640 alpha beta p) := by
  unfold _root_.GD.N0232.N0720.N1439.d013640 _root_.GD.N0232.N0720.N1439.d013615
  fun_prop

theorem d013645 (alpha beta p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1439.d013641 alpha beta p) := by
  unfold _root_.GD.N0232.N0720.N1439.d013641
  exact Measurable.piecewise measurableSet_Ioc
    (_root_.GD.N0232.N0720.N1439.d013644 alpha beta p) measurable_const

theorem d013646 (alpha beta : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1439.d013642 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1439.d013642 _root_.GD.N0232.N0720.N1439.d013615
  have hnear : Measurable
      ((Ioc (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (alpha - 1))) := by
    apply Measurable.indicator _ measurableSet_Ioc
    fun_prop
  have hfar : Measurable
      ((Ioi (1 : ℝ)).indicator (fun x : ℝ => x ^ (alpha - 3))) := by
    apply Measurable.indicator _ measurableSet_Ioi
    fun_prop
  fun_prop

theorem d013647
    {alpha beta p z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 ≤ p) (hz : 0 ≤ z) :
    0 ≤ _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z := by
  have hden : 0 < beta + alpha * p * z := by positivity
  unfold _root_.GD.N0232.N0720.N1439.d013640
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (_root_.GD.N0232.N0720.N1439.d013630 halpha hbeta).le
        (Real.rpow_nonneg hz _))
      (Real.rpow_nonneg (div_nonneg hbeta.le hden.le) _))
    (sq_nonneg _)

theorem d013648
    {alpha beta z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hz : 0 ≤ z) :
    0 ≤ _root_.GD.N0232.N0720.N1439.d013639 alpha beta z := by
  unfold _root_.GD.N0232.N0720.N1439.d013639
  exact mul_nonneg
    (mul_nonneg (_root_.GD.N0232.N0720.N1439.d013630 halpha hbeta).le
      (Real.rpow_nonneg hz _))
    (Real.rpow_nonneg (by linarith) _)



theorem d013649
    {alpha beta p z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) (hz : 0 < z) :
    p ^ 2 * (p * _root_.GD.N0232.N0720.N1439.d013617 alpha beta p (p * z)) =
      p ^ alpha * _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z := by
  have hpz : 0 < p * z := mul_pos hp0 hz
  have hratioDen : 0 < (1 - p) * (p * z) + p := by positivity
  have hfiniteDen : 0 < 1 + (1 - p) * z := by positivity
  have hbetaDen : 0 < beta + alpha * (p * z) := by positivity
  have hpowMul :
      (p * z) ^ (alpha - 1) = p ^ (alpha - 1) * z ^ (alpha - 1) :=
    Real.mul_rpow hp0.le hz.le
  have hpcollect : p * p ^ (alpha - 1) = p ^ alpha := by
    calc
      p * p ^ (alpha - 1) = p ^ (1 : ℝ) * p ^ (alpha - 1) := by
        rw [Real.rpow_one]
      _ = p ^ ((1 : ℝ) + (alpha - 1)) :=
        (Real.rpow_add hp0 1 (alpha - 1)).symm
      _ = p ^ alpha := by ring_nf
  unfold _root_.GD.N0232.N0720.N1439.d013617 _root_.GD.N0232.N0720.N1439.d013616
    _root_.GD.N0232.N0720.N1428.d013136 _root_.GD.N0232.N0720.N1439.d013640
  rw [hpowMul]
  have hdenFactor :
      (1 - p) * (p * z) + p = p * (1 + (1 - p) * z) := by ring
  rw [hdenFactor]
  field_simp [hp0.ne', hfiniteDen.ne', hratioDen.ne', hbetaDen.ne']
  rw [← hpcollect]
  ring


theorem d013650
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    p ^ 2 *
        (∫ X : ℝ in (0 : ℝ)..1,
          _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X) =
      p ^ alpha *
        ∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013641 alpha beta p z := by
  let f : ℝ → ℝ := _root_.GD.N0232.N0720.N1439.d013617 alpha beta p
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (f := f) (a := (0 : ℝ)) (b := 1 / p) p
  have hscaledBounds : p * (0 : ℝ) = 0 ∧ p * (1 / p) = 1 := by
    constructor
    · ring
    · field_simp [hp0.ne']
  rw [hscaledBounds.1, hscaledBounds.2] at hscale
  have hactive :
      (∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013641 alpha beta p z) =
        ∫ z : ℝ in Ioc (0 : ℝ) (1 / p),
          _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with z
    simp only [_root_.GD.N0232.N0720.N1439.d013641, indicator_apply]
  have hinterval :
      (∫ z : ℝ in (0 : ℝ)..(1 / p),
          _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z) =
        ∫ z : ℝ in Ioc (0 : ℝ) (1 / p),
          _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z := by
    rw [intervalIntegral.integral_of_le (one_div_nonneg.mpr hp0.le)]
  calc
    p ^ 2 * (∫ X : ℝ in (0 : ℝ)..1, f X) =
        p ^ 2 *
          (p * ∫ z : ℝ in (0 : ℝ)..(1 / p), f (p * z)) := by
      rw [hscale]
    _ = ∫ z : ℝ in (0 : ℝ)..(1 / p),
          p ^ 2 * (p * f (p * z)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = ∫ z : ℝ in (0 : ℝ)..(1 / p),
          p ^ alpha * _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with z hz
      rw [uIoc_of_le (one_div_nonneg.mpr hp0.le)] at hz
      have hz0 : 0 < z := hz.1
      exact _root_.GD.N0232.N0720.N1439.d013649
        halpha hbeta hp0 hp1 hz0
    _ = p ^ alpha *
          ∫ z : ℝ in (0 : ℝ)..(1 / p),
            _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z := by
      rw [intervalIntegral.integral_const_mul]
    _ = p ^ alpha *
          ∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013641 alpha beta p z := by
      rw [hinterval, ← hactive]

theorem d013651
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta) :
    Integrable (_root_.GD.N0232.N0720.N1439.d013642 alpha beta) := by
  have hnearIoo : IntegrableOn (fun z : ℝ => z ^ (alpha - 1))
      (Ioo (0 : ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  have hnearIoc : IntegrableOn (fun z : ℝ => z ^ (alpha - 1))
      (Ioc (0 : ℝ) 1) :=
    IntegrableOn.congr_set_ae (t := Ioo (0 : ℝ) 1) hnearIoo
      (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
  have hfar : IntegrableOn (fun z : ℝ => z ^ (alpha - 3))
      (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnearIndicator : Integrable
      ((Ioc (0 : ℝ) 1).indicator (fun z : ℝ => z ^ (alpha - 1))) :=
    hnearIoc.integrable_indicator measurableSet_Ioc
  have hfarIndicator : Integrable
      ((Ioi (1 : ℝ)).indicator (fun z : ℝ => z ^ (alpha - 3))) :=
    hfar.integrable_indicator measurableSet_Ioi
  unfold _root_.GD.N0232.N0720.N1439.d013642
  exact (hnearIndicator.add (hfarIndicator.const_mul 4)).const_mul
    (_root_.GD.N0232.N0720.N1439.d013615 alpha beta)

theorem d013652
    {alpha beta z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 ≤ _root_.GD.N0232.N0720.N1439.d013642 alpha beta z := by
  unfold _root_.GD.N0232.N0720.N1439.d013642
  exact mul_nonneg (_root_.GD.N0232.N0720.N1439.d013630 halpha hbeta).le
    (add_nonneg (indicator_nonneg
        (fun x hx => Real.rpow_nonneg hx.1.le _) z)
      (mul_nonneg (by norm_num)
        (indicator_nonneg
          (fun x hx => Real.rpow_nonneg (zero_lt_one.trans hx).le _) z)))



theorem d013653
    {alpha beta p z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hpHalf : p ≤ 1 / 2) :
    _root_.GD.N0232.N0720.N1439.d013641 alpha beta p z ≤
      _root_.GD.N0232.N0720.N1439.d013642 alpha beta z := by
  have hp1 : p < 1 := lt_of_le_of_lt hpHalf (by norm_num)
  unfold _root_.GD.N0232.N0720.N1439.d013641
  split_ifs with hzactive
  · have hz0 : 0 < z := hzactive.1
    have hpz0 : 0 ≤ p * z := (mul_pos hp0 hz0).le
    have hpz1 : p * z ≤ 1 := by
      have := hzactive.2
      rw [le_div_iff₀ hp0] at this
      simpa [mul_comm] using this
    have hbetaDen : 0 < beta + alpha * p * z := by positivity
    have hbase0 : 0 ≤ beta / (beta + alpha * p * z) :=
      div_nonneg hbeta.le hbetaDen.le
    have hbase1 : beta / (beta + alpha * p * z) ≤ 1 :=
      (div_le_one hbetaDen).2 (by nlinarith)
    have hpow :
        (beta / (beta + alpha * p * z)) ^ (alpha + beta) ≤ 1 :=
      Real.rpow_le_one hbase0 hbase1 (by linarith)
    have hpow0 :
        0 ≤ (beta / (beta + alpha * p * z)) ^ (alpha + beta) :=
      Real.rpow_nonneg hbase0 _
    have h1p0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
    have h1pz0 : 0 ≤ 1 - p * z := sub_nonneg.mpr hpz1
    have hratioDen : 0 < 1 + (1 - p) * z := by positivity
    have hratio0 :
        0 ≤ ((1 - p) * (1 - p * z)) / (1 + (1 - p) * z) :=
      div_nonneg (mul_nonneg h1p0 h1pz0) hratioDen.le
    have hlead0 : 0 ≤ _root_.GD.N0232.N0720.N1439.d013615 alpha beta :=
      (_root_.GD.N0232.N0720.N1439.d013630 halpha hbeta).le
    have hzpow0 : 0 ≤ z ^ (alpha - 1) :=
      Real.rpow_nonneg hz0.le _
    rcases le_total z 1 with hz1 | hz1
    · have hnum_le_one : (1 - p) * (1 - p * z) ≤ 1 := by
        nlinarith [mul_nonneg h1p0 h1pz0]
      have hratio1 :
          ((1 - p) * (1 - p * z)) / (1 + (1 - p) * z) ≤ 1 := by
        rw [div_le_one hratioDen]
        nlinarith [mul_nonneg h1p0 hz0.le]
      have hratioSq :
          (((1 - p) * (1 - p * z)) / (1 + (1 - p) * z)) ^ 2 ≤ 1 := by
        nlinarith
      calc
        _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z ≤
            _root_.GD.N0232.N0720.N1439.d013615 alpha beta * z ^ (alpha - 1) := by
          unfold _root_.GD.N0232.N0720.N1439.d013640
          let A := _root_.GD.N0232.N0720.N1439.d013615 alpha beta * z ^ (alpha - 1)
          let D := (beta / (beta + alpha * p * z)) ^ (alpha + beta)
          let R := ((1 - p) * (1 - p * z)) / (1 + (1 - p) * z)
          change A * D * R ^ 2 ≤ A
          calc
            A * D * R ^ 2 ≤ A * 1 * R ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow
                  (mul_nonneg hlead0 hzpow0)) (sq_nonneg R)
            _ ≤ A * 1 * 1 := by
              exact mul_le_mul_of_nonneg_left hratioSq
                (mul_nonneg (mul_nonneg hlead0 hzpow0) zero_le_one)
            _ = A := by ring
        _ = _root_.GD.N0232.N0720.N1439.d013642 alpha beta z := by
          unfold _root_.GD.N0232.N0720.N1439.d013642
          simp [Set.indicator, hz0, hz1, not_lt.mpr hz1]
    · have hz1pos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
      have hnumz :
          z * ((1 - p) * (1 - p * z)) ≤ 1 + (1 - p) * z := by
        have hfactor :
            (1 - p) * (1 - p * z) ≤ 1 - p :=
          mul_le_of_le_one_right h1p0 (by linarith)
        have hzmul := mul_le_mul_of_nonneg_left hfactor hz0.le
        nlinarith
      have hratio_le_inv :
          ((1 - p) * (1 - p * z)) / (1 + (1 - p) * z) ≤ 1 / z := by
        rw [div_le_iff₀ hratioDen]
        have hdiv := (le_div_iff₀ hz1pos).2 (by
          simpa [mul_comm] using hnumz)
        simpa [div_eq_mul_inv, mul_comm] using hdiv
      have hratioSq :
          (((1 - p) * (1 - p * z)) / (1 + (1 - p) * z)) ^ 2 ≤
            (1 / z) ^ 2 := by
        nlinarith [one_div_nonneg.mpr hz0.le]
      have hinvSq : (1 / z) ^ 2 = z ^ (-2 : ℝ) := by
        rw [one_div]
        symm
        rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num,
          Real.rpow_neg_natCast]
        norm_num
        rfl
      have hcollect :
          z ^ (alpha - 1) * (1 / z) ^ 2 = z ^ (alpha - 3) := by
        rw [hinvSq, ← Real.rpow_add hz1pos]
        congr 1
        ring
      calc
        _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z ≤
            _root_.GD.N0232.N0720.N1439.d013615 alpha beta *
              z ^ (alpha - 1) * (1 / z) ^ 2 := by
          unfold _root_.GD.N0232.N0720.N1439.d013640
          let A := _root_.GD.N0232.N0720.N1439.d013615 alpha beta * z ^ (alpha - 1)
          let D := (beta / (beta + alpha * p * z)) ^ (alpha + beta)
          let R := ((1 - p) * (1 - p * z)) / (1 + (1 - p) * z)
          change A * D * R ^ 2 ≤ A * (1 / z) ^ 2
          calc
            A * D * R ^ 2 ≤ A * 1 * R ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow
                  (mul_nonneg hlead0 hzpow0)) (sq_nonneg R)
            _ ≤ A * 1 * (1 / z) ^ 2 := by
              exact mul_le_mul_of_nonneg_left hratioSq
                (mul_nonneg (mul_nonneg hlead0 hzpow0) zero_le_one)
            _ = A * (1 / z) ^ 2 := by ring
        _ = _root_.GD.N0232.N0720.N1439.d013615 alpha beta *
              z ^ (alpha - 3) := by
          rw [mul_assoc, hcollect]
        _ ≤ _root_.GD.N0232.N0720.N1439.d013642 alpha beta z := by
          rcases eq_or_lt_of_le hz1 with rfl | hz1
          · simp [_root_.GD.N0232.N0720.N1439.d013642, Set.indicator]
          · unfold _root_.GD.N0232.N0720.N1439.d013642
            simp [Set.indicator, not_le.mpr hz1, hz1]
            nlinarith [mul_nonneg hlead0
              (Real.rpow_nonneg hz0.le (alpha - 3))]
  · exact (_root_.GD.N0232.N0720.N1439.d013652 halpha hbeta).trans'
      (by simp)

theorem d013654
    {alpha beta p z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hz : 0 ≤ z) :
    0 ≤ _root_.GD.N0232.N0720.N1439.d013641 alpha beta p z := by
  unfold _root_.GD.N0232.N0720.N1439.d013641
  split_ifs
  · exact _root_.GD.N0232.N0720.N1439.d013647 halpha hbeta hp0.le hz
  · exact le_rfl

theorem d013655
    {alpha beta z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hz : 0 < z) :
    _root_.GD.N0232.N0720.N1439.d013640 alpha beta 0 z =
      _root_.GD.N0232.N0720.N1439.d013639 alpha beta z := by
  have h1z : 0 < 1 + z := by linarith
  have hinvSq : (1 / (1 + z)) ^ 2 = (1 + z) ^ (-2 : ℝ) := by
    rw [one_div]
    symm
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num,
      Real.rpow_neg_natCast]
    norm_num
    rfl
  unfold _root_.GD.N0232.N0720.N1439.d013640 _root_.GD.N0232.N0720.N1439.d013639
  rw [show beta + alpha * 0 * z = beta by ring,
    div_self hbeta.ne', Real.one_rpow]
  rw [show ((1 - 0) * (1 - 0 * z)) / (1 + (1 - 0) * z) =
      1 / (1 + z) by ring]
  rw [hinvSq]
  ring

theorem d013656
    {alpha beta z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hz : 0 < z) :
    ContinuousAt (fun p : ℝ => _root_.GD.N0232.N0720.N1439.d013640 alpha beta p z) 0 := by
  have hbetaBase : beta / (beta + alpha * 0 * z) ≠ 0 := by
    simp [hbeta.ne']
  have hratioDen : 1 + (1 - (0 : ℝ)) * z ≠ 0 := by positivity
  have hbaseCont : ContinuousAt
      (fun p : ℝ => beta / (beta + alpha * p * z)) 0 := by
    have hdenCont : ContinuousAt (fun p : ℝ => beta + alpha * p * z) 0 := by
      fun_prop
    exact continuousAt_const.div hdenCont (by simpa using hbeta.ne')
  have hpowCont : ContinuousAt
      (fun p : ℝ =>
        (beta / (beta + alpha * p * z)) ^ (alpha + beta)) 0 :=
    hbaseCont.rpow_const (Or.inl hbetaBase)
  have hratioCont : ContinuousAt
      (fun p : ℝ =>
        ((1 - p) * (1 - p * z)) / (1 + (1 - p) * z)) 0 := by
    fun_prop
  unfold _root_.GD.N0232.N0720.N1439.d013640
  exact ((continuousAt_const.mul continuousAt_const).mul hpowCont).mul
    (hratioCont.pow 2)


theorem d013657
    {alpha beta z : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hz : 0 < z)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) :
    Tendsto (fun n => _root_.GD.N0232.N0720.N1439.d013641 alpha beta (p n) z)
      atTop (nhds (_root_.GD.N0232.N0720.N1439.d013639 alpha beta z)) := by
  have hpz : Tendsto (fun n => p n * z) atTop (nhds 0) := by
    simpa using hp.mul_const z
  have hpzOne : ∀ᶠ n in atTop, p n * z ≤ 1 :=
    ((tendsto_order.1 hpz).2 1 zero_lt_one).mono fun _ hn => hn.le
  have hactive : ∀ᶠ n in atTop, z ∈ Ioc (0 : ℝ) (1 / p n) := by
    filter_upwards [hpzOne] with n hn
    refine ⟨hz, ?_⟩
    rw [le_div_iff₀ (hp0 n)]
    simpa [mul_comm] using hn
  have hraw :=
    (_root_.GD.N0232.N0720.N1439.d013656 halpha hbeta hz).tendsto.comp hp
  rw [_root_.GD.N0232.N0720.N1439.d013655 halpha hbeta hz] at hraw
  apply hraw.congr'
  filter_upwards [hactive] with n hn
  unfold _root_.GD.N0232.N0720.N1439.d013641
  rw [if_pos hn]
  rfl


theorem d013658
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) :
    Tendsto
      (fun n => ∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013641 alpha beta (p n) z)
      atTop
      (nhds (∫ z : ℝ in Ioi (0 : ℝ),
        _root_.GD.N0232.N0720.N1439.d013639 alpha beta z)) := by
  have hpHalf : ∀ᶠ n in atTop, p n ≤ 1 / 2 := by
    filter_upwards [(tendsto_order.1 hp).2 (1 / 2) (by norm_num)] with n hn
    exact hn.le
  have hbound := _root_.GD.N0232.N0720.N1439.d013651 halpha halphaTwo hbeta
  have hdc : Tendsto
      (fun n => ∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013641 alpha beta (p n) z
        ∂volume.restrict (Ioi (0 : ℝ)))
      atTop
      (nhds (∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013639 alpha beta z
        ∂volume.restrict (Ioi (0 : ℝ)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (_root_.GD.N0232.N0720.N1439.d013642 alpha beta)
    · exact Filter.Eventually.of_forall fun n =>
        (_root_.GD.N0232.N0720.N1439.d013645 alpha beta (p n))
          |>.aestronglyMeasurable
    · filter_upwards [hpHalf] with n hn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg (_root_.GD.N0232.N0720.N1439.d013654
          halpha hbeta (hp0 n) hz.le)]
      exact _root_.GD.N0232.N0720.N1439.d013653
        halpha hbeta (hp0 n) hn
    · exact hbound.integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact _root_.GD.N0232.N0720.N1439.d013657 halpha hbeta hz hp hp0
  have hdc' : Tendsto
      (fun n => ∫ z : ℝ in Ioi (0 : ℝ),
        _root_.GD.N0232.N0720.N1439.d013641 alpha beta (p n) z)
      atTop
      (nhds (∫ z : ℝ in Ioi (0 : ℝ),
        _root_.GD.N0232.N0720.N1439.d013639 alpha beta z)) := by
    simpa only [Measure.restrict_apply_univ] using hdc
  apply hdc'.congr'
  filter_upwards with n
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards with z hz
  unfold _root_.GD.N0232.N0720.N1439.d013641
  rw [if_neg]
  intro hactive
  exact hz hactive.1




theorem d013659
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta) :
    (∫ z : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1439.d013639 alpha beta z) =
      (alpha / beta) ^ alpha *
        (ProbabilityTheory.beta alpha (2 - alpha) /
          ProbabilityTheory.beta alpha beta) := by
  have htwo : 0 < 2 - alpha := sub_pos.mpr halphaTwo
  unfold _root_.GD.N0232.N0720.N1439.d013639 _root_.GD.N0232.N0720.N1439.d013615
  have hprime :
      (∫ z : ℝ in Ioi (0 : ℝ),
        z ^ (alpha - 1) * (1 + z) ^ (-2 : ℝ)) =
        ProbabilityTheory.beta alpha (2 - alpha) := by
    convert _root_.GD.N0232.N0720.N1050.d003164 alpha (2 - alpha) halpha htwo using 1 <;>
      ring
  calc
    (∫ z : ℝ in Ioi (0 : ℝ),
        (alpha / beta) ^ alpha / ProbabilityTheory.beta alpha beta *
          z ^ (alpha - 1) * (1 + z) ^ (-2 : ℝ)) =
        ((alpha / beta) ^ alpha / ProbabilityTheory.beta alpha beta) *
          ∫ z : ℝ in Ioi (0 : ℝ),
            z ^ (alpha - 1) * (1 + z) ^ (-2 : ℝ) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z _
      ring
    _ = ((alpha / beta) ^ alpha / ProbabilityTheory.beta alpha beta) *
          ProbabilityTheory.beta alpha (2 - alpha) := by rw [hprime]
    _ = _ := by ring



theorem d013660
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta) :
    (∫ z : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1439.d013639 alpha beta z) =
      ∫ z : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1421.d013122 alpha beta z := by
  rw [_root_.GD.N0232.N0720.N1439.d013659 halpha halphaTwo hbeta,
    _root_.GD.N0232.N0720.N1421.d013124 halpha halphaTwo hbeta]


def d013661 (alpha beta p : ℝ) : ℝ :=
  ∫ X : ℝ in Ioi (1 : ℝ), _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X

theorem d013662
    {alpha beta p X : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 ≤ X) :
    _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X ≤
      _root_.GD.N0232.N0720.N1439.d013616 alpha beta X := by
  have herrAbs := _root_.GD.N0232.N0720.N1427.d013165 hp0 hp1 hX
  have herrSq : _root_.GD.N0232.N0720.N1428.d013136 p X ^ 2 ≤ 1 := by
    have hs := (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 herrAbs
    simpa [sq_abs] using hs
  unfold _root_.GD.N0232.N0720.N1439.d013617
  exact mul_le_of_le_one_right
    (_root_.GD.N0232.N0720.N1439.d013631 halpha hbeta
      (zero_le_one.trans hX)) herrSq

theorem d013663
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 ≤ _root_.GD.N0232.N0720.N1439.d013661 alpha beta p := by
  unfold _root_.GD.N0232.N0720.N1439.d013661
  apply setIntegral_nonneg measurableSet_Ioi
  intro X hX
  exact _root_.GD.N0232.N0720.N1439.d013632 halpha hbeta
    (zero_le_one.trans hX.le)



theorem d013664
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1439.d013661 alpha beta p ≤ 1 := by
  have hregret : IntegrableOn (_root_.GD.N0232.N0720.N1439.d013617 alpha beta p)
      (Ioi (1 : ℝ)) :=
    (_root_.GD.N0232.N0720.N1439.d013637
      halpha hbeta hp0 hp1).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hdensity : IntegrableOn (_root_.GD.N0232.N0720.N1439.d013616 alpha beta)
      (Ioi (1 : ℝ)) :=
    (_root_.GD.N0232.N0720.N1439.d013635
      halpha hbeta).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  unfold _root_.GD.N0232.N0720.N1439.d013661
  calc
    (∫ X : ℝ in Ioi (1 : ℝ), _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X) ≤
        ∫ X : ℝ in Ioi (1 : ℝ), _root_.GD.N0232.N0720.N1439.d013616 alpha beta X := by
      apply setIntegral_mono_on hregret hdensity measurableSet_Ioi
      intro X hX
      exact _root_.GD.N0232.N0720.N1439.d013662
        halpha hbeta hp0 hp1 hX.le
    _ ≤ ∫ X : ℝ in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1439.d013616 alpha beta X := by
      apply setIntegral_mono_set
        (_root_.GD.N0232.N0720.N1439.d013635 halpha hbeta)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
        exact _root_.GD.N0232.N0720.N1439.d013631 halpha hbeta hX.le
      · exact Filter.Eventually.of_forall fun X hX => lt_trans zero_lt_one hX
    _ = 1 := _root_.GD.N0232.N0720.N1439.d013636 halpha hbeta

theorem d013665
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ X : ℝ in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X) =
      (∫ X : ℝ in (0 : ℝ)..1,
        _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X) +
        _root_.GD.N0232.N0720.N1439.d013661 alpha beta p := by
  let f : ℝ → ℝ := _root_.GD.N0232.N0720.N1439.d013617 alpha beta p
  have hglob : IntegrableOn f (Ioi (0 : ℝ)) :=
    _root_.GD.N0232.N0720.N1439.d013637 halpha hbeta hp0 hp1
  have hright : IntegrableOn f (Ioi (1 : ℝ)) :=
    hglob.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hglob hright
  unfold _root_.GD.N0232.N0720.N1439.d013661
  simpa [f] using hsplit.symm



theorem d013666
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => (p n) ^ 2 * _root_.GD.N0232.N0720.N1439.d013661 alpha beta (p n) /
        (p n) ^ alpha)
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n => p n ^ (2 - alpha)) atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1428.d013152 hp (sub_pos.mpr halphaTwo)
  have hrewrite : ∀ n,
      (p n) ^ 2 * _root_.GD.N0232.N0720.N1439.d013661 alpha beta (p n) /
          (p n) ^ alpha =
        (p n) ^ (2 - alpha) * _root_.GD.N0232.N0720.N1439.d013661 alpha beta (p n) := by
    intro n
    rw [Real.rpow_sub (hp0 n),
      show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    field_simp [(Real.rpow_pos_of_pos (hp0 n) alpha).ne']
  apply (squeeze_zero
    (fun n => mul_nonneg (Real.rpow_nonneg (hp0 n).le _)
      (_root_.GD.N0232.N0720.N1439.d013663 halpha hbeta))
    (fun n => mul_le_of_le_one_right
      (Real.rpow_nonneg (hp0 n).le _)
      (_root_.GD.N0232.N0720.N1439.d013664 halpha hbeta (hp0 n) (hp1 n)))
    hpow).congr'
  exact Eventually.of_forall fun n => (hrewrite n).symm





theorem d013667
    {alpha beta p : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 alpha beta p / p ^ alpha =
      (∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013641 alpha beta p z) +
        p ^ 2 * _root_.GD.N0232.N0720.N1439.d013661 alpha beta p / p ^ alpha := by
  have hpow : p ^ alpha ≠ 0 :=
    (Real.rpow_pos_of_pos hp0 alpha).ne'
  have hsplit := _root_.GD.N0232.N0720.N1439.d013665
    halpha hbeta hp0 hp1
  have hleft :=
    _root_.GD.N0232.N0720.N1439.d013650
      halpha hbeta hp0 hp1
  rw [_root_.GD.N0232.N0720.N1439.d013638
    halpha hbeta hp0 hp1, hsplit]
  calc
    p ^ 2 *
          ((∫ X : ℝ in (0 : ℝ)..1,
              _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X) +
            _root_.GD.N0232.N0720.N1439.d013661 alpha beta p) /
        p ^ alpha =
      (p ^ 2 *
          ∫ X : ℝ in (0 : ℝ)..1,
            _root_.GD.N0232.N0720.N1439.d013617 alpha beta p X) / p ^ alpha +
        p ^ 2 * _root_.GD.N0232.N0720.N1439.d013661 alpha beta p / p ^ alpha := by ring
    _ = (p ^ alpha *
          ∫ z : ℝ, _root_.GD.N0232.N0720.N1439.d013641 alpha beta p z) / p ^ alpha +
        p ^ 2 * _root_.GD.N0232.N0720.N1439.d013661 alpha beta p / p ^ alpha := by
      rw [hleft]
    _ = _ := by field_simp [hpow]



theorem d013668
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n) / (p n) ^ alpha)
      atTop
      (nhds (∫ z : ℝ in Ioi (0 : ℝ),
        _root_.GD.N0232.N0720.N1439.d013639 alpha beta z)) := by
  have hactive := _root_.GD.N0232.N0720.N1439.d013658
    halpha halphaTwo hbeta hp hp0
  have hright :=
    _root_.GD.N0232.N0720.N1439.d013666
      halpha halphaTwo hbeta hp hp0 hp1
  have hsum := hactive.add hright
  have hsum' := hsum.congr' (Eventually.of_forall fun n =>
    (_root_.GD.N0232.N0720.N1439.d013667
      halpha hbeta (hp0 n) (hp1 n)).symm)
  simpa only [add_zero] using hsum'


theorem d013669
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n) / (p n) ^ alpha)
      atTop
      (nhds ((alpha / beta) ^ alpha *
        (ProbabilityTheory.beta alpha (2 - alpha) /
          ProbabilityTheory.beta alpha beta))) := by
  have h := _root_.GD.N0232.N0720.N1439.d013668
    halpha halphaTwo hbeta hp hp0 hp1
  rw [_root_.GD.N0232.N0720.N1439.d013659 halpha halphaTwo hbeta] at h
  exact h


theorem d013670
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha < 2)
    (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto
      (fun n => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n) / (p n) ^ alpha)
      atTop
      (nhds ((alpha / beta) ^ alpha *
        Real.Gamma (alpha + beta) * Real.Gamma (2 - alpha) /
          Real.Gamma beta)) := by
  have h := _root_.GD.N0232.N0720.N1439.d013668
    halpha halphaTwo hbeta hp hp0 hp1
  rw [_root_.GD.N0232.N0720.N1439.d013660
      halpha halphaTwo hbeta,
    _root_.GD.N0232.N0720.N1421.d013125 halpha halphaTwo hbeta] at h
  exact h

end

end N1439
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1439.d013626
#print axioms _root_.GD.N0232.N0720.N1439.d013638
#print axioms _root_.GD.N0232.N0720.N1439.d013650
#print axioms _root_.GD.N0232.N0720.N1439.d013658
#print axioms _root_.GD.N0232.N0720.N1439.d013664
#print axioms _root_.GD.N0232.N0720.N1439.d013667
#print axioms _root_.GD.N0232.N0720.N1439.d013669
#print axioms _root_.GD.N0232.N0720.N1439.d013670
