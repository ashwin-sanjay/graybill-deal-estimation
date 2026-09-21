import GD.Module0861
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure












open MeasureTheory Set Filter
open scoped Topology Interval

namespace GD.N0232.N0720.N1320

open _root_.GD.N0232.N0720.N1358 _root_.GD.N0232.N0720.N1338
open _root_.GD.N0232.N0720.N1413 _root_.GD.N0232.N0720.N1415
open _root_.GD.N0232.N0720.N1357

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

abbrev d013309 := Icc (-1 : ℝ) 1

def d013310 (q x : ℝ) : ℝ := (1 - x ^ 2) ^ (q - 3 / 2)
def d013311 (q : ℝ) : ℝ := ∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1320.d013310 q x

theorem d013312 (q : ℝ) (x : _root_.GD.N0232.N0720.N1320.d013309) : 0 ≤ _root_.GD.N0232.N0720.N1320.d013310 q x :=
  Real.rpow_nonneg (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one (x : ℝ)).mpr
    (abs_le.mpr x.2))) _

theorem d013313 (q : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1320.d013310 q x :=
  Real.rpow_pos_of_pos (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr (abs_lt.mpr hx))) _

theorem d013314 {q : ℝ} (hq : 3 / 2 ≤ q) :
    ContinuousOn (_root_.GD.N0232.N0720.N1320.d013310 q) (Icc (-1 : ℝ) 1) := by
  apply ContinuousOn.rpow_const (by fun_prop)
  intro x hx
  exact Or.inr (sub_nonneg.mpr hq)

theorem d013315 {q : ℝ} (hq : 3 / 2 ≤ q) : 0 < _root_.GD.N0232.N0720.N1320.d013311 q :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((_root_.GD.N0232.N0720.N1320.d013314 hq).intervalIntegrable_of_Icc (by norm_num))
    (fun _ hx ↦ _root_.GD.N0232.N0720.N1320.d013313 q hx) (by norm_num)

def d013316 (q : ℝ) (x : _root_.GD.N0232.N0720.N1320.d013309) : ℝ := (_root_.GD.N0232.N0720.N1320.d013311 q)⁻¹ * _root_.GD.N0232.N0720.N1320.d013310 q x

theorem d013317 {q : ℝ} (hq : 3 / 2 ≤ q) (x : _root_.GD.N0232.N0720.N1320.d013309) :
    0 ≤ _root_.GD.N0232.N0720.N1320.d013316 q x :=
  mul_nonneg (inv_nonneg.mpr (_root_.GD.N0232.N0720.N1320.d013315 hq).le) (_root_.GD.N0232.N0720.N1320.d013312 q x)

def d013318 (q : ℝ) : Measure _root_.GD.N0232.N0720.N1320.d013309 :=
  volume.withDensity fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1320.d013316 q x)

theorem d013319 {q : ℝ} (hq : 3 / 2 ≤ q) (f : ℝ → ℝ) :
    (∫ x : _root_.GD.N0232.N0720.N1320.d013309, f x ∂_root_.GD.N0232.N0720.N1320.d013318 q) =
      (_root_.GD.N0232.N0720.N1320.d013311 q)⁻¹ * ∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1320.d013310 q x * f x := by
  rw [_root_.GD.N0232.N0720.N1320.d013318, integral_withDensity_eq_integral_toReal_smul
    (f := fun x : _root_.GD.N0232.N0720.N1320.d013309 ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1320.d013316 q x))
    ((by unfold _root_.GD.N0232.N0720.N1320.d013316 _root_.GD.N0232.N0720.N1320.d013310; fun_prop : Measurable (_root_.GD.N0232.N0720.N1320.d013316 q)).ennreal_ofReal)
    (by simp)]
  calc
    _ = ∫ x : _root_.GD.N0232.N0720.N1320.d013309, (_root_.GD.N0232.N0720.N1320.d013311 q)⁻¹ * (_root_.GD.N0232.N0720.N1320.d013310 q x * f x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1320.d013317 hq x)]
      simp only [smul_eq_mul, _root_.GD.N0232.N0720.N1320.d013316]
      ring
    _ = (_root_.GD.N0232.N0720.N1320.d013311 q)⁻¹ * ∫ x : _root_.GD.N0232.N0720.N1320.d013309, _root_.GD.N0232.N0720.N1320.d013310 q x * f x := by
      rw [integral_const_mul]
    _ = _ := by
      rw [Measure.Subtype.volume_def,
        integral_subtype_comap measurableSet_Icc (fun x : ℝ ↦ _root_.GD.N0232.N0720.N1320.d013310 q x * f x),
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

theorem d013320 {q : ℝ} (hq : 3 / 2 ≤ q) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1320.d013318 q) := by
  have hnorm : (∫ _ : _root_.GD.N0232.N0720.N1320.d013309, (1 : ℝ) ∂_root_.GD.N0232.N0720.N1320.d013318 q) = 1 := by
    rw [_root_.GD.N0232.N0720.N1320.d013319 hq (fun _ ↦ 1)]
    simp only [mul_one]
    exact inv_mul_cancel₀ (_root_.GD.N0232.N0720.N1320.d013315 hq).ne'
  apply isProbabilityMeasure_iff_real.2
  simpa only [integral_const, smul_eq_mul, mul_one] using hnorm



def d013321 (q : ℝ) (hq : 3 / 2 ≤ q) : ProbabilityMeasure _root_.GD.N0232.N0720.N1320.d013309 :=
  ⟨_root_.GD.N0232.N0720.N1320.d013318 q, _root_.GD.N0232.N0720.N1320.d013320 hq⟩

theorem d013322 (q : ℝ) (hq : 3 / 2 ≤ q) (f : ℝ → ℝ) :
    (∫ x : _root_.GD.N0232.N0720.N1320.d013309, f x ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) =
      (_root_.GD.N0232.N0720.N1320.d013311 q)⁻¹ * ∫ x in (-1 : ℝ)..1, _root_.GD.N0232.N0720.N1320.d013310 q x * f x :=
  _root_.GD.N0232.N0720.N1320.d013319 hq f

private theorem d013323 {epsilon : ℝ} (he : |epsilon| < 1)
    (x : _root_.GD.N0232.N0720.N1320.d013309) : 0 < 1 - epsilon * (x : ℝ) := by
  simpa only [_root_.GD.N0232.N0720.N1358.d003992, _root_.GD.N0232.N0720.N1358.d004017 he] using
    _root_.GD.N0232.N0720.N1358.d003996 (_root_.GD.N0232.N0720.N1358.d004016 he) x.2

def d013324 (s : ℝ) (j : ℕ) (epsilon : ℝ) (x : _root_.GD.N0232.N0720.N1320.d013309) : ℝ :=
  (x : ℝ) ^ j * (1 - epsilon * (x : ℝ)) ^ (-s)

theorem d013325 (q : ℝ) (hq : 3 / 2 ≤ q) (s : ℝ) (j : ℕ)
    {epsilon : ℝ} (he : |epsilon| < 1) :
    Integrable (_root_.GD.N0232.N0720.N1320.d013324 s j epsilon) (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) := by
  have hc : Continuous (_root_.GD.N0232.N0720.N1320.d013324 s j epsilon) := by
    unfold _root_.GD.N0232.N0720.N1320.d013324
    apply Continuous.mul
    · fun_prop
    apply Continuous.rpow_const
    · fun_prop
    · intro x
      exact Or.inl (_root_.GD.N0232.N0720.N1320.d013323 he x).ne'
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

theorem d013326 (q : ℝ) (hq : 3 / 2 ≤ q)
    {epsilon : ℝ} (he : |epsilon| < 1) :
    (∫ x : _root_.GD.N0232.N0720.N1320.d013309, ((x : ℝ) - _root_.GD.N0232.N0720.N1358.d004015 epsilon) *
      (1 - epsilon * (x : ℝ)) ^ (-q) ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) = 0 ∧
    (∫ x : _root_.GD.N0232.N0720.N1320.d013309, ((x : ℝ) - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 *
      (1 - epsilon * (x : ℝ)) ^ (-(q + 1)) ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) = 0 := by
  have ha := _root_.GD.N0232.N0720.N1358.d004016 he
  have hfirst := _root_.GD.N0232.N0720.N1338.d013306 hq ha (le_refl (0 : ℝ))
  have hcubic := _root_.GD.N0232.N0720.N1338.d013307 hq ha (le_refl (0 : ℝ))
  simp only [_root_.GD.N0232.N0720.N1357.d004218, zero_mul, add_zero, _root_.GD.N0232.N0720.N1358.d003992, _root_.GD.N0232.N0720.N1358.d004017 he] at hfirst hcubic
  constructor
  · rw [_root_.GD.N0232.N0720.N1320.d013322 q hq
      (fun x : ℝ ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) * (1 - epsilon * x) ^ (-q))]
    have horder : (fun x : ℝ ↦ _root_.GD.N0232.N0720.N1320.d013310 q x *
        ((x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) * (1 - epsilon * x) ^ (-q))) =
        fun x ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) * (1 - x ^ 2) ^ (q - 3 / 2) *
          (1 - epsilon * x) ^ (-q) := by
      funext x
      unfold _root_.GD.N0232.N0720.N1320.d013310
      ring
    rw [horder, hfirst, mul_zero]
  · rw [_root_.GD.N0232.N0720.N1320.d013322 q hq
      (fun x : ℝ ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 * (1 - epsilon * x) ^ (-(q + 1)))]
    have horder : (fun x : ℝ ↦ _root_.GD.N0232.N0720.N1320.d013310 q x *
        ((x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 * (1 - epsilon * x) ^ (-(q + 1)))) =
        fun x ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 * (1 - x ^ 2) ^ (q - 3 / 2) *
          (1 - epsilon * x) ^ (-(q + 1)) := by
      funext x
      unfold _root_.GD.N0232.N0720.N1320.d013310
      ring
    rw [horder, hcubic, mul_zero]

theorem d013327 (q : ℝ) (hq : 3 / 2 ≤ q) :
    (∫ x : _root_.GD.N0232.N0720.N1320.d013309, (x : ℝ) ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) = 0 := by
  have h := (_root_.GD.N0232.N0720.N1320.d013326 q hq (epsilon := 0) (by norm_num)).1
  simpa only [_root_.GD.N0232.N0720.N1358.d004015, zero_div, sub_zero, zero_mul, Real.one_rpow, mul_one] using h

theorem d013328 (q : ℝ) (hq : 3 / 2 ≤ q)
    {epsilon : ℝ} (he : |epsilon| < 1) :
    _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q 1 (_root_.GD.N0232.N0720.N1320.d013321 q hq) epsilon =
      _root_.GD.N0232.N0720.N1358.d004015 epsilon * _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q 0 (_root_.GD.N0232.N0720.N1320.d013321 q hq) epsilon := by
  have h := (_root_.GD.N0232.N0720.N1320.d013326 q hq he).1
  have hi0 := _root_.GD.N0232.N0720.N1320.d013325 q hq q 0 he
  have hi1 := _root_.GD.N0232.N0720.N1320.d013325 q hq q 1 he
  have heq : (fun x : _root_.GD.N0232.N0720.N1320.d013309 ↦ ((x : ℝ) - _root_.GD.N0232.N0720.N1358.d004015 epsilon) *
      (1 - epsilon * (x : ℝ)) ^ (-q)) =
      fun x ↦ _root_.GD.N0232.N0720.N1320.d013324 q 1 epsilon x -
        _root_.GD.N0232.N0720.N1358.d004015 epsilon * _root_.GD.N0232.N0720.N1320.d013324 q 0 epsilon x := by
    funext x
    simp only [_root_.GD.N0232.N0720.N1320.d013324, pow_zero, pow_one, one_mul]
    ring
  rw [heq, integral_sub hi1 (hi0.const_mul _), integral_const_mul] at h
  simpa only [_root_.GD.N0232.N0720.N1413.d004111, _root_.GD.N0232.N0720.N1320.d013324, sub_zero] using sub_eq_zero.mp h

private theorem d013329 : HasDerivAt _root_.GD.N0232.N0720.N1358.d004015 (1 / 2) 0 := by
  have hs := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).pow 2)).sqrt
    (by norm_num : (1 : ℝ) - (0 : ℝ) ^ 2 ≠ 0)
  have hh := (hasDerivAt_id (0 : ℝ)).div ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hs)
    (by norm_num : (1 : ℝ) + Real.sqrt (1 - (0 : ℝ) ^ 2) ≠ 0)
  convert! hh using 1
  norm_num



theorem d013330 (q : ℝ) (hq : 3 / 2 ≤ q) :
    (∫ x : _root_.GD.N0232.N0720.N1320.d013309, (x : ℝ) ^ 2 ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) =
      1 / (2 * q) := by
  let μ : Measure _root_.GD.N0232.N0720.N1320.d013309 := _root_.GD.N0232.N0720.N1320.d013321 q hq
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hzero : (0 : ℝ) ∈ Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 (-1) 1 0 / 2)) (_root_.GD.N0232.N0720.N1413.d004097 (-1) 1 0 / 2) := by
    have hrad := _root_.GD.N0232.N0720.N1413.d004098 (-1) 1 0
    constructor <;> linarith
  have hM : HasDerivAt (_root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q 0 μ)
      (q * ∫ x : _root_.GD.N0232.N0720.N1320.d013309, (x : ℝ) ∂μ) 0 := by
    simpa [iteratedDeriv_zero, _root_.GD.N0232.N0720.N1413.d004105, _root_.GD.N0232.N0720.N1413.d004102, integral_const_mul] using
      _root_.GD.N0232.N0720.N1413.d004112 (-1) 1 0 q 0 μ hzero 0
  have hB : HasDerivAt (_root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q 1 μ)
      (q * ∫ x : _root_.GD.N0232.N0720.N1320.d013309, (x : ℝ) ^ 2 ∂μ) 0 := by
    simpa [iteratedDeriv_zero, _root_.GD.N0232.N0720.N1413.d004105, _root_.GD.N0232.N0720.N1413.d004102, integral_const_mul] using
      _root_.GD.N0232.N0720.N1413.d004112 (-1) 1 0 q 1 μ hzero 0
  have hMzero : _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q 0 μ 0 = 1 := by
    simp [_root_.GD.N0232.N0720.N1413.d004111, μ]
  have heq : _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q 1 μ =ᶠ[𝓝 (0 : ℝ)]
      fun epsilon ↦ _root_.GD.N0232.N0720.N1358.d004015 epsilon * _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q 0 μ epsilon := by
    have hzero' : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
    filter_upwards [isOpen_Ioo.eventually_mem hzero'] with epsilon he
    exact _root_.GD.N0232.N0720.N1320.d013328 q hq (abs_lt.mpr he)
  have hprod := _root_.GD.N0232.N0720.N1320.d013329.mul hM
  have hident := hprod.congr_of_eventuallyEq heq
  have hvalue : q * (∫ x : _root_.GD.N0232.N0720.N1320.d013309, (x : ℝ) ^ 2 ∂μ) = 1 / 2 := by
    simpa only [hMzero, _root_.GD.N0232.N0720.N1358.d004015, zero_div, mul_one, zero_mul, add_zero] using
      hB.unique hident
  apply (eq_div_iff (mul_ne_zero (by norm_num) (by linarith : q ≠ 0))).mpr
  change (∫ x : _root_.GD.N0232.N0720.N1320.d013309, (x : ℝ) ^ 2 ∂μ) * (2 * q) = 1
  nlinarith [hvalue]


theorem d013331 (q : ℝ) (hq : 3 / 2 ≤ q) {epsilon : ℝ} (he : |epsilon| < 1) :
    _root_.GD.N0232.N0720.N1413.d004128 (-1) 1 0 q (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) epsilon = 0 := by
  let a := _root_.GD.N0232.N0720.N1358.d004015 epsilon
  let M := ∫ x, _root_.GD.N0232.N0720.N1320.d013324 q 0 epsilon x ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)
  let B := ∫ x, _root_.GD.N0232.N0720.N1320.d013324 q 1 epsilon x ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)
  let A := fun j ↦ ∫ x, _root_.GD.N0232.N0720.N1320.d013324 (q + 1) j epsilon x ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)
  have hi (s : ℝ) (j : ℕ) := _root_.GD.N0232.N0720.N1320.d013325 q hq s j he
  obtain ⟨hfirst, hcubic⟩ := _root_.GD.N0232.N0720.N1320.d013326 q hq he
  have hfirstEq :
      (∫ x : _root_.GD.N0232.N0720.N1320.d013309, ((x : ℝ) - a) *
        (1 - epsilon * (x : ℝ)) ^ (-q) ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) = B - a * M := by
    calc
      _ = ∫ x, _root_.GD.N0232.N0720.N1320.d013324 q 1 epsilon x -
          a * _root_.GD.N0232.N0720.N1320.d013324 q 0 epsilon x ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [_root_.GD.N0232.N0720.N1320.d013324, pow_one, pow_zero, one_mul]
        ring
      _ = _ := by
        rw [integral_sub (hi q 1) ((hi q 0).const_mul a), integral_const_mul]
  have hB : B = a * M := by
    change (∫ x : _root_.GD.N0232.N0720.N1320.d013309, ((x : ℝ) - a) *
      (1 - epsilon * (x : ℝ)) ^ (-q) ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) = 0 at hfirst
    rw [hfirstEq] at hfirst
    linarith
  have hcubicEq :
      (∫ x : _root_.GD.N0232.N0720.N1320.d013309, ((x : ℝ) - a) ^ 3 *
        (1 - epsilon * (x : ℝ)) ^ (-(q + 1)) ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) =
        A 3 - (3 * a) * A 2 + (3 * a ^ 2) * A 1 - a ^ 3 * A 0 := by
    calc
      _ = ∫ x, _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 3 epsilon x -
          (3 * a) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 2 epsilon x +
          (3 * a ^ 2) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 1 epsilon x -
          a ^ 3 * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 0 epsilon x ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [_root_.GD.N0232.N0720.N1320.d013324, pow_one, pow_zero, one_mul]
        ring
      _ = _ := by
        have hi32 : Integrable (fun x ↦ _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 3 epsilon x -
            (3 * a) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 2 epsilon x) (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) :=
          (hi (q + 1) 3).sub ((hi (q + 1) 2).const_mul (3 * a))
        have hi321 : Integrable (fun x ↦ _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 3 epsilon x -
            (3 * a) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 2 epsilon x +
            (3 * a ^ 2) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 1 epsilon x) (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) :=
          hi32.add ((hi (q + 1) 1).const_mul (3 * a ^ 2))
        rw [integral_sub (f := fun x ↦ _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 3 epsilon x -
              (3 * a) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 2 epsilon x +
              (3 * a ^ 2) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 1 epsilon x)
            (g := fun x ↦ a ^ 3 * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 0 epsilon x)
            hi321 ((hi (q + 1) 0).const_mul (a ^ 3)),
          integral_add (f := fun x ↦ _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 3 epsilon x -
              (3 * a) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 2 epsilon x)
            (g := fun x ↦ (3 * a ^ 2) * _root_.GD.N0232.N0720.N1320.d013324 (q + 1) 1 epsilon x)
            hi32 ((hi (q + 1) 1).const_mul (3 * a ^ 2)),
          integral_sub (hi (q + 1) 3) ((hi (q + 1) 2).const_mul (3 * a)),
          integral_const_mul, integral_const_mul, integral_const_mul]
  have hA : A 3 - (3 * a) * A 2 + (3 * a ^ 2) * A 1 - a ^ 3 * A 0 = 0 := by
    rw [← hcubicEq]
    exact hcubic
  have hq0 (j : ℕ) : _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 q j (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) epsilon =
      ∫ x, _root_.GD.N0232.N0720.N1320.d013324 q j epsilon x ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) := by
    simp [_root_.GD.N0232.N0720.N1413.d004111, _root_.GD.N0232.N0720.N1320.d013324]
  have hq1 (j : ℕ) : _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 (q + 1) j (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) epsilon =
      A j := by
    simp only [_root_.GD.N0232.N0720.N1413.d004111, _root_.GD.N0232.N0720.N1320.d013324, A, sub_zero]
  simp only [_root_.GD.N0232.N0720.N1413.d004128, _root_.GD.N0232.N0720.N1413.d004126, Pi.sub_apply, Pi.add_apply,
    Pi.mul_apply, Pi.pow_apply, hq0, hq1]
  change M ^ 3 * A 3 - 3 * (B * M ^ 2 * A 2) +
    3 * (B ^ 2 * M * A 1) - B ^ 3 * A 0 = 0
  rw [hB]
  linear_combination M ^ 3 * hA



theorem d013332 (q : ℝ) (hq : 3 / 2 ≤ q) :
    _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 (-1) 1 0 (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) = 0 := by
  apply _root_.GD.N0232.N0720.N1413.d004130 (-1) 1 0 q (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  filter_upwards [isOpen_Ioo.eventually_mem hzero] with epsilon he
  exact _root_.GD.N0232.N0720.N1320.d013331 q hq ((abs_lt).2 he)

end
end GD.N0232.N0720.N1320


#print axioms _root_.GD.N0232.N0720.N1320.d013320
#print axioms _root_.GD.N0232.N0720.N1320.d013330
#print axioms _root_.GD.N0232.N0720.N1320.d013332
