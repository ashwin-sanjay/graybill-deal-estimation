import GD.Module0359
import Mathlib.Tactic






































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set intervalIntegral

namespace GD.N0106.N0428.N0765.N1543
open _root_.GD.N0106.N0428.N0765.N1534
noncomputable section




def d005383 (u v w : ℝ) : ℝ := Real.sqrt u * v ^ 4 * w ^ 4



def d005384 : ℝ := ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v)


def d005385 (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * f u v (1 - u - v)) /
    _root_.GD.N0106.N0428.N0765.N1543.d005384

theorem d005386 (u v w : ℝ) : _root_.GD.N0106.N0428.N0765.N1543.d005383 u w v = _root_.GD.N0106.N0428.N0765.N1543.d005383 u v w := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
  ring

theorem d005387 (u w : ℝ) : _root_.GD.N0106.N0428.N0765.N1543.d005383 u 0 w = 0 := by
  simp [_root_.GD.N0106.N0428.N0765.N1543.d005383]

theorem d005388 (u v : ℝ) : _root_.GD.N0106.N0428.N0765.N1543.d005383 u v 0 = 0 := by
  simp [_root_.GD.N0106.N0428.N0765.N1543.d005383]


theorem d005389 (f : ℝ → ℝ → ℝ → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => f u w v) = _root_.GD.N0106.N0428.N0765.N1543.d005385 f := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only
  have hkey : ∀ v : ℝ, 1 - u - (1 - u - v) = v := fun v => by ring
  have h1 : (∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * f u (1 - u - v) v) =
      ∫ v in (0 : ℝ)..(1 - u),
        (fun v => _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * f u v (1 - u - v)) ((1 - u) - v) := by
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [hkey, _root_.GD.N0106.N0428.N0765.N1543.d005386]
  rw [h1, intervalIntegral.integral_comp_sub_left
    (fun v => _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * f u v (1 - u - v)) (1 - u)]
  norm_num



theorem d005390 {f g : ℝ → ℝ → ℝ → ℝ}
    (h : ∀ u v w, 0 ≤ u → 0 < v → 0 < w → f u v w = g u v w) :
    _root_.GD.N0106.N0428.N0765.N1543.d005385 f = _root_.GD.N0106.N0428.N0765.N1543.d005385 g := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le (by norm_num)] at hu
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [Set.uIcc_of_le (by linarith [hu.2])] at hv
  try simp only
  rcases eq_or_lt_of_le hv.1 with hv0 | hv0
  · rw [← hv0, _root_.GD.N0106.N0428.N0765.N1543.d005387, zero_mul, zero_mul]
  rcases eq_or_lt_of_le (sub_nonneg.mpr hv.2 : 0 ≤ 1 - u - v) with hw0 | hw0
  · rw [← hw0, _root_.GD.N0106.N0428.N0765.N1543.d005388, zero_mul, zero_mul]
  rw [h u v (1 - u - v) hu.1 hv0 hw0]

theorem d005391 (c : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => c * f u v w) = c * _root_.GD.N0106.N0428.N0765.N1543.d005385 f := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  rw [← mul_div_assoc]
  congr 1
  simp_rw [mul_left_comm _ c, intervalIntegral.integral_const_mul]




def d005392 (η : ℝ) : ℝ := 1 / (1 + η)


def d005393 (η v w : ℝ) : ℝ := v / (v + η * w)


def d005394 (η u v w : ℝ) : ℝ := 10 * (1 + η) * u / (v + η * w)


def d005395 (η : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005331 η * _root_.GD.N0106.N0428.N0765.N1543.d005385 fun u v w =>
    (_root_.GD.N0106.N0428.N0765.N1543.d005393 η v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) ^ 2


def d005396 (e : ℝ) : ℝ := e⁻¹ * _root_.GD.N0106.N0428.N0765.N1543.d005395 e⁻¹

theorem d005397 {η : ℝ} (hη : 0 < η) : η * _root_.GD.N0106.N0428.N0765.N1534.d005331 η⁻¹ = _root_.GD.N0106.N0428.N0765.N1534.d005331 η := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005331
  field_simp
  ring

theorem d005398 {η : ℝ} (hη : 0 < η) : _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹ = 1 - _root_.GD.N0106.N0428.N0765.N1543.d005392 η := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005392
  have h1 : 1 + η ≠ 0 := (by linarith : (0 : ℝ) < 1 + η).ne'
  field_simp
  ring

theorem d005399 {η v w : ℝ} (hη : 0 < η) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1543.d005393 η⁻¹ w v = 1 - _root_.GD.N0106.N0428.N0765.N1543.d005393 η v w := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005393
  have h1 : v + η * w ≠ 0 := (by positivity : (0 : ℝ) < v + η * w).ne'
  have h2 : w + η⁻¹ * v ≠ 0 := (by positivity : (0 : ℝ) < w + η⁻¹ * v).ne'
  field_simp
  ring


theorem d005400 {η u v w : ℝ} (hη : 0 < η) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1543.d005394 η⁻¹ u w v = _root_.GD.N0106.N0428.N0765.N1543.d005394 η u v w := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005394
  have h1 : v + η * w ≠ 0 := (by positivity : (0 : ℝ) < v + η * w).ne'
  have h2 : w + η⁻¹ * v ≠ 0 := (by positivity : (0 : ℝ) < w + η⁻¹ * v).ne'
  field_simp
  ring


theorem d005401 {η : ℝ} (hη : 0 < η) : _root_.GD.N0106.N0428.N0765.N1543.d005395 η = η * _root_.GD.N0106.N0428.N0765.N1543.d005395 η⁻¹ := by
  have hswap : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1543.d005393 η⁻¹ w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) ^ 2) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1543.d005393 η⁻¹ v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) ^ 2) :=
    _root_.GD.N0106.N0428.N0765.N1543.d005389 _
  have key : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1543.d005393 η⁻¹ w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) ^ 2) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1543.d005393 η v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) ^ 2) := by
    refine _root_.GD.N0106.N0428.N0765.N1543.d005390 fun u v w hu hv hw => ?_
    rw [_root_.GD.N0106.N0428.N0765.N1534.d005346 hη hu hv hw, _root_.GD.N0106.N0428.N0765.N1543.d005399 hη hv hw, _root_.GD.N0106.N0428.N0765.N1543.d005398 hη]
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005395
  rw [← key, hswap, ← mul_assoc, _root_.GD.N0106.N0428.N0765.N1543.d005397 hη]



theorem d005402 {e : ℝ} (he : 0 < e) :
    _root_.GD.N0106.N0428.N0765.N1543.d005396 e = _root_.GD.N0106.N0428.N0765.N1534.d005331 e * _root_.GD.N0106.N0428.N0765.N1543.d005385 fun u v w =>
      (v / (e * v + w) - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2 - (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1534.d005330 e⁻¹ u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005396 _root_.GD.N0106.N0428.N0765.N1543.d005395
  have key : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1543.d005393 e⁻¹ v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 e⁻¹) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1534.d005330 e⁻¹ u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 e⁻¹) ^ 2) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => e ^ 2 *
        ((v / (e * v + w) - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2 -
          (e⁻¹ * _root_.GD.N0106.N0428.N0765.N1534.d005330 e⁻¹ u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 e) ^ 2)) := by
    refine _root_.GD.N0106.N0428.N0765.N1543.d005390 fun u v w hu hv hw => ?_
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005393 _root_.GD.N0106.N0428.N0765.N1543.d005392
    have h1 : e * v + w ≠ 0 := (by positivity : (0 : ℝ) < e * v + w).ne'
    have h2 : v + e⁻¹ * w ≠ 0 := (by positivity : (0 : ℝ) < v + e⁻¹ * w).ne'
    have h3 : 1 + e ≠ 0 := (by linarith : (0 : ℝ) < 1 + e).ne'
    have h4 : 1 + e⁻¹ ≠ 0 := (by positivity : (0 : ℝ) < 1 + e⁻¹).ne'
    field_simp
    ring
  rw [key, _root_.GD.N0106.N0428.N0765.N1543.d005391, ← mul_assoc, ← mul_assoc]
  congr 1
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005331
  field_simp
  ring




def d005403 (a : ℕ) (h : ℝ) : ℝ := h ^ (a + 1) * (1 - h)



def d005404 (k : ℕ) (h : ℝ) : ℝ := h * (1 - h) * (h - 1 / 2) ^ k

theorem d005405 (k : ℕ) (h : ℝ) : _root_.GD.N0106.N0428.N0765.N1543.d005404 k (1 - h) = (-1 : ℝ) ^ k * _root_.GD.N0106.N0428.N0765.N1543.d005404 k h := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005404
  rw [show (1 - h) - 1 / 2 = -(h - 1 / 2) by ring, neg_pow]
  ring


def d005406 (φ : ℝ → ℝ) (η : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1534.d005331 η * _root_.GD.N0106.N0428.N0765.N1543.d005385 fun u v w =>
    (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w) * _root_.GD.N0106.N0428.N0765.N1543.d005394 η u v w


def d005407 (φ : ℝ → ℝ) (η : ℝ) : ℝ :=
  -(_root_.GD.N0106.N0428.N0765.N1534.d005331 η * _root_.GD.N0106.N0428.N0765.N1543.d005385 fun u v w =>
    (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w))


def d005408 (a : ℕ) : Fin 2 → ℝ → ℝ
  | 0 => _root_.GD.N0106.N0428.N0765.N1543.d005407 (_root_.GD.N0106.N0428.N0765.N1543.d005403 a)
  | 1 => _root_.GD.N0106.N0428.N0765.N1543.d005406 (_root_.GD.N0106.N0428.N0765.N1543.d005403 a)


theorem d005409 {φ : ℝ → ℝ} {ε : ℝ} (hφ : ∀ h, φ (1 - h) = ε * φ h) {η : ℝ}
    (hη : 0 < η) : η * _root_.GD.N0106.N0428.N0765.N1543.d005406 φ η⁻¹ = -ε * _root_.GD.N0106.N0428.N0765.N1543.d005406 φ η := by
  have hswap : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v) *
          _root_.GD.N0106.N0428.N0765.N1543.d005394 η⁻¹ u w v) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u v w) *
          _root_.GD.N0106.N0428.N0765.N1543.d005394 η⁻¹ u v w) :=
    _root_.GD.N0106.N0428.N0765.N1543.d005389 _
  have key : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v) *
          _root_.GD.N0106.N0428.N0765.N1543.d005394 η⁻¹ u w v) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => -ε *
        ((_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w) *
          _root_.GD.N0106.N0428.N0765.N1543.d005394 η u v w)) := by
    refine _root_.GD.N0106.N0428.N0765.N1543.d005390 fun u v w hu hv hw => ?_
    rw [_root_.GD.N0106.N0428.N0765.N1534.d005346 hη hu hv hw, _root_.GD.N0106.N0428.N0765.N1543.d005398 hη, _root_.GD.N0106.N0428.N0765.N1543.d005400 hη hv hw, hφ]
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005406
  rw [← hswap, key, _root_.GD.N0106.N0428.N0765.N1543.d005391, ← mul_assoc, ← mul_assoc, _root_.GD.N0106.N0428.N0765.N1543.d005397 hη]
  ring


theorem d005410 {φ : ℝ → ℝ} {ε : ℝ} (hφ : ∀ h, φ (1 - h) = ε * φ h) {η : ℝ}
    (hη : 0 < η) : η * _root_.GD.N0106.N0428.N0765.N1543.d005407 φ η⁻¹ = -ε * _root_.GD.N0106.N0428.N0765.N1543.d005407 φ η := by
  have hswap : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v)) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u v w)) :=
    _root_.GD.N0106.N0428.N0765.N1543.d005389 _
  have key : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w =>
        (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v - _root_.GD.N0106.N0428.N0765.N1543.d005392 η⁻¹) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v)) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => -ε *
        ((_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w - _root_.GD.N0106.N0428.N0765.N1543.d005392 η) * φ (_root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w))) := by
    refine _root_.GD.N0106.N0428.N0765.N1543.d005390 fun u v w hu hv hw => ?_
    rw [_root_.GD.N0106.N0428.N0765.N1534.d005346 hη hu hv hw, _root_.GD.N0106.N0428.N0765.N1543.d005398 hη, hφ]
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005407
  rw [← hswap, key, _root_.GD.N0106.N0428.N0765.N1543.d005391, ← _root_.GD.N0106.N0428.N0765.N1543.d005397 hη]
  ring


theorem d005411 (k : ℕ) {η : ℝ} (hη : 0 < η) :
    _root_.GD.N0106.N0428.N0765.N1543.d005406 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η = -(-1 : ℝ) ^ k * η * _root_.GD.N0106.N0428.N0765.N1543.d005406 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η⁻¹ := by
  have h := _root_.GD.N0106.N0428.N0765.N1543.d005409 (_root_.GD.N0106.N0428.N0765.N1543.d005405 k) hη
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  calc _root_.GD.N0106.N0428.N0765.N1543.d005406 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η = -(-1 : ℝ) ^ k * (-(-1 : ℝ) ^ k * _root_.GD.N0106.N0428.N0765.N1543.d005406 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η) := by
        rw [← mul_assoc, neg_mul_neg, ← sq, hsq, one_mul]
    _ = -(-1 : ℝ) ^ k * η * _root_.GD.N0106.N0428.N0765.N1543.d005406 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η⁻¹ := by rw [← h]; ring


theorem d005412 (k : ℕ) {η : ℝ} (hη : 0 < η) :
    _root_.GD.N0106.N0428.N0765.N1543.d005407 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η = -(-1 : ℝ) ^ k * η * _root_.GD.N0106.N0428.N0765.N1543.d005407 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η⁻¹ := by
  have h := _root_.GD.N0106.N0428.N0765.N1543.d005410 (_root_.GD.N0106.N0428.N0765.N1543.d005405 k) hη
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  calc _root_.GD.N0106.N0428.N0765.N1543.d005407 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η = -(-1 : ℝ) ^ k * (-(-1 : ℝ) ^ k * _root_.GD.N0106.N0428.N0765.N1543.d005407 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η) := by
        rw [← mul_assoc, neg_mul_neg, ← sq, hsq, one_mul]
    _ = -(-1 : ℝ) ^ k * η * _root_.GD.N0106.N0428.N0765.N1543.d005407 (_root_.GD.N0106.N0428.N0765.N1543.d005404 k) η⁻¹ := by rw [← h]; ring

end

end GD.N0106.N0428.N0765.N1543
