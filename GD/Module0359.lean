import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic






















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

open MeasureTheory Set intervalIntegral

namespace GD.N0106.N0428.N0765.N1534
noncomputable section


def d005295 (U₁ U₂ Δ l : ℝ) : ℝ := (1 - l) * U₁ + l * U₂ + 11 * l * (1 - l) * Δ ^ 2


def d005296 (U₁ U₂ Δ l : ℝ) : ℝ :=
  (l * (1 - l)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1534.d005295 U₁ U₂ Δ l ^ (-((21 : ℝ) / 2))


def d005297 (U₁ U₂ Δ : ℝ) : ℝ := ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l


def d005298 (U₁ U₂ Δ : ℝ) : ℝ := ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l



def d005299 (U₁ U₂ Δ : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1534.d005298 U₁ U₂ Δ / _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ


def d005300 (xbar₁ Δ U₁ U₂ : ℝ) : ℝ := xbar₁ + Δ * _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ


def d005301 (U₁ U₂ : ℝ) : ℝ := U₁ / (U₁ + U₂)


def d005302 (U₁ U₂ Δ : ℝ) : ℝ := 110 * Δ ^ 2 / (U₁ + U₂)

section Positivity
variable {U₁ U₂ Δ : ℝ}

theorem d005303 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1534.d005295 U₁ U₂ Δ l := by
  obtain ⟨hl0, hl1⟩ := hl
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005295
  have h3 : 0 ≤ 11 * l * (1 - l) * Δ ^ 2 := by
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 11) hl0) (sub_nonneg.mpr hl1)
    exact mul_nonneg h (sq_nonneg Δ)
  rcases lt_or_eq_of_le hl1 with h | h
  · have h1 : 0 < (1 - l) * U₁ := mul_pos (sub_pos.mpr h) hU₁
    have h2 : 0 ≤ l * U₂ := mul_nonneg hl0 hU₂.le
    linarith
  · subst h
    simpa using hU₂

theorem d005304 : Continuous (_root_.GD.N0106.N0428.N0765.N1534.d005295 U₁ U₂ Δ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005295
  fun_prop

theorem d005305 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005296
  apply ContinuousOn.mul
  · have h : Continuous fun l : ℝ => (l * (1 - l)) ^ ((9 : ℝ) / 2) :=
      (Real.continuous_rpow_const (by norm_num)).comp
        (by fun_prop : Continuous fun l : ℝ => l * (1 - l))
    exact h.continuousOn
  · exact _root_.GD.N0106.N0428.N0765.N1534.d005304.continuousOn.rpow_const
      (fun l hl => Or.inl (_root_.GD.N0106.N0428.N0765.N1534.d005303 hU₁ hU₂ hl).ne')

theorem d005306 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    IntervalIntegrable (_root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ) volume 0 1 :=
  (_root_.GD.N0106.N0428.N0765.N1534.d005305 hU₁ hU₂).intervalIntegrable_of_Icc zero_le_one

theorem d005307 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    IntervalIntegrable (fun l => l * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l) volume 0 1 :=
  (continuousOn_id.mul (_root_.GD.N0106.N0428.N0765.N1534.d005305 hU₁ hU₂)).intervalIntegrable_of_Icc zero_le_one

theorem d005308 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    IntervalIntegrable (fun l => (1 - l) * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l) volume 0 1 :=
  ((continuousOn_const.sub continuousOn_id).mul
    (_root_.GD.N0106.N0428.N0765.N1534.d005305 hU₁ hU₂)).intervalIntegrable_of_Icc zero_le_one

theorem d005309 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005296
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos hl.1 (sub_pos.mpr hl.2)) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1534.d005303 hU₁ hU₂ (Ioo_subset_Icc_self hl)) _)

theorem d005310 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) : 0 < _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ :=
  intervalIntegral_pos_of_pos_on (_root_.GD.N0106.N0428.N0765.N1534.d005306 hU₁ hU₂)
    (fun _ hl => _root_.GD.N0106.N0428.N0765.N1534.d005309 hU₁ hU₂ hl) zero_lt_one

theorem d005311 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) : 0 < _root_.GD.N0106.N0428.N0765.N1534.d005298 U₁ U₂ Δ :=
  intervalIntegral_pos_of_pos_on (_root_.GD.N0106.N0428.N0765.N1534.d005307 hU₁ hU₂)
    (fun _ hl => mul_pos hl.1 (_root_.GD.N0106.N0428.N0765.N1534.d005309 hU₁ hU₂ hl)) zero_lt_one

theorem d005312 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ - _root_.GD.N0106.N0428.N0765.N1534.d005298 U₁ U₂ Δ
      = ∫ l in (0 : ℝ)..1, (1 - l) * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005297 _root_.GD.N0106.N0428.N0765.N1534.d005298
  rw [← integral_sub (_root_.GD.N0106.N0428.N0765.N1534.d005306 hU₁ hU₂)
    (_root_.GD.N0106.N0428.N0765.N1534.d005307 hU₁ hU₂)]
  congr 1
  ext l
  ring

theorem d005313 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005298 U₁ U₂ Δ < _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ := by
  have h : 0 < _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ - _root_.GD.N0106.N0428.N0765.N1534.d005298 U₁ U₂ Δ := by
    rw [_root_.GD.N0106.N0428.N0765.N1534.d005312 hU₁ hU₂]
    exact intervalIntegral_pos_of_pos_on (_root_.GD.N0106.N0428.N0765.N1534.d005308 hU₁ hU₂)
      (fun _ hl => mul_pos (sub_pos.mpr hl.2) (_root_.GD.N0106.N0428.N0765.N1534.d005309 hU₁ hU₂ hl)) zero_lt_one
  linarith

theorem d005314 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) : 0 < _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ :=
  div_pos (_root_.GD.N0106.N0428.N0765.N1534.d005311 hU₁ hU₂) (_root_.GD.N0106.N0428.N0765.N1534.d005310 hU₁ hU₂)

theorem d005315 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) : _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ < 1 :=
  (div_lt_one (_root_.GD.N0106.N0428.N0765.N1534.d005310 hU₁ hU₂)).mpr (_root_.GD.N0106.N0428.N0765.N1534.d005313 hU₁ hU₂)

theorem d005316 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) : _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ ∈ Ioo (0 : ℝ) 1 :=
  ⟨_root_.GD.N0106.N0428.N0765.N1534.d005314 hU₁ hU₂, _root_.GD.N0106.N0428.N0765.N1534.d005315 hU₁ hU₂⟩



theorem d005317 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) (xbar₁ μ : ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1534.d005300 xbar₁ Δ U₁ U₂ - μ) ^ 2 ≤ 2 * (xbar₁ - μ) ^ 2 + 2 * Δ ^ 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005300
  have hw := _root_.GD.N0106.N0428.N0765.N1534.d005316 (Δ := Δ) hU₁ hU₂
  have h1 : (Δ * _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ) ^ 2 ≤ Δ ^ 2 := by
    rw [mul_pow]
    have h : _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
    nlinarith [sq_nonneg Δ]
  nlinarith [sq_nonneg (xbar₁ - μ - Δ * _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ), h1]

end Positivity

section Swap
variable {U₁ U₂ Δ : ℝ}

theorem d005318 (l : ℝ) : _root_.GD.N0106.N0428.N0765.N1534.d005295 U₂ U₁ Δ (1 - l) = _root_.GD.N0106.N0428.N0765.N1534.d005295 U₁ U₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005295
  ring

theorem d005319 (l : ℝ) : _root_.GD.N0106.N0428.N0765.N1534.d005296 U₂ U₁ Δ (1 - l) = _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005296
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005318]
  have h : (1 - l) * (1 - (1 - l)) = l * (1 - l) := by ring
  rw [h]

theorem d005320 : _root_.GD.N0106.N0428.N0765.N1534.d005297 U₂ U₁ Δ = _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005297
  have h := integral_comp_sub_left (a := (0 : ℝ)) (b := 1) (fun l => _root_.GD.N0106.N0428.N0765.N1534.d005296 U₂ U₁ Δ l) 1
  simp only [sub_self, sub_zero] at h
  rw [← h]
  congr 1
  ext l
  exact _root_.GD.N0106.N0428.N0765.N1534.d005319 l

theorem d005321 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005298 U₂ U₁ Δ = _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ - _root_.GD.N0106.N0428.N0765.N1534.d005298 U₁ U₂ Δ := by
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005312 hU₁ hU₂]
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005298
  have h := integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun l => l * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₂ U₁ Δ l) 1
  simp only [sub_self, sub_zero] at h
  rw [← h]
  congr 1
  ext l
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005319]

theorem d005322 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005299 U₂ U₁ Δ = 1 - _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005299
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005321 hU₁ hU₂, _root_.GD.N0106.N0428.N0765.N1534.d005320 (U₁ := U₁) (U₂ := U₂) (Δ := Δ)]
  have hd := (_root_.GD.N0106.N0428.N0765.N1534.d005310 (Δ := Δ) hU₁ hU₂).ne'
  rw [sub_div, div_self hd]

end Swap

section Scale
variable {U₁ U₂ Δ Δ' c : ℝ}

theorem d005323 (hΔ : Δ' ^ 2 = c * Δ ^ 2) (l : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1534.d005295 (c * U₁) (c * U₂) Δ' l = c * _root_.GD.N0106.N0428.N0765.N1534.d005295 U₁ U₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005295
  rw [hΔ]
  ring

theorem d005324 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) (hc : 0 < c) (hΔ : Δ' ^ 2 = c * Δ ^ 2)
    {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1534.d005296 (c * U₁) (c * U₂) Δ' l = c ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005296
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005323 hΔ, Real.mul_rpow hc.le (_root_.GD.N0106.N0428.N0765.N1534.d005303 hU₁ hU₂ hl).le]
  ring

theorem d005325 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) (hc : 0 < c)
    (hΔ : Δ' ^ 2 = c * Δ ^ 2) :
    _root_.GD.N0106.N0428.N0765.N1534.d005297 (c * U₁) (c * U₂) Δ' = c ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1534.d005297 U₁ U₂ Δ := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005297
  rw [← intervalIntegral.integral_const_mul]
  apply integral_congr
  intro l hl
  rw [uIcc_of_le zero_le_one] at hl
  exact _root_.GD.N0106.N0428.N0765.N1534.d005324 hU₁ hU₂ hc hΔ hl

theorem d005326 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) (hc : 0 < c)
    (hΔ : Δ' ^ 2 = c * Δ ^ 2) :
    _root_.GD.N0106.N0428.N0765.N1534.d005298 (c * U₁) (c * U₂) Δ' = c ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1534.d005298 U₁ U₂ Δ := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005298
  rw [← intervalIntegral.integral_const_mul]
  apply integral_congr
  intro l hl
  rw [uIcc_of_le zero_le_one] at hl
  show l * _root_.GD.N0106.N0428.N0765.N1534.d005296 (c * U₁) (c * U₂) Δ' l = c ^ (-((21 : ℝ) / 2)) * (l * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l)
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005324 hU₁ hU₂ hc hΔ hl]
  ring

theorem d005327 (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) (hc : 0 < c) (hΔ : Δ' ^ 2 = c * Δ ^ 2) :
    _root_.GD.N0106.N0428.N0765.N1534.d005299 (c * U₁) (c * U₂) Δ' = _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005299
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005326 hU₁ hU₂ hc hΔ, _root_.GD.N0106.N0428.N0765.N1534.d005325 hU₁ hU₂ hc hΔ]
  have hk : c ^ (-((21 : ℝ) / 2)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  rw [mul_div_mul_left _ _ hk]

end Scale

section Dirichlet


def d005328 (η u v w l : ℝ) : ℝ := v * (1 - l) + η * w * l + (1 + η) * u * l * (1 - l)


def d005329 (η u v w l : ℝ) : ℝ :=
  (l * (1 - l)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1534.d005328 η u v w l ^ (-((21 : ℝ) / 2))


def d005330 (η u v w : ℝ) : ℝ :=
  (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l) /
    ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l


def d005331 (η : ℝ) : ℝ := (1 + η) / 11


def d005332 (η U₁ U₂ Δ : ℝ) : ℝ := Δ ^ 2 / _root_.GD.N0106.N0428.N0765.N1534.d005331 η + U₁ + U₂ / η


def d005333 (η U₁ U₂ Δ : ℝ) : ℝ := (Δ ^ 2 / _root_.GD.N0106.N0428.N0765.N1534.d005331 η) / _root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ


def d005334 (η U₁ U₂ Δ : ℝ) : ℝ := U₁ / _root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ


def d005335 (η U₁ U₂ Δ : ℝ) : ℝ := (U₂ / η) / _root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ

variable {η U₁ U₂ Δ : ℝ}

theorem d005336 (hη : 0 < η) : 0 < _root_.GD.N0106.N0428.N0765.N1534.d005331 η := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005331
  positivity

theorem d005337 (hη : 0 < η) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) : 0 < _root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005332
  have h1 : 0 ≤ Δ ^ 2 / _root_.GD.N0106.N0428.N0765.N1534.d005331 η := div_nonneg (sq_nonneg Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005336 hη).le
  have h2 : 0 < U₂ / η := div_pos hU₂ hη
  linarith

theorem d005338 (hη : 0 < η) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) (l : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1534.d005328 η (_root_.GD.N0106.N0428.N0765.N1534.d005333 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) l
      = (_root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ)⁻¹ * _root_.GD.N0106.N0428.N0765.N1534.d005295 U₁ U₂ Δ l := by
  have hT := (_root_.GD.N0106.N0428.N0765.N1534.d005337 (Δ := Δ) hη hU₁ hU₂).ne'
  have hV := (_root_.GD.N0106.N0428.N0765.N1534.d005336 hη).ne'
  have h11 : (1 + η) ≠ 0 := by linarith
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005328 _root_.GD.N0106.N0428.N0765.N1534.d005333 _root_.GD.N0106.N0428.N0765.N1534.d005334 _root_.GD.N0106.N0428.N0765.N1534.d005335 _root_.GD.N0106.N0428.N0765.N1534.d005295
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005331] at hV ⊢
  field_simp

theorem d005339 (hη : 0 < η) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1534.d005329 η (_root_.GD.N0106.N0428.N0765.N1534.d005333 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) l
      = (_root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ)⁻¹ ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005329 _root_.GD.N0106.N0428.N0765.N1534.d005296
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005338 hη hU₁ hU₂,
    Real.mul_rpow (inv_nonneg.mpr (_root_.GD.N0106.N0428.N0765.N1534.d005337 hη hU₁ hU₂).le) (_root_.GD.N0106.N0428.N0765.N1534.d005303 hU₁ hU₂ hl).le]
  ring


theorem d005340 (hη : 0 < η) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005299 U₁ U₂ Δ = _root_.GD.N0106.N0428.N0765.N1534.d005330 η (_root_.GD.N0106.N0428.N0765.N1534.d005333 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005330 _root_.GD.N0106.N0428.N0765.N1534.d005299 _root_.GD.N0106.N0428.N0765.N1534.d005298 _root_.GD.N0106.N0428.N0765.N1534.d005297
  have hk : (_root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ)⁻¹ ^ (-((21 : ℝ) / 2)) ≠ 0 :=
    (Real.rpow_pos_of_pos (inv_pos.mpr (_root_.GD.N0106.N0428.N0765.N1534.d005337 hη hU₁ hU₂)) _).ne'
  have hnum : (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η (_root_.GD.N0106.N0428.N0765.N1534.d005333 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) l)
      = (_root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ)⁻¹ ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    show l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η (_root_.GD.N0106.N0428.N0765.N1534.d005333 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) l
      = (_root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ)⁻¹ ^ (-((21 : ℝ) / 2)) * (l * _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l)
    rw [_root_.GD.N0106.N0428.N0765.N1534.d005339 hη hU₁ hU₂ hl]
    ring
  have hden : (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 η (_root_.GD.N0106.N0428.N0765.N1534.d005333 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ) (_root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) l)
      = (_root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ)⁻¹ ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005296 U₁ U₂ Δ l := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    exact _root_.GD.N0106.N0428.N0765.N1534.d005339 hη hU₁ hU₂ hl
  rw [hnum, hden, mul_div_mul_left _ _ hk]

theorem d005341 (hη : 0 < η) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ + η * _root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ = (U₁ + U₂) / _root_.GD.N0106.N0428.N0765.N1534.d005332 η U₁ U₂ Δ := by
  have hT := (_root_.GD.N0106.N0428.N0765.N1534.d005337 (Δ := Δ) hη hU₁ hU₂).ne'
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005334 _root_.GD.N0106.N0428.N0765.N1534.d005335
  field_simp


theorem d005342 (hη : 0 < η) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005301 U₁ U₂ = _root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ / (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ + η * _root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) := by
  have hT := (_root_.GD.N0106.N0428.N0765.N1534.d005337 (Δ := Δ) hη hU₁ hU₂).ne'
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005341 hη hU₁ hU₂]
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005301 _root_.GD.N0106.N0428.N0765.N1534.d005334
  rw [div_div_div_cancel_right₀ hT]


theorem d005343 (hη : 0 < η) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    _root_.GD.N0106.N0428.N0765.N1534.d005302 U₁ U₂ Δ = 10 * (1 + η) * _root_.GD.N0106.N0428.N0765.N1534.d005333 η U₁ U₂ Δ / (_root_.GD.N0106.N0428.N0765.N1534.d005334 η U₁ U₂ Δ + η * _root_.GD.N0106.N0428.N0765.N1534.d005335 η U₁ U₂ Δ) := by
  have hT := (_root_.GD.N0106.N0428.N0765.N1534.d005337 (Δ := Δ) hη hU₁ hU₂).ne'
  have hV := (_root_.GD.N0106.N0428.N0765.N1534.d005336 hη).ne'
  have h11 : (1 + η) ≠ 0 := by linarith
  have hsum : 0 < U₁ + U₂ := by linarith
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005341 hη hU₁ hU₂]
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005302 _root_.GD.N0106.N0428.N0765.N1534.d005333
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005331] at hV ⊢
  field_simp
  ring



theorem d005344 {η u : ℝ} (hη : 0 < η) (hu : 0 ≤ u) (v w : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w = _root_.GD.N0106.N0428.N0765.N1534.d005299 v (η * w) (Real.sqrt ((1 + η) * u / 11)) := by
  have hk : ∀ l : ℝ, _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l = _root_.GD.N0106.N0428.N0765.N1534.d005296 v (η * w) (Real.sqrt ((1 + η) * u / 11)) l := by
    intro l
    have hC : _root_.GD.N0106.N0428.N0765.N1534.d005328 η u v w l = _root_.GD.N0106.N0428.N0765.N1534.d005295 v (η * w) (Real.sqrt ((1 + η) * u / 11)) l := by
      unfold _root_.GD.N0106.N0428.N0765.N1534.d005328 _root_.GD.N0106.N0428.N0765.N1534.d005295
      rw [Real.sq_sqrt (by positivity)]
      ring
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005329 _root_.GD.N0106.N0428.N0765.N1534.d005296
    rw [hC]
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005330 _root_.GD.N0106.N0428.N0765.N1534.d005299 _root_.GD.N0106.N0428.N0765.N1534.d005298 _root_.GD.N0106.N0428.N0765.N1534.d005297
  simp_rw [hk]


theorem d005345 {η u v w : ℝ} (hη : 0 < η) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w ∈ Ioo (0 : ℝ) 1 := by
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005344 hη hu]
  exact _root_.GD.N0106.N0428.N0765.N1534.d005316 hv (mul_pos hη hw)



theorem d005346 {η u v w : ℝ} (hη : 0 < η) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 η⁻¹ u w v = 1 - _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w := by
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005344 (inv_pos.mpr hη) hu, _root_.GD.N0106.N0428.N0765.N1534.d005344 hη hu]
  have hΔ : Real.sqrt ((1 + η) * u / 11) ^ 2 = η * Real.sqrt ((1 + η⁻¹) * u / 11) ^ 2 := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [← _root_.GD.N0106.N0428.N0765.N1534.d005327 (U₁ := w) (U₂ := η⁻¹ * v) hw (mul_pos (inv_pos.mpr hη) hv) hη hΔ,
    mul_inv_cancel_left₀ hη.ne']
  exact _root_.GD.N0106.N0428.N0765.N1534.d005322 hv (mul_pos hη hw)

end Dirichlet

section Measurability

theorem d005347 :
    Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005296 q.1.1 q.1.2.1 q.1.2.2 q.2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005296 _root_.GD.N0106.N0428.N0765.N1534.d005295
  fun_prop

theorem d005348 :
    Measurable fun p : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005297 p.1 p.2.1 p.2.2 := by
  have h : (fun p : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005297 p.1 p.2.1 p.2.2)
      = fun p => ∫ l, _root_.GD.N0106.N0428.N0765.N1534.d005296 p.1 p.2.1 p.2.2 l ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext p
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005297
    exact integral_of_le zero_le_one
  rw [h]
  exact (_root_.GD.N0106.N0428.N0765.N1534.d005347.stronglyMeasurable.integral_prod_right').measurable

theorem d005349 :
    Measurable fun p : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005298 p.1 p.2.1 p.2.2 := by
  have hk : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => q.2 * _root_.GD.N0106.N0428.N0765.N1534.d005296 q.1.1 q.1.2.1 q.1.2.2 q.2 :=
    measurable_snd.mul _root_.GD.N0106.N0428.N0765.N1534.d005347
  have h : (fun p : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005298 p.1 p.2.1 p.2.2)
      = fun p => ∫ l, l * _root_.GD.N0106.N0428.N0765.N1534.d005296 p.1 p.2.1 p.2.2 l ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext p
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005298
    exact integral_of_le zero_le_one
  rw [h]
  exact (hk.stronglyMeasurable.integral_prod_right').measurable


theorem d005350 : Measurable fun p : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005299 p.1 p.2.1 p.2.2 :=
  _root_.GD.N0106.N0428.N0765.N1534.d005349.div _root_.GD.N0106.N0428.N0765.N1534.d005348



theorem d005351 :
    Measurable fun p : ℝ × ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005300 p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hmap : Measurable fun p : ℝ × ℝ × ℝ × ℝ => ((p.2.2.1, p.2.2.2, p.2.1) : ℝ × ℝ × ℝ) :=
    measurable_snd.snd.fst.prodMk (measurable_snd.snd.snd.prodMk measurable_snd.fst)
  have hw : Measurable fun p : ℝ × ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1534.d005299 p.2.2.1 p.2.2.2 p.2.1 := by
    have h := _root_.GD.N0106.N0428.N0765.N1534.d005350.comp hmap
    simpa [Function.comp_def] using h
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005300
  exact measurable_fst.add (measurable_snd.fst.mul hw)

end Measurability

end
end GD.N0106.N0428.N0765.N1534

#print axioms _root_.GD.N0106.N0428.N0765.N1534.d005351
