import GD.Module1310












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0106.N0428.N0765.N1672
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663

def d021422 (e a b α β x : ℝ) : ℂ :=
  (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 : ℝ) : ℂ) *
    _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x ^ (-((21 : ℂ) / 2))

def d021423 (e a b α β : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x

def d021424 (e a b α β : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, ((x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x

theorem d021425 {e x : ℝ} (he : 0 < e) (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1663.d021405 e x * (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x * (1 - _root_.GD.N0106.N0428.N0765.N1663.d021404 e x)) ^ ((9 : ℝ) / 2) *
        _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2)) =
      (e⁻¹) ^ 5 * ((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1663.d021414 he hx
  have ht : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hD := (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx).ne'
  have hpow : _root_.GD.N0106.N0428.N0765.N1663.d021405 e x * _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ ((9 : ℝ) / 2) *
      _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2)) = (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ 5)⁻¹ := by
    calc
      _root_.GD.N0106.N0428.N0765.N1663.d021405 e x * _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ ((9 : ℝ) / 2) *
          _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2)) =
          _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (((1 : ℝ) + 9 / 2) + -(21 / 2)) := by
        rw [Real.rpow_add hc, Real.rpow_add hc, Real.rpow_one]
      _ = (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ 5)⁻¹ := by
        norm_num [Real.rpow_neg hc.le]
  rw [_root_.GD.N0106.N0428.N0765.N1663.d021412 he hx, Real.mul_rpow hc.le ht]
  calc
    _root_.GD.N0106.N0428.N0765.N1663.d021405 e x * (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ ((9 : ℝ) / 2) *
        (x * (1 - x)) ^ ((9 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2)) =
      (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x * _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ ((9 : ℝ) / 2) *
        _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2))) * (x * (1 - x)) ^ ((9 : ℝ) / 2) := by ring
    _ = (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ 5)⁻¹ * (x * (1 - x)) ^ ((9 : ℝ) / 2) := by rw [hpow]
    _ = (e⁻¹) ^ 5 * ((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10) := by
      unfold _root_.GD.N0106.N0428.N0765.N1663.d021405
      field_simp [he.ne', hD]


theorem d021426 {e x : ℝ} (he : 0 < e) (hx : x ∈ Icc (0 : ℝ) 1)
    (a b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x) =
      (((e⁻¹) ^ 5 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x := by
  have hc := _root_.GD.N0106.N0428.N0765.N1663.d021414 he hx
  have hz := _root_.GD.N0106.N0428.N0765.N1663.d021420 he hx a b α β hw
  have hcp : (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) ^ (-((21 : ℂ) / 2)) =
      ((_root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2)) : ℝ) : ℂ) := by
    convert (Complex.ofReal_cpow hc.le (-((21 : ℝ) / 2))).symm using 1 <;> push_cast <;> rfl
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021226, _root_.GD.N0106.N0428.N0765.N1663.d021419 he hx a b α β, _root_.GD.N0106.N0428.N0765.N1663.d021421 hc hz, hcp]
  calc
    (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) *
        (((_root_.GD.N0106.N0428.N0765.N1663.d021404 e x * (1 - _root_.GD.N0106.N0428.N0765.N1663.d021404 e x)) ^ ((9 : ℝ) / 2) : ℝ) *
          (((_root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2)) : ℝ) : ℂ) *
            _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x ^ (-((21 : ℂ) / 2)))) =
      ((_root_.GD.N0106.N0428.N0765.N1663.d021405 e x * (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x * (1 - _root_.GD.N0106.N0428.N0765.N1663.d021404 e x)) ^ ((9 : ℝ) / 2) *
        _root_.GD.N0106.N0428.N0765.N1663.d021405 e x ^ (-((21 : ℝ) / 2)) : ℝ) : ℂ) *
          _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x ^ (-((21 : ℂ) / 2)) := by push_cast; ring
    _ = (((e⁻¹) ^ 5 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x := by
      rw [_root_.GD.N0106.N0428.N0765.N1672.d021425 he hx]
      unfold _root_.GD.N0106.N0428.N0765.N1672.d021422
      push_cast
      ring

theorem d021427 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β = (((e⁻¹) ^ 5 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β := by
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021243, ← _root_.GD.N0106.N0428.N0765.N1663.d021417 he (_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β)
    (_root_.GD.N0106.N0428.N0765.N1538.d021227 he a b α β hw)]
  calc
    (∫ x in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x)) =
        ∫ x in (0 : ℝ)..1, (((e⁻¹) ^ 5 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      exact _root_.GD.N0106.N0428.N0765.N1672.d021426 he hx a b α β hw
    _ = (((e⁻¹) ^ 5 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β := by
      rw [intervalIntegral.integral_const_mul]
      rfl

theorem d021428 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ((e⁻¹ : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β =
      (((e⁻¹) ^ 5 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β := by
  let g : ℝ → ℂ := fun l => ((e⁻¹ : ℝ) : ℂ) * ((l : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l)
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul
      (_root_.GD.N0106.N0428.N0765.N1538.d021227 he a b α β hw))
  calc
    ((e⁻¹ : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β = ∫ l in (0 : ℝ)..1, g l := by
      unfold _root_.GD.N0106.N0428.N0765.N1538.d021244 g
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) * g (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x) :=
      (_root_.GD.N0106.N0428.N0765.N1663.d021417 he g hg).symm
    _ = ∫ x in (0 : ℝ)..1, (((e⁻¹) ^ 5 : ℝ) : ℂ) *
        (((x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      have hp : ((e⁻¹ : ℝ) : ℂ) * (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x : ℂ) =
          ((x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℝ) : ℂ) := by
        exact_mod_cast _root_.GD.N0106.N0428.N0765.N1663.d021413 (x := x) he
      calc
        (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) * g (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x) =
            (((e⁻¹ : ℝ) : ℂ) * (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x : ℂ)) *
              ((_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x)) := by
          dsimp [g]
          ring
        _ = (((e⁻¹) ^ 5 : ℝ) : ℂ) *
            (((x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x) := by
          rw [hp, _root_.GD.N0106.N0428.N0765.N1672.d021426 he hx a b α β hw]
          ring
    _ = (((e⁻¹) ^ 5 : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β := by
      rw [intervalIntegral.integral_const_mul]
      rfl


theorem d021429 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021247 e a b α β = _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β := by
  have hc : (((e⁻¹) ^ 5 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 5 (inv_ne_zero he.ne'))
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021247
  rw [← mul_div_assoc, _root_.GD.N0106.N0428.N0765.N1672.d021428 he a b α β hw,
    _root_.GD.N0106.N0428.N0765.N1672.d021427 he a b α β hw, mul_div_mul_left _ _ hc]

theorem d021430 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β / _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β‖ ≤
      (3 / 2 : ℝ) * Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) ^ (-((21 : ℝ) / 2)) *
        (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹ * Real.exp b := by
  rw [← _root_.GD.N0106.N0428.N0765.N1672.d021429 he a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)]
  convert _root_.GD.N0106.N0428.N0765.N1538.d021261 he a b α β hw using 1 <;> ring

end
end GD.N0106.N0428.N0765.N1672

#print axioms _root_.GD.N0106.N0428.N0765.N1672.d021425
#print axioms _root_.GD.N0106.N0428.N0765.N1672.d021426
#print axioms _root_.GD.N0106.N0428.N0765.N1672.d021427
#print axioms _root_.GD.N0106.N0428.N0765.N1672.d021428
#print axioms _root_.GD.N0106.N0428.N0765.N1672.d021429
#print axioms _root_.GD.N0106.N0428.N0765.N1672.d021430
