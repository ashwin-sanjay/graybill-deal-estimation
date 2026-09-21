import GD.Module0235






















namespace GD.N0228.N0547.N0795

noncomputable section

open MeasureTheory Set
open _root_.GD.N0228.N0547.N0794




def d003425 (t R : ℝ) : ℝ := t * R


def d003426 (ξ R : ℝ) : ℝ := ξ * R


def d003427 (ξ R : ℝ) : ℝ := (1 - ξ) * R


def d003428 (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (_root_.GD.N0228.N0547.N0795.d003425 p.1 p.2.2, _root_.GD.N0228.N0547.N0795.d003426 p.2.1 p.2.2,
    _root_.GD.N0228.N0547.N0795.d003427 p.2.1 p.2.2)


def d003429 (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.1 / (p.2.1 + p.2.2), p.2.1 / (p.2.1 + p.2.2),
    p.2.1 + p.2.2)


theorem d003430 (ξ R : ℝ) :
    _root_.GD.N0228.N0547.N0795.d003426 ξ R + _root_.GD.N0228.N0547.N0795.d003427 ξ R = R := by
  simp only [_root_.GD.N0228.N0547.N0795.d003426, _root_.GD.N0228.N0547.N0795.d003427]
  ring



theorem d003431
    {t ξ R : ℝ} (hR : R ≠ 0) :
    _root_.GD.N0228.N0547.N0795.d003425 t R /
        (_root_.GD.N0228.N0547.N0795.d003426 ξ R + _root_.GD.N0228.N0547.N0795.d003427 ξ R) = t := by
  rw [_root_.GD.N0228.N0547.N0795.d003430]
  exact mul_div_cancel_right₀ t hR


theorem d003432
    {ξ R : ℝ} (hR : R ≠ 0) :
    _root_.GD.N0228.N0547.N0795.d003426 ξ R /
        (_root_.GD.N0228.N0547.N0795.d003426 ξ R + _root_.GD.N0228.N0547.N0795.d003427 ξ R) = ξ := by
  rw [_root_.GD.N0228.N0547.N0795.d003430]
  exact mul_div_cancel_right₀ ξ hR



theorem d003433
    {T U V : ℝ} (hUV : U + V ≠ 0) :
    _root_.GD.N0228.N0547.N0795.d003428 (_root_.GD.N0228.N0547.N0795.d003429 (T, U, V)) = (T, U, V) := by
  apply Prod.ext
  · simp only [_root_.GD.N0228.N0547.N0795.d003428, _root_.GD.N0228.N0547.N0795.d003429, _root_.GD.N0228.N0547.N0795.d003425]
    exact div_mul_cancel₀ T hUV
  · apply Prod.ext
    · simp only [_root_.GD.N0228.N0547.N0795.d003428, _root_.GD.N0228.N0547.N0795.d003429, _root_.GD.N0228.N0547.N0795.d003426]
      exact div_mul_cancel₀ U hUV
    · simp only [_root_.GD.N0228.N0547.N0795.d003428, _root_.GD.N0228.N0547.N0795.d003429, _root_.GD.N0228.N0547.N0795.d003427]
      rw [sub_mul, one_mul, div_mul_cancel₀ U hUV]
      ring


theorem d003434
    {t ξ R : ℝ} (hR : R ≠ 0) :
    _root_.GD.N0228.N0547.N0795.d003429 (_root_.GD.N0228.N0547.N0795.d003428 (t, ξ, R)) = (t, ξ, R) := by
  apply Prod.ext
  · exact _root_.GD.N0228.N0547.N0795.d003431 hR
  · apply Prod.ext
    · exact _root_.GD.N0228.N0547.N0795.d003432 hR
    · exact _root_.GD.N0228.N0547.N0795.d003430 ξ R


def d003435 (t ξ R : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![R, 0, t;
     0, R, ξ;
     0, -R, 1 - ξ]


theorem d003436 (t ξ R : ℝ) :
    (_root_.GD.N0228.N0547.N0795.d003435 t ξ R).det = R ^ 2 := by
  rw [Matrix.det_fin_three]
  change
    R * R * (1 - ξ) - R * ξ * (-R) - 0 * 0 * (1 - ξ) +
      0 * ξ * 0 + t * 0 * (-R) - t * R * 0 = R ^ 2
  ring




def d003437 (ρ T U V : ℝ) : ℝ :=
  T + U / ρ + V / (1 - ρ)


theorem d003438 (ρ t ξ R : ℝ) :
    _root_.GD.N0228.N0547.N0795.d003437 ρ (_root_.GD.N0228.N0547.N0795.d003425 t R) (_root_.GD.N0228.N0547.N0795.d003426 ξ R)
        (_root_.GD.N0228.N0547.N0795.d003427 ξ R) =
      R * _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ := by
  simp only [_root_.GD.N0228.N0547.N0795.d003437, _root_.GD.N0228.N0547.N0795.d003425, _root_.GD.N0228.N0547.N0795.d003426, _root_.GD.N0228.N0547.N0795.d003427,
    _root_.GD.N0228.N0547.N0794.d003409]
  ring



theorem d003439
    { ρ t ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    t < _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ := by
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  have h1ξ : 0 < 1 - ξ := sub_pos.mpr hξ1
  simp only [_root_.GD.N0228.N0547.N0794.d003409]
  have hfirst : 0 < ξ / ρ := div_pos hξ0 hρ0
  have hsecond : 0 < (1 - ξ) / (1 - ρ) := div_pos h1ξ h1ρ
  linarith


theorem d003440
    {ρ t ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ht : 0 < t) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    0 < _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ :=
  _root_.GD.N0228.N0547.N0794.d003421 hρ0 hρ1 ht hξ0 hξ1


theorem d003441
    {ρ t ξ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ =
      _root_.GD.N0228.N0547.N0794.d003412 t ξ (_root_.GD.N0228.N0547.N0794.d003410 ρ) (_root_.GD.N0228.N0547.N0794.d003411 ρ) :=
  _root_.GD.N0228.N0547.N0794.d003413 hρ0.ne' (sub_pos.mpr hρ1).ne'




def d003442 (α β : ℝ) : ℝ := α + β + (1 : ℝ) / 2


def d003443 (α β t ξ : ℝ) : ℝ :=
  t ^ (-(1 : ℝ) / 2) * ξ ^ (α - 1) * (1 - ξ) ^ (β - 1)


def d003444 (α β T U V : ℝ) : ℝ :=
  T ^ (-(1 : ℝ) / 2) * U ^ (α - 1) * V ^ (β - 1)



theorem d003445
    {α β t ξ R : ℝ}
    (ht : 0 < t) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hR : 0 < R) :
    _root_.GD.N0228.N0547.N0795.d003444 α β (_root_.GD.N0228.N0547.N0795.d003425 t R) (_root_.GD.N0228.N0547.N0795.d003426 ξ R)
        (_root_.GD.N0228.N0547.N0795.d003427 ξ R) * R ^ 2 =
      _root_.GD.N0228.N0547.N0795.d003443 α β t ξ * R ^ (_root_.GD.N0228.N0547.N0795.d003442 α β - 1) := by
  have h1ξ : 0 < 1 - ξ := sub_pos.mpr hξ1
  simp only [_root_.GD.N0228.N0547.N0795.d003444, _root_.GD.N0228.N0547.N0795.d003425, _root_.GD.N0228.N0547.N0795.d003426, _root_.GD.N0228.N0547.N0795.d003427,
    _root_.GD.N0228.N0547.N0795.d003443, _root_.GD.N0228.N0547.N0795.d003442]
  rw [Real.mul_rpow ht.le hR.le]
  rw [Real.mul_rpow hξ0.le hR.le]
  rw [Real.mul_rpow h1ξ.le hR.le]
  rw [← Real.rpow_two]
  calc
    _ = t ^ (-(1 : ℝ) / 2) * ξ ^ (α - 1) * (1 - ξ) ^ (β - 1) *
        (R ^ (-(1 : ℝ) / 2) * R ^ (α - 1) * R ^ (β - 1) *
          R ^ (2 : ℝ)) := by ring
    _ = t ^ (-(1 : ℝ) / 2) * ξ ^ (α - 1) * (1 - ξ) ^ (β - 1) *
        R ^ (α + β + (1 : ℝ) / 2 - 1) := by
      congr 1
      rw [← Real.rpow_add hR, ← Real.rpow_add hR, ← Real.rpow_add hR]
      congr 1
      ring


theorem d003446 (ρ t ξ R : ℝ) :
    Real.exp (-(_root_.GD.N0228.N0547.N0795.d003437 ρ (_root_.GD.N0228.N0547.N0795.d003425 t R) (_root_.GD.N0228.N0547.N0795.d003426 ξ R)
        (_root_.GD.N0228.N0547.N0795.d003427 ξ R) / 2)) =
      Real.exp (-((_root_.GD.N0228.N0547.N0794.d003409 ρ t ξ / 2) * R)) := by
  rw [_root_.GD.N0228.N0547.N0795.d003438]
  congr 1
  ring




def d003447 (m D R : ℝ) : ℝ :=
  R ^ (m - 1) * Real.exp (-((D / 2) * R))


theorem d003448
    {m D : ℝ} (hm : 0 < m) (hD : 0 < D) :
    ∫ R : ℝ in Ioi 0, _root_.GD.N0228.N0547.N0795.d003447 m D R =
      (2 / D) ^ m * Real.Gamma m := by
  have hrate : 0 < D / 2 := by positivity
  rw [show (∫ R : ℝ in Ioi 0, _root_.GD.N0228.N0547.N0795.d003447 m D R) =
      ∫ R : ℝ in Ioi 0,
        R ^ (m - 1) * Real.exp (-((D / 2) * R)) by rfl]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hm hrate]
  rw [show (1 / (D / 2) : ℝ) = 2 / D by rw [one_div, inv_div]]


def d003449 (α β ρ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-_root_.GD.N0228.N0547.N0795.d003442 α β) *
    (Real.Gamma ((1 : ℝ) / 2))⁻¹ * (Real.Gamma α)⁻¹ *
    (Real.Gamma β)⁻¹ * ρ ^ (-α) * (1 - ρ) ^ (-β)


def d003450 (α β ρ t ξ : ℝ) : ℝ :=
  Real.Gamma (_root_.GD.N0228.N0547.N0795.d003442 α β) *
    (Real.Gamma ((1 : ℝ) / 2))⁻¹ * (Real.Gamma α)⁻¹ *
    (Real.Gamma β)⁻¹ * ρ ^ (-α) * (1 - ρ) ^ (-β) *
    _root_.GD.N0228.N0547.N0795.d003443 α β t ξ *
    _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ ^ (-_root_.GD.N0228.N0547.N0795.d003442 α β)



theorem d003451
    {α β ρ D : ℝ} (hD : 0 < D) :
    _root_.GD.N0228.N0547.N0795.d003449 α β ρ * (2 / D) ^ (_root_.GD.N0228.N0547.N0795.d003442 α β) *
        Real.Gamma (_root_.GD.N0228.N0547.N0795.d003442 α β) =
      Real.Gamma (_root_.GD.N0228.N0547.N0795.d003442 α β) *
        (Real.Gamma ((1 : ℝ) / 2))⁻¹ * (Real.Gamma α)⁻¹ *
        (Real.Gamma β)⁻¹ * ρ ^ (-α) * (1 - ρ) ^ (-β) *
        D ^ (-_root_.GD.N0228.N0547.N0795.d003442 α β) := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  simp only [_root_.GD.N0228.N0547.N0795.d003449]
  rw [Real.div_rpow htwo.le hD.le]
  simp only [div_eq_mul_inv]
  rw [← Real.rpow_neg hD.le]
  calc
    _ = ((2 : ℝ) ^ (-_root_.GD.N0228.N0547.N0795.d003442 α β) * 2 ^ (_root_.GD.N0228.N0547.N0795.d003442 α β)) *
        (Real.Gamma (_root_.GD.N0228.N0547.N0795.d003442 α β) *
          (Real.Gamma ((1 : ℝ) / 2))⁻¹ * (Real.Gamma α)⁻¹ *
          (Real.Gamma β)⁻¹ * ρ ^ (-α) * (1 - ρ) ^ (-β) *
          D ^ (-_root_.GD.N0228.N0547.N0795.d003442 α β)) := by ring
    _ = _ := by
      rw [← Real.rpow_add htwo]
      simp only [neg_add_cancel, Real.rpow_zero, one_mul, one_div]



theorem d003452
    {α β ρ t ξ : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ht : 0 < t) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ∫ R : ℝ in Ioi 0,
        _root_.GD.N0228.N0547.N0795.d003449 α β ρ * _root_.GD.N0228.N0547.N0795.d003443 α β t ξ *
          _root_.GD.N0228.N0547.N0795.d003447 (_root_.GD.N0228.N0547.N0795.d003442 α β) (_root_.GD.N0228.N0547.N0794.d003409 ρ t ξ) R =
      _root_.GD.N0228.N0547.N0795.d003450 α β ρ t ξ := by
  have hm : 0 < _root_.GD.N0228.N0547.N0795.d003442 α β := by
    simp only [_root_.GD.N0228.N0547.N0795.d003442]
    linarith
  have hD : 0 < _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ :=
    _root_.GD.N0228.N0547.N0795.d003440 hρ0 hρ1 ht hξ0 hξ1
  rw [integral_const_mul]
  rw [_root_.GD.N0228.N0547.N0795.d003448 hm hD]
  calc
    _ = _root_.GD.N0228.N0547.N0795.d003443 α β t ξ *
          (_root_.GD.N0228.N0547.N0795.d003449 α β ρ *
            (2 / _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ) ^ _root_.GD.N0228.N0547.N0795.d003442 α β *
            Real.Gamma (_root_.GD.N0228.N0547.N0795.d003442 α β)) := by ring
    _ = _root_.GD.N0228.N0547.N0795.d003443 α β t ξ *
        (Real.Gamma (_root_.GD.N0228.N0547.N0795.d003442 α β) *
          (Real.Gamma ((1 : ℝ) / 2))⁻¹ * (Real.Gamma α)⁻¹ *
          (Real.Gamma β)⁻¹ * ρ ^ (-α) * (1 - ρ) ^ (-β) *
          _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ ^ (-_root_.GD.N0228.N0547.N0795.d003442 α β)) := by
      rw [_root_.GD.N0228.N0547.N0795.d003451 hD]
    _ = _root_.GD.N0228.N0547.N0795.d003450 α β ρ t ξ := by
      simp only [_root_.GD.N0228.N0547.N0795.d003450]
      ring







theorem d003453
    {m rate : ℝ} (hm : 0 < m) (hrate : 0 < rate) :
    ∫ R : ℝ in Ioi 0,
        (rate ^ m / Real.Gamma m) *
          (R ^ (m - 1) * Real.exp (-(rate * R))) = 1 := by
  rw [integral_const_mul]
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hm hrate]
  have hGamma : Real.Gamma m ≠ 0 := (Real.Gamma_pos_of_pos hm).ne'
  have hratepow : rate ^ m ≠ 0 := (Real.rpow_pos_of_pos hrate m).ne'
  rw [one_div, Real.inv_rpow hrate.le]
  calc
    rate ^ m / Real.Gamma m * ((rate ^ m)⁻¹ * Real.Gamma m) =
        (rate ^ m * (rate ^ m)⁻¹) *
          ((Real.Gamma m)⁻¹ * Real.Gamma m) := by ring
    _ = 1 := by
      rw [mul_inv_cancel₀ hratepow, inv_mul_cancel₀ hGamma, one_mul]

end

end GD.N0228.N0547.N0795

#print axioms _root_.GD.N0228.N0547.N0795.d003436
#print axioms _root_.GD.N0228.N0547.N0795.d003433
#print axioms _root_.GD.N0228.N0547.N0795.d003434
#print axioms _root_.GD.N0228.N0547.N0795.d003438
#print axioms _root_.GD.N0228.N0547.N0795.d003440
#print axioms _root_.GD.N0228.N0547.N0795.d003445
#print axioms _root_.GD.N0228.N0547.N0795.d003448
#print axioms _root_.GD.N0228.N0547.N0795.d003451
#print axioms _root_.GD.N0228.N0547.N0795.d003452
#print axioms _root_.GD.N0228.N0547.N0795.d003453
