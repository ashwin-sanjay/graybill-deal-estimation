import GD.Module0232

























namespace GD
namespace N0228
namespace N0547
namespace N0794

noncomputable section


def d003409 (ρ t ξ : ℝ) : ℝ :=
  t + ξ / ρ + (1 - ξ) / (1 - ρ)


def d003410 (ρ : ℝ) : ℝ :=
  1 / (1 - ρ)


def d003411 (ρ : ℝ) : ℝ :=
  1 / ρ - 1 / (1 - ρ)


def d003412 (t ξ d b : ℝ) : ℝ :=
  t + d + b * ξ


theorem d003413
    {ρ t ξ : ℝ} (hρ : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) :
    _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ =
      _root_.GD.N0228.N0547.N0794.d003412 t ξ (_root_.GD.N0228.N0547.N0794.d003410 ρ) (_root_.GD.N0228.N0547.N0794.d003411 ρ) := by
  simp only [_root_.GD.N0228.N0547.N0794.d003409, _root_.GD.N0228.N0547.N0794.d003412, _root_.GD.N0228.N0547.N0794.d003410, _root_.GD.N0228.N0547.N0794.d003411]
  field_simp [hρ, hρ1]
  ring


theorem d003414
    {ρ : ℝ} (hρ : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) :
    _root_.GD.N0228.N0547.N0794.d003410 ρ * (_root_.GD.N0228.N0547.N0794.d003411 ρ + _root_.GD.N0228.N0547.N0794.d003410 ρ) =
      _root_.GD.N0228.N0547.N0794.d003411 ρ + 2 * _root_.GD.N0228.N0547.N0794.d003410 ρ := by
  simp only [_root_.GD.N0228.N0547.N0794.d003410, _root_.GD.N0228.N0547.N0794.d003411]
  field_simp [hρ, hρ1]
  ring


theorem d003415
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    _root_.GD.N0228.N0547.N0794.d003410 ρ * (_root_.GD.N0228.N0547.N0794.d003411 ρ + _root_.GD.N0228.N0547.N0794.d003410 ρ) =
      _root_.GD.N0228.N0547.N0794.d003411 ρ + 2 * _root_.GD.N0228.N0547.N0794.d003410 ρ := by
  exact _root_.GD.N0228.N0547.N0794.d003414 (ne_of_gt hρ0)
    (ne_of_gt (sub_pos.mpr hρ1))



structure d003416 where
  value : ℝ
  dt : ℝ
  dξ : ℝ
  dtt : ℝ
  dtξ : ℝ
  dξξ : ℝ









def d003417 (κ t ξ : ℝ) (J : _root_.GD.N0228.N0547.N0794.d003416) : ℝ :=

  ξ * (1 - ξ) * J.dξξ + 2 * (1 - 2 * ξ) * J.dξ - 2 * J.value

  + (1 - 2 * ξ) * (1 + t) * J.dtξ
  + (1 - 2 * ξ) * J.dξ - 2 * (1 + t) * J.dt - 2 * J.value

  - t * (t + 2) * J.dtt - 4 * (t + 1) * J.dt - 2 * J.value

  - (2 * (κ - 1) * (1 + t) * J.dt + 2 * (κ - 1) * J.value)
  - ((κ - 1) * (2 * ξ - 1) * J.dξ + 2 * (κ - 1) * J.value)

  - κ * (κ - 1) * J.value



def d003418 (m t ξ d b : ℝ) : _root_.GD.N0228.N0547.N0794.d003416 :=
  let D := _root_.GD.N0228.N0547.N0794.d003412 t ξ d b
  { value := D ^ (-m)
    dt := -m * D ^ (-m - 1)
    dξ := -m * b * D ^ (-m - 1)
    dtt := m * (m + 1) * D ^ (-m - 2)
    dtξ := m * (m + 1) * b * D ^ (-m - 2)
    dξξ := m * (m + 1) * b ^ 2 * D ^ (-m - 2) }



theorem d003419
    {m κ t ξ d b : ℝ}
    (hκ : κ = m - 1)
    (hD : 0 < _root_.GD.N0228.N0547.N0794.d003412 t ξ d b) :
    _root_.GD.N0228.N0547.N0794.d003417 κ t ξ (_root_.GD.N0228.N0547.N0794.d003418 m t ξ d b) =
      m * (m + 1) *
        _root_.GD.N0228.N0547.N0794.d003412 t ξ d b ^ (-m - 2) *
          (b + 2 * d - d * (b + d)) := by
  let D := _root_.GD.N0228.N0547.N0794.d003412 t ξ d b
  have hD' : 0 < D := hD
  have hpow₁ : D ^ (-m - 1) = D * D ^ (-m - 2) := by
    calc
      D ^ (-m - 1) = D ^ ((1 : ℝ) + (-m - 2)) := by
        congr 1
        ring
      _ = D ^ (1 : ℝ) * D ^ (-m - 2) :=
        Real.rpow_add hD' (1 : ℝ) (-m - 2)
      _ = D * D ^ (-m - 2) := by rw [Real.rpow_one]
  have hpow₀ : D ^ (-m) = D ^ 2 * D ^ (-m - 2) := by
    calc
      D ^ (-m) = D ^ ((2 : ℝ) + (-m - 2)) := by
        congr 1
        ring
      _ = D ^ (2 : ℝ) * D ^ (-m - 2) :=
        Real.rpow_add hD' (2 : ℝ) (-m - 2)
      _ = D ^ (2 : ℕ) * D ^ (-m - 2) := by
        rw [Real.rpow_two]
  simp only [_root_.GD.N0228.N0547.N0794.d003417, _root_.GD.N0228.N0547.N0794.d003418]
  change _ = m * (m + 1) * D ^ (-m - 2) *
    (b + 2 * d - d * (b + d))
  rw [hκ, hpow₁, hpow₀]
  simp only [D, _root_.GD.N0228.N0547.N0794.d003412]
  ring



theorem d003420
    {m κ t ξ d b : ℝ}
    (hκ : κ = m - 1)
    (hD : 0 < _root_.GD.N0228.N0547.N0794.d003412 t ξ d b)
    (hrel : d * (b + d) = b + 2 * d) :
    _root_.GD.N0228.N0547.N0794.d003417 κ t ξ (_root_.GD.N0228.N0547.N0794.d003418 m t ξ d b) = 0 := by
  rw [_root_.GD.N0228.N0547.N0794.d003419 hκ hD, hrel]
  ring



theorem d003421
    {ρ t ξ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ht : 0 < t)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    0 < _root_.GD.N0228.N0547.N0794.d003409 ρ t ξ := by
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  have h1ξ : 0 < 1 - ξ := sub_pos.mpr hξ1
  simp only [_root_.GD.N0228.N0547.N0794.d003409]
  positivity



theorem d003422
    {ρ m κ t ξ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ht : 0 < t) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hκ : κ = m - 1) :
    _root_.GD.N0228.N0547.N0794.d003417 κ t ξ
        (_root_.GD.N0228.N0547.N0794.d003418 m t ξ (_root_.GD.N0228.N0547.N0794.d003410 ρ) (_root_.GD.N0228.N0547.N0794.d003411 ρ)) = 0 := by
  apply _root_.GD.N0228.N0547.N0794.d003420 hκ
  · rw [← _root_.GD.N0228.N0547.N0794.d003413
      (ne_of_gt hρ0) (ne_of_gt (sub_pos.mpr hρ1))]
    exact _root_.GD.N0228.N0547.N0794.d003421 hρ0 hρ1 ht hξ0 hξ1
  · exact _root_.GD.N0228.N0547.N0794.d003415 hρ0 hρ1


theorem d003423
    {m t ξ d b : ℝ} (hD : 0 < _root_.GD.N0228.N0547.N0794.d003412 t ξ d b) :
    HasDerivAt
      (fun u : ℝ => _root_.GD.N0228.N0547.N0794.d003412 u ξ d b ^ (-m))
      (-m * _root_.GD.N0228.N0547.N0794.d003412 t ξ d b ^ (-m - 1)) t := by
  have hinner :
      HasDerivAt (fun u : ℝ => _root_.GD.N0228.N0547.N0794.d003412 u ξ d b) 1 t := by
    simpa only [_root_.GD.N0228.N0547.N0794.d003412] using
      ((hasDerivAt_id' t).add_const d).add_const (b * ξ)
  have hpow := hinner.rpow_const (p := -m) (Or.inl (ne_of_gt hD))
  simpa only [one_mul] using hpow


theorem d003424
    {m t ξ d b : ℝ} (hD : 0 < _root_.GD.N0228.N0547.N0794.d003412 t ξ d b) :
    HasDerivAt
      (fun u : ℝ => _root_.GD.N0228.N0547.N0794.d003412 t u d b ^ (-m))
      (-m * b * _root_.GD.N0228.N0547.N0794.d003412 t ξ d b ^ (-m - 1)) ξ := by
  have hinner :
      HasDerivAt (fun u : ℝ => _root_.GD.N0228.N0547.N0794.d003412 t u d b) b ξ := by
    simpa only [_root_.GD.N0228.N0547.N0794.d003412, add_assoc, mul_one] using
      ((hasDerivAt_id' ξ).const_mul b).const_add (t + d)
  have hpow := hinner.rpow_const (p := -m) (Or.inl (ne_of_gt hD))
  convert hpow using 1
  ring

#print axioms _root_.GD.N0228.N0547.N0794.d003414
#print axioms _root_.GD.N0228.N0547.N0794.d003419
#print axioms _root_.GD.N0228.N0547.N0794.d003420
#print axioms _root_.GD.N0228.N0547.N0794.d003422
#print axioms _root_.GD.N0228.N0547.N0794.d003423
#print axioms _root_.GD.N0228.N0547.N0794.d003424

end
end N0794
end N0547
end N0228
end GD
