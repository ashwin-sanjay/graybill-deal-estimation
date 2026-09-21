import GD.Module0232















namespace GD.N0232.N0719.N1016

noncomputable section


def d003608
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  (z₁ - z₂) ^ 2 / (p₁ + p₂) +
  (z₁ - z₃) ^ 2 / (p₁ + p₃) +
  (z₂ - z₃) ^ 2 / (p₂ + p₃)



def d003609
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  let u := z₁ - z₃
  let w := z₂ - z₃
  (-(p₁ / 3) * (1 / (p₁ + p₂) + 1 / (p₁ + p₃)) * u ^ 3 +
    p₁ / (p₁ + p₂) * u ^ 2 * w +
    p₂ / (p₁ + p₂) * u * w ^ 2 -
    (p₂ / 3) * (1 / (p₁ + p₂) + 1 / (p₂ + p₃)) * w ^ 3)


def d003610
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  let u := z₁ - z₃
  let w := z₂ - z₃
  (-p₁ * (1 / (p₁ + p₂) + 1 / (p₁ + p₃)) * u ^ 2 +
    2 * p₁ / (p₁ + p₂) * u * w +
    p₂ / (p₁ + p₂) * w ^ 2)


def d003611
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  let u := z₁ - z₃
  let w := z₂ - z₃
  (p₁ / (p₁ + p₂) * u ^ 2 +
    2 * p₂ / (p₁ + p₂) * u * w -
    p₂ * (1 / (p₁ + p₂) + 1 / (p₂ + p₃)) * w ^ 2)


def d003612
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  -_root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ z₁ z₂ z₃ - _root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ z₁ z₂ z₃

theorem d003613
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) :
    HasDerivAt
      (fun x ↦ _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ x z₂ z₃)
      (_root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ z₁ z₂ z₃) z₁ := by
  have hu : HasDerivAt (fun x : ℝ ↦ x - z₃) 1 z₁ :=
    (hasDerivAt_id z₁).sub_const z₃
  have h1 :=
    (hu.pow 3).const_mul
      (-(p₁ / 3) * (1 / (p₁ + p₂) + 1 / (p₁ + p₃)))
  have h2 :=
    (hu.pow 2).const_mul
      (p₁ / (p₁ + p₂) * (z₂ - z₃))
  have h3 :=
    hu.const_mul
      (p₂ / (p₁ + p₂) * (z₂ - z₃) ^ 2)
  have h4 :=
    hasDerivAt_const z₁
      (-(p₂ / 3) *
        (1 / (p₁ + p₂) + 1 / (p₂ + p₃)) * (z₂ - z₃) ^ 3)
  simp only [_root_.GD.N0232.N0719.N1016.d003609, _root_.GD.N0232.N0719.N1016.d003610]
  convert ((h1.add h2).add h3).add h4 using 1
  all_goals first
    | rfl
    | (funext x; simp only [Pi.add_apply, Pi.pow_apply]; ring)
    | ring

theorem d003614
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) :
    HasDerivAt
      (fun x ↦ _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ x z₃)
      (_root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ z₁ z₂ z₃) z₂ := by
  have hw : HasDerivAt (fun x : ℝ ↦ x - z₃) 1 z₂ :=
    (hasDerivAt_id z₂).sub_const z₃
  have h1 :=
    hasDerivAt_const z₂
      (-(p₁ / 3) *
        (1 / (p₁ + p₂) + 1 / (p₁ + p₃)) * (z₁ - z₃) ^ 3)
  have h2 :=
    hw.const_mul
      (p₁ / (p₁ + p₂) * (z₁ - z₃) ^ 2)
  have h3 :=
    (hw.pow 2).const_mul
      (p₂ / (p₁ + p₂) * (z₁ - z₃))
  have h4 :=
    (hw.pow 3).const_mul
      (-(p₂ / 3) * (1 / (p₁ + p₂) + 1 / (p₂ + p₃)))
  simp only [_root_.GD.N0232.N0719.N1016.d003609, _root_.GD.N0232.N0719.N1016.d003611]
  convert ((h1.add h2).add h3).add h4 using 1
  all_goals first
    | rfl
    | (funext x; simp only [Pi.add_apply, Pi.pow_apply]; ring)
    | ring

theorem d003615
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) :
    HasDerivAt
      (fun x ↦ _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ x)
      (_root_.GD.N0232.N0719.N1016.d003612 p₁ p₂ p₃ z₁ z₂ z₃) z₃ := by
  have hu := (hasDerivAt_id z₃).neg.add_const z₁
  have hw := (hasDerivAt_id z₃).neg.add_const z₂
  have h1 :=
    (hu.pow 3).const_mul
      (-(p₁ / 3) * (1 / (p₁ + p₂) + 1 / (p₁ + p₃)))
  have h2 :=
    ((hu.pow 2).mul hw).const_mul
      (p₁ / (p₁ + p₂))
  have h3 :=
    (hu.mul (hw.pow 2)).const_mul
      (p₂ / (p₁ + p₂))
  have h4 :=
    (hw.pow 3).const_mul
      (-(p₂ / 3) * (1 / (p₁ + p₂) + 1 / (p₂ + p₃)))
  simp only [_root_.GD.N0232.N0719.N1016.d003609, _root_.GD.N0232.N0719.N1016.d003610, _root_.GD.N0232.N0719.N1016.d003611, _root_.GD.N0232.N0719.N1016.d003612]
  convert ((h1.add h2).add h3).add h4 using 1
  all_goals first
    | rfl
    | (funext x
       simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.neg_apply, id_eq]
       ring)
    | (simp only [Pi.pow_apply, Pi.neg_apply, id_eq]; ring)
    | ring

theorem d003616
    (p₁ p₂ p₃ z₁ z₂ z₃ c : ℝ) :
    _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ (z₁ + c) (z₂ + c) (z₃ + c) =
      _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by
  simp only [_root_.GD.N0232.N0719.N1016.d003608]
  ring

theorem d003617
    (p₁ p₂ p₃ z₁ z₂ z₃ c : ℝ) :
    _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ (z₁ + c) (z₂ + c) (z₃ + c) =
      _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ := by
  simp only [_root_.GD.N0232.N0719.N1016.d003609]
  ring

theorem d003618
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) :
    _root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ z₁ z₂ z₃ +
        _root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ z₁ z₂ z₃ +
        _root_.GD.N0232.N0719.N1016.d003612 p₁ p₂ p₃ z₁ z₂ z₃ = 0 := by
  simp [_root_.GD.N0232.N0719.N1016.d003612]

theorem d003619
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    0 ≤ _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by
  simp only [_root_.GD.N0232.N0719.N1016.d003608]
  positivity

theorem d003620
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ = 0 ↔
      z₁ = z₂ ∧ z₁ = z₃ := by
  constructor
  · intro h
    have h12n : 0 ≤ (z₁ - z₂) ^ 2 / (p₁ + p₂) := by positivity
    have h13n : 0 ≤ (z₁ - z₃) ^ 2 / (p₁ + p₃) := by positivity
    have h23n : 0 ≤ (z₂ - z₃) ^ 2 / (p₂ + p₃) := by positivity
    have h12z : (z₁ - z₂) ^ 2 / (p₁ + p₂) = 0 := by
      simp only [_root_.GD.N0232.N0719.N1016.d003608] at h
      nlinarith
    have h13z : (z₁ - z₃) ^ 2 / (p₁ + p₃) = 0 := by
      simp only [_root_.GD.N0232.N0719.N1016.d003608] at h
      nlinarith
    have h12s : (z₁ - z₂) ^ 2 = 0 :=
      (div_eq_zero_iff.mp h12z).resolve_right (ne_of_gt h₁₂)
    have h13s : (z₁ - z₃) ^ 2 = 0 :=
      (div_eq_zero_iff.mp h13z).resolve_right (ne_of_gt h₁₃)
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    simp [_root_.GD.N0232.N0719.N1016.d003608]

theorem d003621
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    _root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ z₁ z₂ z₃ +
        p₁ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ =
      (z₂ - z₃) ^ 2 / (p₂ + p₃) := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  simp only [_root_.GD.N0232.N0719.N1016.d003610, _root_.GD.N0232.N0719.N1016.d003608]
  field_simp [h₁₂, h₁₃, h₂₃]
  <;> ring

theorem d003622
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    _root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ z₁ z₂ z₃ +
        p₂ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ =
      (z₁ - z₃) ^ 2 / (p₁ + p₃) := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  simp only [_root_.GD.N0232.N0719.N1016.d003611, _root_.GD.N0232.N0719.N1016.d003608]
  field_simp [h₁₂, h₁₃, h₂₃]
  <;> ring

theorem d003623
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    _root_.GD.N0232.N0719.N1016.d003612 p₁ p₂ p₃ z₁ z₂ z₃ +
        p₃ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ =
      (z₁ - z₂) ^ 2 / (p₁ + p₂) := by
  have h1 := _root_.GD.N0232.N0719.N1016.d003621
    (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
    (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) hsum h₁₂ h₁₃ h₂₃
  have h2 := _root_.GD.N0232.N0719.N1016.d003622
    (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
    (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) hsum h₁₂ h₁₃ h₂₃
  have hD :
      (z₁ - z₂) ^ 2 / (p₁ + p₂) +
          (z₁ - z₃) ^ 2 / (p₁ + p₃) +
          (z₂ - z₃) ^ 2 / (p₂ + p₃) =
        _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by
    rfl
  calc
    _root_.GD.N0232.N0719.N1016.d003612 p₁ p₂ p₃ z₁ z₂ z₃ +
          p₃ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ =
        -(_root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ z₁ z₂ z₃ +
            p₁ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃) -
          (_root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ z₁ z₂ z₃ +
            p₂ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃) +
          (p₁ + p₂ + p₃) * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by
            simp only [_root_.GD.N0232.N0719.N1016.d003612]
            ring
    _ = -(z₂ - z₃) ^ 2 / (p₂ + p₃) -
          (z₁ - z₃) ^ 2 / (p₁ + p₃) +
          _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by
            rw [h1, h2, hsum]
            ring
    _ = (z₁ - z₂) ^ 2 / (p₁ + p₂) := by
            rw [← hD]
            ring

theorem d003624
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    z₁ * _root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ z₁ z₂ z₃ +
        z₂ * _root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ z₁ z₂ z₃ +
        z₃ * _root_.GD.N0232.N0719.N1016.d003612 p₁ p₂ p₃ z₁ z₂ z₃ =
      3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ := by
  simp only [_root_.GD.N0232.N0719.N1016.d003610, _root_.GD.N0232.N0719.N1016.d003611, _root_.GD.N0232.N0719.N1016.d003612, _root_.GD.N0232.N0719.N1016.d003609]
  field_simp [h₁₂, h₁₃, h₂₃]
  <;> ring

theorem d003625
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0)
    (hD : _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ ≠ 0) :
    p₁ * z₁ + p₂ * z₂ + p₃ * z₃ +
        3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ /
          _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ =
      z₁ * ((z₂ - z₃) ^ 2 / (p₂ + p₃)) /
          _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ +
      z₂ * ((z₁ - z₃) ^ 2 / (p₁ + p₃)) /
          _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ +
      z₃ * ((z₁ - z₂) ^ 2 / (p₁ + p₂)) /
          _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by
  have h1 := _root_.GD.N0232.N0719.N1016.d003621
    (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
    (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) hsum h₁₂ h₁₃ h₂₃
  have h2 := _root_.GD.N0232.N0719.N1016.d003622
    (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
    (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) hsum h₁₂ h₁₃ h₂₃
  have h3 := _root_.GD.N0232.N0719.N1016.d003623
    (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
    (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) hsum h₁₂ h₁₃ h₂₃
  have he := _root_.GD.N0232.N0719.N1016.d003624
    (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
    (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) h₁₂ h₁₃ h₂₃
  have hnum :
      (p₁ * z₁ + p₂ * z₂ + p₃ * z₃) *
            _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ +
          3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ =
        z₁ * ((z₂ - z₃) ^ 2 / (p₂ + p₃)) +
          z₂ * ((z₁ - z₃) ^ 2 / (p₁ + p₃)) +
          z₃ * ((z₁ - z₂) ^ 2 / (p₁ + p₂)) := by
    calc
      (p₁ * z₁ + p₂ * z₂ + p₃ * z₃) *
              _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ +
            3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ =
          z₁ * (_root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ z₁ z₂ z₃ +
              p₁ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃) +
            z₂ * (_root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ z₁ z₂ z₃ +
              p₂ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃) +
            z₃ * (_root_.GD.N0232.N0719.N1016.d003612 p₁ p₂ p₃ z₁ z₂ z₃ +
              p₃ * _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃) := by
                rw [← he]
                ring
      _ = z₁ * ((z₂ - z₃) ^ 2 / (p₂ + p₃)) +
            z₂ * ((z₁ - z₃) ^ 2 / (p₁ + p₃)) +
            z₃ * ((z₁ - z₂) ^ 2 / (p₁ + p₂)) := by
              rw [h1, h2, h3]
  calc
    p₁ * z₁ + p₂ * z₂ + p₃ * z₃ +
          3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ /
            _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ =
        ((p₁ * z₁ + p₂ * z₂ + p₃ * z₃) *
              _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ +
            3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃) /
          _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by
            field_simp [hD]
            <;> ring
    _ = (z₁ * ((z₂ - z₃) ^ 2 / (p₂ + p₃)) +
            z₂ * ((z₁ - z₃) ^ 2 / (p₁ + p₃)) +
            z₃ * ((z₁ - z₂) ^ 2 / (p₁ + p₂))) /
          _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by rw [hnum]
    _ = z₁ * ((z₂ - z₃) ^ 2 / (p₂ + p₃)) /
            _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ +
          z₂ * ((z₁ - z₃) ^ 2 / (p₁ + p₃)) /
            _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ +
          z₃ * ((z₁ - z₂) ^ 2 / (p₁ + p₂)) /
            _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ z₁ z₂ z₃ := by ring



def d003626
    (p₁ p₂ p₃ v₁ v₂ v₃ : ℝ) : ℝ :=
  (v₁ + v₂) / (p₁ + p₂) +
  (v₁ + v₃) / (p₁ + p₃) +
  (v₂ + v₃) / (p₂ + p₃)

def d003627
    (p₁ p₂ p₃ v₁ v₂ v₃ : ℝ) : ℝ :=
  (v₂ + v₃) / (p₂ + p₃) -
    p₁ * _root_.GD.N0232.N0719.N1016.d003626 p₁ p₂ p₃ v₁ v₂ v₃

def d003628
    (p₁ p₂ p₃ v₁ v₂ v₃ : ℝ) : ℝ :=
  (v₁ + v₃) / (p₁ + p₃) -
    p₂ * _root_.GD.N0232.N0719.N1016.d003626 p₁ p₂ p₃ v₁ v₂ v₃

def d003629
    (p₁ p₂ p₃ v₁ v₂ v₃ : ℝ) : ℝ :=
  (v₁ + v₂) / (p₁ + p₂) -
    p₃ * _root_.GD.N0232.N0719.N1016.d003626 p₁ p₂ p₃ v₁ v₂ v₃


theorem d003630
    {p₁ p₂ p₃ v₁ v₂ v₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    p₁ * v₁ * _root_.GD.N0232.N0719.N1016.d003627 p₁ p₂ p₃ v₁ v₂ v₃ +
        p₂ * v₂ * _root_.GD.N0232.N0719.N1016.d003628 p₁ p₂ p₃ v₁ v₂ v₃ +
        p₃ * v₃ * _root_.GD.N0232.N0719.N1016.d003629 p₁ p₂ p₃ v₁ v₂ v₃ =
      -_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃
        (p₁ * v₁) (p₂ * v₂) (p₃ * v₃) := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  simp only [_root_.GD.N0232.N0719.N1016.d003627, _root_.GD.N0232.N0719.N1016.d003628, _root_.GD.N0232.N0719.N1016.d003629,
    _root_.GD.N0232.N0719.N1016.d003626, _root_.GD.N0232.N0719.N1016.d003608]
  field_simp [h₁₂, h₁₃, h₂₃]
  <;> ring

theorem d003631
    {p₁ p₂ p₃ v₁ v₂ v₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    p₁ * v₁ * _root_.GD.N0232.N0719.N1016.d003627 p₁ p₂ p₃ v₁ v₂ v₃ +
        p₂ * v₂ * _root_.GD.N0232.N0719.N1016.d003628 p₁ p₂ p₃ v₁ v₂ v₃ +
        p₃ * v₃ * _root_.GD.N0232.N0719.N1016.d003629 p₁ p₂ p₃ v₁ v₂ v₃ ≤ 0 := by
  rw [_root_.GD.N0232.N0719.N1016.d003630 hsum
    (ne_of_gt h₁₂) (ne_of_gt h₁₃) (ne_of_gt h₂₃)]
  exact neg_nonpos.mpr (_root_.GD.N0232.N0719.N1016.d003619 h₁₂ h₁₃ h₂₃)

theorem d003632
    {p₁ p₂ p₃ v₁ v₂ v₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    p₁ * v₁ * _root_.GD.N0232.N0719.N1016.d003627 p₁ p₂ p₃ v₁ v₂ v₃ +
          p₂ * v₂ * _root_.GD.N0232.N0719.N1016.d003628 p₁ p₂ p₃ v₁ v₂ v₃ +
          p₃ * v₃ * _root_.GD.N0232.N0719.N1016.d003629 p₁ p₂ p₃ v₁ v₂ v₃ = 0 ↔
      p₁ * v₁ = p₂ * v₂ ∧ p₁ * v₁ = p₃ * v₃ := by
  rw [_root_.GD.N0232.N0719.N1016.d003630 hsum
    (ne_of_gt h₁₂) (ne_of_gt h₁₃) (ne_of_gt h₂₃)]
  rw [neg_eq_zero]
  exact _root_.GD.N0232.N0719.N1016.d003620 h₁₂ h₁₃ h₂₃

theorem d003633
    {p₁ p₂ p₃ v₁ v₂ v₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃)
    (hmismatch :
      ¬(p₁ * v₁ = p₂ * v₂ ∧ p₁ * v₁ = p₃ * v₃)) :
    p₁ * v₁ * _root_.GD.N0232.N0719.N1016.d003627 p₁ p₂ p₃ v₁ v₂ v₃ +
        p₂ * v₂ * _root_.GD.N0232.N0719.N1016.d003628 p₁ p₂ p₃ v₁ v₂ v₃ +
        p₃ * v₃ * _root_.GD.N0232.N0719.N1016.d003629 p₁ p₂ p₃ v₁ v₂ v₃ < 0 := by
  have hnonpos :=
    _root_.GD.N0232.N0719.N1016.d003631
      (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
      hsum h₁₂ h₁₃ h₂₃
  exact lt_of_le_of_ne hnonpos
    (fun hzero =>
      hmismatch
        ((_root_.GD.N0232.N0719.N1016.d003632
          (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
          (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
          hsum h₁₂ h₁₃ h₂₃).mp hzero))

end

end GD.N0232.N0719.N1016
