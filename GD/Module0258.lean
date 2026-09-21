import GD.Module0256




























namespace GD.N0232.N0719.N0893

noncomputable section

open _root_.GD.N0232.N0719.N1016
open _root_.GD.N0232.N0719.N0888



def d003709
    (p₁ p₂ p₃
      w₁₁ w₂₂ w₃₃ w₁₂ w₁₃ w₂₃ : ℝ) : ℝ :=
  -p₁ * (1 / (p₁ + p₂) + 1 / (p₁ + p₃)) *
      (w₁₁ - 2 * w₁₃ + w₃₃) +
    2 * p₁ / (p₁ + p₂) *
      (w₁₂ - w₁₃ - w₂₃ + w₃₃) +
    p₂ / (p₁ + p₂) *
      (w₂₂ - 2 * w₂₃ + w₃₃)



def d003710
    (p₁ p₂ p₃
      w₁₁ w₂₂ w₃₃ w₁₂ w₁₃ w₂₃ : ℝ) : ℝ :=
  p₁ / (p₁ + p₂) *
      (w₁₁ - 2 * w₁₃ + w₃₃) +
    2 * p₂ / (p₁ + p₂) *
      (w₁₂ - w₁₃ - w₂₃ + w₃₃) -
    p₂ * (1 / (p₁ + p₂) + 1 / (p₂ + p₃)) *
      (w₂₂ - 2 * w₂₃ + w₃₃)



def d003711
    (p₁ p₂ p₃
      w₁₁ w₂₂ w₃₃ w₁₂ w₁₃ w₂₃ : ℝ) : ℝ :=
  -_root_.GD.N0232.N0719.N0893.d003709 p₁ p₂ p₃ w₁₁ w₂₂ w₃₃ w₁₂ w₁₃ w₂₃ -
    _root_.GD.N0232.N0719.N0893.d003710 p₁ p₂ p₃ w₁₁ w₂₂ w₃₃ w₁₂ w₁₃ w₂₃


def d003712
    (iEqj : Bool) (sᵢ βᵢ βⱼ r : ℝ) : ℝ :=
  (if iEqj then sᵢ else 0) + r * βᵢ * βⱼ



theorem d003713
    {p₁ p₂ p₃ s₁ s₂ s₃ β₁ β₂ β₃ r : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    _root_.GD.N0232.N0719.N0893.d003709 p₁ p₂ p₃
        (s₁ + r * β₁ ^ 2)
        (s₂ + r * β₂ ^ 2)
        (s₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) =
      _root_.GD.N0232.N0719.N1016.d003627 p₁ p₂ p₃ s₁ s₂ s₃ +
        r * _root_.GD.N0232.N0719.N1016.d003610 p₁ p₂ p₃ β₁ β₂ β₃ := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N0893.d003709 _root_.GD.N0232.N0719.N1016.d003627 _root_.GD.N0232.N0719.N1016.d003626 _root_.GD.N0232.N0719.N1016.d003610
  field_simp [h₁₂, h₁₃, h₂₃]
  ring



theorem d003714
    {p₁ p₂ p₃ s₁ s₂ s₃ β₁ β₂ β₃ r : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    _root_.GD.N0232.N0719.N0893.d003710 p₁ p₂ p₃
        (s₁ + r * β₁ ^ 2)
        (s₂ + r * β₂ ^ 2)
        (s₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) =
      _root_.GD.N0232.N0719.N1016.d003628 p₁ p₂ p₃ s₁ s₂ s₃ +
        r * _root_.GD.N0232.N0719.N1016.d003611 p₁ p₂ p₃ β₁ β₂ β₃ := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N0893.d003710 _root_.GD.N0232.N0719.N1016.d003628 _root_.GD.N0232.N0719.N1016.d003626 _root_.GD.N0232.N0719.N1016.d003611
  field_simp [h₁₂, h₁₃, h₂₃]
  ring



theorem d003715
    {p₁ p₂ p₃ s₁ s₂ s₃ β₁ β₂ β₃ r : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    _root_.GD.N0232.N0719.N0893.d003711 p₁ p₂ p₃
        (s₁ + r * β₁ ^ 2)
        (s₂ + r * β₂ ^ 2)
        (s₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) =
      _root_.GD.N0232.N0719.N1016.d003629 p₁ p₂ p₃ s₁ s₂ s₃ +
        r * _root_.GD.N0232.N0719.N1016.d003612 p₁ p₂ p₃ β₁ β₂ β₃ := by
  rw [_root_.GD.N0232.N0719.N0893.d003711, _root_.GD.N0232.N0719.N1016.d003612,
    _root_.GD.N0232.N0719.N0893.d003713 hsum h₁₂ h₁₃ h₂₃,
    _root_.GD.N0232.N0719.N0893.d003714 hsum h₁₂ h₁₃ h₂₃]
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N1016.d003627 _root_.GD.N0232.N0719.N1016.d003628 _root_.GD.N0232.N0719.N1016.d003629 _root_.GD.N0232.N0719.N1016.d003626
  field_simp [h₁₂, h₁₃, h₂₃]
  ring








theorem d003716
    {p₁ p₂ p₃ s₁ s₂ s₃ β₁ β₂ β₃ r : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0)
    (hβ₁ : p₁ * s₁ = β₁)
    (hβ₂ : p₂ * s₂ = β₂)
    (hβ₃ : p₃ * s₃ = β₃) :
    β₁ * _root_.GD.N0232.N0719.N0893.d003709 p₁ p₂ p₃
        (s₁ + r * β₁ ^ 2)
        (s₂ + r * β₂ ^ 2)
        (s₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) +
      β₂ * _root_.GD.N0232.N0719.N0893.d003710 p₁ p₂ p₃
        (s₁ + r * β₁ ^ 2)
        (s₂ + r * β₂ ^ 2)
        (s₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) +
      β₃ * _root_.GD.N0232.N0719.N0893.d003711 p₁ p₂ p₃
        (s₁ + r * β₁ ^ 2)
        (s₂ + r * β₂ ^ 2)
        (s₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) =
      -_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃ +
        3 * r * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃ := by
  rw [_root_.GD.N0232.N0719.N0893.d003713 hsum h₁₂ h₁₃ h₂₃,
    _root_.GD.N0232.N0719.N0893.d003714 hsum h₁₂ h₁₃ h₂₃,
    _root_.GD.N0232.N0719.N0893.d003715 hsum h₁₂ h₁₃ h₂₃]
  have hdiag :=
    _root_.GD.N0232.N0719.N1016.d003630
      (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (v₁ := s₁) (v₂ := s₂) (v₃ := s₃)
      hsum h₁₂ h₁₃ h₂₃
  rw [hβ₁, hβ₂, hβ₃] at hdiag
  have heuler :=
    _root_.GD.N0232.N0719.N1016.d003624
      (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (z₁ := β₁) (z₂ := β₂) (z₃ := β₃)
      h₁₂ h₁₃ h₂₃
  linear_combination hdiag + r * heuler



theorem d003717
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) (hp₃ : p₃ ≠ 0)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0)
    (hrank :
      _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t ≠ 0) :
    let β₁ := _root_.GD.N0232.N0719.N0888.d003689 d₁ t
    let β₂ := _root_.GD.N0232.N0719.N0888.d003689 d₂ t
    let β₃ := _root_.GD.N0232.N0719.N0888.d003689 d₃ t
    let d := _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t
    let r := 2 * t / d
    (β₁ / d) * _root_.GD.N0232.N0719.N0893.d003709 p₁ p₂ p₃
        (β₁ / p₁ + r * β₁ ^ 2)
        (β₂ / p₂ + r * β₂ ^ 2)
        (β₃ / p₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) +
      (β₂ / d) * _root_.GD.N0232.N0719.N0893.d003710 p₁ p₂ p₃
        (β₁ / p₁ + r * β₁ ^ 2)
        (β₂ / p₂ + r * β₂ ^ 2)
        (β₃ / p₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) +
      (β₃ / d) * _root_.GD.N0232.N0719.N0893.d003711 p₁ p₂ p₃
        (β₁ / p₁ + r * β₁ ^ 2)
        (β₂ / p₂ + r * β₂ ^ 2)
        (β₃ / p₃ + r * β₃ ^ 2)
        (r * β₁ * β₂)
        (r * β₁ * β₃)
        (r * β₂ * β₃) =
      -_root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t := by
  dsimp
  have hcov :=
    _root_.GD.N0232.N0719.N0893.d003716
      (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (s₁ := _root_.GD.N0232.N0719.N0888.d003689 d₁ t / p₁)
      (s₂ := _root_.GD.N0232.N0719.N0888.d003689 d₂ t / p₂)
      (s₃ := _root_.GD.N0232.N0719.N0888.d003689 d₃ t / p₃)
      (β₁ := _root_.GD.N0232.N0719.N0888.d003689 d₁ t)
      (β₂ := _root_.GD.N0232.N0719.N0888.d003689 d₂ t)
      (β₃ := _root_.GD.N0232.N0719.N0888.d003689 d₃ t)
      (r :=
        2 * t /
          _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t)
      hsum h₁₂ h₁₃ h₂₃
      (by field_simp [hp₁])
      (by field_simp [hp₂])
      (by field_simp [hp₃])
  calc
    _ =
        (_root_.GD.N0232.N0719.N0888.d003689 d₁ t *
              _root_.GD.N0232.N0719.N0893.d003709 p₁ p₂ p₃
                (_root_.GD.N0232.N0719.N0888.d003689 d₁ t / p₁ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₁ t ^ 2)
                (_root_.GD.N0232.N0719.N0888.d003689 d₂ t / p₂ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₂ t ^ 2)
                (_root_.GD.N0232.N0719.N0888.d003689 d₃ t / p₃ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₃ t ^ 2)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₁ t * _root_.GD.N0232.N0719.N0888.d003689 d₂ t)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₁ t * _root_.GD.N0232.N0719.N0888.d003689 d₃ t)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₂ t * _root_.GD.N0232.N0719.N0888.d003689 d₃ t) +
          _root_.GD.N0232.N0719.N0888.d003689 d₂ t *
              _root_.GD.N0232.N0719.N0893.d003710 p₁ p₂ p₃
                (_root_.GD.N0232.N0719.N0888.d003689 d₁ t / p₁ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₁ t ^ 2)
                (_root_.GD.N0232.N0719.N0888.d003689 d₂ t / p₂ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₂ t ^ 2)
                (_root_.GD.N0232.N0719.N0888.d003689 d₃ t / p₃ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₃ t ^ 2)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₁ t * _root_.GD.N0232.N0719.N0888.d003689 d₂ t)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₁ t * _root_.GD.N0232.N0719.N0888.d003689 d₃ t)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₂ t * _root_.GD.N0232.N0719.N0888.d003689 d₃ t) +
          _root_.GD.N0232.N0719.N0888.d003689 d₃ t *
              _root_.GD.N0232.N0719.N0893.d003711 p₁ p₂ p₃
                (_root_.GD.N0232.N0719.N0888.d003689 d₁ t / p₁ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₁ t ^ 2)
                (_root_.GD.N0232.N0719.N0888.d003689 d₂ t / p₂ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₂ t ^ 2)
                (_root_.GD.N0232.N0719.N0888.d003689 d₃ t / p₃ +
                  2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                    _root_.GD.N0232.N0719.N0888.d003689 d₃ t ^ 2)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₁ t * _root_.GD.N0232.N0719.N0888.d003689 d₂ t)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₁ t * _root_.GD.N0232.N0719.N0888.d003689 d₃ t)
                (2 * t / _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
                  _root_.GD.N0232.N0719.N0888.d003689 d₂ t * _root_.GD.N0232.N0719.N0888.d003689 d₃ t)) /
          _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t := by ring
    _ =
        (-_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃
              (_root_.GD.N0232.N0719.N0888.d003689 d₁ t) (_root_.GD.N0232.N0719.N0888.d003689 d₂ t) (_root_.GD.N0232.N0719.N0888.d003689 d₃ t) +
            3 *
              (2 * t /
                _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t) *
              _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃
                (_root_.GD.N0232.N0719.N0888.d003689 d₁ t) (_root_.GD.N0232.N0719.N0888.d003689 d₂ t) (_root_.GD.N0232.N0719.N0888.d003689 d₃ t)) /
          _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t := by rw [hcov]
    _ = -_root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t := by
      unfold _root_.GD.N0232.N0719.N0888.d003692
      dsimp
      field_simp [hrank]
      unfold _root_.GD.N0232.N0719.N0888.d003691
      ring

end

end GD.N0232.N0719.N0893
