import GD.Module0255






























namespace GD.N0232.N0719.N0888

noncomputable section

open _root_.GD.N0232.N0719.N1016
open _root_.GD.N0232.N0719.N0892


def d003689 (d t : ℝ) : ℝ :=
  d / (1 + 2 * t * d)


def d003690
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  p₁ * _root_.GD.N0232.N0719.N0888.d003689 d₁ t + p₂ * _root_.GD.N0232.N0719.N0888.d003689 d₂ t + p₃ * _root_.GD.N0232.N0719.N0888.d003689 d₃ t


def d003691
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  1 - 2 * t * _root_.GD.N0232.N0719.N0888.d003690 p₁ p₂ p₃ d₁ d₂ d₃ t


def d003692
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  let β₁ := _root_.GD.N0232.N0719.N0888.d003689 d₁ t
  let β₂ := _root_.GD.N0232.N0719.N0888.d003689 d₂ t
  let β₃ := _root_.GD.N0232.N0719.N0888.d003689 d₃ t
  let m := _root_.GD.N0232.N0719.N0888.d003690 p₁ p₂ p₃ d₁ d₂ d₃ t
  (_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃ * (1 - 2 * t * m) -
      6 * t * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃) /
    _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t ^ 2



theorem d003693
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (h₁ : 1 + 2 * t * d₁ ≠ 0)
    (h₂ : 1 + 2 * t * d₂ ≠ 0)
    (h₃ : 1 + 2 * t * d₃ ≠ 0) :
    _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t *
        ((1 + 2 * t * d₁) *
          (1 + 2 * t * d₂) *
          (1 + 2 * t * d₃)) =
      _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N0888.d003691 _root_.GD.N0232.N0719.N0888.d003690 _root_.GD.N0232.N0719.N0888.d003689
    _root_.GD.N0232.N0719.N0892.d003671 _root_.GD.N0232.N0719.N0892.d003669 _root_.GD.N0232.N0719.N0892.d003670
  field_simp [h₁, h₂, h₃]
  set_option maxRecDepth 100000 in
    ring

set_option maxHeartbeats 2000000 in






theorem d003694
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (hp₁₂ : p₁ + p₂ ≠ 0)
    (hp₁₃ : p₁ + p₃ ≠ 0)
    (hp₂₃ : p₂ + p₃ ≠ 0)
    (h₁ : 1 + 2 * t * d₁ ≠ 0)
    (h₂ : 1 + 2 * t * d₂ ≠ 0)
    (h₃ : 1 + 2 * t * d₃ ≠ 0)
    (hrank :
      _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t ≠ 0)
    (hdet :
      _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ≠ 0) :
    _root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t =
      _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t /
        _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ 2 := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N0888.d003692
  dsimp only
  unfold _root_.GD.N0232.N0719.N0892.d003672 _root_.GD.N0232.N0719.N0892.d003667 _root_.GD.N0232.N0719.N0892.d003668 _root_.GD.N0232.N0719.N1016.d003608 _root_.GD.N0232.N0719.N1016.d003609 _root_.GD.N0232.N0719.N0888.d003689
  field_simp [hp₁₂, hp₁₃, hp₂₃, h₁, h₂, h₃, hrank, hdet]
  rw [← _root_.GD.N0232.N0719.N0888.d003693 hsum h₁ h₂ h₃]
  unfold _root_.GD.N0232.N0719.N0888.d003691 _root_.GD.N0232.N0719.N0888.d003690 _root_.GD.N0232.N0719.N0888.d003689
  field_simp [h₁, h₂, h₃]
  set_option maxRecDepth 100000 in
    ring



theorem d003695
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (henergy :
      _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0888.d003689 d₁ t) (_root_.GD.N0232.N0719.N0888.d003689 d₂ t) (_root_.GD.N0232.N0719.N0888.d003689 d₃ t) ≠ 0) :
    _root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t =
      let β₁ := _root_.GD.N0232.N0719.N0888.d003689 d₁ t
      let β₂ := _root_.GD.N0232.N0719.N0888.d003689 d₂ t
      let β₃ := _root_.GD.N0232.N0719.N0888.d003689 d₃ t
      let m := _root_.GD.N0232.N0719.N0888.d003690 p₁ p₂ p₃ d₁ d₂ d₃ t
      let ξ :=
        m +
          3 * _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃ /
            _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃
      _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃ /
          _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t ^ 2 *
        (1 - 2 * t * ξ) := by
  unfold _root_.GD.N0232.N0719.N0888.d003692
  dsimp
  field_simp [henergy]
  ring

end

end GD.N0232.N0719.N0888
