import Mathlib
























namespace GD
namespace N0230
namespace N0702

noncomputable section


def d001122 (S₁ S₂ : ℝ) : ℝ :=
  1 + S₁ + S₂


def d001123 (S M : ℝ) : ℝ :=
  M / S



def d001124 (S₁ S₂ M₁ M₂ : ℝ) : ℝ :=
  (M₁ + M₂) / _root_.GD.N0230.N0702.d001122 S₁ S₂


def d001125 (S M Q : ℝ) : ℝ :=
  Q - M ^ 2 / S


def d001126 (S₁ S₂ S M : ℝ) : ℝ :=
  S / _root_.GD.N0230.N0702.d001122 S₁ S₂ * _root_.GD.N0230.N0702.d001123 S M ^ 2


def d001127 (S₁ S₂ M₁ M₂ : ℝ) : ℝ :=
  S₁ * S₂ / _root_.GD.N0230.N0702.d001122 S₁ S₂ *
    (_root_.GD.N0230.N0702.d001123 S₁ M₁ - _root_.GD.N0230.N0702.d001123 S₂ M₂) ^ 2


theorem d001128
    {S₁ S₂ : ℝ} (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) :
    0 < _root_.GD.N0230.N0702.d001122 S₁ S₂ := by
  unfold _root_.GD.N0230.N0702.d001122
  linarith


theorem d001129
    {S₁ S₂ M₁ M₂ : ℝ} (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) :
    0 ≤ _root_.GD.N0230.N0702.d001127 S₁ S₂ M₁ M₂ := by
  have hA : 0 ≤ _root_.GD.N0230.N0702.d001122 S₁ S₂ :=
    (_root_.GD.N0230.N0702.d001128 hS₁ hS₂).le
  unfold _root_.GD.N0230.N0702.d001127
  exact mul_nonneg (div_nonneg (mul_nonneg hS₁ hS₂) hA)
    (sq_nonneg _)



theorem d001130
    {S₁ S₂ M₁ M₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) :
    0 < _root_.GD.N0230.N0702.d001127 S₁ S₂ M₁ M₂ ↔
      _root_.GD.N0230.N0702.d001123 S₁ M₁ ≠ _root_.GD.N0230.N0702.d001123 S₂ M₂ := by
  have hA : 0 < _root_.GD.N0230.N0702.d001122 S₁ S₂ :=
    _root_.GD.N0230.N0702.d001128 hS₁.le hS₂.le
  have hcoef : 0 < S₁ * S₂ / _root_.GD.N0230.N0702.d001122 S₁ S₂ :=
    div_pos (mul_pos hS₁ hS₂) hA
  unfold _root_.GD.N0230.N0702.d001127
  constructor
  · intro hpos heq
    have hzero :
        S₁ * S₂ / _root_.GD.N0230.N0702.d001122 S₁ S₂ *
            (_root_.GD.N0230.N0702.d001123 S₁ M₁ - _root_.GD.N0230.N0702.d001123 S₂ M₂) ^ 2 = 0 := by
      simp [heq]
    linarith
  · intro hne
    exact mul_pos hcoef (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))


theorem d001131
    {S₁ S₂ M₁ M₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) :
    _root_.GD.N0230.N0702.d001127 S₁ S₂ M₁ M₂ = 0 ↔
      _root_.GD.N0230.N0702.d001123 S₁ M₁ = _root_.GD.N0230.N0702.d001123 S₂ M₂ := by
  constructor
  · intro hzero
    by_contra hne
    have hpos := (_root_.GD.N0230.N0702.d001130 hS₁ hS₂).2 hne
    exact (ne_of_gt hpos) hzero
  · intro heq
    simp [_root_.GD.N0230.N0702.d001127, heq]






theorem d001132
    {S₁ S₂ M₁ M₂ Q₁ Q₂ : ℝ}
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) :
    Q₁ + Q₂ - (M₁ + M₂) ^ 2 / _root_.GD.N0230.N0702.d001122 S₁ S₂ =
      _root_.GD.N0230.N0702.d001125 S₁ M₁ Q₁ + _root_.GD.N0230.N0702.d001125 S₂ M₂ Q₂ +
        _root_.GD.N0230.N0702.d001126 S₁ S₂ S₁ M₁ + _root_.GD.N0230.N0702.d001126 S₁ S₂ S₂ M₂ +
          _root_.GD.N0230.N0702.d001127 S₁ S₂ M₁ M₂ := by
  have hA : _root_.GD.N0230.N0702.d001122 S₁ S₂ ≠ 0 :=
    (_root_.GD.N0230.N0702.d001128 hS₁.le hS₂.le).ne'
  have hS₁ne : S₁ ≠ 0 := hS₁.ne'
  have hS₂ne : S₂ ≠ 0 := hS₂.ne'
  unfold _root_.GD.N0230.N0702.d001125 _root_.GD.N0230.N0702.d001126 _root_.GD.N0230.N0702.d001127 _root_.GD.N0230.N0702.d001123 _root_.GD.N0230.N0702.d001122
  field_simp [hA, hS₁ne, hS₂ne]
  ring



theorem d001133
    {S₁ S₂ M₁ M₂ Q₁ Q₂ q : ℝ}
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) :
    q ^ 2 + (S₁ * q ^ 2 - 2 * M₁ * q + Q₁) +
        (S₂ * q ^ 2 - 2 * M₂ * q + Q₂) =
      _root_.GD.N0230.N0702.d001122 S₁ S₂ *
          (q - _root_.GD.N0230.N0702.d001124 S₁ S₂ M₁ M₂) ^ 2 +
        _root_.GD.N0230.N0702.d001125 S₁ M₁ Q₁ + _root_.GD.N0230.N0702.d001125 S₂ M₂ Q₂ +
        _root_.GD.N0230.N0702.d001126 S₁ S₂ S₁ M₁ + _root_.GD.N0230.N0702.d001126 S₁ S₂ S₂ M₂ +
        _root_.GD.N0230.N0702.d001127 S₁ S₂ M₁ M₂ := by
  have hA : _root_.GD.N0230.N0702.d001122 S₁ S₂ ≠ 0 :=
    (_root_.GD.N0230.N0702.d001128 hS₁.le hS₂.le).ne'
  have hS₁ne : S₁ ≠ 0 := hS₁.ne'
  have hS₂ne : S₂ ≠ 0 := hS₂.ne'
  unfold _root_.GD.N0230.N0702.d001124 _root_.GD.N0230.N0702.d001125 _root_.GD.N0230.N0702.d001126 _root_.GD.N0230.N0702.d001127
    _root_.GD.N0230.N0702.d001123 _root_.GD.N0230.N0702.d001122
  field_simp [hA, hS₁ne, hS₂ne]
  ring




def d001134 (S₁ S₂ : ℝ) : ℝ :=
  S₁ + S₂


def d001135 (S₁ S₂ M₁ M₂ : ℝ) : ℝ :=
  (M₁ + M₂) / _root_.GD.N0230.N0702.d001134 S₁ S₂


def d001136 (S₁ S₂ M₁ M₂ : ℝ) : ℝ :=
  S₁ * S₂ / _root_.GD.N0230.N0702.d001134 S₁ S₂ *
    (_root_.GD.N0230.N0702.d001123 S₁ M₁ - _root_.GD.N0230.N0702.d001123 S₂ M₂) ^ 2



def d001137 (S₁ S₂ M₁ M₂ : ℝ) : ℝ :=
  _root_.GD.N0230.N0702.d001134 S₁ S₂ / _root_.GD.N0230.N0702.d001122 S₁ S₂ *
    _root_.GD.N0230.N0702.d001135 S₁ S₂ M₁ M₂ ^ 2



theorem d001138
    {S₁ S₂ M₁ M₂ Q₁ Q₂ : ℝ}
    (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) :
    Q₁ + Q₂ - (M₁ + M₂) ^ 2 / _root_.GD.N0230.N0702.d001122 S₁ S₂ =
      _root_.GD.N0230.N0702.d001125 S₁ M₁ Q₁ + _root_.GD.N0230.N0702.d001125 S₂ M₂ Q₂ +
        _root_.GD.N0230.N0702.d001136 S₁ S₂ M₁ M₂ +
          _root_.GD.N0230.N0702.d001137 S₁ S₂ M₁ M₂ := by
  have hA : _root_.GD.N0230.N0702.d001122 S₁ S₂ ≠ 0 :=
    (_root_.GD.N0230.N0702.d001128 hS₁.le hS₂.le).ne'
  have hS : _root_.GD.N0230.N0702.d001134 S₁ S₂ ≠ 0 := by
    unfold _root_.GD.N0230.N0702.d001134
    positivity
  have hS₁ne : S₁ ≠ 0 := hS₁.ne'
  have hS₂ne : S₂ ≠ 0 := hS₂.ne'
  unfold _root_.GD.N0230.N0702.d001125 _root_.GD.N0230.N0702.d001136 _root_.GD.N0230.N0702.d001137
    _root_.GD.N0230.N0702.d001135 _root_.GD.N0230.N0702.d001123 _root_.GD.N0230.N0702.d001122 _root_.GD.N0230.N0702.d001134
  field_simp [hA, hS, hS₁ne, hS₂ne]
  ring

end

end N0702
end N0230
end GD

#print axioms _root_.GD.N0230.N0702.d001130
#print axioms _root_.GD.N0230.N0702.d001132
#print axioms _root_.GD.N0230.N0702.d001133
#print axioms _root_.GD.N0230.N0702.d001138
