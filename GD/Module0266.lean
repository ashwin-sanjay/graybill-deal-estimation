import GD.Module0252



















namespace GD.N0232.N0719.N1021

noncomputable section

open _root_.GD.N0232.N0719.N1016


def d003810 (w₁ w₂ w₃ : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003608 (1 / 3) (1 / 3) (1 / 3)
    ((1 / 3) * w₁) ((1 / 3) * w₂) ((1 / 3) * w₃)


def d003811 (w₁ w₂ w₃ : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003608 (2 / 5) (4 / 15) (1 / 3)
    ((2 / 5) * w₁) ((4 / 15) * w₂) ((1 / 3) * w₃)

theorem d003812 :
    (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1 := by norm_num

theorem d003813 :
    (2 / 5 : ℝ) + 4 / 15 + 1 / 3 = 1 := by norm_num

theorem d003814 (w₁ w₂ w₃ : ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N1021.d003810 w₁ w₂ w₃ := by
  unfold _root_.GD.N0232.N0719.N1021.d003810
  exact _root_.GD.N0232.N0719.N1016.d003619 (by norm_num) (by norm_num) (by norm_num)

theorem d003815 (w₁ w₂ w₃ : ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N1021.d003811 w₁ w₂ w₃ := by
  unfold _root_.GD.N0232.N0719.N1021.d003811
  exact _root_.GD.N0232.N0719.N1016.d003619 (by norm_num) (by norm_num) (by norm_num)

theorem d003816 (w₁ w₂ w₃ : ℝ) :
    ((w₁ - w₂) ^ 2 + (w₁ - w₃) ^ 2) / 6 ≤
      _root_.GD.N0232.N0719.N1021.d003810 w₁ w₂ w₃ := by
  unfold _root_.GD.N0232.N0719.N1021.d003810 _root_.GD.N0232.N0719.N1016.d003608
  norm_num
  nlinarith [sq_nonneg (w₂ - w₃)]

theorem d003817 (w₁ w₂ w₃ : ℝ) :
    (2 * w₁ + 4 * (w₁ - w₂)) ^ 2 / 150 ≤
      _root_.GD.N0232.N0719.N1021.d003811 w₁ w₂ w₃ := by
  unfold _root_.GD.N0232.N0719.N1021.d003811 _root_.GD.N0232.N0719.N1016.d003608
  norm_num
  nlinarith [sq_nonneg (6 * w₁ - 5 * w₃),
    sq_nonneg (4 * w₂ - 5 * w₃)]



theorem d003818 (w₁ w₂ w₃ : ℝ) :
    (1 / 375) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2) ≤
      _root_.GD.N0232.N0719.N1021.d003810 w₁ w₂ w₃ +
        _root_.GD.N0232.N0719.N1021.d003811 w₁ w₂ w₃ := by
  let a := w₁ - w₂
  let b := w₁ - w₃
  let q := 2 * w₁ + 4 * a
  have hx :
      w₁ ^ 2 ≤ q ^ 2 / 2 + 8 * a ^ 2 := by
    dsimp [q, a]
    nlinarith [sq_nonneg (2 * w₁ + 8 * (w₁ - w₂))]
  have hy :
      w₂ ^ 2 ≤ 2 * w₁ ^ 2 + 2 * a ^ 2 := by
    dsimp [a]
    nlinarith [sq_nonneg (2 * w₁ - w₂)]
  have hz :
      w₃ ^ 2 ≤ 2 * w₁ ^ 2 + 2 * b ^ 2 := by
    dsimp [b]
    nlinarith [sq_nonneg (2 * w₁ - w₃)]
  have hnorm :
      w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2 ≤
        (5 / 2) * q ^ 2 + 42 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith
  have h0 := _root_.GD.N0232.N0719.N1021.d003816 w₁ w₂ w₃
  have h1 := _root_.GD.N0232.N0719.N1021.d003817 w₁ w₂ w₃
  dsimp [a, b, q] at hnorm ⊢
  norm_num at h0 h1 ⊢
  nlinarith



theorem d003819
    {w₁ w₂ w₃ : ℝ}
    (hmax : w₁ = 1 ∨ w₂ = 1 ∨ w₃ = 1) :
    (1 / 375 : ℝ) ≤
      _root_.GD.N0232.N0719.N1021.d003810 w₁ w₂ w₃ +
        _root_.GD.N0232.N0719.N1021.d003811 w₁ w₂ w₃ := by
  have hsquares : 1 ≤ w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2 := by
    rcases hmax with h | h | h
    · rw [h]
      nlinarith [sq_nonneg w₂, sq_nonneg w₃]
    · rw [h]
      nlinarith [sq_nonneg w₁, sq_nonneg w₃]
    · rw [h]
      nlinarith [sq_nonneg w₁, sq_nonneg w₂]
  calc
    (1 / 375 : ℝ) ≤
        (1 / 375) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2) := by
      nlinarith
    _ ≤ _root_.GD.N0232.N0719.N1021.d003810 w₁ w₂ w₃ +
          _root_.GD.N0232.N0719.N1021.d003811 w₁ w₂ w₃ :=
      _root_.GD.N0232.N0719.N1021.d003818 w₁ w₂ w₃



theorem d003820 (w₁ w₂ w₃ : ℝ) :
    _root_.GD.N0232.N0719.N1021.d003810 w₁ w₂ w₃ +
          _root_.GD.N0232.N0719.N1021.d003811 w₁ w₂ w₃ = 0 ↔
      w₁ = 0 ∧ w₂ = 0 ∧ w₃ = 0 := by
  constructor
  · intro h
    have hc := _root_.GD.N0232.N0719.N1021.d003818 w₁ w₂ w₃
    have hs :
        w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2 = 0 := by
      have hnonneg :
          0 ≤ w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2 := by positivity
      norm_num at hc
      nlinarith
    constructor
    · nlinarith [sq_nonneg w₂, sq_nonneg w₃]
    constructor <;> nlinarith [sq_nonneg w₁, sq_nonneg w₂, sq_nonneg w₃]
  · rintro ⟨rfl, rfl, rfl⟩
    simp [_root_.GD.N0232.N0719.N1021.d003810, _root_.GD.N0232.N0719.N1021.d003811, _root_.GD.N0232.N0719.N1016.d003608]

end

end GD.N0232.N0719.N1021
