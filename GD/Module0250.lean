import GD.Module0249















namespace GD.N0232.N0719.N0881

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

def d003570
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  p₁ * z₁ + p₂ * z₂ + p₃ * z₃

def d003571
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  p₁ * z₁ ^ 2 + p₂ * z₂ ^ 2 + p₃ * z₃ ^ 2

def d003572
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  let m := _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z₁ z₂ z₃
  p₁ * (z₁ - m) ^ 2 +
    p₂ * (z₂ - m) ^ 2 +
    p₃ * (z₃ - m) ^ 2

theorem d003573
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1) :
    _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z₁ z₂ z₃ =
      _root_.GD.N0232.N0719.N0881.d003571 p₁ p₂ p₃ z₁ z₂ z₃ -
        _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z₁ z₂ z₃ ^ 2 := by
  unfold _root_.GD.N0232.N0719.N0881.d003572 _root_.GD.N0232.N0719.N0881.d003571 _root_.GD.N0232.N0719.N0881.d003570
  nlinarith


theorem d003574 (s : ℝ) :
    ∫ u : ℝ, Real.exp (s * u) ∂gaussianReal 0 1 =
      Real.exp (s ^ 2 / 2) := by
  have h :=
    congrFun
      (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) s
  simpa [mgf, mul_comm] using h





theorem d003575
    {p₁ p₂ p₃ z₁ z₂ z₃ t : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t) :
    Real.exp
        (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z₁ z₂ z₃) =
      ∫ u : ℝ,
        Real.exp
          (-t * _root_.GD.N0232.N0719.N0881.d003571 p₁ p₂ p₃ z₁ z₂ z₃ +
            Real.sqrt (2 * t) * u *
              _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z₁ z₂ z₃)
        ∂gaussianReal 0 1 := by
  let q := _root_.GD.N0232.N0719.N0881.d003571 p₁ p₂ p₃ z₁ z₂ z₃
  let m := _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z₁ z₂ z₃
  have hsqrt : Real.sqrt (2 * t) ^ 2 = 2 * t := by
    rw [Real.sq_sqrt]
    positivity
  calc
    Real.exp
        (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z₁ z₂ z₃) =
      Real.exp (-t * q + t * m ^ 2) := by
        rw [_root_.GD.N0232.N0719.N0881.d003573 hsum]
        simp only [q, m]
        congr 1
        ring
    _ = Real.exp (-t * q) *
          Real.exp ((Real.sqrt (2 * t) * m) ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        rw [mul_pow, hsqrt]
        ring
    _ = Real.exp (-t * q) *
          ∫ u : ℝ,
            Real.exp ((Real.sqrt (2 * t) * m) * u)
          ∂gaussianReal 0 1 := by
        rw [_root_.GD.N0232.N0719.N0881.d003574]
    _ = ∫ u : ℝ,
          Real.exp (-t * q) *
            Real.exp ((Real.sqrt (2 * t) * m) * u)
        ∂gaussianReal 0 1 := by
          rw [integral_const_mul]
    _ = ∫ u : ℝ,
          Real.exp
            (-t * _root_.GD.N0232.N0719.N0881.d003571 p₁ p₂ p₃ z₁ z₂ z₃ +
              Real.sqrt (2 * t) * u *
                _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z₁ z₂ z₃)
        ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards [] with u
          rw [← Real.exp_add]
          simp only [q, m]
          congr 1
          ring





theorem d003576
    {p₁ p₂ p₃ z₁ z₂ z₃ t : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t) :
    Real.exp
        (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z₁ z₂ z₃) =
      ∫ u : ℝ,
        (Real.exp
            (-t * p₁ * z₁ ^ 2 +
              Real.sqrt (2 * t) * u * p₁ * z₁) *
          Real.exp
            (-t * p₂ * z₂ ^ 2 +
              Real.sqrt (2 * t) * u * p₂ * z₂) *
          Real.exp
            (-t * p₃ * z₃ ^ 2 +
              Real.sqrt (2 * t) * u * p₃ * z₃))
        ∂gaussianReal 0 1 := by
  rw [_root_.GD.N0232.N0719.N0881.d003575 hsum ht]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold _root_.GD.N0232.N0719.N0881.d003571 _root_.GD.N0232.N0719.N0881.d003570
  ring






theorem d003577
    {p₁ p₂ p₃ z₁ z₂ z₃ t c : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t) :
    c * Real.exp
        (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z₁ z₂ z₃) =
      ∫ u : ℝ,
        c *
          (Real.exp
              (-t * p₁ * z₁ ^ 2 +
                Real.sqrt (2 * t) * u * p₁ * z₁) *
            Real.exp
              (-t * p₂ * z₂ ^ 2 +
                Real.sqrt (2 * t) * u * p₂ * z₂) *
            Real.exp
              (-t * p₃ * z₃ ^ 2 +
                Real.sqrt (2 * t) * u * p₃ * z₃))
        ∂gaussianReal 0 1 := by
  rw [_root_.GD.N0232.N0719.N0881.d003576 hsum ht,
    integral_const_mul]

end

end GD.N0232.N0719.N0881
