import Mathlib.Tactic


















namespace GD.N0232.N0720.N1248


noncomputable def d002180 (z : ℝ) : ℝ :=
  z ^ 8 - z ^ 6 + z ^ 4 - z ^ 2 + 1



theorem d002181 (z : ℝ) :
    (z ^ 2 + 1) * _root_.GD.N0232.N0720.N1248.d002180 z = z ^ 10 + 1 := by
  unfold _root_.GD.N0232.N0720.N1248.d002180
  ring


noncomputable def d002182 (z : ℝ) : ℝ :=
  z ^ 16 + z ^ 14 + z ^ 12 + z ^ 10 + 10 * z ^ 8 +
    z ^ 6 + z ^ 4 + z ^ 2 + 1

theorem d002183 (z : ℝ) : 0 < _root_.GD.N0232.N0720.N1248.d002182 z := by
  unfold _root_.GD.N0232.N0720.N1248.d002182
  positivity








theorem d002184 (tau z : ℝ) :
    let q := _root_.GD.N0232.N0720.N1248.d002180 z
    let numerator := tau * (tau * z ^ 10 + tau - z ^ 9 - z)
    let denominator := (tau ^ 2 - 1) * (z ^ 2 + 1) * q
    let numeratorDerivative := tau * (10 * tau * z ^ 9 - 9 * z ^ 8 - 1)
    let qDerivative := 8 * z ^ 7 - 6 * z ^ 5 + 4 * z ^ 3 - 2 * z
    let denominatorDerivative :=
      (tau ^ 2 - 1) * (2 * z * q + (z ^ 2 + 1) * qDerivative)
    numeratorDerivative * denominator -
        numerator * denominatorDerivative =
      (tau ^ 2 - 1) * tau * (z ^ 2 - 1) * _root_.GD.N0232.N0720.N1248.d002182 z := by
  dsimp [_root_.GD.N0232.N0720.N1248.d002180, _root_.GD.N0232.N0720.N1248.d002182]
  ring




theorem d002185 {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) :
    0 < 3 * t ^ 5 - 2 * t + 1 := by
  let x : ℝ := 8 * t - 4
  have hx : 0 ≤ x := by
    dsimp [x]
    linarith
  have hfactor :
      3 * t ^ 5 - 2 * t + 1 =
        (x + 12) *
          (3 * x ^ 4 + 24 * x ^ 3 + 192 * (x - 1) ^ 2 + 64) /
            32768 := by
    dsimp [x]
    ring
  rw [hfactor]
  have hx12 : 0 < x + 12 := by linarith
  have hinner :
      0 < 3 * x ^ 4 + 24 * x ^ 3 + 192 * (x - 1) ^ 2 + 64 := by
    positivity
  positivity


theorem d002186 {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) :
    (1 + t) / (1 + t ^ 5) < (3 / 2 : ℝ) := by
  have ht0 : 0 ≤ t := (by linarith : (0 : ℝ) ≤ t)
  have hden : 0 < 1 + t ^ 5 := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith [_root_.GD.N0232.N0720.N1248.d002185 ht]




theorem d002187 {t : ℝ}
    (ht : (1 / 2 : ℝ) ≤ t) :
    let r : ℝ := 1 / (1 + t)
    r ^ 5 / (r ^ 5 + (1 - r) ^ 5) ≤ (3 / 2 : ℝ) * r := by
  dsimp
  have ht0 : 0 ≤ t := by linarith
  have hone : 0 < 1 + t := by linarith
  have hfive : 0 < 1 + t ^ 5 := by positivity
  have hrewrite :
      (1 / (1 + t) : ℝ) ^ 5 /
          ((1 / (1 + t) : ℝ) ^ 5 +
            (1 - 1 / (1 + t)) ^ 5) =
        1 / (1 + t ^ 5) := by
    field_simp [ne_of_gt hone, ne_of_gt hfive]
    all_goals ring
  rw [hrewrite]
  have hratio := (_root_.GD.N0232.N0720.N1248.d002186 ht).le
  rw [div_le_iff₀ hfive] at hratio
  rw [show (3 / 2 : ℝ) * (1 / (1 + t)) = (3 / 2) / (1 + t) by ring]
  exact (div_le_div_iff₀ hfive hone).2 (by nlinarith)



theorem d002188
    {r H Hzero second : ℝ}
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hH : H ≤ Hzero) (hHzero : 0 ≤ Hzero) (hsecond : 0 ≤ second)
    (hmoment :
      (8 + 6 * r) * Hzero = 11 * r + (6 * r - 3) * second) :
    H ≤ (3 / 2 : ℝ) * r := by
  have hcoefficient : 6 * r - 3 ≤ 0 := by linarith
  have hterm : (6 * r - 3) * second ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoefficient hsecond
  have hrHzero : 0 ≤ r * Hzero := mul_nonneg hr.le hHzero
  nlinarith









theorem d002189
    {r H Hzero second : ℝ}
    (hr : 0 < r)
    (hHone : H ≤ 1)
    (hHzero : 0 ≤ Hzero)
    (hsecond : 0 ≤ second)
    (hmoment :
      (8 + 6 * r) * Hzero = 11 * r + (6 * r - 3) * second)
    (hlow : r ≤ 1 / 2 → H ≤ Hzero)
    (hhigh : 1 / 2 ≤ r →
      H ≤ r ^ 5 / (r ^ 5 + (1 - r) ^ 5)) :
    H ≤ (3 / 2 : ℝ) * r := by
  by_cases hrhalf : r ≤ 1 / 2
  · exact _root_.GD.N0232.N0720.N1248.d002188 hr hrhalf (hlow hrhalf) hHzero hsecond hmoment
  · have hhalf : (1 / 2 : ℝ) ≤ r := (le_of_lt (lt_of_not_ge hrhalf))
    by_cases htwo : (2 / 3 : ℝ) ≤ r
    · nlinarith
    · have hrle : r ≤ 2 / 3 := le_of_lt (lt_of_not_ge htwo)
      let t : ℝ := (1 - r) / r
      have ht : (1 / 2 : ℝ) ≤ t := by
        dsimp [t]
        rw [le_div_iff₀ hr]
        linarith
      have hrparam : r = 1 / (1 + t) := by
        dsimp [t]
        field_simp [ne_of_gt hr]
        all_goals ring
      have hendpoint := _root_.GD.N0232.N0720.N1248.d002187 ht
      dsimp at hendpoint
      rw [← hrparam] at hendpoint
      exact (hhigh hhalf).trans hendpoint



theorem d002190
    {eta H WG : ℝ} (heta : 0 ≤ eta)
    (h : H ≤ (3 / 2 : ℝ) * WG) :
    eta * H ≤ (3 / 2 : ℝ) * (eta * WG) := by
  nlinarith [mul_nonneg heta (sub_nonneg.mpr h)]

end GD.N0232.N0720.N1248
