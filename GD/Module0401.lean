




import Mathlib

namespace GD.N0155




theorem d006177 (η k₁ k₂ r : ℝ) (hr : r = (1 - η) * k₁ + η * k₂)
    (h : r ≠ 0) :
    η * k₂ / r - η = η * (1 - η) * (k₂ - k₁) / r := by
  subst hr; field_simp; ring




theorem d006178 (m₁ m₂ a : ℝ) :
    m₁ * (m₂ / 2 + a - 1) - m₂ * (m₁ / 2 - a) = a * (m₁ + m₂) - m₁ := by
  ring


theorem d006179 (m₁ m₂ a : ℝ) (h : m₁ + m₂ ≠ 0)
    (heq : m₁ * (m₂ / 2 + a - 1) = m₂ * (m₁ / 2 - a)) :
    a = m₁ / (m₁ + m₂) := by
  have h2 : a * (m₁ + m₂) = m₁ := by nlinarith [_root_.GD.N0155.d006178 m₁ m₂ a]
  field_simp
  linarith



theorem d006180 (e d lam η : ℝ) :
    (e + lam * d) ^ 2
      = (e + η * d) ^ 2 + 2 * (e + η * d) * ((lam - η) * d) + ((lam - η) * d) ^ 2 := by
  ring




theorem d006181 (d s : ℝ) (hs : s ≠ 0) :
    0 < 294 * d ^ 2 - 280 * s * d + 125 * s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith [sq_nonneg (588 * d - 280 * s)]


theorem d006182 (d s : ℝ) :
    1176 * (294 * d ^ 2 - 280 * s * d + 125 * s ^ 2)
      = (588 * d - 280 * s) ^ 2 + 68600 * s ^ 2 := by
  ring



theorem d006183 (C A κ : ℝ) (hκ : 0 < κ) (hA : 0 < A)
    (hC : 2 * C < -κ * A) :
    2 * (κ / 2) * C + (κ / 2) ^ 2 * A < -(κ ^ 2 / 4) * A ∧ -(κ ^ 2 / 4) * A < 0 := by
  constructor
  · nlinarith
  · nlinarith [sq_nonneg κ, mul_pos (mul_pos hκ hκ) hA]

end GD.N0155
