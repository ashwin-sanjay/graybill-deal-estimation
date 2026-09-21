import GD.Module0650
import GD.Module0255
import GD.Module0261










namespace GD.N0232.N0719.N0884

noncomputable section

open scoped NNReal


theorem d009601
    (q₀ q₁ q₂ V w₀ w₁ w₂ : ℝ) :
    _root_.GD.N0232.N0719.N0892.d003667 q₀ q₁ q₂
        (q₀ * (V * w₀))
        (q₁ * (V * w₁))
        (q₂ * (V * w₂)) =
      V ^ 2 *
        _root_.GD.N0232.N0719.N1016.d003608 q₀ q₁ q₂
          (q₀ * w₀) (q₁ * w₁) (q₂ * w₂) := by
  unfold _root_.GD.N0232.N0719.N0892.d003667 _root_.GD.N0232.N0719.N1016.d003608
  have hq₀ : q₀ * (V * w₀) = V * (q₀ * w₀) := by ac_rfl
  have hq₁ : q₁ * (V * w₁) = V * (q₁ * w₁) := by ac_rfl
  have hq₂ : q₂ * (V * w₂) = V * (q₂ * w₂) := by ac_rfl
  have h01 :
      (q₀ * (V * w₀) - q₁ * (V * w₁)) ^ 2 =
        V ^ 2 * (q₀ * w₀ - q₁ * w₁) ^ 2 := by
    rw [hq₀, hq₁, ← mul_sub, mul_pow]
  have h02 :
      (q₀ * (V * w₀) - q₂ * (V * w₂)) ^ 2 =
        V ^ 2 * (q₀ * w₀ - q₂ * w₂) ^ 2 := by
    rw [hq₀, hq₂, ← mul_sub, mul_pow]
  have h12 :
      (q₁ * (V * w₁) - q₂ * (V * w₂)) ^ 2 =
        V ^ 2 * (q₁ * w₁ - q₂ * w₂) ^ 2 := by
    rw [hq₁, hq₂, ← mul_sub, mul_pow]
  rw [h01, h02, h12]
  simp only [mul_div_assoc, mul_add]


theorem d009602
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (p : Fin k → ℝ) (V : ℝ) (w : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0892.d003667
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 0)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 1)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 2)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 0 * (V * w 0))
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 1 * (V * w 1))
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 2 * (V * w 2)) =
      V ^ 2 * _root_.GD.N0232.N0719.N0856.d009528 triangle p w := by
  unfold _root_.GD.N0232.N0719.N0856.d009528
  exact _root_.GD.N0232.N0719.N0884.d009601
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 0)
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 1)
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 2)
    V (w 0) (w 1) (w 2)





theorem d009603
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (p : Fin k → ℝ) (V : ℝ) (w : Fin 3 → ℝ)
    (v₀ v₁ v₂ : ℝ≥0)
    (hv₀ : (v₀ : ℝ) = V * w 0)
    (hv₁ : (v₁ : ℝ) = V * w 1)
    (hv₂ : (v₂ : ℝ) = V * w 2) :
    _root_.GD.N0232.N0719.N0892.d003667
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 0)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 1)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle p 2)
        (_root_.GD.N0232.N0719.N0895.d003746
          (_root_.GD.N0232.N0719.N0951.d003586 triangle p 0) v₀)
        (_root_.GD.N0232.N0719.N0895.d003746
          (_root_.GD.N0232.N0719.N0951.d003586 triangle p 1) v₁)
        (_root_.GD.N0232.N0719.N0895.d003746
          (_root_.GD.N0232.N0719.N0951.d003586 triangle p 2) v₂) =
      V ^ 2 * _root_.GD.N0232.N0719.N0856.d009528 triangle p w := by
  unfold _root_.GD.N0232.N0719.N0895.d003746
  rw [hv₀, hv₁, hv₂]
  exact _root_.GD.N0232.N0719.N0884.d009602 triangle p V w
















theorem d009604
    {r ω V : ℝ} (hr : r ≠ 0) :
    r ^ 2 / (ω / r + V) =
      r ^ 3 / (ω + r * V) := by
  field_simp [hr]





theorem d009605
    {r ω V : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hω : 0 ≤ ω) (hV : 0 < V) :
    r ^ 3 / (ω + V) ≤
      r ^ 2 / (ω / r + V) := by
  rw [_root_.GD.N0232.N0719.N0884.d009604 hr.ne']
  have hsmall : 0 < ω + r * V := by
    exact add_pos_of_nonneg_of_pos hω (mul_pos hr hV)
  have hden :
      ω + r * V ≤ ω + V := by
    nlinarith
  exact div_le_div_of_nonneg_left
    (by positivity : 0 ≤ r ^ 3) hsmall hden





theorem d009606
    {rFloor r ω V : ℝ}
    (hfloor : 0 ≤ rFloor) (hfloor_r : rFloor ≤ r)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hω : 0 ≤ ω) (hV : 0 < V) :
    rFloor * r ^ 2 / (ω + V) ≤
      r ^ 2 / (ω / r + V) := by
  have hden : 0 < ω + V := add_pos_of_nonneg_of_pos hω hV
  have hnum :
      rFloor * r ^ 2 ≤ r ^ 3 := by
    calc
      rFloor * r ^ 2 ≤ r * r ^ 2 :=
        mul_le_mul_of_nonneg_right hfloor_r (sq_nonneg r)
      _ = r ^ 3 := by ring
  exact
    (div_le_div_of_nonneg_right hnum hden.le).trans
      (_root_.GD.N0232.N0719.N0884.d009605
        hr hr1 hω hV)

end

end GD.N0232.N0719.N0884
