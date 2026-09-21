import GD.Module1398






set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped Interval

namespace GD.N0161
noncomputable section
open _root_.GD.N0179 _root_.GD.N0201

theorem d022526 {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    (∫ x in Ioi b, _root_.GD.N0179.d006018 u x) = 1 / u ^ 2 - _root_.GD.N0179.d006021 u b := by
  exact integral_Ioi_of_hasDerivAt_of_nonneg
    (_root_.GD.N0179.d006036 hu hb).continuousAt.continuousWithinAt
    (fun x hx => _root_.GD.N0179.d006036 hu (hb.trans hx))
    (fun x hx => by
      have hx0 : 0 < x := hb.trans hx
      unfold _root_.GD.N0179.d006018
      positivity)
    (_root_.GD.N0201.d022503 hu)

theorem d022527 {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, _root_.GD.N0179.d006018 u x) = _root_.GD.N0179.d006021 u a := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (_root_.GD.N0201.d022505 hu) ha.le
  rw [_root_.GD.N0201.d022506 hu, _root_.GD.N0161.d022526 hu ha] at h
  linarith


theorem d022528 {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    1 / u ^ 2 - _root_.GD.N0179.d006021 u b ≤ 15 / (2 * b ^ 2) := by
  unfold _root_.GD.N0179.d006021
  set y := _root_.GD.N0179.d006020 u b with hy
  have hy0 : 0 ≤ y := _root_.GD.N0179.d006023 u b
  have hy1 : y ≤ 1 := _root_.GD.N0179.d006025 hu hb.le
  have hy2 : 1 - y ^ 2 = 2 * u / (b + 2 * u) := by
    rw [hy, _root_.GD.N0179.d006024 hu hb.le]
    field_simp
    ring
  have hF := _root_.GD.N0179.d006029 hy0 hy1
  rw [hy2] at hF
  have hfrac : 2 * u / (b + 2 * u) ≤ 2 * u / b :=
    div_le_div_of_nonneg_left (by positivity) hb (by linarith)
  have hsq : (2 * u / (b + 2 * u)) ^ 2 ≤ (2 * u / b) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfrac 2
  have hbound : 1 - _root_.GD.N0179.d006019 y ≤ (15 / 2 : ℝ) * u ^ 2 / b ^ 2 := by
    calc
      _ ≤ 15 / 8 * (2 * u / (b + 2 * u)) ^ 2 := hF
      _ ≤ 15 / 8 * (2 * u / b) ^ 2 := by gcongr
      _ = _ := by ring
  have hu2 : 0 < u ^ 2 := by positivity
  rw [show 1 / u ^ 2 - _root_.GD.N0179.d006019 y / u ^ 2 =
      (1 - _root_.GD.N0179.d006019 y) / u ^ 2 by ring, div_le_iff₀ hu2]
  calc
    _ ≤ (15 / 2 : ℝ) * u ^ 2 / b ^ 2 := hbound
    _ = 15 / (2 * b ^ 2) * u ^ 2 := by ring

theorem d022529 {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    (∫ x in Ioi b, _root_.GD.N0179.d006018 u x) ≤ 15 / (2 * b ^ 2) ∧
      15 / (2 * b ^ 2) ≤ 8 / b ^ 2 := by
  constructor
  · rw [_root_.GD.N0161.d022526 hu hb]
    exact _root_.GD.N0161.d022528 hu hb
  · have hb2 : 0 < b ^ 2 := by positivity
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * b ^ 2) hb2).2
    nlinarith

theorem d022530 {x : ℝ} (hx : 0 < x) :
    x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one]

theorem d022531 {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    u ^ 2 * (∫ x in (0 : ℝ)..a, _root_.GD.N0179.d006018 u x) ≤ (a / u) ^ (3 / 2 : ℝ) := by
  rw [_root_.GD.N0161.d022527 hu ha]
  rw [← _root_.GD.N0161.d022530 (div_pos ha hu)]
  exact _root_.GD.N0179.d006042 hu ha

end
end GD.N0161

#print axioms _root_.GD.N0161.d022526
#print axioms _root_.GD.N0161.d022527
#print axioms _root_.GD.N0161.d022528
#print axioms _root_.GD.N0161.d022529
#print axioms _root_.GD.N0161.d022530
#print axioms _root_.GD.N0161.d022531
