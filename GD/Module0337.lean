import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped Interval

namespace GD.N0013
noncomputable section

def d005011 (q : ℝ) : ℝ := ∫ x : ℝ in 0..1, (1 - q * x ^ 2)⁻¹

theorem d005012 {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 < 1 - q * x ^ 2 := by
  have hsq : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hmul := mul_le_mul_of_nonneg_left hsq hq0
  nlinarith

theorem d005013 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    IntervalIntegrable (fun x : ℝ => (1 - q * x ^ 2)⁻¹) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  exact (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2))).inv₀
    (fun x hx => (_root_.GD.N0013.d005012 hq0 hq1 hx).ne')

theorem d005014 {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    IntervalIntegrable (fun x : ℝ => (1 + q * x ^ 2) / (1 - q * x ^ 2) ^ 2)
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact pow_ne_zero 2 (_root_.GD.N0013.d005012 hq0 hq1 hx).ne'

theorem d005015 {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∫ x : ℝ in 0..1, (1 + q * x ^ 2) / (1 - q * x ^ 2) ^ 2) =
      1 / (1 - q) := by
  have hd (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun y => y / (1 - q * y ^ 2))
        ((1 + q * x ^ 2) / (1 - q * x ^ 2) ^ 2) x := by
    have hpos := _root_.GD.N0013.d005012 hq0 hq1 (by simpa using hx)
    exact ((hasDerivAt_id x).div
      ((((hasDerivAt_id x).pow 2).const_mul q).const_sub 1) hpos.ne').congr_deriv (by
        simp only [Pi.pow_apply, id_eq]
        ring)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (_root_.GD.N0013.d005014 hq0 hq1)

theorem d005016 {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 - q * x ^ 2)⁻¹ ≤ 1 + (q / (1 - q)) * x ^ 2 := by
  have hden := _root_.GD.N0013.d005012 hq0 hq1 hx
  have hq : 0 < 1 - q := sub_pos.mpr hq1
  have hsq : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hle : 1 - q ≤ 1 - q * x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hq0]
  calc
    _ = 1 + (q * x ^ 2) / (1 - q * x ^ 2) := by field_simp; ring
    _ ≤ 1 + (q * x ^ 2) / (1 - q) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (mul_nonneg hq0 (sq_nonneg x)) hq hle)
    _ = _ := by ring

theorem d005017 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    _root_.GD.N0013.d005011 q ≤ 1 + q / (3 * (1 - q)) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hsq : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  have hbound := intervalIntegral.integral_mono_on zero_le_one
    (_root_.GD.N0013.d005013 hq0 hq1) (hconst.add (hsq.const_mul (q / (1 - q))))
    (fun x hx => _root_.GD.N0013.d005016 hq0 hq1 hx)
  calc
    _root_.GD.N0013.d005011 q ≤ ∫ x : ℝ in 0..1, 1 + (q / (1 - q)) * x ^ 2 := hbound
    _ = 1 + q / (3 * (1 - q)) := by
      rw [intervalIntegral.integral_add hconst (hsq.const_mul _),
        intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      field_simp [(sub_pos.mpr hq1).ne']

theorem d005018 :
    IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹) volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact (continuous_const.add (continuous_id.pow 2)).inv₀
    (fun x => (by positivity : (0 : ℝ) < 1 + x ^ 2).ne')

theorem d005019 :
    IntervalIntegrable (fun x : ℝ => ((1 + x ^ 2) ^ 2)⁻¹) volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact ((continuous_const.add (continuous_id.pow 2)).pow 2).inv₀
    (fun x => pow_ne_zero 2 (by positivity : (0 : ℝ) < 1 + x ^ 2).ne')

theorem d005020 :
    (∫ x : ℝ in 0..1, (1 + x ^ 2)⁻¹) = Real.pi / 4 := by
  rw [integral_inv_one_add_sq]
  simp [Real.arctan_one]

theorem d005021 :
    (∫ x : ℝ in 0..1, ((1 + x ^ 2) ^ 2)⁻¹) = 1 / 4 + Real.pi / 8 := by
  have hd (x : ℝ) (_hx : x ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun y => (Real.arctan y + y / (1 + y ^ 2)) / 2)
        (((1 + x ^ 2) ^ 2)⁻¹) x := by
    have hx : 1 + x ^ 2 ≠ 0 := (by positivity : (0 : ℝ) < 1 + x ^ 2).ne'
    apply (((Real.hasDerivAt_arctan x).add
      ((hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).const_add 1) hx)).div_const 2).congr_deriv
    simp only [Pi.pow_apply, id_eq]
    field_simp
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd _root_.GD.N0013.d005019
  simp only [Real.arctan_one, Real.arctan_zero, one_pow, add_zero, zero_div,
    sub_zero] at h
  rw [h]
  ring

end
end GD.N0013

#print axioms _root_.GD.N0013.d005012
#print axioms _root_.GD.N0013.d005013
#print axioms _root_.GD.N0013.d005014
#print axioms _root_.GD.N0013.d005015
#print axioms _root_.GD.N0013.d005016
#print axioms _root_.GD.N0013.d005017
#print axioms _root_.GD.N0013.d005018
#print axioms _root_.GD.N0013.d005019
#print axioms _root_.GD.N0013.d005020
#print axioms _root_.GD.N0013.d005021
