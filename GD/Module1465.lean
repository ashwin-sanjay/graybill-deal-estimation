import GD.Module0534
import GD.Module0640

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set

namespace GD.N0213.N0520
noncomputable section
open _root_.GD.N0213.N0519 _root_.GD.N0213.N0495
open _root_.GD.N0232.N0719

theorem d023081 {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (f : ℝ → ℝ) :
    (∫ x, f x ∂gammaMeasure (s + 1) r) =
      (r ^ (s + 1) / Real.Gamma (s + 1)) *
        ∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 s r x * f x := by
  rw [_root_.GD.N0232.N0719.N0954.d009351
    (by linarith : 0 < s + 1) hr]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero
    (s := Ioi 0) (f := fun x => gammaPDFReal (s + 1) r x * f x)]
  · rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [gammaPDFReal, if_pos (show 0 ≤ x from le_of_lt hx), add_sub_cancel_right, _root_.GD.N0213.N0519.d007966]
    ring
  · filter_upwards with x
    intro hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hx0 : x = 0
    · subst x
      simp [gammaPDFReal, Real.zero_rpow hs.ne']
    · simp [gammaPDFReal, not_le.mpr (lt_of_le_of_ne hxle hx0)]

theorem d023082 {s r L b : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hL : 0 < L) (hb : 0 ≤ b) :
    (∫ x, x⁻¹ * _root_.GD.N0213.N0495.d007174 L (x + b) ^ 2 ∂gammaMeasure (s + 1) r) =
      (r / s) * (∫ x, _root_.GD.N0213.N0495.d007174 L (x + b) ^ 2 ∂gammaMeasure (s + 1) r) -
        (2 / s) * (∫ x, _root_.GD.N0213.N0495.d007174 L (x + b) * _root_.GD.N0213.N0495.d007175 L (x + b)
          ∂gammaMeasure (s + 1) r) := by
  simp_rw [_root_.GD.N0213.N0520.d023081 hs hr]
  have hi : (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 s r x * (x⁻¹ * _root_.GD.N0213.N0495.d007174 L (x + b) ^ 2)) =
      ∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (s - 1) r x * _root_.GD.N0213.N0495.d007174 L (x + b) ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [_root_.GD.N0213.N0519.d007970 s r hx]
    field_simp [ne_of_gt (show 0 < x from hx)]
  rw [hi, _root_.GD.N0213.N0519.d007986 hs hr hL hb]
  ring

end
end GD.N0213.N0520

#print axioms _root_.GD.N0213.N0520.d023081
#print axioms _root_.GD.N0213.N0520.d023082
