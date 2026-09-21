import GD.Module0351
import GD.Module0492











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1531
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1605

theorem d007567 {f : ℂ → ℂ} {d y : ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) (hy : |y| ≤ d) :
    Continuous (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y) := by
  have hz : (y : ℂ) * Complex.I ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005164, mem_setOf_eq, Complex.mul_I_im, Complex.ofReal_re] using hy
  exact _root_.GD.N0106.N0428.N0765.N1533.d005170 hc hz



theorem d007568 {f : ℂ → ℂ} {d M T y : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) (hy : |y| ≤ d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) :
    (∫ t : ℝ in Icc (-T) T, ‖_root_.GD.N0106.N0428.N0765.N1530.d005194 f y t‖) ≤ _root_.GD.N0106.N0428.N0765.N1530.d005196 f d y := by
  have hg := _root_.GD.N0106.N0428.N0765.N1531.d007567 hc hy
  have hu : Measurable (fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1605.d007560 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y t)) :=
    _root_.GD.N0106.N0428.N0765.N1605.d007561.comp hg.measurable
  have hunorm : ∀ t : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1605.d007560 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y t)‖ ≤ 1 :=
    fun t => _root_.GD.N0106.N0428.N0765.N1605.d007562 _
  have h := _root_.GD.N0106.N0428.N0765.N1530.d005207 hd hT hy hc hf hu hunorm hM hminus hplus
  have heq : ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T (fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1605.d007560 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y t)) f
      ((y : ℂ) * Complex.I)‖ = (∫ t : ℝ in Icc (-T) T, ‖_root_.GD.N0106.N0428.N0765.N1530.d005194 f y t‖) := by
    change ‖∫ t : ℝ in Icc (-T) T, _root_.GD.N0106.N0428.N0765.N1605.d007560 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y t) * _root_.GD.N0106.N0428.N0765.N1530.d005194 f y t‖ = _
    exact _root_.GD.N0106.N0428.N0765.N1605.d007565 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y) T
  rw [heq] at h
  exact h



theorem d007569 {f : ℂ → ℂ} {d M y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y) ∧ _root_.GD.N0106.N0428.N0765.N1530.d005195 f y ≤ _root_.GD.N0106.N0428.N0765.N1530.d005196 f d y := by
  apply _root_.GD.N0106.N0428.N0765.N1605.d007566 (_root_.GD.N0106.N0428.N0765.N1531.d007567 hc hy)
  intro T hT
  exact _root_.GD.N0106.N0428.N0765.N1531.d007568 hd hT hy hc hf hM hminus hplus

theorem d007570 {f : ℂ → ℂ} {d M y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) :
    _root_.GD.N0106.N0428.N0765.N1530.d005195 f y ≤ max (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d)) (_root_.GD.N0106.N0428.N0765.N1530.d005195 f d) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1531.d007569 hd hy hc hf hM hminus hplus).2
  have hy' := abs_le.mp hy
  have hm : 0 ≤ (d - y) / (2 * d) := div_nonneg (by linarith) (by positivity)
  have hp : 0 ≤ (d + y) / (2 * d) := div_nonneg (by linarith) (by positivity)
  have hsum : (d - y) / (2 * d) + (d + y) / (2 * d) = 1 := by
    field_simp [ne_of_gt hd]
    ring
  apply h.trans
  unfold _root_.GD.N0106.N0428.N0765.N1530.d005196
  calc
    _ ≤ ((d - y) / (2 * d)) * max (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d)) (_root_.GD.N0106.N0428.N0765.N1530.d005195 f d) +
        ((d + y) / (2 * d)) * max (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d)) (_root_.GD.N0106.N0428.N0765.N1530.d005195 f d) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hm)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hp)
    _ = _ := by rw [← add_mul, hsum, one_mul]



theorem d007571 {f : ℂ → ℂ} {d M y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) :
    _root_.GD.N0106.N0428.N0765.N1530.d005195 f y + _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-y) ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d := by
  have hpos := (_root_.GD.N0106.N0428.N0765.N1531.d007569 hd hy hc hf hM hminus hplus).2
  have hneg := (_root_.GD.N0106.N0428.N0765.N1531.d007569 (y := -y) hd (by simpa only [abs_neg] using hy)
    hc hf hM hminus hplus).2
  calc
    _ ≤ _root_.GD.N0106.N0428.N0765.N1530.d005196 f d y + _root_.GD.N0106.N0428.N0765.N1530.d005196 f d (-y) := add_le_add hpos hneg
    _ = _ := by
      unfold _root_.GD.N0106.N0428.N0765.N1530.d005196
      field_simp [ne_of_gt hd]
      ring

end
end GD.N0106.N0428.N0765.N1531

#print axioms _root_.GD.N0106.N0428.N0765.N1531.d007568
#print axioms _root_.GD.N0106.N0428.N0765.N1531.d007569
#print axioms _root_.GD.N0106.N0428.N0765.N1531.d007570
#print axioms _root_.GD.N0106.N0428.N0765.N1531.d007571
