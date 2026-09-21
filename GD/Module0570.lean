import GD.Module0495














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1635
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1531
open scoped FourierTransform Topology


theorem d008410 {f : ℂ → ℂ} {d M : ℝ}
    (hd : 0 < d) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d))) (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) :
    ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) 0‖ ≤ (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d) / 2 := by
  have hb := (_root_.GD.N0106.N0428.N0765.N1531.d007569 (y := 0) hd
    (by simpa only [abs_zero] using hd.le) hc hf hM hminus hplus).2
  have heq : _root_.GD.N0106.N0428.N0765.N1530.d005196 f d 0 = (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d) / 2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1530.d005196
    field_simp [hd.ne'] <;> ring
  rw [heq] at hb
  rw [_root_.GD.N0106.N0428.N0765.N1613.d005632]
  exact (norm_integral_le_integral_norm _).trans hb




theorem d008411 {f : ℂ → ℂ} {d : ℝ}
    (hd : 0 < d) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d))) (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (ξ : ℝ) :
    ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) ξ‖ ≤ Real.exp (-(2 * Real.pi * d) * |ξ|) *
      (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d) := by
  obtain ⟨M, _hMpos, hM⟩ := _root_.GD.N0106.N0428.N0765.N1551.d006791 hc hdecay
  have h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0) :=
    (_root_.GD.N0106.N0428.N0765.N1531.d007569 (y := 0) hd
      (by simpa only [abs_zero] using hd.le) hc hf hM hminus hplus).1
  obtain ⟨hpos, hneg⟩ := _root_.GD.N0106.N0428.N0765.N1554.d007599
    hd hc hf h0 hminus hplus hdecay
  have hm : 0 ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) := _root_.GD.N0106.N0428.N0765.N1530.d005197 f (-d)
  have hp : 0 ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f d := _root_.GD.N0106.N0428.N0765.N1530.d005197 f d
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · have hb := hneg (-ξ) (neg_pos.mpr hξ)
    rw [neg_neg] at hb
    calc
      _ ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f d * Real.exp (-(2 * Real.pi * d) * (-ξ)) := hb
      _ ≤ (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d) *
          Real.exp (-(2 * Real.pi * d) * (-ξ)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hm) (Real.exp_pos _).le
      _ = _ := by rw [abs_of_neg hξ]; ring
  · have hb := _root_.GD.N0106.N0428.N0765.N1635.d008410 hd hc hf hM hminus hplus
    have hhalf : (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d) / 2 ≤
        _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d := by linarith
    simpa only [abs_zero, mul_zero, Real.exp_zero, one_mul] using hb.trans hhalf
  · calc
      _ ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) * Real.exp (-(2 * Real.pi * d) * ξ) := hpos ξ hξ
      _ ≤ (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d) *
          Real.exp (-(2 * Real.pi * d) * ξ) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hp) (Real.exp_pos _).le
      _ = _ := by rw [abs_of_pos hξ]; ring

end
end GD.N0106.N0428.N0765.N1635

#print axioms _root_.GD.N0106.N0428.N0765.N1635.d008410
#print axioms _root_.GD.N0106.N0428.N0765.N1635.d008411
