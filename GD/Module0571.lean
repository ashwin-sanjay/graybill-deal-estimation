import GD.Module0442














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1636
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1550
open scoped Topology FourierTransform

theorem d008412 {f : ℂ → ℂ} {d y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ContinuousOn f {z : ℂ | |z.im| ≤ d})
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < d})
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0))
    (hyint : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f y))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (ξ : ℝ) :
    (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 ξ f) 0 x) =
      ∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 ξ f) y x := by
  have hec : Continuous (fun z : ℂ =>
      Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * (z * Complex.I))) := by
    fun_prop
  have htc : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1550.d005483 ξ f) {z : ℂ | |z.im| ≤ d} :=
    hec.continuousOn.mul hc
  have htf : DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1550.d005483 ξ f) {z : ℂ | |z.im| < d} := by
    intro z hz
    have he : DifferentiableAt ℂ (fun z : ℂ =>
        Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * (z * Complex.I))) z := by
      fun_prop
    exact he.differentiableWithinAt.mul (hf z hz)
  have htdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖_root_.GD.N0106.N0428.N0765.N1550.d005483 ξ f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε := by
    intro ε hε
    let C : ℝ := Real.exp (2 * Real.pi * |ξ| * d)
    have hC : 0 < C := Real.exp_pos _
    obtain ⟨R, hR⟩ := hdecay (ε / C) (div_pos hε hC)
    refine ⟨R, ?_⟩
    intro x s hx hs
    calc
      _ ≤ C * ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ :=
        _root_.GD.N0106.N0428.N0765.N1550.d005485 ξ (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hs)
      _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left (hR x s hx hs) hC.le
      _ = ε := by field_simp [hC.ne']
  exact _root_.GD.N0106.N0428.N0765.N1522.d005494 hd hy htc htf
    (_root_.GD.N0106.N0428.N0765.N1550.d005487 ξ h0) (_root_.GD.N0106.N0428.N0765.N1550.d005487 ξ hyint) htdecay

end
end GD.N0106.N0428.N0765.N1636

#print axioms _root_.GD.N0106.N0428.N0765.N1636.d008412
