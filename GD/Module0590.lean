import GD.Module0585
import GD.Module0579
















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1654
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1641
open scoped FourierTransform Topology

theorem d008557 {F : ℂ → ℂ → ℂ} {d B : ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hplanes : ∀ α β : ℝ, |α| ≤ d → |β| ≤ d →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B)
    (hdecay : ∀ x : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (x : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 (x, b)) := by
  have hx : (x : ℂ) ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
    change |(x : ℂ).im| ≤ d
    simpa only [Complex.ofReal_im, abs_zero] using hd.le
  have hcRow : ContinuousOn (fun w : ℂ => F (x : ℂ) w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    have hm : Continuous (fun w : ℂ => ((x : ℂ), w)) := by fun_prop
    exact hc.comp hm.continuousOn (fun w hw => ⟨hx, hw⟩)
  have hm : |(-d : ℝ)| ≤ d := by simp [abs_of_pos hd]
  have hp : |d| ≤ d := by simp [abs_of_pos hd]
  have hminus := _root_.GD.N0106.N0428.N0765.N1641.d008519 hd hm hc hfA hplanes x
  have hplus := _root_.GD.N0106.N0428.N0765.N1641.d008519 hd hp hc hfA hplanes x
  have hcontrols := _root_.GD.N0106.N0428.N0765.N1655.d008461
    hd hcRow (hfB _ hx) hminus hplus (hdecay x)
  have hrow : _root_.GD.N0106.N0428.N0765.N1530.d005194 (fun w : ℂ => F (x : ℂ) w) 0 =
      (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 (x, b)) := by
    funext b
    simp [_root_.GD.N0106.N0428.N0765.N1530.d005194, _root_.GD.N0106.N0428.N0765.N1658.d008467, _root_.GD.N0106.N0428.N0765.N1658.d008466]
  rw [← hrow]
  exact hcontrols

theorem d008558 {F : ℂ → ℂ → ℂ} {d M : ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖F z w‖ ≤ M)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) (-d)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) d) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d (-d)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d d) (volume.prod volume))
    (hdecay : ∀ x : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (x : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813 (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 (x, b)) := by
  apply _root_.GD.N0106.N0428.N0765.N1654.d008557 (B := _root_.GD.N0106.N0428.N0765.N1650.d008510 F d)
    hd hc hfA hfB _ hdecay x
  intro α β hα hβ
  exact _root_.GD.N0106.N0428.N0765.N1650.d008512
    hd hα hβ hc hfA hfB hM hmm hmp hpm hpp

end
end GD.N0106.N0428.N0765.N1654

#print axioms _root_.GD.N0106.N0428.N0765.N1654.d008557
#print axioms _root_.GD.N0106.N0428.N0765.N1654.d008558
