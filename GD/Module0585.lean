import GD.Module0570
import GD.Module0584
import GD.Module0583


























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1641
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530
open scoped FourierTransform Topology BigOperators

def d008514 (F : ℂ → ℂ → ℂ) (β : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  F z (_root_.GD.N0106.N0428.N0765.N1658.d008466 b β)

theorem d008515 (F : ℂ → ℂ → ℂ) (α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008462 (_root_.GD.N0106.N0428.N0765.N1641.d008514 F β) α = _root_.GD.N0106.N0428.N0765.N1658.d008467 F α β := rfl

theorem d008516 (F : ℂ → ℂ → ℂ) (α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008463 (_root_.GD.N0106.N0428.N0765.N1641.d008514 F β) α = _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β := rfl

theorem d008517 {F : ℂ → ℂ → ℂ} {d β : ℝ}
    (hβ : |β| ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d)) :
    ContinuousOn (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1641.d008514 F β))
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)) := by
  have hm : Continuous (fun p : ℂ × ℝ => (p.1, _root_.GD.N0106.N0428.N0765.N1658.d008466 p.2 β)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1658.d008466
    fun_prop
  exact hc.comp hm.continuousOn (fun p hp =>
    ⟨hp.1, _root_.GD.N0106.N0428.N0765.N1658.d008469 hβ p.2⟩)

theorem d008518 {F : ℂ → ℂ → ℂ} {d β : ℝ}
    (hβ : |β| ≤ d)
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) :
    ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => _root_.GD.N0106.N0428.N0765.N1641.d008514 F β z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) := by
  intro b
  exact hfA _ (_root_.GD.N0106.N0428.N0765.N1658.d008469 hβ b)



theorem d008519 {F : ℂ → ℂ → ℂ} {d B β : ℝ}
    (hd : 0 < d) (hβ : |β| ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hplanes : ∀ α β : ℝ, |α| ≤ d → |β| ≤ d →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B)
    (x : ℝ) : Integrable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1641.d008514 F β (x : ℂ) b) := by
  apply _root_.GD.N0106.N0428.N0765.N1642.d008481
    (R := d / 2) (B := B) (by positivity) (by linarith)
    (_root_.GD.N0106.N0428.N0765.N1641.d008517 hβ hc) (_root_.GD.N0106.N0428.N0765.N1641.d008518 hβ hfA)
  intro α hα
  simpa only [_root_.GD.N0106.N0428.N0765.N1641.d008515, _root_.GD.N0106.N0428.N0765.N1641.d008516] using
    hplanes α β (hα.trans (by linarith)) hβ




theorem d008520
    {F : ℂ → ℂ → ℂ} {d B : ℝ}
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
    (x ξ : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ x‖ ≤
      Real.exp (-(2 * Real.pi * d) * |ξ|) *
        (_root_.GD.N0106.N0428.N0765.N1647.d008502 (_root_.GD.N0106.N0428.N0765.N1641.d008514 F (-d)) x +
          _root_.GD.N0106.N0428.N0765.N1647.d008502 (_root_.GD.N0106.N0428.N0765.N1641.d008514 F d) x) := by
  have hx : (x : ℂ) ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
    change |(x : ℂ).im| ≤ d
    simpa only [Complex.ofReal_im, abs_zero] using hd.le
  have hcRow : ContinuousOn (fun w : ℂ => F (x : ℂ) w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    have hm : Continuous (fun w : ℂ => ((x : ℂ), w)) := by fun_prop
    exact hc.comp hm.continuousOn (fun w hw => ⟨hx, hw⟩)
  have hm : |(-d : ℝ)| ≤ d := by simp only [abs_neg, abs_of_pos hd, le_refl]
  have hp : |d| ≤ d := by simp only [abs_of_pos hd, le_refl]
  have hminus := _root_.GD.N0106.N0428.N0765.N1641.d008519 hd hm hc hfA hplanes x
  have hplus := _root_.GD.N0106.N0428.N0765.N1641.d008519 hd hp hc hfA hplanes x
  have hb := _root_.GD.N0106.N0428.N0765.N1635.d008411
    hd hcRow (hfB _ hx) hminus hplus (hdecay x) ξ
  have hrow : _root_.GD.N0106.N0428.N0765.N1530.d005194 (fun w : ℂ => F (x : ℂ) w) 0 =
      (fun b : ℝ => F (x : ℂ) (b : ℂ)) := by
    funext b
    simp [_root_.GD.N0106.N0428.N0765.N1530.d005194]
  rw [hrow] at hb
  simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005816, _root_.GD.N0106.N0428.N0765.N1658.d008467, _root_.GD.N0106.N0428.N0765.N1658.d008466,
    _root_.GD.N0106.N0428.N0765.N1530.d005194, _root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005473,
    _root_.GD.N0106.N0428.N0765.N1530.d005195, _root_.GD.N0106.N0428.N0765.N1647.d008502, _root_.GD.N0106.N0428.N0765.N1641.d008514,
    Complex.ofReal_zero, zero_mul, add_zero] using hb



theorem d008521 {F : ℂ → ℂ → ℂ} {d B : ℝ}
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
    (a : ℝ) : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0)
        (p.2 : ℝ) (a + (p.1 : ℝ))) := by
  have hheight (s : Bool) : |if s then d else -d| ≤ d := by
    cases s <;> simp [abs_of_pos hd]
  refine _root_.GD.N0106.N0428.N0765.N1647.d008509
    (F := fun s : Bool => _root_.GD.N0106.N0428.N0765.N1641.d008514 F (if s then d else -d))
    (g := fun x n => _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (n : ℝ) x)
    (d := d) (R := d / 2) (k := 2 * Real.pi * d) (B := fun _ => B)
    (by positivity) (by linarith) (by positivity) ?_ ?_ ?_ ?_ a
  · intro s
    exact _root_.GD.N0106.N0428.N0765.N1641.d008517 (hheight s) hc
  · intro s
    exact _root_.GD.N0106.N0428.N0765.N1641.d008518 (hheight s) hfA
  · intro s α hα
    simpa only [_root_.GD.N0106.N0428.N0765.N1641.d008515, _root_.GD.N0106.N0428.N0765.N1641.d008516] using
      hplanes α (if s then d else -d) (hα.trans (by linarith)) (hheight s)
  · intro x n
    exact _root_.GD.N0106.N0428.N0765.N1641.d008520
      hd hc hfA hfB hplanes hdecay x n




theorem d008522 {F : ℂ → ℂ → ℂ} {d M : ℝ}
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
    (a : ℝ) : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0)
        (p.2 : ℝ) (a + (p.1 : ℝ))) := by
  apply _root_.GD.N0106.N0428.N0765.N1641.d008521 (B := _root_.GD.N0106.N0428.N0765.N1650.d008510 F d)
    hd hc hfA hfB _ hdecay a
  intro α β hα hβ
  exact _root_.GD.N0106.N0428.N0765.N1650.d008512
    hd hα hβ hc hfA hfB hM hmm hmp hpm hpp

end
end GD.N0106.N0428.N0765.N1641

#print axioms _root_.GD.N0106.N0428.N0765.N1641.d008519
#print axioms _root_.GD.N0106.N0428.N0765.N1641.d008520
#print axioms _root_.GD.N0106.N0428.N0765.N1641.d008521
#print axioms _root_.GD.N0106.N0428.N0765.N1641.d008522
