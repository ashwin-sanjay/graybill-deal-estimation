import GD.Module0586
import GD.Module0585





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1651
noncomputable section

open MeasureTheory Set Complex TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1641
open scoped Topology FourierTransform



theorem d008554 (F : ℂ → ℂ → ℂ) (ν : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ν = fun x : ℝ =>
      ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0) *
        _root_.GD.N0106.N0428.N0765.N1641.d008514 F 0 (x : ℂ) b := by
  funext x
  have h := _root_.GD.N0106.N0428.N0765.N1644.d008528
    (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 (x, b)) ν
  simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005816, _root_.GD.N0106.N0428.N0765.N1658.d008467, _root_.GD.N0106.N0428.N0765.N1658.d008466,
    _root_.GD.N0106.N0428.N0765.N1641.d008514, Complex.ofReal_zero, zero_mul, add_zero] using h



theorem d008555
    {F : ℂ → ℂ → ℂ} {d B : ℝ} (hd : 0 < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hplanes : ∀ α β : ℝ, |α| ≤ d → |β| ≤ d →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B)
    (ν : ℝ)
    (hfreq : Summable (fun n : ℤ =>
      𝓕 (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ν) n)) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813
      (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ν) := by
  have hz : |(0 : ℝ)| ≤ d := by simpa only [abs_zero] using hd.le
  have hR : 0 < d / 2 := by positivity
  have hRd : d / 2 < d := by linarith
  have hc0 := _root_.GD.N0106.N0428.N0765.N1641.d008517 hz hc
  have hf0 := _root_.GD.N0106.N0428.N0765.N1641.d008518 hz hfA
  have hslice : ∀ y : ℝ, |y| ≤ d / 2 →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 (_root_.GD.N0106.N0428.N0765.N1641.d008514 F 0) y) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008463 (_root_.GD.N0106.N0428.N0765.N1641.d008514 F 0) y ≤ B := by
    intro y hy
    simpa only [_root_.GD.N0106.N0428.N0765.N1641.d008515, _root_.GD.N0106.N0428.N0765.N1641.d008516] using
      hplanes y 0 (hy.trans (by linarith)) hz
  have huc : Continuous (fun b : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1644.d008523 _root_.GD.N0106.N0428.N0765.N1550.d005473
    fun_prop
  have hu := huc.measurable
  have hunorm : ∀ b : ℝ,
      ‖_root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)‖ ≤ 1 := by
    intro b
    rw [_root_.GD.N0106.N0428.N0765.N1644.d008525]
    simp only [mul_zero, Real.exp_zero, le_refl]
  have hweighted := _root_.GD.N0106.N0428.N0765.N1642.d008482
    hR hRd hc0 hf0 hslice hu hunorm
  have heq := _root_.GD.N0106.N0428.N0765.N1651.d008554 F ν
  have hcont : Continuous (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ν) := by
    rw [heq]
    exact hweighted
  refine ⟨hcont, ?_, hfreq⟩
  intro K
  have hs := _root_.GD.N0106.N0428.N0765.N1647.d008508
    hR hRd hc0 hf0 hslice hu hunorm K
  have hmap :
      (⟨_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ν, hcont⟩ : C(ℝ, ℂ)) =
        (⟨fun x : ℝ => ∫ b : ℝ,
          _root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0) *
            _root_.GD.N0106.N0428.N0765.N1641.d008514 F 0 (x : ℂ) b, hweighted⟩ : C(ℝ, ℂ)) := by
    ext x
    exact congrFun heq x
  rw [hmap]
  exact hs



theorem d008556 {F : ℂ → ℂ → ℂ} {d M : ℝ}
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
    (hdecayA : ∀ β : ℝ, |β| ≤ d → ∀ b : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ,
        R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (ν : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005813
      (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ν) := by
  have hbound := _root_.GD.N0106.N0428.N0765.N1644.d008532
    hd hc hfA hfB hM hmm hmp hpm hpp hdecayA hdecayB
  have hfreq := _root_.GD.N0106.N0428.N0765.N1644.d008533
    (by positivity : 0 < 2 * Real.pi * d) hbound ν
  apply _root_.GD.N0106.N0428.N0765.N1651.d008555
    (B := _root_.GD.N0106.N0428.N0765.N1650.d008510 F d) hd hc hfA _ ν hfreq
  intro α β hα hβ
  exact _root_.GD.N0106.N0428.N0765.N1650.d008512
    hd hα hβ hc hfA hfB hM hmm hmp hpm hpp

end
end GD.N0106.N0428.N0765.N1651

#print axioms _root_.GD.N0106.N0428.N0765.N1651.d008554
#print axioms _root_.GD.N0106.N0428.N0765.N1651.d008555
#print axioms _root_.GD.N0106.N0428.N0765.N1651.d008556
