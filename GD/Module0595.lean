import GD.Module0578
import GD.Module0594
import GD.Module0587
import GD.Module0350
































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1659
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1640
open scoped Topology FourierTransform BigOperators

theorem d008574 {h : ℝ} (hh : 0 < h) (d x : ℝ) :
    Real.exp (-(2 * Real.pi * d) * |x / h|) =
      Real.exp (-(2 * Real.pi * d / h) * |x|) := by
  congr 1
  rw [abs_div, abs_of_pos hh]
  simp only [div_eq_mul_inv]
  ring



theorem d008575 {f : ℝ × ℝ → ℂ} {C d h : ℝ}
    (hd : 0 < d) (hh : 0 < h) (hC : 0 ≤ C)
    (hb : ∀ ξ ν : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 f ξ ν‖ ≤
      C * Real.exp (-(2 * Real.pi * d) * |ξ|) *
        Real.exp (-(2 * Real.pi * d) * |ν|)) :
    Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1652.d005817 f ((p.1 : ℝ) / h) ((p.2 : ℝ) / h)) := by
  have hk : 0 < 2 * Real.pi * d / h := by positivity
  have hs := _root_.GD.N0106.N0428.N0765.N1660.d008566 hk
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819 (hs.mul_left C) hs
    (fun n => mul_nonneg hC (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le)
  intro p
  simpa only [_root_.GD.N0106.N0428.N0765.N1659.d008574 hh] using hb ((p.1 : ℝ) / h) ((p.2 : ℝ) / h)





theorem d008576
    {F : ℂ → ℂ → ℂ} {d₀ d₁ M h : ℝ}
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hh : 0 < h)
    (hcMixed : ContinuousOn (Function.uncurry F)
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d₁ ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d₁))
    (hfMixedA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d₁,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d₁))
    (hfMixedB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d₁,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d₁))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d₁, ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d₁, ‖F z w‖ ≤ M)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d₁) (-d₁)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d₁) d₁) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d₁ (-d₁)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d₁ d₁) (volume.prod volume))
    (hdecayMixedA : ∀ β : ℝ, |β| ≤ d₁ → ∀ b : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ, R ≤ |a| → |s| ≤ d₁ →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayMixedB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d₁ → ‖F (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (hcAxisA : ∀ b : ℝ,
      ContinuousOn (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d₀))
    (hfAxisA : ∀ b : ℝ,
      DifferentiableOn ℂ (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d₀))
    (hcAxisB : ∀ a : ℝ,
      ContinuousOn (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d₀))
    (hfAxisB : ∀ a : ℝ,
      DifferentiableOn ℂ (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d₀))
    (hAxisAm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d₀) 0) (volume.prod volume))
    (hAxisAp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d₀ 0) (volume.prod volume))
    (hAxisBm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 (-d₀)) (volume.prod volume))
    (hAxisBp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 d₀) (volume.prod volume))
    (hdecayAxisA : ∀ b : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d₀ → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)‖ ≤ ε)
    (hdecayAxisB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d₀ → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (x y : ℝ) :
    ‖(∫ p : ℝ × ℝ, F (p.1 : ℂ) (p.2 : ℂ) ∂(volume.prod volume)) -
        h ^ 2 • (∑' p : ℤ × ℤ,
          F ((x + h * (p.1 : ℝ) : ℝ) : ℂ) ((y + h * (p.2 : ℝ) : ℝ) : ℂ))‖ ≤
      (2 * _root_.GD.N0106.N0428.N0765.N1640.d008538 F d₀ + 2 * _root_.GD.N0106.N0428.N0765.N1640.d008539 F d₀) /
          (Real.exp (2 * Real.pi * d₀ / h) - 1) +
        4 * _root_.GD.N0106.N0428.N0765.N1650.d008510 F d₁ /
          (Real.exp (2 * Real.pi * d₁ / h) - 1) ^ 2 := by
  obtain ⟨_hcFaceA, hfFaceA, _hcFaceB, hfFaceB⟩ :=
    _root_.GD.N0106.N0428.N0765.N1525.d005193 hd₁ hcMixed hfMixedA hfMixedB
  have hz : |(0 : ℝ)| ≤ d₁ := by simpa only [abs_zero] using hd₁.le
  have hbase : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume) :=
    (_root_.GD.N0106.N0428.N0765.N1650.d008512
      hd₁ hz hz hcMixed hfFaceA hfFaceB hM hmm hmp hpm hpp).1
  have hdecayMixedB' : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d₁ →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005478] using hdecayMixedB
  let c : ℤ → ℤ → ℂ := fun m n =>
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ((m : ℝ) / h) ((n : ℝ) / h)
  let φa : ℤ → ℂ := fun n => fourier n ((x / h : ℝ) : UnitAddCircle)
  let φb : ℤ → ℂ := fun n => fourier n ((y / h : ℝ) : UnitAddCircle)
  have hbound := _root_.GD.N0106.N0428.N0765.N1644.d008532
    hd₁ hcMixed hfFaceA hfFaceB hM hmm hmp hpm hpp hdecayMixedA hdecayMixedB'
  have hcoeff : Summable (fun p : ℤ × ℤ => c p.1 p.2) :=
    _root_.GD.N0106.N0428.N0765.N1659.d008575 hd₁ hh (_root_.GD.N0106.N0428.N0765.N1660.d008565 F d₁) hbound
  have hzero : c 0 0 =
      ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 p ∂(volume.prod volume) := by
    simp only [c, Int.cast_zero, zero_div]
    rw [_root_.GD.N0106.N0428.N0765.N1652.d005818]
    exact (integral_prod _ hbase).symm
  have hrep : h ^ 2 • (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0
      (x + h * (p.1 : ℝ), y + h * (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, c p.1 p.2 * φa p.1 * φb p.2 :=
    _root_.GD.N0106.N0428.N0765.N1648.d008573 hd₁ hh hcMixed hfFaceA hfFaceB hM
      hmm hmp hpm hpp hdecayMixedA hdecayMixedB x y
  have haxisA : ∀ m : ℤ, m ≠ 0 →
      ‖c m 0‖ ≤ _root_.GD.N0106.N0428.N0765.N1640.d008538 F d₀ * Real.exp (-(2 * Real.pi * d₀ / h) * |(m : ℝ)|) := by
    intro m _hm
    have hb := _root_.GD.N0106.N0428.N0765.N1640.d008540 hd₀ hcAxisA hfAxisA hbase
      hAxisAm hAxisAp hdecayAxisA ((m : ℝ) / h)
    simpa only [c, Int.cast_zero, zero_div, _root_.GD.N0106.N0428.N0765.N1659.d008574 hh] using hb
  have haxisB : ∀ n : ℤ, n ≠ 0 →
      ‖c 0 n‖ ≤ _root_.GD.N0106.N0428.N0765.N1640.d008539 F d₀ * Real.exp (-(2 * Real.pi * d₀ / h) * |(n : ℝ)|) := by
    intro n _hn
    have hb := _root_.GD.N0106.N0428.N0765.N1640.d008541 hd₀ hcAxisB hfAxisB hbase
      hAxisBm hAxisBp hdecayAxisB ((n : ℝ) / h)
    simpa only [c, Int.cast_zero, zero_div, _root_.GD.N0106.N0428.N0765.N1659.d008574 hh] using hb
  have hmixed : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ‖c m n‖ ≤ _root_.GD.N0106.N0428.N0765.N1650.d008510 F d₁ *
        Real.exp (-(2 * Real.pi * d₁ / h) * |(m : ℝ)|) *
          Real.exp (-(2 * Real.pi * d₁ / h) * |(n : ℝ)|) := by
    intro m n _hm _hn
    simpa only [c, _root_.GD.N0106.N0428.N0765.N1659.d008574 hh] using hbound ((m : ℝ) / h) ((n : ℝ) / h)
  have hφa (n : ℤ) : ‖φa n‖ = 1 := Circle.norm_coe _
  have hφb (n : ℤ) : ‖φb n‖ = 1 := Circle.norm_coe _
  have hφa0 : φa 0 = 1 := by simp only [φa, fourier_zero]
  have hφb0 : φb 0 = 1 := by simp only [φb, fourier_zero]
  have herror := _root_.GD.N0106.N0428.N0765.N1643.d008460
    (c := c) (φa := φa) (φb := φb)
    (Ma := _root_.GD.N0106.N0428.N0765.N1640.d008538 F d₀) (Mb := _root_.GD.N0106.N0428.N0765.N1640.d008539 F d₀)
    (Mab := _root_.GD.N0106.N0428.N0765.N1650.d008510 F d₁)
    (k₀ := 2 * Real.pi * d₀ / h) (k₁ := 2 * Real.pi * d₁ / h)
    (by positivity) (by positivity) hφa hφb hφa0 hφb0 hcoeff hzero hrep haxisA haxisB hmixed
  simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008467, _root_.GD.N0106.N0428.N0765.N1658.d008466, Complex.ofReal_zero,
    zero_mul, add_zero] using herror

end
end GD.N0106.N0428.N0765.N1659

#print axioms _root_.GD.N0106.N0428.N0765.N1659.d008574
#print axioms _root_.GD.N0106.N0428.N0765.N1659.d008575
#print axioms _root_.GD.N0106.N0428.N0765.N1659.d008576
