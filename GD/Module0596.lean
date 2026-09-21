import GD.Module0591
import GD.Module0595



































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1657
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1640 _root_.GD.N0106.N0428.N0765.N1659
open scoped Topology FourierTransform BigOperators



private theorem d008577
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
    (hdecayA : ∀ β : ℝ, |β| ≤ d → ∀ b ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ, R ≤ |a| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayB : ∀ a ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (ξ ν : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν‖ ≤
      B * Real.exp (-(2 * Real.pi * d) * |ξ|) *
        Real.exp (-(2 * Real.pi * d) * |ν|) := by
  let α : ℝ := if 0 ≤ ξ then -d else d
  let β : ℝ := if 0 ≤ ν then -d else d
  have hα : |α| ≤ d := by simp only [α]; split <;> simp [abs_of_pos hd]
  have hβ : |β| ≤ d := by simp only [β]; split <;> simp [abs_of_pos hd]
  have hz : |(0 : ℝ)| ≤ d := by simpa only [abs_zero] using hd.le
  have hdecayB' : ∀ a ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005478] using hdecayB
  have hb := _root_.GD.N0106.N0428.N0765.N1644.d008531
    hd hα hβ hc hfA hfB
    (hplanes 0 0 hz hz).1 (hplanes 0 β hz hβ).1 (hplanes α β hα hβ).1
    (hdecayA β hβ) hdecayB' ξ ν
  have heA : 2 * Real.pi * ξ * α = -(2 * Real.pi * d) * |ξ| := by
    unfold α
    split_ifs with hξ
    · rw [abs_of_nonneg hξ]; ring
    · rw [abs_of_neg (lt_of_not_ge hξ)]; ring
  have heB : 2 * Real.pi * ν * β = -(2 * Real.pi * d) * |ν| := by
    unfold β
    split_ifs with hν
    · rw [abs_of_nonneg hν]; ring
    · rw [abs_of_neg (lt_of_not_ge hν)]; ring
  calc
    _ ≤ (Real.exp (2 * Real.pi * ξ * α) * Real.exp (2 * Real.pi * ν * β)) *
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β := hb
    _ ≤ (Real.exp (2 * Real.pi * ξ * α) * Real.exp (2 * Real.pi * ν * β)) * B :=
      mul_le_mul_of_nonneg_left (hplanes α β hα hβ).2 (by positivity)
    _ = _ := by rw [heA, heB]; ring



private theorem d008578
    {F : ℂ → ℂ → ℂ} {d B h : ℝ}
    (hd : 0 < d) (hh : 0 < h)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hplanes : ∀ α β : ℝ, |α| ≤ d → |β| ≤ d →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B)
    (hdecayA : ∀ β : ℝ, |β| ≤ d → ∀ b ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ, R ≤ |a| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayB : ∀ a ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (x y : ℝ) :
    h ^ 2 • (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0
      (x + h * (p.1 : ℝ), y + h * (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0)
        (p.1 / h) (p.2 / h) * fourier p.1 ((x / h : ℝ) : UnitAddCircle) *
          fourier p.2 ((y / h : ℝ) : UnitAddCircle) := by
  have hd' : 0 < d / h := div_pos hd hh
  have hz : |(0 : ℝ)| ≤ d := by simpa only [abs_zero] using hd.le
  have hB : 0 ≤ B :=
    (show 0 ≤ _root_.GD.N0106.N0428.N0765.N1658.d008468 F 0 0 from
      integral_nonneg (fun _ => norm_nonneg _)).trans (hplanes 0 0 hz hz).2
  have hplanes' (α β : ℝ) (hα : |α| ≤ d / h) (hβ : |β| ≤ d / h) :
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) α β)
          (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) α β ≤ (h ^ 2)⁻¹ * B := by
    have hα' : |h * α| ≤ d := by
      simpa only [abs_mul, abs_of_pos hh, mul_comm] using (le_div_iff₀ hh).mp hα
    have hβ' : |h * β| ≤ d := by
      simpa only [abs_mul, abs_of_pos hh, mul_comm] using (le_div_iff₀ hh).mp hβ
    refine ⟨(_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh α β).2
      (hplanes (h * α) (h * β) hα' hβ').1, ?_⟩
    rw [_root_.GD.N0106.N0428.N0765.N1649.d008545 F hh]
    exact mul_le_mul_of_nonneg_left (hplanes (h * α) (h * β) hα' hβ').2 (by positivity)
  have hc' := _root_.GD.N0106.N0428.N0765.N1649.d008548 hh hc
  have hfA' := _root_.GD.N0106.N0428.N0765.N1649.d008549 hh hfA
  have hfB' := _root_.GD.N0106.N0428.N0765.N1649.d008550 hh hfB
  have hdecayA' := _root_.GD.N0106.N0428.N0765.N1648.d008571 hh hdecayA
  have hdecayB' := _root_.GD.N0106.N0428.N0765.N1648.d008572 hh hdecayB
  have hbound := _root_.GD.N0106.N0428.N0765.N1657.d008577
    hd' hc' hfA' hfB' hplanes' hdecayA' hdecayB'
  have hrows := _root_.GD.N0106.N0428.N0765.N1654.d008557
    hd' hc' hfA' hfB' hplanes' hdecayB'
  have hcolumns (n : ℤ) :=
    _root_.GD.N0106.N0428.N0765.N1651.d008555
      hd' hc' hfA' hplanes' (n : ℝ)
      (_root_.GD.N0106.N0428.N0765.N1644.d008533
        (by positivity : 0 < 2 * Real.pi * (d / h)) hbound (n : ℝ))
  have hsamples : Summable (fun p : ℤ × ℤ =>
      _root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) 0 0
        (x / h + (p.1 : ℝ), y / h + (p.2 : ℝ))) := by
    have hs := _root_.GD.N0106.N0428.N0765.N1645.d008501
      (F := _root_.GD.N0106.N0428.N0765.N1649.d008542 F h) (d := d / h) (R := (d / h) / 2)
      (B := (h ^ 2)⁻¹ * B) (by positivity) (by linarith)
      hc' hfA' hfB'
      (fun α β hα hβ => hplanes' α β
        (hα.trans (by linarith)) (hβ.trans (by linarith))) (x / h) (y / h)
    simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008467, _root_.GD.N0106.N0428.N0765.N1658.d008466, Complex.ofReal_zero,
      zero_mul, add_zero] using hs
  have hcross := _root_.GD.N0106.N0428.N0765.N1641.d008521
    hd' hc' hfA' hfB' hplanes' hdecayB' (x / h)
  have hcoeff := _root_.GD.N0106.N0428.N0765.N1660.d008567
    (by positivity : 0 < 2 * Real.pi * (d / h))
    (mul_nonneg (by positivity : 0 ≤ (h ^ 2)⁻¹) hB) hbound
  simp only [_root_.GD.N0106.N0428.N0765.N1648.d008570] at hrows hcolumns hsamples hcross hcoeff
  exact _root_.GD.N0106.N0428.N0765.N1652.d005826 hh hrows hcolumns x y hsamples hcross hcoeff




theorem d008579
    {F : ℂ → ℂ → ℂ} {d₀ d₁ h : ℝ}
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hh : 0 < h)
    (hcMixed : ContinuousOn (Function.uncurry F)
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d₁ ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d₁))
    (hfMixedA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d₁,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d₁))
    (hfMixedB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d₁,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d₁))
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d₁) (-d₁)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d₁) d₁) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d₁ (-d₁)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d₁ d₁) (volume.prod volume))
    (hdecayMixedA : ∀ β : ℝ, |β| ≤ d₁ → ∀ b : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ, R ≤ |a| → |s| ≤ d₁ →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayMixedB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d₁ → ‖F (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (hdecayMixedBEdge : ∀ α : ℝ, α = -d₁ ∨ α = d₁ → ∀ a ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ b s : ℝ, R ≤ |b| → |s| ≤ d₁ →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
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
  have hplanes (α β : ℝ) (hα : |α| ≤ d₁) (hβ : |β| ≤ d₁) :
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ _root_.GD.N0106.N0428.N0765.N1650.d008510 F d₁ := by
    refine _root_.GD.N0106.N0428.N0765.N1656.d008562
      hd₁ hα hβ hcMixed hfFaceA hfFaceB ?_ ?_ hmm hmp hpm hpp
    · simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008466, _root_.GD.N0106.N0428.N0765.N1550.d005473] using hdecayMixedA
    · simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008466, _root_.GD.N0106.N0428.N0765.N1550.d005473] using hdecayMixedBEdge
  have hbase : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume) :=
    (hplanes 0 0 hz hz).1
  let c : ℤ → ℤ → ℂ := fun m n =>
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ((m : ℝ) / h) ((n : ℝ) / h)
  let φa : ℤ → ℂ := fun n => fourier n ((x / h : ℝ) : UnitAddCircle)
  let φb : ℤ → ℂ := fun n => fourier n ((y / h : ℝ) : UnitAddCircle)
  have hbound := _root_.GD.N0106.N0428.N0765.N1657.d008577
    hd₁ hcMixed hfFaceA hfFaceB hplanes hdecayMixedA hdecayMixedB
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
    _root_.GD.N0106.N0428.N0765.N1657.d008578 hd₁ hh hcMixed hfFaceA hfFaceB
      hplanes hdecayMixedA hdecayMixedB x y
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
end GD.N0106.N0428.N0765.N1657

#print axioms _root_.GD.N0106.N0428.N0765.N1657.d008579
