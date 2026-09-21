import GD.Module0571
import GD.Module0584



























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1644
noncomputable section

open MeasureTheory Set Complex Filter
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1550
open scoped Topology FourierTransform BigOperators

def d008523 (ξ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((-2 * Real.pi * ξ : ℝ) : ℂ) * (z * Complex.I))

def d008524 (F : ℂ → ℂ → ℂ) (α β ξ ν : ℝ) (p : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1644.d008523 ξ (_root_.GD.N0106.N0428.N0765.N1550.d005473 p.1 α) * _root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 p.2 β) *
    _root_.GD.N0106.N0428.N0765.N1658.d008467 F α β p

theorem d008525 (ξ x α : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1644.d008523 ξ (_root_.GD.N0106.N0428.N0765.N1550.d005473 x α)‖ = Real.exp (2 * Real.pi * ξ * α) := by
  have h := _root_.GD.N0106.N0428.N0765.N1550.d005484 ξ (fun _ => (1 : ℂ)) (_root_.GD.N0106.N0428.N0765.N1550.d005473 x α)
  simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005483, _root_.GD.N0106.N0428.N0765.N1644.d008523, mul_one, norm_one, _root_.GD.N0106.N0428.N0765.N1550.d005477] using h

theorem d008526 (F : ℂ → ℂ → ℂ) (α β ξ ν : ℝ) (p : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν p‖ =
      (Real.exp (2 * Real.pi * ξ * α) * Real.exp (2 * Real.pi * ν * β)) *
        ‖_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β p‖ := by
  simp only [_root_.GD.N0106.N0428.N0765.N1644.d008524, norm_mul, _root_.GD.N0106.N0428.N0765.N1644.d008525]

theorem d008527 {F : ℂ → ℂ → ℂ} {α β : ℝ}
    (hi : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume))
    (ξ ν : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν) (volume.prod volume) := by
  have hcA : Continuous (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1644.d008523 ξ (_root_.GD.N0106.N0428.N0765.N1550.d005473 p.1 α)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1644.d008523 _root_.GD.N0106.N0428.N0765.N1550.d005473
    fun_prop
  have hcB : Continuous (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 p.2 β)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1644.d008523 _root_.GD.N0106.N0428.N0765.N1550.d005473
    fun_prop
  have hm : AEStronglyMeasurable (_root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν) (volume.prod volume) :=
    (hcA.aestronglyMeasurable.mul hcB.aestronglyMeasurable).mul hi.aestronglyMeasurable
  exact Integrable.mono'
    (hi.norm.const_mul (Real.exp (2 * Real.pi * ξ * α) * Real.exp (2 * Real.pi * ν * β)))
    hm (ae_of_all _ (fun p => (_root_.GD.N0106.N0428.N0765.N1644.d008526 F α β ξ ν p).le))

theorem d008528 (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008523 ξ (_root_.GD.N0106.N0428.N0765.N1550.d005473 x 0) * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [_root_.GD.N0106.N0428.N0765.N1644.d008523, _root_.GD.N0106.N0428.N0765.N1550.d005478, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem d008529 (F : ℂ → ℂ → ℂ) (ξ ν : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν =
      ∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b) := by
  unfold _root_.GD.N0106.N0428.N0765.N1652.d005817 _root_.GD.N0106.N0428.N0765.N1652.d005816
  rw [_root_.GD.N0106.N0428.N0765.N1644.d008528]
  simp_rw [_root_.GD.N0106.N0428.N0765.N1644.d008528, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [] with b
  unfold _root_.GD.N0106.N0428.N0765.N1644.d008524
  ring



theorem d008530 {F : ℂ → ℂ → ℂ} {d α β : ℝ}
    (hd : 0 < d) (hα : |α| ≤ d) (hβ : |β| ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (h0β : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 β) (volume.prod volume))
    (hαβ : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume))
    (hdecayA : ∀ b : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (ξ ν : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν =
      ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν p ∂(volume.prod volume) := by
  have hz : |(0 : ℝ)| ≤ d := by simpa only [abs_zero] using hd.le
  have hshiftB : ∀ᵐ a : ℝ,
      (∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b)) =
        ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν (a, b) := by
    filter_upwards [h00.prod_right_ae, h0β.prod_right_ae] with a ha0 haβ
    have hpa : _root_.GD.N0106.N0428.N0765.N1550.d005473 a 0 ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := _root_.GD.N0106.N0428.N0765.N1658.d008469 hz a
    have hcRow : ContinuousOn (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
      have hm : Continuous (fun w : ℂ => (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0, w)) := by fun_prop
      exact hc.comp hm.continuousOn (fun w hw => ⟨hpa, hw⟩)
    have hs := _root_.GD.N0106.N0428.N0765.N1636.d008412
      hd hβ hcRow (hfB _ hpa) ha0 haβ (hdecayB a) ν
    simp only [_root_.GD.N0106.N0428.N0765.N1644.d008524, _root_.GD.N0106.N0428.N0765.N1658.d008467, mul_assoc]
    rw [integral_const_mul, integral_const_mul]
    exact congrArg (fun v : ℂ => _root_.GD.N0106.N0428.N0765.N1644.d008523 ξ (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) * v) hs
  have hshiftA : ∀ᵐ b : ℝ,
      (∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν (a, b)) =
        ∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν (a, b) := by
    filter_upwards [h0β.prod_left_ae, hαβ.prod_left_ae] with b hb0 hbα
    have hpb : _root_.GD.N0106.N0428.N0765.N1550.d005473 b β ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := _root_.GD.N0106.N0428.N0765.N1658.d008469 hβ b
    have hcRow : ContinuousOn (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
      have hm : Continuous (fun z : ℂ => (z, _root_.GD.N0106.N0428.N0765.N1550.d005473 b β)) := by fun_prop
      exact hc.comp hm.continuousOn (fun z hz' => ⟨hz', hpb⟩)
    have hs := _root_.GD.N0106.N0428.N0765.N1636.d008412
      hd hα hcRow (hfA _ hpb) hb0 hbα (hdecayA b) ξ
    have hm := congrArg (fun v : ℂ => _root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β) * v) hs
    simp only [← integral_const_mul, _root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005483, _root_.GD.N0106.N0428.N0765.N1644.d008524, _root_.GD.N0106.N0428.N0765.N1658.d008467,
      _root_.GD.N0106.N0428.N0765.N1644.d008523] at hm ⊢
    simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008466, _root_.GD.N0106.N0428.N0765.N1550.d005473, mul_assoc, mul_left_comm, mul_comm] using hm
  rw [_root_.GD.N0106.N0428.N0765.N1644.d008529]
  calc
    (∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b)) =
        ∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν (a, b) := integral_congr_ae hshiftB
    _ = ∫ b : ℝ, ∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν (a, b) :=
      integral_integral_swap (_root_.GD.N0106.N0428.N0765.N1644.d008527 h0β ξ ν)
    _ = ∫ b : ℝ, ∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν (a, b) := integral_congr_ae hshiftA
    _ = ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν p ∂(volume.prod volume) :=
      (integral_prod_symm _ (_root_.GD.N0106.N0428.N0765.N1644.d008527 hαβ ξ ν)).symm


theorem d008531 {F : ℂ → ℂ → ℂ} {d α β : ℝ}
    (hd : 0 < d) (hα : |α| ≤ d) (hβ : |β| ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (h0β : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 β) (volume.prod volume))
    (hαβ : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume))
    (hdecayA : ∀ b : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (ξ ν : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν‖ ≤
      (Real.exp (2 * Real.pi * ξ * α) * Real.exp (2 * Real.pi * ν * β)) *
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β := by
  rw [_root_.GD.N0106.N0428.N0765.N1644.d008530 hd hα hβ hc hfA hfB h00 h0β hαβ hdecayA hdecayB]
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1644.d008524 F α β ξ ν p‖ ∂(volume.prod volume) :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [_root_.GD.N0106.N0428.N0765.N1644.d008526]
      exact integral_const_mul _ _



theorem d008532 {F : ℂ → ℂ → ℂ} {d M : ℝ}
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
    (ξ ν : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν‖ ≤
      _root_.GD.N0106.N0428.N0765.N1650.d008510 F d * Real.exp (-(2 * Real.pi * d) * |ξ|) *
        Real.exp (-(2 * Real.pi * d) * |ν|) := by
  let α : ℝ := if 0 ≤ ξ then -d else d
  let β : ℝ := if 0 ≤ ν then -d else d
  have hα : |α| ≤ d := by simp only [α]; split <;> simp [abs_of_pos hd]
  have hβ : |β| ≤ d := by simp only [β]; split <;> simp [abs_of_pos hd]
  have hz : |(0 : ℝ)| ≤ d := by simpa only [abs_zero] using hd.le
  have hplanes (u v : ℝ) (hu : |u| ≤ d) (hv : |v| ≤ d) :
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F u v) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F u v ≤ _root_.GD.N0106.N0428.N0765.N1650.d008510 F d :=
    _root_.GD.N0106.N0428.N0765.N1650.d008512
      hd hu hv hc hfA hfB hM hmm hmp hpm hpp
  have hb := _root_.GD.N0106.N0428.N0765.N1644.d008531 hd hα hβ hc hfA hfB
    (hplanes 0 0 hz hz).1 (hplanes 0 β hz hβ).1 (hplanes α β hα hβ).1
    (hdecayA β hβ) hdecayB ξ ν
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
    _ ≤ (Real.exp (2 * Real.pi * ξ * α) * Real.exp (2 * Real.pi * ν * β)) *
        _root_.GD.N0106.N0428.N0765.N1650.d008510 F d :=
      mul_le_mul_of_nonneg_left (hplanes α β hα hβ).2 (by positivity)
    _ = _ := by rw [heA, heB]; ring



theorem d008533 {f : ℝ × ℝ → ℂ} {C k : ℝ}
    (hk : 0 < k)
    (hb : ∀ ξ ν : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 f ξ ν‖ ≤
      C * Real.exp (-k * |ξ|) * Real.exp (-k * |ν|))
    (ν : ℝ) : Summable (fun n : ℤ => 𝓕 (_root_.GD.N0106.N0428.N0765.N1652.d005816 f ν) n) := by
  apply _root_.GD.N0106.N0428.N0765.N1613.d005630 (C := C * Real.exp (-k * |ν|)) hk
  intro n
  simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005817, mul_assoc, mul_left_comm, mul_comm] using hb n ν

end
end GD.N0106.N0428.N0765.N1644

#print axioms _root_.GD.N0106.N0428.N0765.N1644.d008530
#print axioms _root_.GD.N0106.N0428.N0765.N1644.d008531
#print axioms _root_.GD.N0106.N0428.N0765.N1644.d008532
#print axioms _root_.GD.N0106.N0428.N0765.N1644.d008533
