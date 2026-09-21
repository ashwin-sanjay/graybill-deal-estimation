import GD.Module0586




















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1640
noncomputable section

open MeasureTheory Set Complex Filter
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1550 _root_.GD.N0106.N0428.N0765.N1644
open scoped Topology FourierTransform



theorem d008534 {F : ℂ → ℂ → ℂ} {d α : ℝ}
    (hd : 0 < d) (hα : |α| ≤ d)
    (hcA : ∀ b : ℝ,
      ContinuousOn (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ b : ℝ,
      DifferentiableOn ℂ (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (hα0 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α 0) (volume.prod volume))
    (hdecayA : ∀ b : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)‖ ≤ ε)
    (ξ ν : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν =
      ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α 0 ξ ν p ∂(volume.prod volume) := by
  have hshiftA : ∀ᵐ b : ℝ,
      (∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b)) =
        ∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α 0 ξ ν (a, b) := by
    filter_upwards [h00.prod_left_ae, hα0.prod_left_ae] with b hb0 hbα
    have hs := _root_.GD.N0106.N0428.N0765.N1636.d008412
      hd hα (hcA b) (hfA b) hb0 hbα (hdecayA b) ξ
    have hm := congrArg (fun v : ℂ => _root_.GD.N0106.N0428.N0765.N1644.d008523 ν (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0) * v) hs
    simp only [← integral_const_mul, _root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005483, _root_.GD.N0106.N0428.N0765.N1644.d008524, _root_.GD.N0106.N0428.N0765.N1658.d008467,
      _root_.GD.N0106.N0428.N0765.N1644.d008523] at hm ⊢
    simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008466, _root_.GD.N0106.N0428.N0765.N1550.d005473,
      mul_assoc, mul_left_comm, mul_comm] using hm
  rw [_root_.GD.N0106.N0428.N0765.N1644.d008529]
  calc
    (∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b)) =
        ∫ b : ℝ, ∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b) :=
      integral_integral_swap (_root_.GD.N0106.N0428.N0765.N1644.d008527 h00 ξ ν)
    _ = ∫ b : ℝ, ∫ a : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α 0 ξ ν (a, b) :=
      integral_congr_ae hshiftA
    _ = ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F α 0 ξ ν p ∂(volume.prod volume) :=
      (integral_prod_symm _ (_root_.GD.N0106.N0428.N0765.N1644.d008527 hα0 ξ ν)).symm


theorem d008535 {F : ℂ → ℂ → ℂ} {d β : ℝ}
    (hd : 0 < d) (hβ : |β| ≤ d)
    (hcB : ∀ a : ℝ,
      ContinuousOn (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfB : ∀ a : ℝ,
      DifferentiableOn ℂ (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (h0β : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 β) (volume.prod volume))
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (ξ ν : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν =
      ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν p ∂(volume.prod volume) := by
  have hshiftB : ∀ᵐ a : ℝ,
      (∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b)) =
        ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν (a, b) := by
    filter_upwards [h00.prod_right_ae, h0β.prod_right_ae] with a ha0 haβ
    have hs := _root_.GD.N0106.N0428.N0765.N1636.d008412
      hd hβ (hcB a) (hfB a) ha0 haβ (hdecayB a) ν
    have hm := congrArg (fun v : ℂ => _root_.GD.N0106.N0428.N0765.N1644.d008523 ξ (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) * v) hs
    simp only [← integral_const_mul, _root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005483, _root_.GD.N0106.N0428.N0765.N1644.d008524, _root_.GD.N0106.N0428.N0765.N1658.d008467,
      _root_.GD.N0106.N0428.N0765.N1644.d008523] at hm ⊢
    simpa only [_root_.GD.N0106.N0428.N0765.N1658.d008466, _root_.GD.N0106.N0428.N0765.N1550.d005473,
      mul_assoc, mul_left_comm, mul_comm] using hm
  rw [_root_.GD.N0106.N0428.N0765.N1644.d008529]
  calc
    (∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 0 ξ ν (a, b)) =
        ∫ a : ℝ, ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν (a, b) :=
      integral_congr_ae hshiftB
    _ = ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν p ∂(volume.prod volume) :=
      (integral_prod _ (_root_.GD.N0106.N0428.N0765.N1644.d008527 h0β ξ ν)).symm


theorem d008536 {F : ℂ → ℂ → ℂ} {d α : ℝ}
    (hd : 0 < d) (hα : |α| ≤ d)
    (hcA : ∀ b : ℝ,
      ContinuousOn (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ b : ℝ,
      DifferentiableOn ℂ (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (hα0 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α 0) (volume.prod volume))
    (hdecayA : ∀ b : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)‖ ≤ ε)
    (ξ ν : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν‖ ≤
      Real.exp (2 * Real.pi * ξ * α) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F α 0 := by
  rw [_root_.GD.N0106.N0428.N0765.N1640.d008534 hd hα hcA hfA h00 hα0 hdecayA]
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1644.d008524 F α 0 ξ ν p‖ ∂(volume.prod volume) :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [_root_.GD.N0106.N0428.N0765.N1644.d008526]
      simp only [mul_zero, Real.exp_zero, mul_one]
      exact integral_const_mul _ _


theorem d008537 {F : ℂ → ℂ → ℂ} {d β : ℝ}
    (hd : 0 < d) (hβ : |β| ≤ d)
    (hcB : ∀ a : ℝ,
      ContinuousOn (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfB : ∀ a : ℝ,
      DifferentiableOn ℂ (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (h0β : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 β) (volume.prod volume))
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (ξ ν : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ ν‖ ≤
      Real.exp (2 * Real.pi * ν * β) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F 0 β := by
  rw [_root_.GD.N0106.N0428.N0765.N1640.d008535 hd hβ hcB hfB h00 h0β hdecayB]
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1644.d008524 F 0 β ξ ν p‖ ∂(volume.prod volume) :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [_root_.GD.N0106.N0428.N0765.N1644.d008526]
      simp only [mul_zero, Real.exp_zero, one_mul]
      exact integral_const_mul _ _


def d008538 (F : ℂ → ℂ → ℂ) (d : ℝ) : ℝ :=
  max (_root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) 0) (_root_.GD.N0106.N0428.N0765.N1658.d008468 F d 0)


def d008539 (F : ℂ → ℂ → ℂ) (d : ℝ) : ℝ :=
  max (_root_.GD.N0106.N0428.N0765.N1658.d008468 F 0 (-d)) (_root_.GD.N0106.N0428.N0765.N1658.d008468 F 0 d)



theorem d008540 {F : ℂ → ℂ → ℂ} {d : ℝ}
    (hd : 0 < d)
    (hcA : ∀ b : ℝ,
      ContinuousOn (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ b : ℝ,
      DifferentiableOn ℂ (fun z : ℂ => F z (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (hm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) 0) (volume.prod volume))
    (hp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d 0) (volume.prod volume))
    (hdecayA : ∀ b : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b 0)‖ ≤ ε)
    (ξ : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) ξ 0‖ ≤
      _root_.GD.N0106.N0428.N0765.N1640.d008538 F d * Real.exp (-(2 * Real.pi * d) * |ξ|) := by
  let α : ℝ := if 0 ≤ ξ then -d else d
  have hα : |α| ≤ d := by
    dsimp only [α]
    split_ifs <;> simp [abs_of_pos hd]
  have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α 0) (volume.prod volume) := by
    dsimp only [α]
    split_ifs <;> assumption
  have hmass : _root_.GD.N0106.N0428.N0765.N1658.d008468 F α 0 ≤ _root_.GD.N0106.N0428.N0765.N1640.d008538 F d := by
    dsimp only [α, _root_.GD.N0106.N0428.N0765.N1640.d008538]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have he : 2 * Real.pi * ξ * α = -(2 * Real.pi * d) * |ξ| := by
    dsimp only [α]
    split_ifs with hξ
    · rw [abs_of_nonneg hξ]; ring
    · rw [abs_of_neg (lt_of_not_ge hξ)]; ring
  calc
    _ ≤ Real.exp (2 * Real.pi * ξ * α) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F α 0 :=
      _root_.GD.N0106.N0428.N0765.N1640.d008536 hd hα hcA hfA h00 hi hdecayA ξ 0
    _ ≤ Real.exp (2 * Real.pi * ξ * α) * _root_.GD.N0106.N0428.N0765.N1640.d008538 F d :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = _ := by rw [he]; ring


theorem d008541 {F : ℂ → ℂ → ℂ} {d : ℝ}
    (hd : 0 < d)
    (hcB : ∀ a : ℝ,
      ContinuousOn (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfB : ∀ a : ℝ,
      DifferentiableOn ℂ (fun w : ℂ => F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (h00 : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) (volume.prod volume))
    (hm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 (-d)) (volume.prod volume))
    (hp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 d) (volume.prod volume))
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (ν : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) 0 ν‖ ≤
      _root_.GD.N0106.N0428.N0765.N1640.d008539 F d * Real.exp (-(2 * Real.pi * d) * |ν|) := by
  let β : ℝ := if 0 ≤ ν then -d else d
  have hβ : |β| ≤ d := by
    dsimp only [β]
    split_ifs <;> simp [abs_of_pos hd]
  have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 β) (volume.prod volume) := by
    dsimp only [β]
    split_ifs <;> assumption
  have hmass : _root_.GD.N0106.N0428.N0765.N1658.d008468 F 0 β ≤ _root_.GD.N0106.N0428.N0765.N1640.d008539 F d := by
    dsimp only [β, _root_.GD.N0106.N0428.N0765.N1640.d008539]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have he : 2 * Real.pi * ν * β = -(2 * Real.pi * d) * |ν| := by
    dsimp only [β]
    split_ifs with hν
    · rw [abs_of_nonneg hν]; ring
    · rw [abs_of_neg (lt_of_not_ge hν)]; ring
  calc
    _ ≤ Real.exp (2 * Real.pi * ν * β) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F 0 β :=
      _root_.GD.N0106.N0428.N0765.N1640.d008537 hd hβ hcB hfB h00 hi hdecayB 0 ν
    _ ≤ Real.exp (2 * Real.pi * ν * β) * _root_.GD.N0106.N0428.N0765.N1640.d008539 F d :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = _ := by rw [he]; ring

end
end GD.N0106.N0428.N0765.N1640
