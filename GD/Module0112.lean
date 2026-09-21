import GD.Module0111







































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0597

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0572
open _root_.GD.N0230.N0574
open _root_.GD.N0230.N0607

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} (ψ : Θ → H) (m w : H)






theorem d001415
    (hchar : ∀ (s : ℝ) (d : H),
      _root_.GD.N0230.N0572.d001400 m w (Real.exp s • d) =
        Real.exp s * _root_.GD.N0230.N0572.d001400 m w d) :
    ⟪m, w⟫ = 0 := by
  have h := hchar 1 m
  rw [_root_.GD.N0230.N0572.d001401, mul_zero] at h
  unfold _root_.GD.N0230.N0572.d001400 at h
  have hgt : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hsub : Real.exp 1 • m - m = (Real.exp 1 - 1) • m := by
    rw [sub_smul, one_smul]
  rw [hsub, real_inner_smul_left] at h
  have h2 : (Real.exp 1 - 1) * ⟪m, w⟫ = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact h3


theorem d001416 {v : H}
    (hloc : ∀ d : H, _root_.GD.N0230.N0572.d001400 m w (d + v) =
      _root_.GD.N0230.N0572.d001400 m w d) :
    ⟪v, w⟫ = 0 := by
  have h := hloc m
  rw [_root_.GD.N0230.N0572.d001401] at h
  unfold _root_.GD.N0230.N0572.d001400 at h
  rw [show m + v - m = v from by abel] at h
  linarith



theorem d001417
    (horth : ⟪m, w⟫ = 0) (d : H) :
    _root_.GD.N0230.N0572.d001400 m w d = -2 * ⟪d, w⟫ := by
  unfold _root_.GD.N0230.N0572.d001400
  rw [inner_sub_left, horth]
  ring



theorem d001418
    (horth : ⟪m, w⟫ = 0) (η : ℝ) :
    {d : H | _root_.GD.N0230.N0572.d001400 m w d ≤ -η} =
      _root_.GD.N0230.N0607.d001361 (-w) (η / 2) := by
  rw [_root_.GD.N0230.N0574.d001413 m w η, horth, add_zero]






theorem d001419
    {d : H} (hd : d ∈ _root_.GD.N0230.N0669.d001375 ψ m)
    (hpos : 0 < ⟪d - m, w⟫)
    {η : ℝ} (hη : 0 < η) (hbudget : η < 2 * ⟪d - m, w⟫) :
    Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
      (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
      ∃ p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
        ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖p - ψ θ‖ ^ 2 := by
  have hne : d ≠ m := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hu : d - m ≠ 0 := sub_ne_zero.mpr hne
  have hn : (0 : ℝ) < ‖d - m‖ ^ 2 := by
    have := norm_pos_iff.mpr hu
    positivity
  have hfloor : ∀ θ, ‖d - m‖ ^ 2 / 2 ≤ ⟪d - m, ψ θ - m⟫ := by
    intro θ
    have := (_root_.GD.N0230.N0669.d001379 ψ m d).mp hd θ
    linarith
  have hbudget' : η <
      4 * ⟪d - m, w⟫ * (‖d - m‖ ^ 2 / 2) / ‖d - m‖ ^ 2 := by
    have h4 : 4 * ⟪d - m, w⟫ * (‖d - m‖ ^ 2 / 2) / ‖d - m‖ ^ 2 =
        2 * ⟪d - m, w⟫ := by
      field_simp
      ring
    rw [h4]
    exact hbudget
  exact _root_.GD.N0230.N0574.d001414 ψ m w hu hfloor
    (by positivity) (le_refl _) hpos hη hbudget'






theorem d001420
    (hsupp : ∀ d ∈ _root_.GD.N0230.N0669.d001375 ψ m, 0 ≤ ⟪d - m, w⟫) :
    (∃ γ : ℝ, 0 < γ ∧ ∀ η : ℝ, 0 < η → η < 2 * γ →
      Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
        (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
        ∃ p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
          ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖p - ψ θ‖ ^ 2) ∨
      (∀ d ∈ _root_.GD.N0230.N0669.d001375 ψ m, ⟪d - m, w⟫ = 0) := by
  by_cases hex : ∃ d ∈ _root_.GD.N0230.N0669.d001375 ψ m, 0 < ⟪d - m, w⟫
  · left
    obtain ⟨d, hd, hpos⟩ := hex
    exact ⟨⟪d - m, w⟫, hpos, fun η hη hbudget ↦
      _root_.GD.N0230.N0597.d001419 ψ m w hd hpos hη hbudget⟩
  · right
    push Not at hex
    intro d hd
    exact le_antisymm (hex d hd) (hsupp d hd)

end

end N0597
end N0230
end GD

#print axioms _root_.GD.N0230.N0597.d001415
#print axioms _root_.GD.N0230.N0597.d001416
#print axioms _root_.GD.N0230.N0597.d001418
#print axioms _root_.GD.N0230.N0597.d001419
#print axioms _root_.GD.N0230.N0597.d001420
