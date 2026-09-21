import GD.Module0110








































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0574

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0679
open _root_.GD.N0230.N0572
open _root_.GD.N0230.N0607

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} (ψ : Θ → H) (m w : H)






theorem d001408
    {d : H} (hd : d ∈ _root_.GD.N0230.N0669.d001375 ψ m) (hne : d ≠ m) :
    d - m ∈ _root_.GD.N0230.N0679.d001389 ψ m := by
  have hpos : (0 : ℝ) < ‖d - m‖ ^ 2 := by
    have : d - m ≠ 0 := sub_ne_zero.mpr hne
    have := norm_pos_iff.mpr this
    positivity
  refine ⟨‖d - m‖ ^ 2 / 2, by positivity, fun θ ↦ ?_⟩
  have := (_root_.GD.N0230.N0669.d001379 ψ m d).mp hd θ
  linarith




theorem d001409 {x y : H} {s r : ℝ} (hsr : s + r = 1) :
    _root_.GD.N0230.N0572.d001400 m w (s • x + r • y) =
      s * _root_.GD.N0230.N0572.d001400 m w x + r * _root_.GD.N0230.N0572.d001400 m w y := by
  unfold _root_.GD.N0230.N0572.d001400
  have h1 : s • (x - m) + r • (y - m) =
      s • x + r • y - (s • m + r • m) := by
    rw [smul_sub, smul_sub]
    abel
  have h2 : s • m + r • m = m := by
    rw [← add_smul, hsr, one_smul]
  have hcomb : s • x + r • y - m = s • (x - m) + r • (y - m) := by
    rw [h1, h2]
  rw [hcomb, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  ring


theorem d001410 (η : ℝ) :
    Convex ℝ {d : H | _root_.GD.N0230.N0572.d001400 m w d ≤ -η} := by
  intro x hx y hy s r hs hr hsr
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [_root_.GD.N0230.N0574.d001409 m w hsr]
  have h1 := mul_le_mul_of_nonneg_left hx hs
  have h2 := mul_le_mul_of_nonneg_left hy hr
  have h3 : s * -η + r * -η = -η := by
    rw [← add_mul, hsr]
    ring
  linarith [h1, h2, h3]



def d001411 (η : ℝ) : Set H :=
  _root_.GD.N0230.N0669.d001375 ψ m ∩ {d : H | _root_.GD.N0230.N0572.d001400 m w d ≤ -η}


theorem d001412 (η : ℝ) :
    Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) :=
  (_root_.GD.N0230.N0669.d001387 ψ m).inter (_root_.GD.N0230.N0574.d001410 m w η)







theorem d001413 (η : ℝ) :
    {d : H | _root_.GD.N0230.N0572.d001400 m w d ≤ -η} =
      _root_.GD.N0230.N0607.d001361 (-w) (η / 2 + ⟪m, w⟫) := by
  ext d
  unfold _root_.GD.N0230.N0607.d001361 _root_.GD.N0230.N0572.d001400
  simp only [Set.mem_setOf_eq, inner_neg_right, inner_sub_left]
  constructor <;> intro h <;> linarith








theorem d001414
    {u : H} {c γ η : ℝ} (hu : u ≠ 0)
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) (hc : 0 < c)
    (hslope : γ ≤ ⟪u, w⟫) (hγ : 0 < γ)
    (hη : 0 < η) (hbudget : η < 4 * γ * c / ‖u‖ ^ 2) :
    Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
      (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
      ∃ d ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
        ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖d - ψ θ‖ ^ 2 := by
  have hn : (0 : ℝ) < ‖u‖ ^ 2 := by
    have := norm_pos_iff.mpr hu
    positivity
  have hends : η / (2 * γ) < 2 * c / ‖u‖ ^ 2 := by
    rw [div_lt_div_iff₀ (by linarith) hn]
    have hb : η * ‖u‖ ^ 2 < 4 * γ * c := by
      have := mul_lt_mul_of_pos_right hbudget hn
      have h2 : 4 * γ * c / ‖u‖ ^ 2 * ‖u‖ ^ 2 = 4 * γ * c := by
        rw [div_mul_cancel₀ _ hn.ne']
      linarith [this, h2.le, h2.symm.le]
    nlinarith [hb]
  set t₀ := (η / (2 * γ) + 2 * c / ‖u‖ ^ 2) / 2 with ht₀
  have ht₀pos : 0 < t₀ := by
    rw [ht₀]
    positivity
  have ht₀lo : η / (2 * γ) ≤ t₀ := by
    rw [ht₀]
    linarith
  have ht₀hi : t₀ * ‖u‖ ^ 2 < 2 * c := by
    have h1 : t₀ < 2 * c / ‖u‖ ^ 2 := by
      rw [ht₀]
      linarith
    have := mul_lt_mul_of_pos_right h1 hn
    have h2 : 2 * c / ‖u‖ ^ 2 * ‖u‖ ^ 2 = 2 * c := by
      rw [div_mul_cancel₀ _ hn.ne']
    linarith [this, h2.le, h2.symm.le]
  have hseg := _root_.GD.N0230.N0572.d001405 ψ m w hfloor hslope hγ ht₀pos
    ht₀lo ht₀hi
  have hmem := _root_.GD.N0230.N0572.d001404 ψ m w hfloor hslope hγ ht₀pos
    ht₀lo ht₀hi.le
  have hd : m + t₀ • u ∈ _root_.GD.N0230.N0574.d001411 ψ m w η :=
    ⟨hmem.1, hmem.2⟩
  refine ⟨_root_.GD.N0230.N0574.d001412 ψ m w η, ⟨m + t₀ • u, hd⟩,
    ⟨m + t₀ • u, hd, ?_⟩⟩
  intro θ
  have := hseg.1 θ
  have hrw : m + t₀ • u - ψ θ = m + t₀ • u - ψ θ := rfl
  linarith [this]

end

end N0574
end N0230
end GD

#print axioms _root_.GD.N0230.N0574.d001408
#print axioms _root_.GD.N0230.N0574.d001409
#print axioms _root_.GD.N0230.N0574.d001412
#print axioms _root_.GD.N0230.N0574.d001413
#print axioms _root_.GD.N0230.N0574.d001414
