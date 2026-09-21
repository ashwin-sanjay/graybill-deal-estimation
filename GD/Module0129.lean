import GD.Module0128

































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0687

noncomputable section

open _root_.GD.N0230.N0604
open _root_.GD.N0230.N0696
open _root_.GD.N0230.N0669

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}




theorem d001509 {ψ : Θ → H} {m u : H} {c t : ℝ}
    (hc : 0 < c) (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫)
    (ht0 : 0 < t) (ht2 : t * ‖u‖ ^ 2 < 2 * c) :
    ∀ θ, ‖m + t • u - ψ θ‖ < ‖m - ψ θ‖ := by
  intro θ
  have hsq : ‖m + t • u - ψ θ‖ ^ 2 =
      ‖m - ψ θ‖ ^ 2 - 2 * t * ⟪u, ψ θ - m⟫ + t ^ 2 * ‖u‖ ^ 2 := by
    have h1 : m + t • u - ψ θ = (m - ψ θ) + t • u := by abel
    rw [h1, norm_add_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    have h2 : ⟪m - ψ θ, u⟫ = -⟪u, ψ θ - m⟫ := by
      rw [real_inner_comm,
        show m - ψ θ = -(ψ θ - m) from by abel, inner_neg_right]
    rw [h2]
    ring
  have hlt : ‖m + t • u - ψ θ‖ ^ 2 < ‖m - ψ θ‖ ^ 2 := by
    have k1 : t * (t * ‖u‖ ^ 2) < t * (2 * c) :=
      mul_lt_mul_of_pos_left ht2 ht0
    have k2 : 2 * t * c ≤ 2 * t * ⟪u, ψ θ - m⟫ :=
      mul_le_mul_of_nonneg_left (hfloor θ) (by positivity)
    rw [hsq]
    nlinarith [k1, k2]
  have h := Real.sqrt_lt_sqrt (by positivity) hlt
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    at h




theorem d001510 {S : Set H} {ψ : Θ → H}
    {dstar : H}
    (hdown : ∀ y x : H, x ∈ S → _root_.GD.N0230.N0604.d001484 ψ y x → y ∈ S)
    (hterm : _root_.GD.N0230.N0604.d001486 S ψ dstar) :
    _root_.GD.N0230.N0604.d001486 Set.univ ψ dstar := by
  refine ⟨Set.mem_univ _, ?_⟩
  rintro d' - hstr
  exact hterm.2 d' (hdown d' dstar hterm.1 hstr.1) hstr


theorem d001511 {ψ : Θ → H} {m : H} :
    ∀ y x : H, x ∈ _root_.GD.N0230.N0669.d001375 ψ m → _root_.GD.N0230.N0604.d001484 ψ y x →
      y ∈ _root_.GD.N0230.N0669.d001375 ψ m :=
  fun _y _x hx hyx ↦
    _root_.GD.N0230.N0696.d001494.mp (_root_.GD.N0230.N0696.d001493 hyx hx)


theorem d001512 {ψ : Θ → H}
    {m dstar : H}
    (hterm : _root_.GD.N0230.N0604.d001486 (_root_.GD.N0230.N0669.d001375 ψ m) ψ dstar) :
    _root_.GD.N0230.N0604.d001486 Set.univ ψ dstar :=
  _root_.GD.N0230.N0687.d001510 _root_.GD.N0230.N0687.d001511 hterm




theorem d001513
    [CompleteSpace H] [Nonempty Θ]
    {ψ : Θ → H} {m u : H} {c : ℝ}
    (hu : u ≠ 0) (hc : 0 < c) (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) :
    ∃ dstar ∈ _root_.GD.N0230.N0669.d001375 ψ m,
      (∀ θ, ‖dstar - ψ θ‖ < ‖m - ψ θ‖) ∧
      _root_.GD.N0230.N0604.d001486 (_root_.GD.N0230.N0669.d001375 ψ m) ψ dstar := by
  have hnorm : (0 : ℝ) < ‖u‖ ^ 2 := by
    have := norm_pos_iff.mpr hu
    positivity
  set t : ℝ := c / ‖u‖ ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t * ‖u‖ ^ 2 < 2 * c := by
    rw [ht, div_mul_cancel₀ _ hnorm.ne']
    linarith
  have hstrict := _root_.GD.N0230.N0687.d001509 hc hfloor ht0 ht2
  have hd₀mem : m + t • u ∈ _root_.GD.N0230.N0669.d001375 ψ m :=
    fun θ ↦ (hstrict θ).le
  exact _root_.GD.N0230.N0696.d001497
    (_root_.GD.N0230.N0669.d001387 ψ m)
    (_root_.GD.N0230.N0575.d001454 ψ m)
    hd₀mem hstrict (Classical.arbitrary Θ)





theorem d001514 [CompleteSpace H] [Nonempty Θ]
    {ψ : Θ → H} {m u : H} {c : ℝ}
    (hu : u ≠ 0) (hc : 0 < c) (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) :
    ∃ dstar, (∀ θ, ‖dstar - ψ θ‖ < ‖m - ψ θ‖) ∧
      _root_.GD.N0230.N0604.d001486 Set.univ ψ dstar := by
  obtain ⟨dstar, _hmem, hstrict, hterm⟩ :=
    _root_.GD.N0230.N0687.d001513 hu hc hfloor
  exact ⟨dstar, hstrict,
    _root_.GD.N0230.N0687.d001512 hterm⟩

end

end N0687
end N0230
end GD

#print axioms _root_.GD.N0230.N0687.d001509
#print axioms _root_.GD.N0230.N0687.d001510
#print axioms _root_.GD.N0230.N0687.d001512
#print axioms _root_.GD.N0230.N0687.d001513
#print axioms _root_.GD.N0230.N0687.d001514
