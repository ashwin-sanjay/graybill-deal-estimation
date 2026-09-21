import GD.Module0120

































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0663

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0572
open _root_.GD.N0230.N0574
open _root_.GD.N0230.N0575

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}
variable (ψ : Θ → H) (m w : H)





theorem d001464
    {S : Set H} {T : H → H} {lam : ℝ} (hlam : 0 < lam)
    (hsim : ∀ x y : H, ‖T x - T y‖ = lam * ‖x - y‖)
    {d p : H}
    (hmem : p ∈ S) (hmin : ∀ q ∈ S, ‖d - p‖ ≤ ‖d - q‖) :
    T p ∈ T '' S ∧ ∀ q ∈ T '' S, ‖T d - T p‖ ≤ ‖T d - q‖ := by
  refine ⟨Set.mem_image_of_mem T hmem, ?_⟩
  rintro q ⟨q₀, hq₀, rfl⟩
  rw [hsim, hsim]
  exact mul_le_mul_of_nonneg_left (hmin q₀ hq₀) hlam.le



theorem d001465
    {S S' : Set H} {T : H → H} {lam : ℝ} (hlam : 0 < lam)
    (hsim : ∀ x y : H, ‖T x - T y‖ = lam * ‖x - y‖)
    (himg : S' = T '' S)
    {d p : H}
    (hmem : p ∈ S) (hmin : ∀ q ∈ S, ‖d - p‖ ≤ ‖d - q‖)
    {p' : H}
    (huniq : ∀ r : H,
      (r ∈ S' ∧ ∀ q ∈ S', ‖T d - r‖ ≤ ‖T d - q‖) → r = p') :
    T p = p' := by
  apply huniq
  rw [himg]
  exact _root_.GD.N0230.N0663.d001464 hlam hsim hmem hmin







theorem d001466 {t : ℝ} (ht : 0 < t)
    (η : ℝ) :
    (fun d : H ↦ t • d) '' _root_.GD.N0230.N0574.d001411 ψ m w η =
      _root_.GD.N0230.N0574.d001411 (fun θ ↦ t • ψ θ) (t • m) w (t * η) := by
  ext x
  constructor
  · rintro ⟨d, ⟨hcone, hcharge⟩, rfl⟩
    constructor
    · intro θ
      have h1 : t • d - t • ψ θ = t • (d - ψ θ) := by
        rw [smul_sub]
      have h2 : t • m - t • ψ θ = t • (m - ψ θ) := by
        rw [smul_sub]
      rw [h1, h2, norm_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left (hcone θ) ht.le
    · show _root_.GD.N0230.N0572.d001400 (t • m) w (t • d) ≤ -(t * η)
      have hQ : _root_.GD.N0230.N0572.d001400 (t • m) w (t • d) =
          t * _root_.GD.N0230.N0572.d001400 m w d := by
        unfold _root_.GD.N0230.N0572.d001400
        rw [show t • d - t • m = t • (d - m) from by rw [smul_sub],
          real_inner_smul_left]
        ring
      rw [hQ]
      have := mul_le_mul_of_nonneg_left hcharge ht.le
      linarith [this]
  · rintro ⟨hcone, hcharge⟩
    have htne : t ≠ 0 := ht.ne'
    refine ⟨t⁻¹ • x, ⟨?_, ?_⟩, by
      show t • t⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ htne, one_smul]⟩
    · intro θ
      have h1 := hcone θ
      have e1 : x - t • ψ θ = t • (t⁻¹ • x - ψ θ) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ htne, one_smul]
      have e2 : t • m - t • ψ θ = t • (m - ψ θ) := by
        rw [smul_sub]
      rw [e1, e2, norm_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht] at h1
      exact le_of_mul_le_mul_left h1 ht
    · show _root_.GD.N0230.N0572.d001400 m w (t⁻¹ • x) ≤ -η
      have hQ : _root_.GD.N0230.N0572.d001400 (t • m) w x =
          t * _root_.GD.N0230.N0572.d001400 m w (t⁻¹ • x) := by
        unfold _root_.GD.N0230.N0572.d001400
        rw [show x - t • m = t • (t⁻¹ • x - m) from by
          rw [smul_sub, smul_smul, mul_inv_cancel₀ htne, one_smul],
          real_inner_smul_left]
        ring
      have h1 : t * _root_.GD.N0230.N0572.d001400 m w (t⁻¹ • x) ≤ -(t * η) := by
        rw [← hQ]
        exact hcharge
      have h2 : t * _root_.GD.N0230.N0572.d001400 m w (t⁻¹ • x) ≤ t * (-η) := by
        linarith [h1]
      exact le_of_mul_le_mul_left h2 ht






theorem d001467 [CompleteSpace H]
    {u : H} {c γ η : ℝ} (hu : u ≠ 0)
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) (hc : 0 < c)
    (hslope : γ ≤ ⟪u, w⟫) (hγ : 0 < γ)
    (hη : 0 < η) (hbudget : η < 4 * γ * c / ‖u‖ ^ 2)
    {t : ℝ} (ht : 0 < t) (d : H) {p p' : H}
    (hp : p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η ∧
      ∀ q ∈ _root_.GD.N0230.N0574.d001411 ψ m w η, ‖d - p‖ ≤ ‖d - q‖)
    (hp' : p' ∈ _root_.GD.N0230.N0574.d001411 (fun θ ↦ t • ψ θ) (t • m) w
        (t * η) ∧
      ∀ q ∈ _root_.GD.N0230.N0574.d001411 (fun θ ↦ t • ψ θ) (t • m) w (t * η),
        ‖t • d - p'‖ ≤ ‖t • d - q‖) :
    p' = t • p := by
  have hfloor' : ∀ θ, t * c ≤ ⟪u, t • ψ θ - t • m⟫ := by
    intro θ
    rw [show t • ψ θ - t • m = t • (ψ θ - m) from by rw [smul_sub],
      real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hfloor θ) ht.le
  have hbudget' : t * η < 4 * γ * (t * c) / ‖u‖ ^ 2 := by
    have hn : (0 : ℝ) < ‖u‖ ^ 2 := by
      have := norm_pos_iff.mpr hu
      positivity
    rw [show 4 * γ * (t * c) / ‖u‖ ^ 2 =
      t * (4 * γ * c / ‖u‖ ^ 2) from by ring]
    exact mul_lt_mul_of_pos_left hbudget ht
  obtain ⟨p₀, hp₀, huniq⟩ :=
    _root_.GD.N0230.N0575.d001459 (fun θ ↦ t • ψ θ) (t • m) w hu
      hfloor' (by positivity) hslope hγ (by positivity) hbudget'
      (t • d)
  have h1 : p' = p₀ := huniq p' hp'
  have h2 : t • p = p₀ := by
    apply huniq
    have hsim : ∀ x y : H, ‖t • x - t • y‖ = t * ‖x - y‖ := by
      intro x y
      rw [show t • x - t • y = t • (x - y) from by rw [smul_sub],
        norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hmin := _root_.GD.N0230.N0663.d001464
      (T := fun x : H ↦ t • x) ht hsim hp.1 hp.2
    rw [_root_.GD.N0230.N0663.d001466 ψ m w ht η] at hmin
    exact hmin
  rw [h1, h2]

end

end N0663
end N0230
end GD

#print axioms _root_.GD.N0230.N0663.d001464
#print axioms _root_.GD.N0230.N0663.d001465
#print axioms _root_.GD.N0230.N0663.d001466
#print axioms _root_.GD.N0230.N0663.d001467
