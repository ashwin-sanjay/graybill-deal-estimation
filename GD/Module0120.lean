import GD.Module0119
































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0662

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0572
open _root_.GD.N0230.N0574
open _root_.GD.N0230.N0575

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}
variable (ψ : Θ → H) (m w : H)





theorem d001460
    {S : Set H} {T : H → H}
    (hiso : ∀ x y : H, ‖T x - T y‖ = ‖x - y‖)
    {d p : H}
    (hmem : p ∈ S) (hmin : ∀ q ∈ S, ‖d - p‖ ≤ ‖d - q‖) :
    T p ∈ T '' S ∧ ∀ q ∈ T '' S, ‖T d - T p‖ ≤ ‖T d - q‖ := by
  refine ⟨Set.mem_image_of_mem T hmem, ?_⟩
  rintro q ⟨q₀, hq₀, rfl⟩
  rw [hiso, hiso]
  exact hmin q₀ hq₀




theorem d001461
    {S S' : Set H} {T : H → H}
    (hiso : ∀ x y : H, ‖T x - T y‖ = ‖x - y‖)
    (himg : S' = T '' S)
    {d p : H}
    (hmem : p ∈ S) (hmin : ∀ q ∈ S, ‖d - p‖ ≤ ‖d - q‖)
    {p' : H}
    (huniq : ∀ r : H,
      (r ∈ S' ∧ ∀ q ∈ S', ‖T d - r‖ ≤ ‖T d - q‖) → r = p') :
    T p = p' := by
  apply huniq
  rw [himg]
  exact _root_.GD.N0230.N0662.d001460 hiso hmem hmin





theorem d001462 (v : H) (η : ℝ) :
    (fun d : H ↦ d + v) '' _root_.GD.N0230.N0574.d001411 ψ m w η =
      _root_.GD.N0230.N0574.d001411 (fun θ ↦ ψ θ + v) (m + v) w η := by
  ext x
  constructor
  · rintro ⟨d, ⟨hcone, hcharge⟩, rfl⟩
    constructor
    · intro θ
      have h1 : d + v - (ψ θ + v) = d - ψ θ := by abel
      have h2 : m + v - (ψ θ + v) = m - ψ θ := by abel
      rw [h1, h2]
      exact hcone θ
    · show _root_.GD.N0230.N0572.d001400 (m + v) w (d + v) ≤ -η
      have hQ : _root_.GD.N0230.N0572.d001400 (m + v) w (d + v) =
          _root_.GD.N0230.N0572.d001400 m w d := by
        unfold _root_.GD.N0230.N0572.d001400
        rw [show d + v - (m + v) = d - m from by abel]
      rw [hQ]
      exact hcharge
  · rintro ⟨hcone, hcharge⟩
    refine ⟨x - v, ⟨?_, ?_⟩, by abel⟩
    · intro θ
      have h1 := hcone θ
      have e1 : x - v - ψ θ = x - (ψ θ + v) := by abel
      have e2 : m - ψ θ = m + v - (ψ θ + v) := by abel
      rw [e1, e2]
      exact h1
    · show _root_.GD.N0230.N0572.d001400 m w (x - v) ≤ -η
      have hQ : _root_.GD.N0230.N0572.d001400 m w (x - v) =
          _root_.GD.N0230.N0572.d001400 (m + v) w x := by
        unfold _root_.GD.N0230.N0572.d001400
        rw [show x - v - m = x - (m + v) from by abel]
      rw [hQ]
      exact hcharge




theorem d001463 [CompleteSpace H]
    {u : H} {c γ η : ℝ} (hu : u ≠ 0)
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) (hc : 0 < c)
    (hslope : γ ≤ ⟪u, w⟫) (hγ : 0 < γ)
    (hη : 0 < η) (hbudget : η < 4 * γ * c / ‖u‖ ^ 2)
    (v d : H) {p p' : H}
    (hp : p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η ∧
      ∀ q ∈ _root_.GD.N0230.N0574.d001411 ψ m w η, ‖d - p‖ ≤ ‖d - q‖)
    (hp' : p' ∈ _root_.GD.N0230.N0574.d001411 (fun θ ↦ ψ θ + v) (m + v) w η ∧
      ∀ q ∈ _root_.GD.N0230.N0574.d001411 (fun θ ↦ ψ θ + v) (m + v) w η,
        ‖d + v - p'‖ ≤ ‖d + v - q‖) :
    p' = p + v := by
  have hfloor' : ∀ θ, c ≤ ⟪u, (ψ θ + v) - (m + v)⟫ := by
    intro θ
    rw [show ψ θ + v - (m + v) = ψ θ - m from by abel]
    exact hfloor θ
  obtain ⟨p₀, hp₀, huniq⟩ :=
    _root_.GD.N0230.N0575.d001459 (fun θ ↦ ψ θ + v) (m + v) w hu
      hfloor' hc hslope hγ hη hbudget (d + v)
  have h1 : p' = p₀ := huniq p' hp'
  have h2 : p + v = p₀ := by
    apply huniq
    have hiso : ∀ x y : H, ‖x + v - (y + v)‖ = ‖x - y‖ := by
      intro x y
      rw [show x + v - (y + v) = x - y from by abel]
    have hmin := _root_.GD.N0230.N0662.d001460
      (T := fun x : H ↦ x + v) hiso hp.1 hp.2
    rw [_root_.GD.N0230.N0662.d001462 ψ m w v η] at hmin
    exact hmin
  rw [h1, h2]

end

end N0662
end N0230
end GD

#print axioms _root_.GD.N0230.N0662.d001460
#print axioms _root_.GD.N0230.N0662.d001461
#print axioms _root_.GD.N0230.N0662.d001462
#print axioms _root_.GD.N0230.N0662.d001463
