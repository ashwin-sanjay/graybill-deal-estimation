import Mathlib.Analysis.InnerProductSpace.Dual
import GD.Module0117




























open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0711

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0574
open _root_.GD.N0230.N0568

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} [MeasurableSpace Θ]


theorem d001450
    {v : ℕ → H} {ℓ : H → ℝ}
    (hconv : ∀ d : H, Tendsto (fun n ↦ ⟪d, v n⟫) atTop
      (nhds (ℓ d))) :
    IsLinearMap ℝ ℓ := by
  refine ⟨?_, ?_⟩
  · intro x y
    have hsum := (hconv x).add (hconv y)
    have heq : (fun n ↦ ⟪x, v n⟫ + ⟪y, v n⟫) =
        fun n ↦ ⟪x + y, v n⟫ :=
      funext fun n ↦ by rw [inner_add_left]
    rw [heq] at hsum
    exact tendsto_nhds_unique (hconv (x + y)) hsum
  · intro c x
    have hmul := (hconv x).const_mul c
    have heq : (fun n ↦ c * ⟪x, v n⟫) =
        fun n ↦ ⟪c • x, v n⟫ :=
      funext fun n ↦ by rw [real_inner_smul_left]
    rw [heq] at hmul
    have h := tendsto_nhds_unique (hconv (c • x)) hmul
    rw [smul_eq_mul]
    exact h


theorem d001451
    {v : ℕ → H} {ℓ : H → ℝ} {B : ℝ}
    (hconv : ∀ d : H, Tendsto (fun n ↦ ⟪d, v n⟫) atTop
      (nhds (ℓ d)))
    (hB : ∀ n, ‖v n‖ ≤ B) (d : H) :
    |ℓ d| ≤ B * ‖d‖ := by
  have habs : Tendsto (fun n ↦ |⟪d, v n⟫|) atTop (nhds |ℓ d|) :=
    (hconv d).abs
  exact le_of_tendsto' habs fun n ↦ by
    calc
      |⟪d, v n⟫| ≤ ‖d‖ * ‖v n‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖d‖ * B := mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)
      _ = B * ‖d‖ := by ring




theorem d001452 [CompleteSpace H]
    {v : ℕ → H} {ℓ : H → ℝ} {B : ℝ}
    (hconv : ∀ d : H, Tendsto (fun n ↦ ⟪d, v n⟫) atTop
      (nhds (ℓ d)))
    (hB : ∀ n, ‖v n‖ ≤ B) :
    ∃ w : H, ∀ d : H,
      Tendsto (fun n ↦ ⟪d, v n⟫) atTop (nhds ⟪d, w⟫) := by
  have hlin := _root_.GD.N0230.N0711.d001450 hconv
  have hbound := _root_.GD.N0230.N0711.d001451 hconv hB
  set φ : H →L[ℝ] ℝ :=
    LinearMap.mkContinuous (IsLinearMap.mk' ℓ hlin) B (fun x ↦ by
      rw [IsLinearMap.mk'_apply]
      simpa [Real.norm_eq_abs] using hbound x) with hφ
  refine ⟨(InnerProductSpace.toDual ℝ H).symm φ, fun d ↦ ?_⟩
  have hpair : ⟪d, (InnerProductSpace.toDual ℝ H).symm φ⟫ = ℓ d := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  rw [hpair]
  exact hconv d






theorem d001453 [CompleteSpace H]
    (ψ : Θ → H) (m h₀ : H)
    {μ : Measure Θ} {K : ℕ → Set Θ} {c B : ℝ}
    (hu0 : h₀ ≠ 0) (hc : 0 < c)
    (hfloor : ∀ θ, c ≤ ⟪h₀, ψ θ - m⟫)
    (hint : ∀ n, IntegrableOn (fun θ ↦ ψ θ - m) (K n) μ)
    (hM : ∀ n, (∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) ≠ 0)
    (hB : ∀ n, ‖_root_.GD.N0230.N0568.d001435 ψ m h₀ μ (K n)‖ ≤ B)
    {ℓ : H → ℝ}
    (hconv : ∀ d : H, Tendsto
      (fun n ↦ ⟪d, _root_.GD.N0230.N0568.d001435 ψ m h₀ μ (K n)⟫)
      atTop (nhds (ℓ d))) :
    ∃ w : H, ⟪h₀, w⟫ = 1 ∧
      ∀ η : ℝ, 0 < η → η < 4 * c / ‖h₀‖ ^ 2 →
        Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
          (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
          ∃ p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
            ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖p - ψ θ‖ ^ 2 := by
  obtain ⟨w, hw⟩ := _root_.GD.N0230.N0711.d001452 hconv hB
  have hone : (fun n ↦
      ⟪h₀, _root_.GD.N0230.N0568.d001435 ψ m h₀ μ (K n)⟫) =
      fun _ ↦ (1 : ℝ) :=
    funext fun n ↦
      _root_.GD.N0230.N0568.d001437 ψ m h₀ (hint n) (hM n)
  have hpair := hw h₀
  rw [hone] at hpair
  have hw1 : ⟪h₀, w⟫ = 1 :=
    tendsto_nhds_unique hpair tendsto_const_nhds
  refine ⟨w, hw1, fun η hη hbudget ↦ ?_⟩
  have hbudget' : η < 4 * 1 * c / ‖h₀‖ ^ 2 := by
    have h4 : 4 * (1 : ℝ) * c / ‖h₀‖ ^ 2 = 4 * c / ‖h₀‖ ^ 2 := by
      ring
    rw [h4]
    exact hbudget
  exact _root_.GD.N0230.N0574.d001414 ψ m w hu0 hfloor hc
    hw1.ge one_pos hη hbudget'

end

end N0711
end N0230
end GD

#print axioms _root_.GD.N0230.N0711.d001450
#print axioms _root_.GD.N0230.N0711.d001451
#print axioms _root_.GD.N0230.N0711.d001452
#print axioms _root_.GD.N0230.N0711.d001453
