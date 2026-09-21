import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import GD.Module0114


































open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0568

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0574

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} [MeasurableSpace Θ]
variable (ψ : Θ → H) (m h₀ : H)


def d001434 (θ : Θ) : ℝ := ⟪h₀, ψ θ - m⟫


def d001435 (μ : Measure Θ) (K : Set Θ) : H :=
  (∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ)⁻¹ •
    ∫ θ in K, (ψ θ - m) ∂μ


theorem d001436 [CompleteSpace H]
    {μ : Measure Θ} {K : Set Θ}
    (hint : IntegrableOn (fun θ ↦ ψ θ - m) K μ) :
    ∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ =
      ⟪h₀, ∫ θ in K, (ψ θ - m) ∂μ⟫ := by
  have h := (innerSL ℝ h₀).integral_comp_comm hint
  simpa [_root_.GD.N0230.N0568.d001434, innerSL_apply_apply] using h


theorem d001437 [CompleteSpace H]
    {μ : Measure Θ} {K : Set Θ}
    (hint : IntegrableOn (fun θ ↦ ψ θ - m) K μ)
    (hM : (∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) ≠ 0) :
    ⟪h₀, _root_.GD.N0230.N0568.d001435 ψ m h₀ μ K⟫ = 1 := by
  unfold _root_.GD.N0230.N0568.d001435
  rw [real_inner_smul_right,
    ← _root_.GD.N0230.N0568.d001436 ψ m h₀ hint]
  exact inv_mul_cancel₀ hM


theorem d001438
    {μ : Measure Θ} {K : Set Θ} {κ : ℝ} (hκ : 0 < κ)
    (hangle : ∀ θ, κ * ‖ψ θ - m‖ ≤ _root_.GD.N0230.N0568.d001434 ψ m h₀ θ)
    (hnint : IntegrableOn (fun θ ↦ ‖ψ θ - m‖) K μ)
    (hgint : IntegrableOn (_root_.GD.N0230.N0568.d001434 ψ m h₀) K μ)
    (hMpos : 0 < ∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) :
    ‖_root_.GD.N0230.N0568.d001435 ψ m h₀ μ K‖ ≤ 1 / κ := by
  unfold _root_.GD.N0230.N0568.d001435
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hMpos.le)]
  have h1 : ‖∫ θ in K, (ψ θ - m) ∂μ‖ ≤
      ∫ θ in K, ‖ψ θ - m‖ ∂μ :=
    norm_integral_le_integral_norm _
  have h2 : (∫ θ in K, ‖ψ θ - m‖ ∂μ) ≤
      (∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) / κ := by
    have hmono := integral_mono hnint (hgint.div_const κ)
      (fun θ ↦ by
        have := hangle θ
        rw [le_div_iff₀ hκ]
        linarith)
    calc
      (∫ θ in K, ‖ψ θ - m‖ ∂μ) ≤
          ∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ / κ ∂μ := hmono
      _ = (∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) / κ :=
        integral_div κ _
  calc
    (∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ)⁻¹ *
        ‖∫ θ in K, (ψ θ - m) ∂μ‖ ≤
        (∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ)⁻¹ *
          ((∫ θ in K, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) / κ) :=
      mul_le_mul_of_nonneg_left (h1.trans h2)
        (inv_nonneg.mpr hMpos.le)
    _ = 1 / κ := by
      field_simp





theorem d001439 [CompleteSpace H]
    {μ : Measure Θ} {K : ℕ → Set Θ} {c : ℝ} {w : H}
    (hu0 : h₀ ≠ 0) (hc : 0 < c)
    (hfloor : ∀ θ, c ≤ ⟪h₀, ψ θ - m⟫)
    (hint : ∀ n, IntegrableOn (fun θ ↦ ψ θ - m) (K n) μ)
    (hM : ∀ n, (∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) ≠ 0)
    (hlim : Tendsto (fun n ↦ _root_.GD.N0230.N0568.d001435 ψ m h₀ μ (K n))
      atTop (nhds w)) :
    ⟪h₀, w⟫ = 1 ∧ w ≠ 0 ∧
      ∀ η : ℝ, 0 < η → η < 4 * c / ‖h₀‖ ^ 2 →
        Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
          (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
          ∃ p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
            ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖p - ψ θ‖ ^ 2 := by
  have hpair : Tendsto
      (fun n ↦ ⟪h₀, _root_.GD.N0230.N0568.d001435 ψ m h₀ μ (K n)⟫)
      atTop (nhds ⟪h₀, w⟫) :=
    Tendsto.inner tendsto_const_nhds hlim
  have hconst :
      (fun n ↦ ⟪h₀, _root_.GD.N0230.N0568.d001435 ψ m h₀ μ (K n)⟫) =
        fun _ ↦ (1 : ℝ) :=
    funext fun n ↦
      _root_.GD.N0230.N0568.d001437 ψ m h₀ (hint n) (hM n)
  rw [hconst] at hpair
  have hw1 : ⟪h₀, w⟫ = 1 :=
    tendsto_nhds_unique hpair tendsto_const_nhds
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right] at hw1
    norm_num at hw1
  refine ⟨hw1, hwne, fun η hη hbudget ↦ ?_⟩
  have hbudget' : η < 4 * 1 * c / ‖h₀‖ ^ 2 := by
    have h4 : 4 * (1 : ℝ) * c / ‖h₀‖ ^ 2 = 4 * c / ‖h₀‖ ^ 2 := by
      ring
    rw [h4]
    exact hbudget
  exact _root_.GD.N0230.N0574.d001414 ψ m w hu0 hfloor hc
    hw1.ge one_pos hη hbudget'




theorem d001440
    {μ : Measure Θ} {K : ℕ → Set Θ}
    (hdiv : Tendsto (fun n ↦
      (∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) /
        (μ (K n)).toReal) atTop atTop) :
    Tendsto (fun n ↦
      (∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ)⁻¹ *
        (μ (K n)).toReal) atTop (nhds 0) := by
  have h := hdiv.inv_tendsto_atTop
  have heq : (fun n ↦
      ((∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ) /
        (μ (K n)).toReal)⁻¹) = fun n ↦
      (∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ)⁻¹ *
        (μ (K n)).toReal := by
    funext n
    rw [inv_div, div_eq_mul_inv, mul_comm]
  rw [← heq]
  exact h

end

end N0568
end N0230
end GD

#print axioms _root_.GD.N0230.N0568.d001436
#print axioms _root_.GD.N0230.N0568.d001437
#print axioms _root_.GD.N0230.N0568.d001438
#print axioms _root_.GD.N0230.N0568.d001439
#print axioms _root_.GD.N0230.N0568.d001440
