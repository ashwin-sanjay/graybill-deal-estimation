import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Metric Topology
namespace GD.N0106.N0428.N0771
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}



theorem d029138 {F F' : ℂ → X → ℂ} {U : Set ℂ} {M : ℂ → ℝ} {W : X → ℝ}
    (hU : IsOpen U) (hM : ContinuousOn M U)
    (hW : Integrable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x)
    (hm : ∀ z ∈ U, AEStronglyMeasurable (F z) μ)
    (hm' : ∀ z ∈ U, AEStronglyMeasurable (F' z) μ)
    (hF : ∀ᵐ x ∂μ, ∀ z ∈ U,
      HasDerivAt (fun w => F w x) (F' z x) z ∧ ‖F z x‖ ≤ M z * W x)
    {z : ℂ} (hz : z ∈ U) :
    Integrable (F' z) μ ∧
      HasDerivAt (fun w => ∫ x, F w x ∂μ) (∫ x, F' z x ∂μ) z := by
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  obtain ⟨C, hC⟩ := (isCompact_closedBall z R).exists_bound_of_continuousOn (hM.mono hRU)
  have hs : closedBall z r ⊆ U := by
    intro w hw
    apply hRU
    exact closedBall_subset_closedBall (by dsimp [r]; linarith) hw
  have hsub {w : ℂ} (hw : w ∈ closedBall z r) : closedBall w r ⊆ closedBall z R := by
    intro v hv
    have h1 : dist v w ≤ r := mem_closedBall.mp hv
    have h2 : dist w z ≤ r := mem_closedBall.mp hw
    apply mem_closedBall.mpr
    calc dist v z ≤ dist v w + dist w z := dist_triangle _ _ _
      _ ≤ R := by dsimp [r] at *; linarith
  have hb : ∀ᵐ x ∂μ, ∀ w ∈ closedBall z r, ‖F' w x‖ ≤ (C / r) * W x := by
    filter_upwards [hF, hW0] with x hx hx0
    intro w hw
    have hd : DifferentiableOn ℂ (fun v => F v x) U :=
      fun v hv => (hx v hv).1.differentiableAt.differentiableWithinAt
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hd.diffContOnCl_ball ((hsub hw).trans hRU))
      (fun v hv => ((hx v (hRU (hsub hw (sphere_subset_closedBall hv)))).2).trans
        (mul_le_mul_of_nonneg_right
          ((le_abs_self (M v)).trans (hC v (hsub hw (sphere_subset_closedBall hv)))) hx0))
    rw [(hx w (hs hw)).1.deriv] at hc
    simpa only [mul_div_right_comm] using hc
  have hi : Integrable (F z) μ := (hW.const_mul (M z)).mono' (hm z hz)
    (hF.mono fun x hx => (hx z hz).2)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds z hr)
    ((show ∀ᶠ w in 𝓝 z, w ∈ U from hU.mem_nhds hz).mono fun w hw => hm w hw) hi (hm' z hz)
    hb (hW.const_mul (C / r))
    (hF.mono fun x hx w hw => (hx w (hs hw)).1)

end
end GD.N0106.N0428.N0771
#print axioms _root_.GD.N0106.N0428.N0771.d029138
