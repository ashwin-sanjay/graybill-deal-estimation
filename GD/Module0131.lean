import GD.Module0130
























open Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0713

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]




theorem d001521 {w : H} {wN : ℕ → H}
    (hweak : ∀ v : H,
      Tendsto (fun n ↦ ⟪v, wN n⟫) atTop (nhds ⟪v, w⟫))
    (hnorm : Tendsto (fun n ↦ ‖wN n‖) atTop (nhds ‖w‖)) :
    Tendsto wN atTop (nhds w) := by
  have h1 : Tendsto (fun n ↦ ‖wN n‖ ^ 2) atTop
      (nhds (‖w‖ ^ 2)) := by
    have := hnorm.mul hnorm
    simpa [sq] using this
  have h2 : Tendsto (fun n ↦ ⟪w, wN n⟫) atTop
      (nhds (‖w‖ ^ 2)) := by
    have := hweak w
    rwa [real_inner_self_eq_norm_sq] at this
  have h3 : Tendsto
      (fun n ↦ ‖wN n‖ ^ 2 - 2 * ⟪w, wN n⟫ + ‖w‖ ^ 2) atTop
      (nhds (‖w‖ ^ 2 - 2 * ‖w‖ ^ 2 + ‖w‖ ^ 2)) :=
    (h1.sub (h2.const_mul 2)).add tendsto_const_nhds
  have heq : ∀ n, ‖wN n‖ ^ 2 - 2 * ⟪w, wN n⟫ + ‖w‖ ^ 2 =
      ‖wN n - w‖ ^ 2 := by
    intro n
    rw [norm_sub_sq_real, real_inner_comm]
  have h4 : Tendsto (fun n ↦ ‖wN n - w‖ ^ 2) atTop (nhds 0) := by
    have h0 : ‖w‖ ^ 2 - 2 * ‖w‖ ^ 2 + ‖w‖ ^ 2 = 0 := by ring
    rw [h0] at h3
    exact h3.congr heq
  have h5 : Tendsto (fun n ↦ ‖wN n - w‖) atTop (nhds 0) := by
    have hcomp := (Real.continuous_sqrt.tendsto 0).comp h4
    simp only [Function.comp_def, Real.sqrt_zero] at hcomp
    exact hcomp.congr fun n ↦ Real.sqrt_sq (norm_nonneg _)
  rw [tendsto_iff_dist_tendsto_zero]
  exact h5.congr fun n ↦ (dist_eq_norm _ _).symm





theorem d001522 {w : H} {wN : ℕ → H}
    (hnorm : Tendsto (fun n ↦ ‖wN n‖) atTop (nhds ‖w‖))
    (hnot : ¬ Tendsto wN atTop (nhds w)) :
    ∃ v : H, ¬ Tendsto (fun n ↦ ⟪v, wN n⟫) atTop (nhds ⟪v, w⟫) := by
  by_contra hall
  push Not at hall
  exact hnot (_root_.GD.N0230.N0713.d001521 hall hnorm)

end

end N0713
end N0230
end GD

#print axioms _root_.GD.N0230.N0713.d001521
#print axioms _root_.GD.N0230.N0713.d001522
