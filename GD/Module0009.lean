import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure














open Filter MeasureTheory Set

namespace GD
namespace N0230
namespace N0588

noncomputable section

variable {X E : Type*}
  [TopologicalSpace X] [NormalSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem d000066
    (mu : Measure X) [IsFiniteMeasure mu] [mu.WeaklyRegular]
    {p : ENNReal} (hpTop : p ≠ ⊤) (hpZero : p ≠ 0)
    (d : X → E) (hd : MemLp d p mu)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ h : X → E, Continuous h ∧
      mu.real {x | ε ≤ dist (d x) (h x)} < δ := by
  classical
  have happ : ∀ n : ℕ,
      ∃ g : BoundedContinuousFunction X E,
        eLpNorm (d - (g : X → E)) p mu ≤
            (n : ENNReal)⁻¹ ∧
          MemLp (g : X → E) p mu := by
    intro n
    exact hd.exists_boundedContinuous_eLpNorm_sub_le hpTop (by simp)
  choose g hnorm hg using happ
  have herror : Tendsto
      (fun n ↦ eLpNorm (d - (g n : X → E)) p mu)
      atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero
      (Filter.Eventually.of_forall fun n ↦ bot_le)
      (Filter.Eventually.of_forall hnorm)
  have hresidual : TendstoInMeasure mu
      (fun n x ↦ d x - g n x) atTop (fun _ ↦ (0 : E)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm hpZero
    · intro n
      exact hd.aestronglyMeasurable.sub (hg n).aestronglyMeasurable
    · exact aestronglyMeasurable_const
    · have heq :
          (fun n ↦ eLpNorm
            ((fun x ↦ d x - g n x) - (fun _ ↦ (0 : E))) p mu) =
          (fun n ↦ eLpNorm (d - (g n : X → E)) p mu) := by
        funext n
        congr 1
        funext x
        simp
      rw [heq]
      exact herror
  have hmeasure :=
    (tendstoInMeasure_iff_measureReal_dist.mp hresidual) ε hε
  rw [Metric.tendsto_atTop] at hmeasure
  obtain ⟨N, hN⟩ := hmeasure δ hδ
  refine ⟨(g N : X → E), (g N).continuous, ?_⟩
  have hsmall := hN N le_rfl
  have hsmall' :
      |mu.real {x | ε ≤ ‖d x - (g N : X → E) x‖}| < δ := by
    simpa only [dist_zero_right, dist_eq_norm, sub_zero, Real.dist_eq,
      Real.norm_eq_abs]
      using hsmall
  simpa only [dist_eq_norm, abs_of_nonneg measureReal_nonneg] using hsmall'

end

end N0588
end N0230
end GD

#print axioms _root_.GD.N0230.N0588.d000066
