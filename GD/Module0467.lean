import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0768
noncomputable section
variable {X : Type*} [MeasurableSpace X]

theorem d007219 {F : ℂ → X → ℂ} {D : X → ℂ} {z : ℂ}
    (hm : ∀ w : ℂ, Measurable (F w))
    (hd : ∀ x : X, HasDerivAt (fun w => F w x) (D x) z) : Measurable D := by
  let step : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1)
  have hstep0 : Tendsto step atTop (𝓝 (0 : ℂ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hn (n : ℕ) : step n ≠ 0 := by
    apply one_div_ne_zero
    exact Nat.cast_add_one_ne_zero n
  have hstep : Tendsto step atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hstep0, Filter.Eventually.of_forall hn⟩
  apply measurable_of_tendsto_metrizable
    (f := fun n x => (step n)⁻¹ • (F (z + step n) x - F z x))
    (fun n => ((hm (z + step n)).sub (hm z)).const_smul ((step n)⁻¹))
  apply tendsto_pi_nhds.mpr
  intro x
  exact (hd x).tendsto_slope_zero.comp hstep

end
end GD.N0106.N0428.N0768
#print axioms _root_.GD.N0106.N0428.N0768.d007219
