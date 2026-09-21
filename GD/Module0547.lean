import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter
open scoped ENNReal Topology

namespace GD.N0222
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]



theorem d008136
    (l : Filter ι) [l.NeBot] (μ : Measure Ω) (ν : ι → Measure Ω)
    (g : Ω → ℝ≥0∞) (E : ι → ℝ≥0∞)
    (hretained : ∀ᶠ i in l, μ ≤ ν i)
    (hbound : ∀ᶠ i in l, (∫⁻ x, g x ∂ν i) ≤ E i)
    (hE : Tendsto E l (𝓝 0)) : (∫⁻ x, g x ∂μ) = 0 := by
  apply le_antisymm _ (zero_le)
  apply ge_of_tendsto hE
  filter_upwards [hretained, hbound] with i hμ hB
  exact (lintegral_mono' hμ le_rfl).trans hB

theorem d008137
    (l : Filter ι) [l.NeBot] (μ : Measure Ω) (ν : ι → Measure Ω)
    (g : Ω → ℝ≥0∞) (hg : AEMeasurable g μ) (E : ι → ℝ≥0∞)
    (hretained : ∀ᶠ i in l, μ ≤ ν i)
    (hbound : ∀ᶠ i in l, (∫⁻ x, g x ∂ν i) ≤ E i)
    (hE : Tendsto E l (𝓝 0)) : g =ᵐ[μ] 0 :=
  (lintegral_eq_zero_iff' hg).mp
    (_root_.GD.N0222.d008136 l μ ν g E hretained hbound hE)

theorem d008138
    (l : Filter ι) [l.NeBot] (μ : Measure Ω) [NeZero μ] (ν : ι → Measure Ω)
    (g : Ω → ℝ≥0∞) (hg : AEMeasurable g μ) (E : ι → ℝ≥0∞)
    (hpositive : ∀ᵐ x ∂μ, 0 < g x)
    (hretained : ∀ᶠ i in l, μ ≤ ν i)
    (hbound : ∀ᶠ i in l, (∫⁻ x, g x ∂ν i) ≤ E i)
    (hE : Tendsto E l (𝓝 0)) : False := by
  have hz := _root_.GD.N0222.d008137 l μ ν g hg E hretained hbound hE
  have hf : ∀ᵐ x ∂μ, False := by
    filter_upwards [hz, hpositive] with x hx hp
    exact hp.ne' hx
  exact (Eventually.exists hf).elim (fun _ h => h)



theorem d008139
    (l : Filter ι) [l.NeBot] (μ : Measure Ω) (ν : ι → Measure Ω)
    (g : Ω → ℝ) (hg : AEMeasurable g μ) (E : ι → ℝ≥0∞)
    (hnonneg : 0 ≤ᵐ[μ] g)
    (hretained : ∀ᶠ i in l, μ ≤ ν i)
    (hbound : ∀ᶠ i in l, (∫⁻ x, ENNReal.ofReal (g x) ∂ν i) ≤ E i)
    (hE : Tendsto E l (𝓝 0)) : g =ᵐ[μ] 0 := by
  have hz := _root_.GD.N0222.d008137 l μ ν _ hg.ennreal_ofReal E
    hretained hbound hE
  filter_upwards [hz, hnonneg] with x hx hn
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx) hn

theorem d008140
    (l : Filter ι) [l.NeBot] (μ : Measure Ω) [NeZero μ] (ν : ι → Measure Ω)
    (g : Ω → ℝ) (hg : AEMeasurable g μ) (E : ι → ℝ≥0∞)
    (hpositive : ∀ᵐ x ∂μ, 0 < g x)
    (hretained : ∀ᶠ i in l, μ ≤ ν i)
    (hbound : ∀ᶠ i in l, (∫⁻ x, ENNReal.ofReal (g x) ∂ν i) ≤ E i)
    (hE : Tendsto E l (𝓝 0)) : False := by
  apply _root_.GD.N0222.d008138 l μ ν _ hg.ennreal_ofReal E _ hretained hbound hE
  filter_upwards [hpositive] with x hx
  exact ENNReal.ofReal_pos.mpr hx

end
end GD.N0222

#print axioms _root_.GD.N0222.d008136
#print axioms _root_.GD.N0222.d008137
#print axioms _root_.GD.N0222.d008138
#print axioms _root_.GD.N0222.d008139
#print axioms _root_.GD.N0222.d008140
