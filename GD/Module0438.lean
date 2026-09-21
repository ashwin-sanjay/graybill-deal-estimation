import GD.Module0396
import Mathlib.MeasureTheory.Integral.Prod








set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GD.N0106.N0428.N0770.N1701
noncomputable section

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {ν : Measure Ω} [IsFiniteMeasure ν]



theorem d006761 {w : Ω → ι → ℝ} (i : ι)
    (hw : Measurable (fun ω => w ω i))
    (hb : ∀ᵐ ω ∂ν, w ω i ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => (w ω i) ^ 2) ν := by
  exact (memLp_of_bounded hb hw.aestronglyMeasurable 2).integrable_sq



theorem d006762 {w : Ω → ι → ℝ} (v : ι → ℝ≥0)
    (hw : ∀ i, Measurable (fun ω => w ω i))
    (hb : ∀ i, ∀ᵐ ω ∂ν, w ω i ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => ∑ i, (w ω i) ^ 2 * (v i : ℝ)) ν := by
  apply integrable_finsetSum
  intro i _
  exact (_root_.GD.N0106.N0428.N0770.N1701.d006761 i (hw i) (hb i)).mul_const (v i : ℝ)


theorem d006763 (μ : ℝ) {w : Ω → ι → ℝ}
    (hw : ∀ i, Measurable (fun ω => w ω i)) :
    Measurable (fun z : Ω × (ι → ℝ) => ((∑ i, w z.1 i * z.2 i) - μ) ^ 2) := by
  have hsum : Measurable (fun z : Ω × (ι → ℝ) => ∑ i, w z.1 i * z.2 i) :=
    Finset.measurable_sum _ fun i _ =>
      ((hw i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)
  exact (hsum.sub measurable_const).pow_const 2



theorem d006764 (μ : ℝ) (v : ι → ℝ≥0) (w : Ω → ι → ℝ)
    (hs : ∀ᵐ ω ∂ν, ∑ i, w ω i = 1) :
    ∀ᵐ ω ∂ν,
      (∫ y : ι → ℝ, ((∑ i, w ω i * y i) - μ) ^ 2
        ∂Measure.pi (fun i => gaussianReal μ (v i))) =
          ∑ i, (w ω i) ^ 2 * (v i : ℝ) := by
  exact hs.mono fun ω hω =>
    _root_.GD.N0106.N0428.N0770.N1700.d006096 μ (w ω) v hω



theorem d006765 (μ : ℝ) (v : ι → ℝ≥0) (w : Ω → ι → ℝ)
    (hw : ∀ i, Measurable (fun ω => w ω i))
    (hb : ∀ i, ∀ᵐ ω ∂ν, w ω i ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∀ᵐ ω ∂ν, ∑ i, w ω i = 1) :
    Integrable (fun z : Ω × (ι → ℝ) => ((∑ i, w z.1 i * z.2 i) - μ) ^ 2)
      (ν.prod (Measure.pi (fun i => gaussianReal μ (v i)))) := by
  apply (integrable_prod_iff (_root_.GD.N0106.N0428.N0770.N1701.d006763 μ hw).aestronglyMeasurable).mpr
  constructor
  · exact hs.mono fun ω hω =>
      _root_.GD.N0106.N0428.N0770.N1700.d006095 μ (w ω) v hω
  · apply (_root_.GD.N0106.N0428.N0770.N1701.d006762 v hw hb).congr
    filter_upwards [_root_.GD.N0106.N0428.N0770.N1701.d006764 μ v w hs] with ω hω
    simpa only [Real.norm_eq_abs, abs_sq] using hω.symm




theorem d006766 (μ : ℝ) (v : ι → ℝ≥0) (w : Ω → ι → ℝ)
    (hw : ∀ i, Measurable (fun ω => w ω i))
    (hb : ∀ i, ∀ᵐ ω ∂ν, w ω i ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∀ᵐ ω ∂ν, ∑ i, w ω i = 1) :
    (∫ z : Ω × (ι → ℝ), ((∑ i, w z.1 i * z.2 i) - μ) ^ 2
      ∂ν.prod (Measure.pi (fun i => gaussianReal μ (v i)))) =
        ∑ i, (v i : ℝ) * (∫ ω, (w ω i) ^ 2 ∂ν) := by
  rw [integral_prod _ (_root_.GD.N0106.N0428.N0770.N1701.d006765 μ v w hw hb hs)]
  calc
    _ = ∫ ω, (∑ i, (w ω i) ^ 2 * (v i : ℝ)) ∂ν :=
      integral_congr_ae (_root_.GD.N0106.N0428.N0770.N1701.d006764 μ v w hs)
    _ = _ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_mul_const, mul_comm]
      · intro i _
        exact (_root_.GD.N0106.N0428.N0770.N1701.d006761 i (hw i) (hb i)).mul_const (v i : ℝ)

end
end GD.N0106.N0428.N0770.N1701

#print axioms _root_.GD.N0106.N0428.N0770.N1701.d006761
#print axioms _root_.GD.N0106.N0428.N0770.N1701.d006762
#print axioms _root_.GD.N0106.N0428.N0770.N1701.d006763
#print axioms _root_.GD.N0106.N0428.N0770.N1701.d006764
#print axioms _root_.GD.N0106.N0428.N0770.N1701.d006765
#print axioms _root_.GD.N0106.N0428.N0770.N1701.d006766
