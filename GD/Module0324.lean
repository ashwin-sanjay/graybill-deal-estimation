import Mathlib.Probability.Moments.Variance
























open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GD
namespace N0238
namespace N0756

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]


theorem d004824
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (p : ℝ) :
    (∫ ω, (X ω - p) ^ 2 ∂μ) =
      variance X μ + ((∫ ω, X ω ∂μ) - p) ^ 2 := by
  have hXint : Integrable X μ := hX.integrable one_le_two
  have hXsq : Integrable (fun ω ↦ X ω ^ 2) μ := hX.integrable_sq
  calc
    (∫ ω, (X ω - p) ^ 2 ∂μ) =
        ∫ ω, X ω ^ 2 - 2 * p * X ω + p ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ =
        (∫ ω, X ω ^ 2 ∂μ) -
          2 * p * (∫ ω, X ω ∂μ) + p ^ 2 := by
      have hsub_int :
          Integrable (fun ω ↦ X ω ^ 2 - 2 * p * X ω) μ :=
        hXsq.sub (hXint.const_mul (2 * p))
      calc
        (∫ ω, X ω ^ 2 - 2 * p * X ω + p ^ 2 ∂μ) =
            (∫ ω, X ω ^ 2 - 2 * p * X ω ∂μ) +
              ∫ _ : Ω, p ^ 2 ∂μ := by
          simpa only [Pi.add_apply] using
            integral_add hsub_int (integrable_const (μ := μ) (p ^ 2))
        _ =
            ((∫ ω, X ω ^ 2 ∂μ) -
              ∫ ω, 2 * p * X ω ∂μ) +
              ∫ _ : Ω, p ^ 2 ∂μ := by
          rw [integral_sub hXsq (hXint.const_mul (2 * p))]
        _ =
            (∫ ω, X ω ^ 2 ∂μ) -
              2 * p * (∫ ω, X ω ∂μ) + p ^ 2 := by
          rw [integral_const_mul, integral_const, probReal_univ, one_smul]
    _ = variance X μ + ((∫ ω, X ω ∂μ) - p) ^ 2 := by
      rw [variance_eq_sub hX]
      simp only [Pi.pow_apply]
      ring

section Finite

variable [Fintype ι]





theorem d004825
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (trace : ι → Ω → ℝ)
    (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ) :
    (∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ) =
      (∑ i, weight i * variance (trace i) μ) +
      ∑ i, weight i *
        ((∫ ω, trace i ω ∂μ) - target i) ^ 2 := by
  calc
    (∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ) =
        ∑ i, ∫ ω, weight i * (trace i ω - target i) ^ 2 ∂μ := by
      rw [integral_finsetSum]
      intro i hi
      exact
        ((htrace i).sub (memLp_const (target i))).integrable_sq
          |>.const_mul (weight i)
    _ = ∑ i, weight i *
        (variance (trace i) μ +
          ((∫ ω, trace i ω ∂μ) - target i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
      rw [_root_.GD.N0238.N0756.d004824
        μ (htrace i) (target i)]
    _ =
        (∑ i, weight i * variance (trace i) μ) +
        ∑ i, weight i *
          ((∫ ω, trace i ω ∂μ) - target i) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring





theorem d004826
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (trace : ι → Ω → ℝ)
    (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i) :
    (∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ) =
      ∑ i, weight i * variance (trace i) μ := by
  rw [_root_.GD.N0238.N0756.d004825
    μ weight trace target htrace]
  simp [hmatch]








theorem d004827
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (trace : ι → Ω → ℝ)
    (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin :
      ∀ᵐ ω ∂μ, δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2) :
    0 < ∑ i, weight i * variance (trace i) μ := by
  have hcost_integrable :
      Integrable
        (fun ω ↦ ∑ i, weight i * (trace i ω - target i) ^ 2) μ := by
    apply integrable_finsetSum
    intro i hi
    exact
      ((htrace i).sub (memLp_const (target i))).integrable_sq
        |>.const_mul (weight i)
  have hlower :
      δ ≤
        ∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ := by
    calc
      δ = ∫ _ : Ω, δ ∂μ := by simp
      _ ≤ ∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ :=
        integral_mono_ae (integrable_const _) hcost_integrable hmargin
  rw [_root_.GD.N0238.N0756.d004826
    μ weight trace target htrace hmatch] at hlower
  exact hδ.trans_le hlower





theorem d004828
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (trace : ι → Ω → ℝ)
    (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i)
    (hvariance : ∑ i, weight i * variance (trace i) μ = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ᵐ ω ∂μ,
      δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2 := by
  intro hmargin
  have hpos :=
    _root_.GD.N0238.N0756.d004827
      μ weight trace target htrace hmatch δ hδ hmargin
  exact (ne_of_gt hpos) hvariance

end Finite

end

end N0756
end N0238
end GD
