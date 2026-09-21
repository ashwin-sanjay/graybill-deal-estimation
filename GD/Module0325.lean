import GD.Module0324
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Support


















open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD
namespace N0238
namespace N0749

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]








theorem d004829
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Ω → ℝ) (hF : Integrable F μ)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ)
    (hF_nonneg : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hmargin : ∀ᵐ ω ∂μ, ω ∈ boundary → δ ≤ F ω) :
    δ * (μ boundary).toReal ≤ ∫ ω, F ω ∂μ := by
  let lower : Ω → ℝ := boundary.indicator (fun _ ↦ δ)
  have hlower_integrable : Integrable lower μ := by
    exact (integrable_const δ).indicator hboundary
  have hlower : ∀ᵐ ω ∂μ, lower ω ≤ F ω := by
    filter_upwards [hF_nonneg, hmargin] with ω hnonneg hboundary_margin
    by_cases hω : ω ∈ boundary
    · simpa [lower, hω] using hboundary_margin hω
    · simpa [lower, hω] using hnonneg
  have hintegral :
      (∫ ω, lower ω ∂μ) ≤ ∫ ω, F ω ∂μ :=
    integral_mono_ae hlower_integrable hF hlower
  have hlower_integral :
      (∫ ω, lower ω ∂μ) = δ * (μ boundary).toReal := by
    simp [lower, integral_indicator hboundary, measureReal_def, mul_comm]
  rwa [hlower_integral] at hintegral





theorem d004830
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Ω → ℝ) (hF : Integrable F μ)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ) (hδ : 0 < δ)
    (hF_nonneg : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hmargin : ∀ᵐ ω ∂μ, ω ∈ boundary → δ ≤ F ω)
    (hintegral : (∫ ω, F ω ∂μ) = 0) :
    μ boundary = 0 := by
  have hmass :=
    _root_.GD.N0238.N0749.d004829
      μ F hF boundary hboundary δ hF_nonneg hmargin
  rw [hintegral] at hmass
  have hreal_nonneg : 0 ≤ (μ boundary).toReal :=
    ENNReal.toReal_nonneg
  have hreal_zero : (μ boundary).toReal = 0 := by
    nlinarith
  have hcases :
      μ boundary = 0 ∨ μ boundary = ∞ :=
    (ENNReal.toReal_eq_zero_iff (μ boundary)).mp hreal_zero
  exact hcases.resolve_right (measure_ne_top μ boundary)







theorem d004831
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℝ) (hT : MemLp T 2 μ) :
    (∫ z : Ω × Ω, (T z.1 - T z.2) ^ 2 ∂(μ.prod μ)) =
      2 * variance T μ := by
  let Δ : Ω × Ω → ℝ := fun z ↦ T z.1 - T z.2
  have hΔ : MemLp Δ 2 (μ.prod μ) :=
    (hT.comp_fst μ).sub (hT.comp_snd μ)
  have hTint : Integrable T μ := hT.integrable one_le_two
  have hfst :
      (∫ z : Ω × Ω, T z.1 ∂(μ.prod μ)) =
        ∫ x, T x ∂μ := by
    rw [integral_prod _ (hTint.comp_fst μ)]
    simp
  have hsnd :
      (∫ z : Ω × Ω, T z.2 ∂(μ.prod μ)) =
        ∫ x, T x ∂μ := by
    rw [integral_prod _ (hTint.comp_snd μ)]
    simp
  have hmean : (∫ z, Δ z ∂(μ.prod μ)) = 0 := by
    unfold Δ
    rw [integral_sub (hTint.comp_fst μ) (hTint.comp_snd μ)]
    rw [hfst, hsnd, sub_self]
  have hvariance :
      variance Δ (μ.prod μ) = 2 * variance T μ := by
    have hadd :=
      ProbabilityTheory.variance_add_prod hT hT.neg
    calc
      variance Δ (μ.prod μ) =
          variance (fun z : Ω × Ω ↦
            T z.1 + (fun x ↦ -T x) z.2) (μ.prod μ) := by
        congr 1
      _ =
          variance T μ + variance (fun x ↦ -T x) μ := hadd
      _ = 2 * variance T μ := by
        change variance T μ + variance (-T) μ =
          2 * variance T μ
        rw [ProbabilityTheory.variance_neg]
        ring
  have hdecomp :=
    _root_.GD.N0238.N0756.d004824
      (μ.prod μ) hΔ 0
  change
    (∫ z, (Δ z - 0) ^ 2 ∂(μ.prod μ)) =
      variance Δ (μ.prod μ) +
        ((∫ z, Δ z ∂(μ.prod μ)) - 0) ^ 2 at hdecomp
  rw [hmean] at hdecomp
  norm_num at hdecomp
  calc
    (∫ z : Ω × Ω, (T z.1 - T z.2) ^ 2 ∂(μ.prod μ)) =
        variance Δ (μ.prod μ) := by simpa [Δ] using hdecomp
    _ = 2 * variance T μ := hvariance

section Finite

variable [Fintype ι]



def d004832
    (μ : Measure Ω) (weight : ι → ℝ)
    (trace : ι → Ω → ℝ) : ℝ :=
  2 * ∑ i, weight i * variance (trace i) μ



def d004833
    (μ : Measure Ω) (weight : ι → ℝ)
    (trace : ι → Ω → ℝ) : ℝ :=
  ∫ z : Ω × Ω,
    ∑ i, weight i * (trace i z.1 - trace i z.2) ^ 2
      ∂(μ.prod μ)



def d004834
    (μ : Measure Ω) (weight : ι → ℝ)
    (trace : ι → Ω → ℝ) (target : ι → ℝ) : ℝ :=
  ∑ i, weight i *
    ((∫ ω, trace i ω ∂μ) - target i) ^ 2



theorem d004835
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ) (target : ι → ℝ) (ω : Ω) :
    0 ≤ ∑ i, weight i * (trace i ω - target i) ^ 2 := by
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hweight i) (sq_nonneg (trace i ω - target i))





theorem d004836
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (trace : ι → Ω → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ) :
    _root_.GD.N0238.N0749.d004833 μ weight trace =
      _root_.GD.N0238.N0749.d004832 μ weight trace := by
  unfold _root_.GD.N0238.N0749.d004833 _root_.GD.N0238.N0749.d004832
  calc
    (∫ z : Ω × Ω,
        ∑ i, weight i * (trace i z.1 - trace i z.2) ^ 2
          ∂(μ.prod μ)) =
        ∑ i,
          ∫ z : Ω × Ω,
            weight i * (trace i z.1 - trace i z.2) ^ 2
              ∂(μ.prod μ) := by
      rw [integral_finsetSum]
      intro i hi
      exact
        (((htrace i).comp_fst μ).sub ((htrace i).comp_snd μ))
          |>.integrable_sq
          |>.const_mul (weight i)
    _ =
        ∑ i, weight i * (2 * variance (trace i) μ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
      rw [_root_.GD.N0238.N0749.d004831 μ (trace i) (htrace i)]
    _ = ∑ i, 2 * (weight i * variance (trace i) μ) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 2 * ∑ i, weight i * variance (trace i) μ := by
      rw [Finset.mul_sum]









theorem d004837
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ) (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ)
    (hmargin :
      ∀ᵐ ω ∂μ, ω ∈ boundary →
        δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2) :
    δ * (μ boundary).toReal ≤
      _root_.GD.N0238.N0749.d004832 μ weight trace / 2 +
        _root_.GD.N0238.N0749.d004834 μ weight trace target := by
  let F : Ω → ℝ :=
    fun ω ↦ ∑ i, weight i * (trace i ω - target i) ^ 2
  have hF_integrable : Integrable F μ := by
    apply integrable_finsetSum
    intro i hi
    exact
      ((htrace i).sub (memLp_const (target i))).integrable_sq
        |>.const_mul (weight i)
  have hF_nonneg : ∀ᵐ ω ∂μ, 0 ≤ F ω :=
    Filter.Eventually.of_forall fun ω ↦
      _root_.GD.N0238.N0749.d004835
        weight hweight trace target ω
  have hmass :
      δ * (μ boundary).toReal ≤ ∫ ω, F ω ∂μ :=
    _root_.GD.N0238.N0749.d004829
      μ F hF_integrable boundary hboundary δ hF_nonneg hmargin
  have hdecomp :
      (∫ ω, F ω ∂μ) =
        (∑ i, weight i * variance (trace i) μ) +
          _root_.GD.N0238.N0749.d004834 μ weight trace target := by
    exact
      _root_.GD.N0238.N0756.d004825
        μ weight trace target htrace
  rw [hdecomp] at hmass
  unfold _root_.GD.N0238.N0749.d004832
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hmass





theorem d004838
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ) (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ)
    (hmargin :
      ∀ᵐ ω ∂μ, ω ∈ boundary →
        δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2) :
    δ * (μ boundary).toReal ≤
      _root_.GD.N0238.N0749.d004833 μ weight trace / 2 +
        _root_.GD.N0238.N0749.d004834 μ weight trace target := by
  have hbound :=
    _root_.GD.N0238.N0749.d004837
      μ weight hweight trace target htrace boundary hboundary δ hmargin
  have hpair :=
    _root_.GD.N0238.N0749.d004836
      μ weight trace htrace
  rwa [hpair]








theorem d004839
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ) (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ)
    (hmargin :
      ∀ᵐ ω ∂μ, ω ∈ boundary →
        δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2) :
    δ * (μ boundary).toReal ≤
        ∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ ∧
    (∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ) =
        ∑ i, weight i * variance (trace i) μ ∧
    (∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ) =
        _root_.GD.N0238.N0749.d004832 μ weight trace / 2 := by
  let F : Ω → ℝ :=
    fun ω ↦ ∑ i, weight i * (trace i ω - target i) ^ 2
  have hF_integrable : Integrable F μ := by
    apply integrable_finsetSum
    intro i hi
    exact
      ((htrace i).sub (memLp_const (target i))).integrable_sq
        |>.const_mul (weight i)
  have hF_nonneg : ∀ᵐ ω ∂μ, 0 ≤ F ω :=
    Filter.Eventually.of_forall fun ω ↦
      _root_.GD.N0238.N0749.d004835
        weight hweight trace target ω
  have hmass :
      δ * (μ boundary).toReal ≤ ∫ ω, F ω ∂μ :=
    _root_.GD.N0238.N0749.d004829
      μ F hF_integrable boundary hboundary δ hF_nonneg hmargin
  have hvariance :
      (∫ ω, F ω ∂μ) =
        ∑ i, weight i * variance (trace i) μ := by
    exact
      _root_.GD.N0238.N0756.d004826
        μ weight trace target htrace hmatch
  refine ⟨hmass, hvariance, ?_⟩
  rw [hvariance]
  unfold _root_.GD.N0238.N0749.d004832
  ring





theorem d004840
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ) (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ)
    (hmargin :
      ∀ᵐ ω ∂μ, ω ∈ boundary →
        δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2) :
    δ * (μ boundary).toReal ≤
        _root_.GD.N0238.N0749.d004833 μ weight trace / 2 ∧
    (∫ ω, ∑ i, weight i * (trace i ω - target i) ^ 2 ∂μ) =
        _root_.GD.N0238.N0749.d004833 μ weight trace / 2 := by
  obtain ⟨hmass, hvariance, hhalf⟩ :=
    _root_.GD.N0238.N0749.d004839
      μ weight hweight trace target htrace hmatch
      boundary hboundary δ hmargin
  have hpair :=
    _root_.GD.N0238.N0749.d004836
      μ weight trace htrace
  constructor
  · calc
      δ * (μ boundary).toReal ≤
          ∫ ω, ∑ i, weight i *
            (trace i ω - target i) ^ 2 ∂μ := hmass
      _ = _root_.GD.N0238.N0749.d004832 μ weight trace / 2 := hhalf
      _ = _root_.GD.N0238.N0749.d004833 μ weight trace / 2 := by
        rw [hpair]
  · calc
      (∫ ω, ∑ i, weight i *
          (trace i ω - target i) ^ 2 ∂μ) =
          _root_.GD.N0238.N0749.d004832 μ weight trace / 2 := hhalf
      _ = _root_.GD.N0238.N0749.d004833 μ weight trace / 2 := by
        rw [hpair]





theorem d004841
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ) (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin :
      ∀ᵐ ω ∂μ, ω ∈ boundary →
        δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2)
    (hdispersion :
      _root_.GD.N0238.N0749.d004832 μ weight trace = 0) :
    μ boundary = 0 := by
  obtain ⟨hmass, hvariance, hhalf⟩ :=
    _root_.GD.N0238.N0749.d004839
      μ weight hweight trace target htrace hmatch
      boundary hboundary δ hmargin
  rw [hdispersion, zero_div] at hhalf
  have hmass_zero :
      δ * (μ boundary).toReal ≤ 0 := by
    rw [← hhalf]
    exact hmass
  have hreal_nonneg : 0 ≤ (μ boundary).toReal :=
    ENNReal.toReal_nonneg
  have hreal_zero : (μ boundary).toReal = 0 := by
    nlinarith
  have hcases :
      μ boundary = 0 ∨ μ boundary = ∞ :=
    (ENNReal.toReal_eq_zero_iff (μ boundary)).mp hreal_zero
  exact hcases.resolve_right (measure_ne_top μ boundary)





theorem d004842
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ) (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i)
    (boundary : Set Ω) (hboundary : MeasurableSet boundary)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin :
      ∀ᵐ ω ∂μ, ω ∈ boundary →
        δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2)
    (hpair :
      _root_.GD.N0238.N0749.d004833 μ weight trace = 0) :
    μ boundary = 0 := by
  have hpair_eq :=
    _root_.GD.N0238.N0749.d004836
      μ weight trace htrace
  apply _root_.GD.N0238.N0749.d004841
    μ weight hweight trace target htrace hmatch
    boundary hboundary δ hδ hmargin
  rw [← hpair_eq]
  exact hpair

end Finite

section Support

variable [TopologicalSpace Ω] [BorelSpace Ω]






theorem d004843
    (μ : Measure Ω)
    (F : Ω → ℝ) (hF_continuous : Continuous F)
    (hF_integrable : Integrable F μ)
    (hF_nonneg : ∀ ω, 0 ≤ F ω)
    (hintegral : (∫ ω, F ω ∂μ) = 0) :
    μ.support ⊆ {ω | F ω = 0} := by
  have hae_zero : ∀ᵐ ω ∂μ, F ω = 0 :=
    (integral_eq_zero_iff_of_nonneg
      hF_nonneg hF_integrable).mp hintegral
  apply Measure.support_subset_of_isClosed
  · exact isClosed_eq hF_continuous continuous_const
  · exact hae_zero






theorem d004844
    (μ : Measure Ω)
    (F : Ω → ℝ) (hF_continuous : Continuous F)
    (hF_integrable : Integrable F μ)
    (hF_nonneg : ∀ ω, 0 ≤ F ω)
    (hintegral : (∫ ω, F ω ∂μ) = 0)
    (boundary : Set Ω)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ ω ∈ boundary, δ ≤ F ω) :
    μ.support ∩ boundary = ∅ := by
  have hsupp :=
    _root_.GD.N0238.N0749.d004843
      μ F hF_continuous hF_integrable hF_nonneg hintegral
  rw [eq_empty_iff_forall_notMem]
  intro ω hω
  have hzero : F ω = 0 := hsupp hω.1
  have hlower := hmargin ω hω.2
  rw [hzero] at hlower
  linarith

section FiniteSupport

variable [Fintype ι]









theorem d004845
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (trace : ι → Ω → ℝ)
    (htrace_continuous : ∀ i, Continuous (trace i))
    (target : ι → ℝ)
    (htrace : ∀ i, MemLp (trace i) 2 μ)
    (hmatch : ∀ i, (∫ ω, trace i ω ∂μ) = target i)
    (hdispersion :
      _root_.GD.N0238.N0749.d004832 μ weight trace = 0)
    (boundary : Set Ω)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin :
      ∀ ω ∈ boundary,
        δ ≤ ∑ i, weight i * (trace i ω - target i) ^ 2) :
    μ.support ∩ boundary = ∅ := by
  let F : Ω → ℝ :=
    fun ω ↦ ∑ i, weight i * (trace i ω - target i) ^ 2
  have hF_continuous : Continuous F := by
    exact continuous_finsetSum _ fun i _ ↦
      continuous_const.mul
        (((htrace_continuous i).sub continuous_const).pow 2)
  have hF_integrable : Integrable F μ := by
    apply integrable_finsetSum
    intro i hi
    exact
      ((htrace i).sub (memLp_const (target i))).integrable_sq
        |>.const_mul (weight i)
  have hF_nonneg : ∀ ω, 0 ≤ F ω := fun ω ↦
    _root_.GD.N0238.N0749.d004835
      weight hweight trace target ω
  have hvariance :
      (∫ ω, F ω ∂μ) =
        ∑ i, weight i * variance (trace i) μ :=
    _root_.GD.N0238.N0756.d004826
      μ weight trace target htrace hmatch
  have hsum_zero :
      ∑ i, weight i * variance (trace i) μ = 0 := by
    unfold _root_.GD.N0238.N0749.d004832 at hdispersion
    linarith
  have hintegral : (∫ ω, F ω ∂μ) = 0 := hvariance.trans hsum_zero
  exact _root_.GD.N0238.N0749.d004844
    μ F hF_continuous hF_integrable hF_nonneg hintegral
    boundary δ hδ hmargin

end FiniteSupport

end Support

end

end N0749
end N0238
end GD
