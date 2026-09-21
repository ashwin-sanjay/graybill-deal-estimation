import GD.Module0014
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Semicontinuity.Basic






















open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GD
namespace N0230
namespace N0591

variable {Ω Θ : Type*} [MeasurableSpace Ω]



noncomputable def d000126
    (base : Measure Ω) (density : Θ → Ω → ℝ)
    (target : Θ → ℝ) (d : Ω → ℝ) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal
    (density θ ω * (d ω - target θ) ^ 2) ∂base




theorem d000127
    (base : Measure Ω) (density : Θ → Ω → ℝ)
    (target : Θ → ℝ) (d : Ω → ℝ)
    (θs : ℕ → Θ) (θ : Θ)
    (hdensity : ∀ ω,
      Tendsto (fun n ↦ density (θs n) ω) atTop (𝓝 (density θ ω)))
    (htarget : Tendsto (fun n ↦ target (θs n)) atTop (𝓝 (target θ)))
    (hmeas : ∀ η,
      AEMeasurable
        (fun ω ↦ ENNReal.ofReal
          (density η ω * (d ω - target η) ^ 2)) base) :
    _root_.GD.N0230.N0591.d000126 base density target d θ ≤
      liminf (fun n ↦
        _root_.GD.N0230.N0591.d000126 base density target d (θs n)) atTop := by
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ENNReal.ofReal
    (density (θs n) ω * (d ω - target (θs n)) ^ 2)
  have hfmeas : ∀ n, AEMeasurable (f n) base := fun n ↦ hmeas (θs n)
  have hlim : ∀ ω,
      Tendsto (fun n ↦ f n ω) atTop
        (𝓝 (ENNReal.ofReal
          (density θ ω * (d ω - target θ) ^ 2))) := by
    intro ω
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    exact (hdensity ω).mul
      ((tendsto_const_nhds.sub htarget).pow 2)
  calc
    _root_.GD.N0230.N0591.d000126 base density target d θ =
        ∫⁻ ω, liminf (fun n ↦ f n ω) atTop ∂base := by
      apply lintegral_congr
      intro ω
      exact (hlim ω).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ ω, f n ω ∂base) atTop :=
      lintegral_liminf_le' hfmeas
    _ = liminf (fun n ↦
        _root_.GD.N0230.N0591.d000126 base density target d (θs n)) atTop := rfl




theorem d000128
    [TopologicalSpace Θ] [SequentialSpace Θ]
    (base : Measure Ω) (density : Θ → Ω → ℝ)
    (target : Θ → ℝ) (d : Ω → ℝ)
    (hdensity : ∀ ω, Continuous (fun θ ↦ density θ ω))
    (htarget : Continuous target)
    (hmeas : ∀ θ,
      AEMeasurable
        (fun ω ↦ ENNReal.ofReal
          (density θ ω * (d ω - target θ) ^ 2)) base) :
    LowerSemicontinuous
      (_root_.GD.N0230.N0591.d000126 base density target d) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro cap
  apply IsSeqClosed.isClosed
  intro θs θ hθs hθsθ
  have hfatou := _root_.GD.N0230.N0591.d000127
    base density target d θs θ
    (fun ω ↦ (hdensity ω).tendsto θ |>.comp hθsθ)
    (htarget.tendsto θ |>.comp hθsθ) hmeas
  exact hfatou.trans <|
    liminf_le_of_frequently_le' <|
      Filter.Eventually.frequently <|
        Filter.Eventually.of_forall hθs







theorem d000129
    [TopologicalSpace Θ] [SequentialSpace Θ]
    (base : Measure Ω) (density : Θ → Ω → ℝ)
    (target : Θ → ℝ) (d : Ω → ℝ)
    (hdensity : ∀ ω, Continuous (fun θ ↦ density θ ω))
    (htarget : Continuous target)
    (hmeas : ∀ θ,
      AEMeasurable
        (fun ω ↦ ENNReal.ofReal
          (density θ ω * (d ω - target θ) ^ 2)) base)
    (hdominated : ∀ θ, ∃ U ∈ 𝓝 θ, ∃ bound : Ω → ℝ≥0∞,
      (∫⁻ ω, bound ω ∂base) ≠ ∞ ∧
      ∀ η ∈ U, ∀ᵐ ω ∂base,
        ENNReal.ofReal
            (density η ω * (d ω - target η) ^ 2) ≤ bound ω) :
    Continuous (_root_.GD.N0230.N0591.d000126 base density target d) := by
  apply SeqContinuous.continuous
  intro θs θ hθsθ
  obtain ⟨U, hU, bound, hbound_finite, hbound⟩ := hdominated θ
  apply tendsto_lintegral_filter_of_dominated_convergence' bound
  · exact Filter.Eventually.of_forall fun n ↦ hmeas (θs n)
  · filter_upwards [hθsθ.eventually hU] with n hn
    exact hbound (θs n) hn
  · exact hbound_finite
  · exact Filter.Eventually.of_forall fun ω ↦
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp <|
        (((hdensity ω).tendsto θ).comp hθsθ).mul
          ((tendsto_const_nhds.sub
            ((htarget.tendsto θ).comp hθsθ)).pow 2)



theorem d000130
    {μ₀ μ : Measure Ω} (density : Ω → ℝ)
    (target : ℝ) (d : _root_.GD.N0230.N0602.d000116 μ₀)
    (hlaw : μ = μ₀.withDensity (fun ω ↦ ENNReal.ofReal (density ω)))
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ ω, 0 ≤ density ω) :
    _root_.GD.N0230.N0602.d000117
        (μ₀ := μ₀) μ target d =
      _root_.GD.N0230.N0591.d000126 μ₀ (fun _ : Unit ↦ density)
        (fun _ ↦ target) d () := by
  rw [hlaw, _root_.GD.N0230.N0602.d000117,
    _root_.GD.N0230.N0591.d000126,
    lintegral_withDensity_eq_lintegral_mul₀]
  · apply lintegral_congr
    intro ω
    simp only [Pi.mul_apply]
    exact (ENNReal.ofReal_mul (hdensity_nonneg ω)).symm
  · exact hdensity.ennreal_ofReal.aemeasurable
  · exact
      (((_root_.GD.N0230.N0602.d000116 μ₀
        |> fun _ ↦ Lp.aestronglyMeasurable d).aemeasurable.sub
          aemeasurable_const).pow_const 2).ennreal_ofReal




theorem d000131
    [TopologicalSpace Θ] [SequentialSpace Θ]
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω)
    (density : Θ → Ω → ℝ) (target : Θ → ℝ)
    (d : _root_.GD.N0230.N0602.d000116 μ₀)
    (hlaw : ∀ θ,
      μ θ = μ₀.withDensity
        (fun ω ↦ ENNReal.ofReal (density θ ω)))
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_nonneg : ∀ θ ω, 0 ≤ density θ ω)
    (hdensity_continuous : ∀ ω, Continuous (fun θ ↦ density θ ω))
    (htarget : Continuous target) :
    LowerSemicontinuous (fun θ ↦
      _root_.GD.N0230.N0602.d000117
        (μ₀ := μ₀) (μ θ) (target θ) d) := by
  have heq : (fun θ ↦
      _root_.GD.N0230.N0602.d000117
        (μ₀ := μ₀) (μ θ) (target θ) d) =
      _root_.GD.N0230.N0591.d000126 μ₀ density target d := by
    funext θ
    exact _root_.GD.N0230.N0591.d000130
      (density θ) (target θ) d (hlaw θ)
      (hdensity_measurable θ) (hdensity_nonneg θ)
  rw [heq]
  apply _root_.GD.N0230.N0591.d000128
    μ₀ density target d hdensity_continuous htarget
  intro θ
  exact
    (((hdensity_measurable θ).aemeasurable.mul
      (((Lp.aestronglyMeasurable d).aemeasurable.sub
        aemeasurable_const).pow_const 2)).ennreal_ofReal)



theorem d000132
    [TopologicalSpace Θ] [SequentialSpace Θ]
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω)
    (density : Θ → Ω → ℝ) (target : Θ → ℝ)
    (d : _root_.GD.N0230.N0602.d000116 μ₀)
    (hlaw : ∀ θ,
      μ θ = μ₀.withDensity
        (fun ω ↦ ENNReal.ofReal (density θ ω)))
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_nonneg : ∀ θ ω, 0 ≤ density θ ω)
    (hdensity_continuous : ∀ ω, Continuous (fun θ ↦ density θ ω))
    (htarget : Continuous target)
    (hdominated : ∀ θ, ∃ U ∈ 𝓝 θ, ∃ bound : Ω → ℝ≥0∞,
      (∫⁻ ω, bound ω ∂μ₀) ≠ ∞ ∧
      ∀ η ∈ U, ∀ᵐ ω ∂μ₀,
        ENNReal.ofReal
            (density η ω * (d ω - target η) ^ 2) ≤ bound ω) :
    Continuous (fun θ ↦
      _root_.GD.N0230.N0602.d000117
        (μ₀ := μ₀) (μ θ) (target θ) d) := by
  have heq : (fun θ ↦
      _root_.GD.N0230.N0602.d000117
        (μ₀ := μ₀) (μ θ) (target θ) d) =
      _root_.GD.N0230.N0591.d000126 μ₀ density target d := by
    funext θ
    exact _root_.GD.N0230.N0591.d000130
      (density θ) (target θ) d (hlaw θ)
      (hdensity_measurable θ) (hdensity_nonneg θ)
  rw [heq]
  apply _root_.GD.N0230.N0591.d000129
    μ₀ density target d hdensity_continuous htarget
  · intro θ
    exact
      (((hdensity_measurable θ).aemeasurable.mul
        (((Lp.aestronglyMeasurable d).aemeasurable.sub
          aemeasurable_const).pow_const 2)).ennreal_ofReal)
  · exact hdominated


noncomputable def d000133
    (base : Measure Ω) (density : Θ → Ω → ℝ)
    (observable : Ω → ℝ) (θ : Θ) : ℝ :=
  ∫ ω, density θ ω * observable ω ∂base




theorem d000134
    [TopologicalSpace Θ] [SequentialSpace Θ]
    (base : Measure Ω) (density : Θ → Ω → ℝ)
    (observable : Ω → ℝ)
    (hdensity : ∀ ω, Continuous (fun θ ↦ density θ ω))
    (hmeas : ∀ θ,
      AEStronglyMeasurable
        (fun ω ↦ density θ ω * observable ω) base)
    (hdominated : ∀ θ, ∃ U ∈ 𝓝 θ, ∃ bound : Ω → ℝ,
      Integrable bound base ∧
      ∀ η ∈ U, ∀ᵐ ω ∂base,
        ‖density η ω * observable ω‖ ≤ bound ω) :
    Continuous (_root_.GD.N0230.N0591.d000133 base density observable) := by
  apply SeqContinuous.continuous
  intro θs θ hθsθ
  obtain ⟨U, hU, bound, hbound_integrable, hbound⟩ := hdominated θ
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun n ↦ hmeas (θs n)
  · filter_upwards [hθsθ.eventually hU] with n hn
    exact hbound (θs n) hn
  · exact hbound_integrable
  · exact Filter.Eventually.of_forall fun ω ↦
      (((hdensity ω).tendsto θ).comp hθsθ).mul_const (observable ω)



theorem d000135
    {μ₀ μ : Measure Ω} (density observable : Ω → ℝ)
    (hlaw : μ = μ₀.withDensity (fun ω ↦ ENNReal.ofReal (density ω)))
    (hdensity : Measurable density)
    (hdensity_nonneg : ∀ ω, 0 ≤ density ω) :
    (∫ ω, observable ω ∂μ) =
      _root_.GD.N0230.N0591.d000133 μ₀ (fun _ : Unit ↦ density) observable () := by
  rw [hlaw,
    integral_withDensity_eq_integral_toReal_smul
      hdensity.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards with ω
  simp [ENNReal.toReal_ofReal (hdensity_nonneg ω), smul_eq_mul]



theorem d000136
    [TopologicalSpace Θ] [SequentialSpace Θ]
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω)
    (density : Θ → Ω → ℝ) (observable : Ω → ℝ)
    (hlaw : ∀ θ,
      μ θ = μ₀.withDensity
        (fun ω ↦ ENNReal.ofReal (density θ ω)))
    (hdensity_measurable : ∀ θ, Measurable (density θ))
    (hdensity_nonneg : ∀ θ ω, 0 ≤ density θ ω)
    (hdensity_continuous : ∀ ω, Continuous (fun θ ↦ density θ ω))
    (hmeas : ∀ θ,
      AEStronglyMeasurable
        (fun ω ↦ density θ ω * observable ω) μ₀)
    (hdominated : ∀ θ, ∃ U ∈ 𝓝 θ, ∃ bound : Ω → ℝ,
      Integrable bound μ₀ ∧
      ∀ η ∈ U, ∀ᵐ ω ∂μ₀,
        ‖density η ω * observable ω‖ ≤ bound ω) :
    Continuous (fun θ ↦ ∫ ω, observable ω ∂μ θ) := by
  have heq : (fun θ ↦ ∫ ω, observable ω ∂μ θ) =
      _root_.GD.N0230.N0591.d000133 μ₀ density observable := by
    funext θ
    exact _root_.GD.N0230.N0591.d000135
      (density θ) observable (hlaw θ)
      (hdensity_measurable θ) (hdensity_nonneg θ)
  rw [heq]
  exact _root_.GD.N0230.N0591.d000134
    μ₀ density observable hdensity_continuous hmeas hdominated




theorem d000137
    [TopologicalSpace Θ]
    (candidate benchmark : Θ → ℝ≥0∞)
    (hcandidate : LowerSemicontinuous candidate)
    (hbenchmark : UpperSemicontinuous benchmark) :
    IsOpen {θ | benchmark θ < candidate θ} := by
  rw [isOpen_iff_eventually]
  intro θ hθ
  have hθ' : benchmark θ < candidate θ := hθ
  obtain ⟨c, hbc, hcr⟩ := exists_between hθ'
  filter_upwards
    [hbenchmark θ c hbc,
      hcandidate θ c hcr] with η hbη hη
  exact hbη.trans hη



theorem d000138
    [TopologicalSpace Θ]
    (candidate benchmark : Θ → ℝ≥0∞)
    (hcandidate : LowerSemicontinuous candidate)
    (hbenchmark : Continuous benchmark) :
    IsOpen {θ | benchmark θ < candidate θ} :=
  _root_.GD.N0230.N0591.d000137
    candidate benchmark hcandidate hbenchmark.upperSemicontinuous




theorem d000139
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (sample : ℕ → Θ)
    (hdense : DenseRange sample) (bar d : Rule)
    (hd : LowerSemicontinuous (fun θ ↦ risk θ d))
    (hbar : UpperSemicontinuous (fun θ ↦ risk θ bar)) :
    (∀ n, risk (sample n) d ≤ risk (sample n) bar) ↔
      ∀ θ, risk θ d ≤ risk θ bar := by
  constructor
  · intro hsample θ
    by_contra hθ
    have hopen : IsOpen {η | risk η bar < risk η d} :=
      _root_.GD.N0230.N0591.d000137
        (fun η ↦ risk η d) (fun η ↦ risk η bar) hd hbar
    have hUne : ({η | risk η bar < risk η d} : Set Θ).Nonempty :=
      ⟨θ, lt_of_not_ge hθ⟩
    obtain ⟨n, hn⟩ := hdense.exists_mem_open hopen hUne
    exact (not_lt_of_ge (hsample n)) hn
  · intro hall n
    exact hall (sample n)


theorem d000140
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (sample : ℕ → Θ)
    (hdense : DenseRange sample) (bar d : Rule)
    (hd : LowerSemicontinuous (fun θ ↦ risk θ d))
    (hbar : Continuous (fun θ ↦ risk θ bar)) :
    (∀ n, risk (sample n) d ≤ risk (sample n) bar) ↔
      ∀ θ, risk θ d ≤ risk θ bar :=
  _root_.GD.N0230.N0591.d000139
    risk sample hdense bar d hd hbar.upperSemicontinuous

end N0591
end N0230
end GD
