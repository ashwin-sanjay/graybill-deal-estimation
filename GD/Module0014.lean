import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add




















open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GD
namespace N0230
namespace N0602

variable {Ω Θ : Type*} [MeasurableSpace Ω]


abbrev d000116 (μ₀ : Measure Ω) := Lp ℝ 2 μ₀







noncomputable def d000117
    {μ₀ : Measure Ω} (μ : Measure Ω) (target : ℝ)
    (d : _root_.GD.N0230.N0602.d000116 μ₀) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((d ω - target) ^ 2) ∂μ


def d000118
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω)
    (target : Θ → ℝ) (cap : Θ → ℝ≥0∞) :
    Set (_root_.GD.N0230.N0602.d000116 μ₀) :=
  {d | ∀ θ, _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) (μ θ) (target θ) d ≤ cap θ}

lemma d000119
    {μ₀ μ : Measure Ω} (hμ : μ ≪ μ₀)
    (target : ℝ) (d : _root_.GD.N0230.N0602.d000116 μ₀) :
    AEMeasurable
      (fun ω => ENNReal.ofReal ((d ω - target) ^ 2)) μ := by
  exact
    (((AEStronglyMeasurable.mono_ac hμ
        (Lp.aestronglyMeasurable d)).aemeasurable.sub
      aemeasurable_const).pow_const 2).ennreal_ofReal








theorem d000120
    {μ₀ μ : Measure Ω} (hμ : μ ≪ μ₀)
    (target : ℝ)
    {d : _root_.GD.N0230.N0602.d000116 μ₀} {ds : ℕ → _root_.GD.N0230.N0602.d000116 μ₀}
    (hds : Tendsto ds atTop (𝓝 d))
    (cap : ℝ≥0∞)
    (hcap :
      ∀ n, _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target (ds n) ≤ cap) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target d ≤ cap := by
  obtain ⟨ns, _hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hds).exists_seq_tendsto_ae
  have hpointμ :
      ∀ᵐ ω ∂μ, Tendsto (fun n => ds (ns n) ω) atTop (𝓝 (d ω)) :=
    hμ.ae_le hpoint
  let f : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => ENNReal.ofReal ((ds (ns n) ω - target) ^ 2)
  have hfmeas : ∀ n, AEMeasurable (f n) μ := by
    intro n
    exact _root_.GD.N0230.N0602.d000119 hμ target (ds (ns n))
  have hlim :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n => f n ω) atTop
          (𝓝 (ENNReal.ofReal ((d ω - target) ^ 2))) := by
    filter_upwards [hpointμ] with ω hω
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hω.sub_const target).pow 2)
  calc
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target d =
        ∫⁻ ω, liminf (fun n => f n ω) atTop ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hlim] with ω hω
          exact hω.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂μ) atTop :=
      lintegral_liminf_le' hfmeas
    _ ≤ cap :=
      liminf_le_of_frequently_le' <|
        Filter.Eventually.frequently <|
          Filter.Eventually.of_forall fun n => hcap (ns n)





theorem d000121
    {μ₀ μ : Measure Ω} (hμ : μ ≪ μ₀)
    (target : ℝ) (d e : _root_.GD.N0230.N0602.d000116 μ₀)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target (a • d + b • e) ≤
      ENNReal.ofReal a * _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target d +
        ENNReal.ofReal b * _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target e := by
  have hcoe0 :
      ∀ᵐ ω ∂μ₀,
        (a • d + b • e : _root_.GD.N0230.N0602.d000116 μ₀) ω =
          a * d ω + b * e ω := by
    filter_upwards [Lp.coeFn_add (a • d) (b • e),
      Lp.coeFn_smul a d, Lp.coeFn_smul b e] with ω hadd had hbd
    simp only [hadd, had, hbd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcoe :
      ∀ᵐ ω ∂μ,
        (a • d + b • e : _root_.GD.N0230.N0602.d000116 μ₀) ω =
          a * d ω + b * e ω :=
    hμ.ae_le hcoe0
  have hdmeas :=
    _root_.GD.N0230.N0602.d000119 hμ target d
  have hemeas :=
    _root_.GD.N0230.N0602.d000119 hμ target e
  calc
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target (a • d + b • e) =
        ∫⁻ ω,
          ENNReal.ofReal
            (((a * d ω + b * e ω) - target) ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hcoe] with ω hω
      rw [hω]
    _ ≤ ∫⁻ ω,
          (ENNReal.ofReal a *
              ENNReal.ofReal ((d ω - target) ^ 2) +
            ENNReal.ofReal b *
              ENNReal.ofReal ((e ω - target) ^ 2)) ∂μ := by
      apply lintegral_mono
      intro ω
      have hsq :
          ((a * d ω + b * e ω) - target) ^ 2 ≤
            a * (d ω - target) ^ 2 +
              b * (e ω - target) ^ 2 := by
        have ha1 : a ≤ 1 := by linarith
        have hb_eq : b = 1 - a := by linarith
        rw [hb_eq]
        nlinarith [
          mul_nonneg ha (sub_nonneg.mpr ha1),
          sq_nonneg (d ω - e ω)]
      calc
        ENNReal.ofReal (((a * d ω + b * e ω) - target) ^ 2) ≤
            ENNReal.ofReal
              (a * (d ω - target) ^ 2 +
                b * (e ω - target) ^ 2) :=
          ENNReal.ofReal_le_ofReal hsq
        _ =
            ENNReal.ofReal a *
                ENNReal.ofReal ((d ω - target) ^ 2) +
              ENNReal.ofReal b *
                ENNReal.ofReal ((e ω - target) ^ 2) := by
          rw [ENNReal.ofReal_add]
          · rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
          · positivity
          · positivity
    _ =
          ENNReal.ofReal a * _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target d +
          ENNReal.ofReal b * _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ target e := by
      simp only [_root_.GD.N0230.N0602.d000117]
      rw [lintegral_add_left']
      · rw [lintegral_const_mul'' _ hdmeas,
          lintegral_const_mul'' _ hemeas]
      · exact hdmeas.const_mul _





theorem d000122
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω)
    (target : Θ → ℝ) (cap : Θ → ℝ≥0∞)
    (hμ : ∀ θ, μ θ ≪ μ₀) :
    IsClosed (_root_.GD.N0230.N0602.d000118 μ₀ μ target cap) := by
  apply IsSeqClosed.isClosed
  intro d ds hdsC hds θ
  exact _root_.GD.N0230.N0602.d000120
    (hμ θ) (target θ) hds (cap θ) (fun n => hdsC n θ)


theorem d000123
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω)
    (target : Θ → ℝ) (cap : Θ → ℝ≥0∞)
    (hμ : ∀ θ, μ θ ≪ μ₀) :
    Convex ℝ (_root_.GD.N0230.N0602.d000118 μ₀ μ target cap) := by
  rw [convex_iff_segment_subset]
  intro d hd e he z hz
  rw [segment_eq_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  simp only [Set.mem_Icc] at ha
  intro θ
  have hcombo :=
    _root_.GD.N0230.N0602.d000121 (hμ θ) (target θ) d e
      (sub_nonneg.mpr ha.2) ha.1 (by ring)
  calc
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) (μ θ) (target θ)
        ((1 - a) • d + a • e) ≤
        ENNReal.ofReal (1 - a) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) (μ θ) (target θ) d +
          ENNReal.ofReal a *
            _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) (μ θ) (target θ) e :=
      hcombo
    _ ≤
        ENNReal.ofReal (1 - a) * cap θ +
          ENNReal.ofReal a * cap θ := by
      gcongr
      · exact hd θ
      · exact he θ
    _ = cap θ := by
      rw [← add_mul,
        ← ENNReal.ofReal_add (sub_nonneg.mpr ha.2) ha.1]
      simp





theorem d000124
    (μ₀ : Measure Ω) (d : _root_.GD.N0230.N0602.d000116 μ₀) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := μ₀) μ₀ 0 d =
      ENNReal.ofReal (‖(0 : _root_.GD.N0230.N0602.d000116 μ₀) - d‖ ^ 2) := by
  have hint : Integrable (fun ω => (d ω) ^ 2) μ₀ := by
    simpa [pow_two, real_inner_comm] using
      (L2.integrable_inner (𝕜 := ℝ) d d)
  have hnonneg : 0 ≤ᵐ[μ₀] fun ω => (d ω) ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  rw [_root_.GD.N0230.N0602.d000117]
  simp_rw [sub_zero]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  calc
    (∫ x, (d x) ^ 2 ∂μ₀) = inner ℝ d d := by
      rw [L2.inner_def]
      congr 1
      funext x
      simp
    _ = ‖d‖ ^ 2 := real_inner_self_eq_norm_sq d
    _ = ‖(0 : _root_.GD.N0230.N0602.d000116 μ₀) - d‖ ^ 2 := by simp


theorem d000125
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω)
    (target : Θ → ℝ) (cap : Θ → ℝ≥0∞)
    (hμ : ∀ θ, μ θ ≪ μ₀) :
    IsComplete (_root_.GD.N0230.N0602.d000118 μ₀ μ target cap) :=
  (_root_.GD.N0230.N0602.d000122 μ₀ μ target cap hμ).isComplete

end N0602
end N0230
end GD
