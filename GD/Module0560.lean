import GD.Module0559




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0006

noncomputable section

open _root_.GD.N0082.N0334
open _root_.GD.N0149.N0432 _root_.GD.N0149.N0433

theorem d008331
    (H : ℝ → ℝ) (hH : Measurable H) (C : ℝ)
    (hI : ∀ t ∈ Ioo (0 : ℝ) 1,
      Integrable (fun u => ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2)
        (volume.restrict (Ioo (0 : ℝ) 1)))
    (hcap : ∀ t ∈ Ioo (0 : ℝ) 1, _root_.GD.N0082.N0334.d008258 H t ≤ C)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun u => ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) ∧ _root_.GD.N0082.N0334.d008258 H t ≤ C := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℝ → ℝ → ℝ≥0∞ := fun s u =>
    ENNReal.ofReal (((H u - s) / _root_.GD.N0082.N0334.d008256 s u) ^ 2)
  have hmeas (s : ℝ) : Measurable (fun u => ((H u - s) / _root_.GD.N0082.N0334.d008256 s u) ^ 2) := by
    unfold _root_.GD.N0082.N0334.d008256
    fun_prop
  have hFmeas (s : ℝ) : Measurable (F s) := (hmeas s).ennreal_ofReal
  haveI : (𝓝[Ioo (0 : ℝ) 1] t).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact ht)
  have hlim : ∀ᵐ u ∂μ,
      Tendsto (fun s => F s u) (𝓝[Ioo (0 : ℝ) 1] t) (𝓝 (F t u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hc : ContinuousAt (fun s => ((H u - s) / _root_.GD.N0082.N0334.d008256 s u) ^ 2) t := by
      apply ContinuousAt.pow
      apply ContinuousAt.div
      · fun_prop
      · unfold _root_.GD.N0082.N0334.d008256; fun_prop
      · exact (_root_.GD.N0082.N0334.d008263 ht hu).ne'
    exact (ENNReal.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left
      nhdsWithin_le_nhds
  have hfatou : (∫⁻ u, F t u ∂μ) ≤
      liminf (fun s => ∫⁻ u, F s u ∂μ) (𝓝[Ioo (0 : ℝ) 1] t) := by
    calc
      _ = ∫⁻ u, liminf (fun s => F s u) (𝓝[Ioo (0 : ℝ) 1] t) ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hu => hu.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le hFmeas
  have hbound : ∀ᶠ s in 𝓝[Ioo (0 : ℝ) 1] t,
      (∫⁻ u, F s u ∂μ) ≤ ENNReal.ofReal C := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change (∫⁻ u, ENNReal.ofReal (((H u - s) / _root_.GD.N0082.N0334.d008256 s u) ^ 2) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hI s hs)
      (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hcap s hs)
  have hle : (∫⁻ u, F t u ∂μ) ≤ ENNReal.ofReal C :=
    hfatou.trans (liminf_le_of_frequently_le' hbound.frequently)
  have hint : Integrable (fun u => ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2) μ := by
    refine ⟨(hmeas t).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).mpr
    exact hle.trans_lt ENNReal.ofReal_lt_top
  have hC : 0 ≤ C :=
    (_root_.GD.N0082.N0334.d008268 H (1 / 2)).trans (hcap (1 / 2) (by constructor <;> norm_num))
  refine ⟨hint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  change ENNReal.ofReal (∫ u, ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2 ∂μ) ≤ _
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
  exact hle

theorem d008332
    (H : ℝ → ℝ) (hH : Measurable H) (C : ℝ)
    (hI : ∀ t ∈ Ioo (0 : ℝ) 1,
      Integrable (fun u => ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2)
        (volume.restrict (Ioo (0 : ℝ) 1)))
    (hcap : ∀ t ∈ Ioo (0 : ℝ) 1, _root_.GD.N0082.N0334.d008258 H t ≤ C) :
    _root_.GD.N0149.N0433.d008323 H := by
  have h0 := (_root_.GD.N0006.d008331 H hH C hI hcap
    (t := 0) (by constructor <;> norm_num)).1
  have h1 := (_root_.GD.N0006.d008331 H hH C hI hcap
    (t := 1) (by constructor <;> norm_num)).1
  refine ⟨hH, (h0.add h1).congr ?_⟩
  filter_upwards with u
  change ((H u - 0) / _root_.GD.N0082.N0334.d008256 0 u) ^ 2 +
    ((H u - 1) / _root_.GD.N0082.N0334.d008256 1 u) ^ 2 = _root_.GD.N0149.N0432.d008291 H u
  simp only [_root_.GD.N0149.N0432.d008291, _root_.GD.N0082.N0334.d008256, mul_zero, add_zero, sub_zero]
  congr 2; ring

theorem d008333
    (H : ℝ → ℝ) (hH : Measurable H) (C : ℝ)
    (hI : ∀ t ∈ Ioo (0 : ℝ) 1,
      Integrable (fun u => ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2)
        (volume.restrict (Ioo (0 : ℝ) 1)))
    (hcap : ∀ t ∈ Ioo (0 : ℝ) 1, _root_.GD.N0082.N0334.d008258 H t ≤ C) :
    _root_.GD.N0082.N0334.d008258 H 0 ≤ C ∧ _root_.GD.N0082.N0334.d008258 H 1 ≤ C :=
  ⟨(_root_.GD.N0006.d008331 H hH C hI hcap
    (t := 0) (by constructor <;> norm_num)).2,
    (_root_.GD.N0006.d008331 H hH C hI hcap
    (t := 1) (by constructor <;> norm_num)).2⟩

end
end GD.N0006

#print axioms _root_.GD.N0006.d008331
#print axioms _root_.GD.N0006.d008332
#print axioms _root_.GD.N0006.d008333
