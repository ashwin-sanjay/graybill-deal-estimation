import GD.Module1336
import GD.Module0434
import GD.Module0435
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0101.N0370
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1242
open _root_.GD.N0101.N0387 _root_.GD.N0101.N0369

def d021717 (δ r b : ℝ) : Set _root_.GD.N0232.N0720.N1436.d013217 :=
  Ioo δ (1 - δ) ×ˢ Ioo r b

theorem d021718 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0101.N0387.d021709 u * (2 / 3 : ℝ) = betaPDFReal (1 / 2 : ℝ) (1 / 2) u := by
  rw [_root_.GD.N0232.N0720.N1242.d002142 hu]
  unfold _root_.GD.N0101.N0387.d021709
  rw [Real.rpow_neg hu.1.le, Real.rpow_neg (sub_pos.mpr hu.2).le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul hu.1.le]
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr hu.1).ne',
    (Real.sqrt_pos.mpr (sub_pos.mpr hu.2)).ne']

theorem d021719 {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ u in Ioo δ (1 - δ), ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 u * (2 / 3 : ℝ))) =
      ENNReal.ofReal (_root_.GD.N0101.N0369.d006733 δ) := by
  letI := _root_.GD.N0232.N0720.N1242.d002140
  have hpdf :
      (∫⁻ u in Ioo δ (1 - δ), ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u)) =
        _root_.GD.N0232.N0720.N1242.d002139 (Ioo δ (1 - δ)) := by
    unfold _root_.GD.N0232.N0720.N1242.d002139 betaMeasure
    rw [withDensity_apply _ measurableSet_Ioo]
    rfl
  calc
    _ = ∫⁻ u in Ioo δ (1 - δ), ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      rw [_root_.GD.N0101.N0370.d021718 ⟨hδ.trans hu.1, by linarith [hu.2]⟩]
    _ = _root_.GD.N0232.N0720.N1242.d002139 (Ioo δ (1 - δ)) := hpdf
    _ = _ := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

theorem d021720 {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b) :
    (∫⁻ s in Ioo r b, ENNReal.ofReal ((1 : ℝ) / s)) =
      ENNReal.ofReal (Real.log (b / r)) := by
  have hb := hr.trans_le hrb
  have hc : ContinuousOn (fun s : ℝ => (1 : ℝ) / s) (Icc r b) :=
    continuousOn_const.div continuousOn_id (fun s hs => (hr.trans_le hs.1).ne')
  have hi := (hc.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo r b)] (fun s : ℝ => (1 : ℝ) / s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (one_div_pos.mpr (hr.trans hs.1)).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have heq := integral_inv_of_pos hr hb
  rw [intervalIntegral.integral_of_le hrb, integral_Ioc_eq_integral_Ioo] at heq
  simpa only [one_div] using congrArg ENNReal.ofReal heq



theorem d021721 {δ r b K : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hrb : r ≤ b) (hK : 0 ≤ K) :
    (∫⁻ z in _root_.GD.N0101.N0370.d021717 δ r b,
      ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 z.1 * (2 / 3 : ℝ) * K / z.2)) =
      ENNReal.ofReal (_root_.GD.N0101.N0369.d006733 δ * K * Real.log (b / r)) := by
  have hmA : Measurable (fun u => ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 u * (2 / 3 : ℝ))) := by
    unfold _root_.GD.N0101.N0387.d021709
    fun_prop
  have hmS : Measurable (fun s : ℝ => ENNReal.ofReal ((1 : ℝ) / s)) := by fun_prop
  have hsplit :
      (∫⁻ z in _root_.GD.N0101.N0370.d021717 δ r b,
        ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 z.1 * (2 / 3 : ℝ) * K / z.2)) =
      ∫⁻ z in _root_.GD.N0101.N0370.d021717 δ r b,
        ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 z.1 * (2 / 3 : ℝ)) *
          (ENNReal.ofReal K * ENNReal.ofReal ((1 : ℝ) / z.2)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    have hu : z.1 ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans hz.1.1, by linarith [hz.1.2]⟩
    have hA := mul_nonneg (_root_.GD.N0101.N0387.d021711 hu).le (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hA]
    congr 1
    ring
  rw [hsplit]
  change (∫⁻ z, ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 z.1 * (2 / 3 : ℝ)) *
      (ENNReal.ofReal K * ENNReal.ofReal ((1 : ℝ) / z.2))
      ∂((volume : Measure ℝ).prod volume).restrict (Ioo δ (1 - δ) ×ˢ Ioo r b)) = _
  rw [← Measure.prod_restrict, lintegral_prod_mul hmA.aemeasurable
    (measurable_const.mul hmS).aemeasurable,
    lintegral_const_mul _ hmS, _root_.GD.N0101.N0370.d021719 hδ, _root_.GD.N0101.N0370.d021720 hr hrb]
  rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul (_root_.GD.N0101.N0369.d006734 δ)]
  congr 1
  ring



theorem d021722 (G : _root_.GD.N0232.N0720.N1436.d013217 → ℝ≥0∞)
    {δ r b K : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hrb : r ≤ b) (hK : 0 ≤ K)
    (hbound : ∀ z ∈ _root_.GD.N0101.N0370.d021717 δ r b,
      ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 z.1 * (2 / 3 : ℝ) * K / z.2) ≤ G z) :
    ENNReal.ofReal (_root_.GD.N0101.N0369.d006733 δ * K * Real.log (b / r)) ≤
      ∫⁻ z, G z ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  have hsubset : _root_.GD.N0101.N0370.d021717 δ r b ⊆ _root_.GD.N0232.N0720.N1436.d013218 := by
    intro z hz
    exact ⟨⟨hδ.trans hz.1.1, by linarith [hz.1.2]⟩, hr.trans hz.2.1⟩
  calc
    _ = ∫⁻ z in _root_.GD.N0101.N0370.d021717 δ r b,
        ENNReal.ofReal (_root_.GD.N0101.N0387.d021709 z.1 * (2 / 3 : ℝ) * K / z.2) :=
      (_root_.GD.N0101.N0370.d021721 hδ hr hrb hK).symm
    _ ≤ ∫⁻ z in _root_.GD.N0101.N0370.d021717 δ r b, G z :=
      setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Ioo) hbound
    _ ≤ _ := lintegral_mono_set hsubset

end
end GD.N0101.N0370

#print axioms _root_.GD.N0101.N0370.d021718
#print axioms _root_.GD.N0101.N0370.d021719
#print axioms _root_.GD.N0101.N0370.d021720
#print axioms _root_.GD.N0101.N0370.d021721
#print axioms _root_.GD.N0101.N0370.d021722
