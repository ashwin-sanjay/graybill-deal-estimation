import GD.Module0463
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace GD.N0213.N0514
noncomputable section
open _root_.GD.N0213.N0495

theorem d007715 (r : ℝ) :
    (volume.restrict (Ioi (0 : ℝ))) (Iic r) = ENNReal.ofReal r := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hi : Iic r ∩ Ioi (0 : ℝ) = Ioc 0 r := by ext x; simp [and_comm]
  rw [hi, Real.volume_Ioc, sub_zero]

theorem d007716 (μ : Measure ℝ) (C : ℝ≥0)
    (hμ : ∀ r : ℝ, μ (Iic r) = C * ENNReal.ofReal r) :
    μ = (C : ℝ≥0∞) • volume.restrict (Ioi (0 : ℝ)) := by
  let ν : Measure ℝ := (C : ℝ≥0∞) • volume.restrict (Ioi (0 : ℝ))
  have hν (r : ℝ) : ν (Iic r) = C * ENNReal.ofReal r := by
    simp only [ν, Measure.smul_apply, smul_eq_mul, _root_.GD.N0213.N0514.d007715]
  have hf (r : ℝ) : μ (Iic r) ≠ ⊤ := by rw [hμ]; finiteness
  apply Measure.ext_of_Ioc' μ ν
  · intro a b _
    exact ne_top_of_le_ne_top (hf b) (measure_mono Ioc_subset_Iic_self)
  · intro a b hab
    rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet
      (hf a), measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet
      (by rw [hν]; finiteness), hμ, hμ, hν, hν]

variable {Ω : Type*} [MeasurableSpace Ω]

theorem d007717 (μ : Measure Ω) (R : Ω → ℝ) (C : ℝ≥0)
    (hR : Measurable R) (hpos : ∀ᵐ x ∂μ, 0 < R x)
    (hmass : ∀ r : ℝ, 0 < r → μ {x | R x ≤ r} = C * ENNReal.ofReal r) :
    μ.map R = (C : ℝ≥0∞) • volume.restrict (Ioi (0 : ℝ)) := by
  apply _root_.GD.N0213.N0514.d007716
  intro r
  rw [Measure.map_apply hR measurableSet_Iic]
  change μ {x | R x ≤ r} = C * ENNReal.ofReal r
  by_cases hr : 0 < r
  · exact hmass r hr
  · have hz : μ {x | R x ≤ r} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hpos] with x hx
      exact not_le.mpr (lt_of_le_of_lt (le_of_not_gt hr) hx)
    simpa only [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hr), mul_zero] using hz

theorem d007718 (μ : Measure Ω) (R : Ω → ℝ) (C : ℝ≥0)
    (hR : Measurable R) (hmap : μ.map R = (C : ℝ≥0∞) • volume.restrict (Ioi (0 : ℝ)))
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f (R x) ∂μ) = (C : ℝ) * ∫ r in Ioi (0 : ℝ), f r := by
  rw [← integral_map hR.aemeasurable hf.aestronglyMeasurable, hmap,
    integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]

theorem d007719 (μ : Measure Ω) (R : Ω → ℝ)
    (S : ℝ → Ω → Ω) (hR : Measurable R)
    (hpos : ∀ᵐ x ∂μ, 0 < R x)
    (hSm : ∀ c : ℝ, 0 < c → Measurable (S c))
    (hscale : ∀ c : ℝ, 0 < c → μ.map (S c) = (ENNReal.ofReal c)⁻¹ • μ)
    (hSR : ∀ c : ℝ, 0 < c → ∀ x, R (S c x) = c * R x)
    (hfinite : μ {x | R x ≤ 1} ≠ ⊤) :
    μ.map R = μ {x | R x ≤ 1} • volume.restrict (Ioi (0 : ℝ)) := by
  have hm (r : ℝ) (hr : 0 < r) :
      μ {x | R x ≤ r} = (μ {x | R x ≤ 1}).toNNReal * ENNReal.ofReal r := by
    have h := congrArg (fun ν : Measure Ω => ν {x | R x ≤ 1})
      (hscale r⁻¹ (inv_pos.mpr hr))
    rw [Measure.map_apply (hSm _ (inv_pos.mpr hr)) (measurableSet_le hR measurable_const),
      Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_inv_of_pos hr,
      inv_inv] at h
    rw [ENNReal.coe_toNNReal hfinite]
    have heq : (S r⁻¹) ⁻¹' {x | R x ≤ 1} = {x | R x ≤ r} := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, hSR _ (inv_pos.mpr hr)]
      rw [inv_mul_le_iff₀ hr, mul_one]
    rw [heq] at h
    simpa only [mul_comm] using h
  simpa only [ENNReal.coe_toNNReal hfinite] using
    _root_.GD.N0213.N0514.d007717 μ R (μ {x | R x ≤ 1}).toNNReal hR hpos hm

theorem d007720 (μ : Measure Ω) (R : Ω → ℝ) (C : ℝ≥0)
    (hR : Measurable R) (hmap : μ.map R = (C : ℝ≥0∞) • volume.restrict (Ioi (0 : ℝ)))
    {L : ℝ} (hL : 0 < L) :
    (∫ x, R x * _root_.GD.N0213.N0495.d007175 L (R x) ^ 2 ∂μ) =
      (C : ℝ) * (4 * _root_.GD.N0213.N0495.d007186 / L) := by
  rw [_root_.GD.N0213.N0514.d007718 μ R C hR hmap (fun r => r * _root_.GD.N0213.N0495.d007175 L r ^ 2)
    (by dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]; fun_prop), _root_.GD.N0213.N0495.d007190 hL]

theorem d007721 (μ : Measure Ω) (R : Ω → ℝ) (C : ℝ≥0)
    (hR : Measurable R) (hmap : μ.map R = (C : ℝ≥0∞) • volume.restrict (Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => ∫ x, R x * _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (R x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have h := _root_.GD.N0213.N0495.d007191.const_mul (C : ℝ)
  have heq (n : ℕ) := _root_.GD.N0213.N0514.d007718 μ R C hR hmap
    (fun r => r * _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) r ^ 2)
    (by dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]; fun_prop)
  simp_rw [heq]
  simpa only [mul_zero] using h

end
end GD.N0213.N0514

#print axioms _root_.GD.N0213.N0514.d007716
#print axioms _root_.GD.N0213.N0514.d007717
#print axioms _root_.GD.N0213.N0514.d007718
#print axioms _root_.GD.N0213.N0514.d007719
#print axioms _root_.GD.N0213.N0514.d007721
