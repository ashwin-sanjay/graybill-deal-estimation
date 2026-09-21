import GD.Module0926
import GD.Module0006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace GD.N0149.N0431
noncomputable section

open _root_.GD.N0230.N0564
open _root_.GD.N0232.N0720.N1092
open _root_.GD.N0001

def d014474 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
def d014475 : Measure ℝ := betaMeasure (1/2) (1/2)

instance : IsProbabilityMeasure _root_.GD.N0149.N0431.d014475 := isProbabilityMeasureBeta (by norm_num) (by norm_num)
instance : IsProbabilityMeasure _root_.GD.N0149.N0431.d014474 := by
  constructor
  simp [_root_.GD.N0149.N0431.d014474]

def d014476 (t u : ℝ) : ℝ≥0 :=
  if t ∈ Ioo (0 : ℝ) 1 then Real.toNNReal (1/_root_.GD.N0001.d014462 u t^2) else 0

theorem d014477 : Measurable (Function.uncurry _root_.GD.N0149.N0431.d014476) := by
  change Measurable (fun z : ℝ×ℝ => if z.1 ∈ Ioo (0 : ℝ) 1 then
    Real.toNNReal (1/_root_.GD.N0001.d014462 z.2 z.1^2) else 0)
  apply Measurable.ite (measurableSet_Ioo.preimage measurable_fst)
  · unfold _root_.GD.N0001.d014462
    fun_prop
  · exact measurable_const

theorem d014478 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (u : ℝ) :
    (_root_.GD.N0149.N0431.d014476 t u : ℝ)=1/_root_.GD.N0001.d014462 u t^2 := by
  rw [_root_.GD.N0149.N0431.d014476,if_pos ht,Real.coe_toNNReal _ (by positivity)]

def d014479 (H : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (((H u-t)/_root_.GD.N0001.d014462 u t)^2) ∂_root_.GD.N0149.N0431.d014474

theorem d014480 (H : ℝ → ℝ) (hH : Measurable H)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0230.N0564.d000052 _root_.GD.N0149.N0431.d014474 _root_.GD.N0149.N0431.d014476 id t H=_root_.GD.N0149.N0431.d014479 H t := by
  rw [_root_.GD.N0230.N0564.d000054 _root_.GD.N0149.N0431.d014477 hH]
  apply lintegral_congr
  intro u
  change (_root_.GD.N0149.N0431.d014476 t u : ℝ≥0∞)*ENNReal.ofReal ((H u-t)^2)=_
  rw [_root_.GD.N0149.N0431.d014476,if_pos ht]
  change ENNReal.ofReal (1/_root_.GD.N0001.d014462 u t^2)*ENNReal.ofReal ((H u-t)^2)=_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem d014481 (H : ℝ → ℝ) (hH : Measurable H)
    {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) : _root_.GD.N0230.N0564.d000052 _root_.GD.N0149.N0431.d014474 _root_.GD.N0149.N0431.d014476 id t H=0 := by
  rw [_root_.GD.N0230.N0564.d000054 _root_.GD.N0149.N0431.d014477 hH]
  simp [_root_.GD.N0149.N0431.d014476,ht]

theorem d014482 (t : ℝ) : _root_.GD.N0230.N0564.d000052 _root_.GD.N0149.N0431.d014474 _root_.GD.N0149.N0431.d014476 id t id≤1 := by
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · rw [_root_.GD.N0149.N0431.d014480 id measurable_id ht]
    calc
      _ ≤ ∫⁻ _u, (1 : ℝ≥0∞) ∂_root_.GD.N0149.N0431.d014474 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        apply ENNReal.ofReal_le_one.mpr
        simpa only [id_eq,div_pow] using _root_.GD.N0001.d014473 hu ht
      _ = 1 := by simp
  · rw [_root_.GD.N0149.N0431.d014481 id measurable_id ht]
    exact bot_le

theorem d014483 : ∫⁻ t, _root_.GD.N0230.N0564.d000052 _root_.GD.N0149.N0431.d014474 _root_.GD.N0149.N0431.d014476 id t id ∂_root_.GD.N0149.N0431.d014475 ≠ ⊤ := by
  apply ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
  calc
    _ ≤ ∫⁻ _t, (1 : ℝ≥0∞) ∂_root_.GD.N0149.N0431.d014475 := lintegral_mono _root_.GD.N0149.N0431.d014482
    _ = 1 := by simp

theorem d014484 :
    ∀ᵐ u ∂_root_.GD.N0149.N0431.d014474, ∫ t, (u-t)*(_root_.GD.N0149.N0431.d014476 t u : ℝ) ∂_root_.GD.N0149.N0431.d014475=0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  calc
    _ = ∫ t, (u-t)/_root_.GD.N0001.d014462 u t^2 ∂_root_.GD.N0149.N0431.d014475 := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 (1/2) (1/2)] with t ht
      rw [_root_.GD.N0149.N0431.d014478 ht]
      ring
    _ = 0 := _root_.GD.N0001.d014472 hu

theorem d014485 : ∀ᵐ u ∂_root_.GD.N0149.N0431.d014474, 0<∫⁻ t, (_root_.GD.N0149.N0431.d014476 t u : ℝ≥0∞) ∂_root_.GD.N0149.N0431.d014475 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm : Measurable (fun t => (_root_.GD.N0149.N0431.d014476 t u : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (_root_.GD.N0149.N0431.d014477.comp (measurable_id.prodMk measurable_const))
  have hae := (lintegral_eq_zero_iff hm).mp hz
  have ht : ∀ᵐ t ∂_root_.GD.N0149.N0431.d014475, t ∈ Ioo (0 : ℝ) 1 := _root_.GD.N0232.N0720.N1092.d013031 (1/2) (1/2)
  obtain ⟨t,ht,hzero⟩ := (ht.and hae).exists
  have hp : 0<(_root_.GD.N0149.N0431.d014476 t u : ℝ≥0∞) := by
    rw [_root_.GD.N0149.N0431.d014476,if_pos ht]
    change 0<ENNReal.ofReal (1/_root_.GD.N0001.d014462 u t^2)
    exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (sq_pos_of_pos (_root_.GD.N0001.d014466 hu ht)))
  exact hp.ne' hzero

theorem d014486 (H : ℝ → ℝ) (hH : Measurable H)
    (hdom : ∀ t ∈ Ioo (0 : ℝ) 1, _root_.GD.N0149.N0431.d014479 H t≤_root_.GD.N0149.N0431.d014479 id t) :
    H =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] id := by
  apply _root_.GD.N0230.N0564.d000056 (π := _root_.GD.N0149.N0431.d014475)
    _root_.GD.N0149.N0431.d014477 measurable_id measurable_id hH
    _root_.GD.N0149.N0431.d014484 _root_.GD.N0149.N0431.d014483 _root_.GD.N0149.N0431.d014485
  intro t
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · rw [_root_.GD.N0149.N0431.d014480 H hH ht,_root_.GD.N0149.N0431.d014480 id measurable_id ht]
    exact hdom t ht
  · rw [_root_.GD.N0149.N0431.d014481 H hH ht,_root_.GD.N0149.N0431.d014481 id measurable_id ht]

end
end GD.N0149.N0431

#print axioms _root_.GD.N0149.N0431.d014484
#print axioms _root_.GD.N0149.N0431.d014483
#print axioms _root_.GD.N0149.N0431.d014485
#print axioms _root_.GD.N0149.N0431.d014486
