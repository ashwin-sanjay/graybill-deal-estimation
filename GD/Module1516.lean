import GD.Module1515
import GD.Module0877
import Mathlib.MeasureTheory.Measure.Regular

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0024.N0281

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0024.N0277 _root_.GD.N0024.N0280

instance d023600 : IsFiniteMeasureOnCompacts _root_.GD.N0232.N0720.N1436.d013288 := by
  unfold _root_.GD.N0232.N0720.N1436.d013288
  infer_instance

def d023601 (t : _root_.GD.N0024.N0277.d007878) : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0232.N0720.N1436.d013289 6 6 t.1

instance d023602 (t : _root_.GD.N0024.N0277.d007878) : IsProbabilityMeasure (_root_.GD.N0024.N0281.d023601 t) :=
  _root_.GD.N0232.N0720.N1434.d013564 (by norm_num) (by norm_num) t.2.1 t.2.2

theorem d023603 (t : _root_.GD.N0024.N0277.d007878) :
    _root_.GD.N0024.N0281.d023601 t ≪ _root_.GD.N0232.N0720.N1436.d013288 :=
  _root_.GD.N0232.N0720.N1436.d013290 6 6 t.1

theorem d023604
    (E : Set _root_.GD.N0232.N0720.N1436.d013217) (hE : MeasurableSet E)
    (hED : E ⊆ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0024.N0277.d007878) :
    (_root_.GD.N0024.N0281.d023601 t).real E / _root_.GD.N0024.N0277.d007879 t =
      ∫ z in E, _root_.GD.N0024.N0280.d023591 (t.1, z) ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  have hid := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := _root_.GD.N0232.N0720.N1436.d013288)
    (_root_.GD.N0232.N0720.N1436.d013279 6 6 t.1).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (fun _ : _root_.GD.N0232.N0720.N1436.d013217 => (1 : ℝ)) hE
  have hmass : (_root_.GD.N0024.N0281.d023601 t).real E =
      ∫ z in E, _root_.GD.N0232.N0720.N1436.d013273 6 6 t.1 z ∂_root_.GD.N0232.N0720.N1436.d013288 := by
    have heq : (∫ z in E, (ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 6 6 t.1 z)).toReal • (1 : ℝ)
        ∂_root_.GD.N0232.N0720.N1436.d013288) =
        ∫ z in E, _root_.GD.N0232.N0720.N1436.d013273 6 6 t.1 z ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hE] with z hz
      rw [ENNReal.toReal_ofReal
        (_root_.GD.N0232.N0720.N1436.d013286 (by norm_num) (by norm_num) t.2.1 t.2.2 (hED hz)).le,
        smul_eq_mul, mul_one]
    simpa only [_root_.GD.N0024.N0281.d023601, _root_.GD.N0232.N0720.N1436.d013289, integral_const, measureReal_def,
      Measure.restrict_apply_univ, smul_eq_mul, mul_one] using hid.trans heq
  rw [hmass, ← integral_div]
  apply setIntegral_congr_fun hE
  intro z hz
  exact (_root_.GD.N0024.N0280.d023599 t z (hED hz)).symm

theorem d023605
    (K E : Set _root_.GD.N0232.N0720.N1436.d013217) (hK : IsCompact K)
    (hKD : K ⊆ _root_.GD.N0232.N0720.N1436.d013218) (hEK : E ⊆ K) (t : _root_.GD.N0024.N0277.d007878) :
    IntegrableOn (fun z => _root_.GD.N0024.N0280.d023591 (t.1, z)) E _root_.GD.N0232.N0720.N1436.d013288 := by
  have hc : ContinuousOn (fun z => _root_.GD.N0024.N0280.d023591 (t.1, z)) K :=
    _root_.GD.N0024.N0280.d023594.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨⟨t.2.1.le, t.2.2.le⟩, hKD hz⟩)
  exact (hc.integrableOn_compact hK).mono_set hEK

theorem d023606
    (K E : Set _root_.GD.N0232.N0720.N1436.d013217) (hK : IsCompact K)
    (hKD : K ⊆ _root_.GD.N0232.N0720.N1436.d013218) (hE : MeasurableSet E) (hEK : E ⊆ K)
    (hpos : 0 < _root_.GD.N0232.N0720.N1436.d013288 E)
    (d : ℝ) (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ M k : ℝ, 0 ≤ M ∧ 0 < k ∧
      (∀ t : _root_.GD.N0024.N0277.d007878, (_root_.GD.N0024.N0281.d023601 t).real E / _root_.GD.N0024.N0277.d007879 t ≤ M) ∧
      (∀ t : _root_.GD.N0024.N0277.d007878, d ≤ t.1 → t.1 ≤ 1 - d →
        k ≤ (_root_.GD.N0024.N0281.d023601 t).real E / _root_.GD.N0024.N0277.d007879 t) := by
  have hKne : K.Nonempty := (nonempty_of_measure_ne_zero hpos.ne').mono hEK
  have hfinite : _root_.GD.N0232.N0720.N1436.d013288 E ≠ ⊤ :=
    ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono hEK)
  have hp : 0 < _root_.GD.N0232.N0720.N1436.d013288.real E :=
    ENNReal.toReal_pos hpos.ne' hfinite
  exact _root_.GD.N0024.N0266.d007897
    _root_.GD.N0232.N0720.N1436.d013288 _root_.GD.N0024.N0281.d023601 K E hK hKne hE hEK hfinite hp _root_.GD.N0024.N0280.d023591
    (_root_.GD.N0024.N0280.d023594.mono (fun p hp => ⟨hp.1, hKD hp.2⟩))
    (fun t ht z hz => _root_.GD.N0024.N0280.d023595 t ht z (hKD hz))
    (_root_.GD.N0024.N0281.d023605 K E hK hKD hEK)
    (_root_.GD.N0024.N0281.d023604 E hE (hEK.trans hKD)) d hd hdhalf

theorem d023607
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (d V : ℝ) (hd : 0 < d)
    (hcap : ∀ t : _root_.GD.N0024.N0277.d007878, _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0281.d023601 g t ≤ V) :
    ∃ E : Set _root_.GD.N0232.N0720.N1436.d013217, IsCompact E ∧ MeasurableSet E ∧
      E ⊆ _root_.GD.N0232.N0720.N1436.d013218 ∧ (∀ z ∈ E, g z < d) ∧
      0 < _root_.GD.N0232.N0720.N1436.d013288 E := by
  let t₀ : _root_.GD.N0024.N0277.d007878 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hQ : ∀ t : _root_.GD.N0024.N0277.d007878, _root_.GD.N0024.N0281.d023601 t ≪ _root_.GD.N0024.N0281.d023601 t₀ := by
    intro t
    exact _root_.GD.N0232.N0720.N1436.d013292
      (by norm_num) (by norm_num) t.2.1 t.2.2 t₀.2.1 t₀.2.2
  have hlower := _root_.GD.N0024.N0277.d007894 _root_.GD.N0024.N0281.d023601 (_root_.GD.N0024.N0281.d023601 t₀) hQ g hg hb d V hd hcap
  have hdomain : ∀ᵐ z ∂_root_.GD.N0024.N0281.d023601 t₀, z ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    (_root_.GD.N0024.N0281.d023603 t₀).ae_le (ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219)
  have heq : (_root_.GD.N0024.N0281.d023601 t₀) ({z | g z < d} ∩ _root_.GD.N0232.N0720.N1436.d013218) = (_root_.GD.N0024.N0281.d023601 t₀) {z | g z < d} := by
    apply measure_congr
    filter_upwards [hdomain] with z hz
    apply propext
    change (g z < d ∧ z ∈ _root_.GD.N0232.N0720.N1436.d013218) ↔ g z < d
    exact and_iff_left hz
  have hinter : MeasurableSet ({z | g z < d} ∩ _root_.GD.N0232.N0720.N1436.d013218) :=
    (measurableSet_lt hg measurable_const).inter _root_.GD.N0232.N0720.N1436.d013219
  have hpos : 0 < (_root_.GD.N0024.N0281.d023601 t₀) ({z | g z < d} ∩ _root_.GD.N0232.N0720.N1436.d013218) := heq ▸ hlower
  obtain ⟨E, hEsub, hEc, hEpos⟩ :=
    hinter.exists_lt_isCompact_of_ne_top (measure_ne_top (_root_.GD.N0024.N0281.d023601 t₀) _) hpos
  have hposRef : 0 < _root_.GD.N0232.N0720.N1436.d013288 E := by
    by_contra hnot
    have hzero : _root_.GD.N0232.N0720.N1436.d013288 E = 0 := le_antisymm (not_lt.mp hnot) bot_le
    have hz := _root_.GD.N0024.N0281.d023603 t₀ hzero
    exact hEpos.ne' hz
  refine ⟨E, hEc, hEc.measurableSet, hEsub.trans inter_subset_right, ?_, hposRef⟩
  intro z hz
  exact (hEsub hz).1

theorem d023608
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (d V h : ℝ) (hd : 0 < d) (hdhalf : d < 1 / 2) (hh : 0 < h)
    (hcap : ∀ t : _root_.GD.N0024.N0277.d007878, _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0281.d023601 g t ≤ V)
    (hslack : ∀ t : _root_.GD.N0024.N0277.d007878,
      t.1 < d ∨ 1 - d < t.1 → _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0281.d023601 g t ≤ V - h)
    (hminimax : ∀ f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable f →
      (∀ z, f z ∈ Icc (0 : ℝ) 1) →
      ∀ ε : ℝ, 0 < ε → ∃ t, V - ε < _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0281.d023601 f t) : False := by
  obtain ⟨E, hEc, hE, hED, hlow, hpos⟩ :=
    _root_.GD.N0024.N0281.d023607 g hg hb (d / 2) V (by positivity) hcap
  obtain ⟨M, k, hM, hk, hupper, hlower⟩ :=
    _root_.GD.N0024.N0281.d023606 E E hEc hED hE (Subset.refl E) hpos d hd hdhalf
  exact _root_.GD.N0024.N0277.d007896 _root_.GD.N0024.N0281.d023601 E hE g hg hb d V h k M hd
    (by linarith) hh hk hM (fun z hz => (hlow z hz).le)
    hcap hslack hupper hlower hminimax

#print axioms _root_.GD.N0024.N0281.d023602
#print axioms _root_.GD.N0024.N0281.d023600
#print axioms _root_.GD.N0024.N0281.d023603
#print axioms _root_.GD.N0024.N0281.d023604
#print axioms _root_.GD.N0024.N0281.d023605
#print axioms _root_.GD.N0024.N0281.d023606
#print axioms _root_.GD.N0024.N0281.d023607
#print axioms _root_.GD.N0024.N0281.d023608

end
end GD.N0024.N0281
