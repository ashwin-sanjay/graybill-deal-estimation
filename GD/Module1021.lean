import GD.Module1020
import GD.Module0170

set_option warningAsError true
set_option autoImplicit false
set_option linter.unusedSectionVars false










open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GD.N0232.N0720.N1237

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1240 _root_.GD.N0232.N0720.N1229
open _root_.GD.N0232.N0720.N1241
open _root_.GD.N0232.N0720.N1236 _root_.GD.N0232.N0720.N1235 _root_.GD.N0232.N0720.N1232

variable {ι : Type*} [Fintype ι]

def d016241 (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  _root_.GD.N0232.N0720.N1436.d013273 2 2 t

theorem d016242 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    ∀ᵐ z ∂_root_.GD.N0232.N0720.N1436.d013288, 0 < _root_.GD.N0232.N0720.N1237.d016241 t z := by
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with z hz
  exact _root_.GD.N0232.N0720.N1436.d013286 (by norm_num) (by norm_num)
    t.property.1 t.property.2 hz

theorem d016243 (t : _root_.GD.N0232.N0720.N1441.d013676) (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ z, f z ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 t) =
      ∫ z, _root_.GD.N0232.N0720.N1237.d016241 t z * f z ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  unfold _root_.GD.N0232.N0720.N1441.d013678 _root_.GD.N0232.N0720.N1436.d013289
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0720.N1436.d013279 2 2 t).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1237.d016242 t] with z hz
  change (ENNReal.ofReal (_root_.GD.N0232.N0720.N1237.d016241 t z)).toReal • f z = _root_.GD.N0232.N0720.N1237.d016241 t z * f z
  rw [ENNReal.toReal_ofReal hz.le, smul_eq_mul]

theorem d016244 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    Integrable (fun z ↦ _root_.GD.N0232.N0720.N1237.d016241 t z * f z) _root_.GD.N0232.N0720.N1436.d013288 := by
  have hi := _root_.GD.N0232.N0720.N1434.d013559
    (m := 2) (n := 2) (by norm_num) (by norm_num)
    t.property.1 t.property.2 f hf hB
  have hi' := (integrable_withDensity_iff_integrable_smul₀'
    (μ := _root_.GD.N0232.N0720.N1436.d013288)
    (f := fun z ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t z))
    (_root_.GD.N0232.N0720.N1436.d013279 2 2 t).ennreal_ofReal.aemeasurable
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hi
  apply hi'.congr
  filter_upwards [_root_.GD.N0232.N0720.N1237.d016242 t] with z hz
  change (ENNReal.ofReal (_root_.GD.N0232.N0720.N1237.d016241 t z)).toReal • f z = _root_.GD.N0232.N0720.N1237.d016241 t z * f z
  rw [ENNReal.toReal_ofReal hz.le, smul_eq_mul]

theorem d016245 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (_root_.GD.N0232.N0720.N1237.d016241 t) _root_.GD.N0232.N0720.N1436.d013288 := by
  simpa using _root_.GD.N0232.N0720.N1237.d016244 t (fun _ ↦ 1) measurable_const
    (B := 1) (by intro _; norm_num)

def d016246 (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (3 / (2 * Real.pi)) *
    (z.1 ^ (-(1 / 2 : ℝ)) * (1 - z.1) ^ (-(1 / 2 : ℝ)) * z.2 ^ (1 / 2 : ℝ))

theorem d016247 (t : _root_.GD.N0232.N0720.N1441.d013676) {z : _root_.GD.N0232.N0720.N1436.d013217}
    (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1237.d016241 t z = _root_.GD.N0232.N0720.N1237.d016246 z * ((t : ℝ) * (1 - (t : ℝ))) ^ 2 *
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 t z.1 z.2) (-5 / 2) := by
  rw [_root_.GD.N0232.N0720.N1237.d016241, _root_.GD.N0232.N0720.N1236.d016218
    t.property hz.1 hz.2]
  have hQ : _root_.GD.N0232.N0720.N1242.d002130 t z.1 +
      _root_.GD.N0232.N0720.N1236.d016210 t * z.2 = _root_.GD.N0232.N0720.N1240.d002099 t z.1 z.2 := by
    unfold _root_.GD.N0232.N0720.N1242.d002130 _root_.GD.N0232.N0720.N1236.d016210 _root_.GD.N0232.N0720.N1240.d002099
    ring
  unfold _root_.GD.N0232.N0720.N1236.d016211
  rw [hQ]
  change _root_.GD.N0232.N0720.N1237.d016246 z * ((t : ℝ) * (1 - (t : ℝ))) ^ 2 *
    Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 t z.1 z.2) (-(5 / 2 : ℝ)) = _
  norm_num

theorem d016248 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676)
    (ha : ∀ i, 0 ≤ a i) (hpos : ∃ i, 0 < a i)
    {z : _root_.GD.N0232.N0720.N1436.d013217} (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    (∑ i, (a i * _root_.GD.N0232.N0720.N1237.d016241 (t i) z) * (t i : ℝ)) =
      _root_.GD.N0232.N0720.N1229.d013586 (_root_.GD.N0232.N0720.N1235.d016239 a t) z * ∑ i, a i * _root_.GD.N0232.N0720.N1237.d016241 (t i) z := by
  classical
  let K (i : ι) : ℝ := Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (t i) z.1 z.2) (-5 / 2)
  have hK (i : ι) : 0 < K i := by
    apply Real.rpow_pos_of_pos
    have heq : (_root_.GD.N0232.N0720.N1235.d016229 (t i) : ℝ) + 1 / 2 = (t i : ℝ) := by
      simp [_root_.GD.N0232.N0720.N1235.d016229]
    simpa only [heq] using _root_.GD.N0232.N0720.N1241.d013580 (_root_.GD.N0232.N0720.N1235.d016229 (t i)) hz
  have hden : 0 < ∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i * K i := by
    obtain ⟨i, hi⟩ := hpos
    exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (_root_.GD.N0232.N0720.N1235.d016231 a t ha j) (hK j).le)
      ⟨i, Finset.mem_univ i, mul_pos (_root_.GD.N0232.N0720.N1235.d016232 a t hi) (hK i)⟩
  have hp : _root_.GD.N0232.N0720.N1229.d013586 (_root_.GD.N0232.N0720.N1235.d016239 a t) z *
      (∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i * K i) =
        ∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i * (t i : ℝ) * K i := by
    rw [_root_.GD.N0232.N0720.N1235.d016240 a t ha hpos]
    exact div_mul_cancel₀ _ hden.ne'
  have hmass : (∑ i, a i * _root_.GD.N0232.N0720.N1237.d016241 (t i) z) =
      _root_.GD.N0232.N0720.N1237.d016246 z * ∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i * K i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.GD.N0232.N0720.N1237.d016247 (t i) hz]
    unfold _root_.GD.N0232.N0720.N1235.d016230 K
    ring
  have hmoment : (∑ i, (a i * _root_.GD.N0232.N0720.N1237.d016241 (t i) z) * (t i : ℝ)) =
      _root_.GD.N0232.N0720.N1237.d016246 z * ∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i * (t i : ℝ) * K i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.GD.N0232.N0720.N1237.d016247 (t i) hz]
    unfold _root_.GD.N0232.N0720.N1235.d016230 K
    ring
  rw [hmass, hmoment, ← hp]
  ring

theorem d016249
    (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676) (i₀ : ι)
    (ha : ∀ i, 0 ≤ a i) (ha₀ : a i₀ = 1) (ht₀ : t i₀ = _root_.GD.N0232.N0720.N1441.d013677)
    (h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hh : Measurable h)
    (hb : ∀ z, h z ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1229.d013591 h (_root_.GD.N0232.N0720.N1235.d016239 a t) ≤
      (∑ i, a i * ∫ z, (h z - (t i : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 (t i)) -
        (∑ i, a i * ∫ z,
          (_root_.GD.N0232.N0720.N1229.d013586 (_root_.GD.N0232.N0720.N1235.d016239 a t) z - (t i : ℝ)) ^ 2
            ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 (t i)) := by
  have hpos : ∃ i, 0 < a i := ⟨i₀, by rw [ha₀]; norm_num⟩
  have hpb : ∀ᵐ z ∂_root_.GD.N0232.N0720.N1436.d013288,
      _root_.GD.N0232.N0720.N1229.d013586 (_root_.GD.N0232.N0720.N1235.d016239 a t) z ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with z hz
    exact _root_.GD.N0232.N0720.N1241.d013581 (_root_.GD.N0232.N0720.N1235.d016239 a t) hz
  have hnorm : ∀ᵐ z ∂_root_.GD.N0232.N0720.N1436.d013288,
      (∑ i, (a i * _root_.GD.N0232.N0720.N1237.d016241 (t i) z) * (t i : ℝ)) =
        _root_.GD.N0232.N0720.N1229.d013586 (_root_.GD.N0232.N0720.N1235.d016239 a t) z * ∑ i, a i * _root_.GD.N0232.N0720.N1237.d016241 (t i) z := by
    filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with z hz
    exact _root_.GD.N0232.N0720.N1237.d016248 a t ha hpos hz
  have hmain := _root_.GD.N0232.N0720.N1232.d002007
    _root_.GD.N0232.N0720.N1436.d013288 (fun i ↦ _root_.GD.N0232.N0720.N1237.d016241 (t i)) a (fun i ↦ (t i : ℝ))
    h (_root_.GD.N0232.N0720.N1229.d013586 (_root_.GD.N0232.N0720.N1235.d016239 a t)) i₀ ha₀ ha
    (fun i ↦ _root_.GD.N0232.N0720.N1237.d016245 (t i))
    (fun i ↦ (_root_.GD.N0232.N0720.N1237.d016242 (t i)).mono fun _ hz ↦ hz.le)
    hh.aestronglyMeasurable (_root_.GD.N0232.N0720.N1229.d013587 _).aestronglyMeasurable
    (ae_of_all _ hb) hpb (fun i ↦ ⟨(t i).property.1.le, (t i).property.2.le⟩) hnorm
  simp_rw [← _root_.GD.N0232.N0720.N1237.d016243] at hmain
  rw [ht₀] at hmain
  exact hmain

end
end GD.N0232.N0720.N1237

#print axioms _root_.GD.N0232.N0720.N1237.d016248
#print axioms _root_.GD.N0232.N0720.N1237.d016249
