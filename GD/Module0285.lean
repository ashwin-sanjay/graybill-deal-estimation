import GD.Module0283
import Mathlib.MeasureTheory.Measure.OpenPos













open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1359

open _root_.GD.N0232.N0720.N1353 _root_.GD.N0232.N0720.N1414
open _root_.GD.N0232.N0720.N1290

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

theorem d004239 : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂volume, 0 < _root_.GD.N0232.N0720.N1353.d004180 x := by
  have hleft : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂volume, (x : ℝ) ≠ -1 := by
    exact (ae_restrict_iff_subtype measurableSet_Icc).1
      (((volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1)).ae_ne (-1))
  have hright : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂volume, (x : ℝ) ≠ 1 := by
    exact (ae_restrict_iff_subtype measurableSet_Icc).1
      (((volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1)).ae_ne 1)
  filter_upwards [hleft, hright] with x hl hr
  have hxl : -1 < (x : ℝ) := lt_of_le_of_ne x.2.1 hl.symm
  have hxr : (x : ℝ) < 1 := lt_of_le_of_ne x.2.2 hr
  have hprod : 0 < (1 - (x : ℝ)) * ((x : ℝ) + 1) :=
    mul_pos (by linarith) (by linarith)
  unfold _root_.GD.N0232.N0720.N1353.d004180
  nlinarith


theorem d004240 :
    (volume : Measure _root_.GD.N0232.N0720.N1353.d004179) ≪ _root_.GD.N0232.N0720.N1353.d004182 := by
  apply withDensity_absolutelyContinuous'
    ((by unfold _root_.GD.N0232.N0720.N1353.d004180; fun_prop : Measurable _root_.GD.N0232.N0720.N1353.d004180).ennreal_ofReal.aemeasurable)
  filter_upwards [_root_.GD.N0232.N0720.N1359.d004239] with x hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)



theorem d004241 {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂_root_.GD.N0232.N0720.N1353.d004182, 0 ≤ f x) :
    ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x := by
  have hv : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂volume, 0 ≤ f x :=
    _root_.GD.N0232.N0720.N1359.d004240.ae_le h
  have hr : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1), 0 ≤ f x :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hv
  have heq : (fun x : ℝ ↦ max 0 (-f x)) =ᵐ[
      (volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1)] (fun _ ↦ 0) := by
    filter_upwards [hr] with x hx
    exact max_eq_left (neg_nonpos.mpr hx)
  have hpoint := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ)
    (by norm_num : (-1 : ℝ) ≠ 1) heq
    ((continuous_const.max hf.neg).continuousOn) continuous_const.continuousOn
  intro x hx
  have hmax := hpoint hx
  change max 0 (-f x) = 0 at hmax
  have hle := le_max_right (0 : ℝ) (-f x)
  rw [hmax] at hle
  linarith

theorem d004242 (center r : ℝ) (hr : 0 ≤ r) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1414.d004209 center r, x ∈ Icc (center - r) (center + r) := by
  unfold _root_.GD.N0232.N0720.N1414.d004209
  apply (ae_map_iff
    (f := fun x : _root_.GD.N0232.N0720.N1353.d004179 ↦ center + r * (x : ℝ)) (μ := _root_.GD.N0232.N0720.N1353.d004182)
    (p := fun x : ℝ ↦ x ∈ Icc (center - r) (center + r))
    ((by fun_prop : Measurable (fun x : _root_.GD.N0232.N0720.N1353.d004179 ↦ center + r * (x : ℝ))).aemeasurable)
    measurableSet_Icc).2
  filter_upwards with x
  constructor
  · have hx := mul_le_mul_of_nonneg_left x.2.1 hr
    linarith
  · have hx := mul_le_mul_of_nonneg_left x.2.2 hr
    linarith



theorem d004243 {center r a b : ℝ}
    (h : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1414.d004209 center r, x ∈ Icc a b) :
    a ≤ center - r ∧ center + r ≤ b := by
  have hm : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂_root_.GD.N0232.N0720.N1353.d004182,
      center + r * (x : ℝ) ∈ Icc a b :=
    ae_of_ae_map
      (f := fun x : _root_.GD.N0232.N0720.N1353.d004179 ↦ center + r * (x : ℝ))
      (μ := _root_.GD.N0232.N0720.N1353.d004182) (p := fun x : ℝ ↦ x ∈ Icc a b)
      ((by fun_prop : Measurable (fun x : _root_.GD.N0232.N0720.N1353.d004179 ↦ center + r * (x : ℝ))).aemeasurable) h
  have hl : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂_root_.GD.N0232.N0720.N1353.d004182,
      0 ≤ center + r * (x : ℝ) - a := hm.mono fun x hx ↦ sub_nonneg.mpr hx.1
  have hu : ∀ᵐ x : _root_.GD.N0232.N0720.N1353.d004179 ∂_root_.GD.N0232.N0720.N1353.d004182,
      0 ≤ b - (center + r * (x : ℝ)) := hm.mono fun x hx ↦ sub_nonneg.mpr hx.2
  have hlp := _root_.GD.N0232.N0720.N1359.d004241
    (f := fun x : ℝ ↦ center + r * x - a) (by fun_prop) hl
    (-1) (by norm_num)
  have hup := _root_.GD.N0232.N0720.N1359.d004241
    (f := fun x : ℝ ↦ b - (center + r * x)) (by fun_prop) hu
    1 (by norm_num)
  constructor <;> linarith




theorem d004244 {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} {center r : ℝ}
    (hclass : Measure.map (fun x : _root_.GD.N0232.N0720.N1290.d004131 ↦ (x : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 center r) :
    0 ≤ center - r ∧ center + r ≤ 1 := by
  apply _root_.GD.N0232.N0720.N1359.d004243
  rw [← hclass, (MeasurableEmbedding.subtype_coe measurableSet_Icc).ae_map_iff]
  exact ae_of_all _ fun x ↦ x.2

theorem d004245 {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} {center r : ℝ}
    (hr : 0 ≤ r)
    (hclass : Measure.map (fun x : _root_.GD.N0232.N0720.N1290.d004131 ↦ (x : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 center r) :
    ∀ᵐ x : _root_.GD.N0232.N0720.N1290.d004131 ∂mu, (x : ℝ) ∈ Icc (center - r) (center + r) := by
  have h := _root_.GD.N0232.N0720.N1359.d004242 center r hr
  rw [← hclass, (MeasurableEmbedding.subtype_coe measurableSet_Icc).ae_map_iff] at h
  exact h



theorem d004246 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : Continuous P) (hpos : ∀ t, 0 < P t)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] {a b : ℝ}
    (hs : ∀ᵐ t : _root_.GD.N0232.N0720.N1290.d004131 ∂mu, (t : ℝ) ∈ Icc a b) :
    _root_.GD.N0232.N0720.N1290.d004140 q P mu ∈ Icc a b := by
  have hK : Integrable (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (P t) ^ (-q)) mu := by
    simpa using _root_.GD.N0232.N0720.N1290.d004135 q (phi := fun _ ↦ 1)
      continuous_const hP hpos mu
  have hTK : Integrable (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ) * (P t) ^ (-q)) mu :=
    _root_.GD.N0232.N0720.N1290.d004135 q continuous_subtype_val hP hpos mu
  have hD := _root_.GD.N0232.N0720.N1290.d004146 q P hP hpos mu
  have hl : a * _root_.GD.N0232.N0720.N1290.d004139 q P mu ≤ ∫ t : _root_.GD.N0232.N0720.N1290.d004131, (t : ℝ) * (P t) ^ (-q) ∂mu := by
    rw [_root_.GD.N0232.N0720.N1290.d004139, ← integral_const_mul]
    apply integral_mono_ae (hK.const_mul a) hTK
    filter_upwards [hs] with t ht
    exact mul_le_mul_of_nonneg_right ht.1 (Real.rpow_pos_of_pos (hpos t) _).le
  have hu : (∫ t : _root_.GD.N0232.N0720.N1290.d004131, (t : ℝ) * (P t) ^ (-q) ∂mu) ≤ b * _root_.GD.N0232.N0720.N1290.d004139 q P mu := by
    rw [_root_.GD.N0232.N0720.N1290.d004139, ← integral_const_mul]
    apply integral_mono_ae hTK (hK.const_mul b)
    filter_upwards [hs] with t ht
    exact mul_le_mul_of_nonneg_right ht.2 (Real.rpow_pos_of_pos (hpos t) _).le
  exact ⟨(le_div_iff₀ hD).2 hl, (div_le_iff₀ hD).2 hu⟩

end
end GD.N0232.N0720.N1359

#print axioms _root_.GD.N0232.N0720.N1359.d004244
#print axioms _root_.GD.N0232.N0720.N1359.d004246
