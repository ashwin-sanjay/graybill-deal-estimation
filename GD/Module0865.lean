import GD.Module0863
import Mathlib.MeasureTheory.Measure.OpenPos












open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1340

open _root_.GD.N0232.N0720.N1320 _root_.GD.N0232.N0720.N1344
open _root_.GD.N0232.N0720.N1290

noncomputable section
attribute [local instance] Measure.Subtype.measureSpace

theorem d013348 (q : ℝ) (hq : 3 / 2 ≤ q) : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂volume, 0 < _root_.GD.N0232.N0720.N1320.d013316 q x := by
  have hleft : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂volume, (x : ℝ) ≠ -1 := by
    exact (ae_restrict_iff_subtype measurableSet_Icc).1
      (((volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1)).ae_ne (-1))
  have hright : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂volume, (x : ℝ) ≠ 1 := by
    exact (ae_restrict_iff_subtype measurableSet_Icc).1
      (((volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1)).ae_ne 1)
  filter_upwards [hleft, hright] with x hl hr
  have hxl : -1 < (x : ℝ) := lt_of_le_of_ne x.2.1 hl.symm
  have hxr : (x : ℝ) < 1 := lt_of_le_of_ne x.2.2 hr
  exact mul_pos (inv_pos.mpr (_root_.GD.N0232.N0720.N1320.d013315 hq)) (_root_.GD.N0232.N0720.N1320.d013313 q ⟨hxl, hxr⟩)


theorem d013349 (q : ℝ) (hq : 3 / 2 ≤ q) :
    (volume : Measure _root_.GD.N0232.N0720.N1320.d013309) ≪ (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) := by
  apply withDensity_absolutelyContinuous'
    ((by unfold _root_.GD.N0232.N0720.N1320.d013316 _root_.GD.N0232.N0720.N1320.d013310; fun_prop : Measurable (_root_.GD.N0232.N0720.N1320.d013316 q)).ennreal_ofReal.aemeasurable)
  filter_upwards [_root_.GD.N0232.N0720.N1340.d013348 q hq] with x hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)



theorem d013350 (q : ℝ) (hq : 3 / 2 ≤ q) {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309), 0 ≤ f x) :
    ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ f x := by
  have hv : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂volume, 0 ≤ f x :=
    (_root_.GD.N0232.N0720.N1340.d013349 q hq).ae_le h
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

theorem d013351 (q : ℝ) (hq : 3 / 2 ≤ q) (center r : ℝ) (hr : 0 ≤ r) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1344.d013339 q hq center r, x ∈ Icc (center - r) (center + r) := by
  unfold _root_.GD.N0232.N0720.N1344.d013339
  apply (ae_map_iff
    (f := fun x : _root_.GD.N0232.N0720.N1320.d013309 ↦ center + r * (x : ℝ)) (μ := (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309))
    (p := fun x : ℝ ↦ x ∈ Icc (center - r) (center + r))
    ((by fun_prop : Measurable (fun x : _root_.GD.N0232.N0720.N1320.d013309 ↦ center + r * (x : ℝ))).aemeasurable)
    measurableSet_Icc).2
  filter_upwards with x
  constructor
  · have hx := mul_le_mul_of_nonneg_left x.2.1 hr
    linarith
  · have hx := mul_le_mul_of_nonneg_left x.2.2 hr
    linarith



theorem d013352 (q : ℝ) (hq : 3 / 2 ≤ q) {center r a b : ℝ}
    (h : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1344.d013339 q hq center r, x ∈ Icc a b) :
    a ≤ center - r ∧ center + r ≤ b := by
  have hm : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309),
      center + r * (x : ℝ) ∈ Icc a b :=
    ae_of_ae_map
      (f := fun x : _root_.GD.N0232.N0720.N1320.d013309 ↦ center + r * (x : ℝ))
      (μ := (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) (p := fun x : ℝ ↦ x ∈ Icc a b)
      ((by fun_prop : Measurable (fun x : _root_.GD.N0232.N0720.N1320.d013309 ↦ center + r * (x : ℝ))).aemeasurable) h
  have hl : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309),
      0 ≤ center + r * (x : ℝ) - a := hm.mono fun x hx ↦ sub_nonneg.mpr hx.1
  have hu : ∀ᵐ x : _root_.GD.N0232.N0720.N1320.d013309 ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309),
      0 ≤ b - (center + r * (x : ℝ)) := hm.mono fun x hx ↦ sub_nonneg.mpr hx.2
  have hlp := _root_.GD.N0232.N0720.N1340.d013350 q hq
    (f := fun x : ℝ ↦ center + r * x - a) (by fun_prop) hl
    (-1) (by norm_num)
  have hup := _root_.GD.N0232.N0720.N1340.d013350 q hq
    (f := fun x : ℝ ↦ b - (center + r * x)) (by fun_prop) hu
    1 (by norm_num)
  constructor <;> linarith




theorem d013353 (q : ℝ) (hq : 3 / 2 ≤ q) {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} {center r : ℝ}
    (hclass : Measure.map (fun x : _root_.GD.N0232.N0720.N1290.d004131 ↦ (x : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq center r) :
    0 ≤ center - r ∧ center + r ≤ 1 := by
  apply _root_.GD.N0232.N0720.N1340.d013352 q hq
  rw [← hclass, (MeasurableEmbedding.subtype_coe measurableSet_Icc).ae_map_iff]
  exact ae_of_all _ fun x ↦ x.2

theorem d013354 (q : ℝ) (hq : 3 / 2 ≤ q) {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} {center r : ℝ}
    (hr : 0 ≤ r)
    (hclass : Measure.map (fun x : _root_.GD.N0232.N0720.N1290.d004131 ↦ (x : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq center r) :
    ∀ᵐ x : _root_.GD.N0232.N0720.N1290.d004131 ∂mu, (x : ℝ) ∈ Icc (center - r) (center + r) := by
  have h := _root_.GD.N0232.N0720.N1340.d013351 q hq center r hr
  rw [← hclass, (MeasurableEmbedding.subtype_coe measurableSet_Icc).ae_map_iff] at h
  exact h


end
end GD.N0232.N0720.N1340

#print axioms _root_.GD.N0232.N0720.N1340.d013353
#print axioms _root_.GD.N0232.N0720.N1340.d013354
