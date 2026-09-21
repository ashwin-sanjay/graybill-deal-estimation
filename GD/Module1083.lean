import GD.Module1040
import GD.Module1000
import Mathlib.MeasureTheory.Measure.OpenPos






































open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0720
namespace N1485

noncomputable section

open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1111



attribute [local instance] Measure.Subtype.measureSpace





def d017328 : Measure (Set.Ioo (0 : ℝ) 1) :=
  volume



noncomputable instance d017329 :
    IsFiniteMeasure _root_.GD.N0232.N0720.N1485.d017328 := by
  refine ⟨?_⟩
  rw [_root_.GD.N0232.N0720.N1485.d017328,
    Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]
  simp [Real.volume_Ioo]

noncomputable local instance d017330 :
    IsLocallyFiniteMeasure (volume : Measure (Set.Ioi (0 : ℝ))) := by
  refine ⟨fun q ↦ ?_⟩
  let U : Set (Set.Ioi (0 : ℝ)) :=
    ((↑) : Set.Ioi (0 : ℝ) → ℝ) ⁻¹' Set.Ioo 0 ((q : ℝ) + 1)
  refine ⟨U, ?_, ?_⟩
  · exact (isOpen_Ioo.preimage continuous_subtype_val).mem_nhds
      ⟨q.property, lt_add_one (q : ℝ)⟩
  · rw [volume_preimage_coe
      measurableSet_Ioi.nullMeasurableSet measurableSet_Ioo]
    have hsubset :
        Set.Ioo (0 : ℝ) ((q : ℝ) + 1) ∩ Set.Ioi 0 ⊆
          Set.Icc 0 ((q : ℝ) + 1) := by
      intro x hx
      exact ⟨hx.1.1.le, hx.1.2.le⟩
    exact (measure_mono hsubset).trans_lt (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top)



@[fun_prop]
theorem d017331 :
    Continuous _root_.GD.N0232.N0720.N1486.d015857 := by
  unfold _root_.GD.N0232.N0720.N1486.d015857
  apply Continuous.rpow_const continuous_subtype_val
  intro q
  exact Or.inl q.property.ne'

noncomputable local instance d017332 :
    IsLocallyFiniteMeasure _root_.GD.N0232.N0720.N1486.d015866 := by
  unfold _root_.GD.N0232.N0720.N1486.d015866 _root_.GD.N0232.N0720.N1486.d015860
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    _root_.GD.N0232.N0720.N1485.d017331

noncomputable local instance d017333 :
    (volume : Measure (Set.Ioi (0 : ℝ))).IsOpenPosMeasure := by
  exact Measure.IsOpenPosMeasure.comap
    (volume : Measure ℝ) isOpen_Ioi.isOpenEmbedding_subtypeVal

noncomputable local instance d017334 :
    _root_.GD.N0232.N0720.N1485.d017328.IsOpenPosMeasure := by
  unfold _root_.GD.N0232.N0720.N1485.d017328
  exact Measure.IsOpenPosMeasure.comap
    (volume : Measure ℝ) isOpen_Ioo.isOpenEmbedding_subtypeVal



noncomputable local instance d017335 :
    _root_.GD.N0232.N0720.N1486.d015866.IsOpenPosMeasure := by
  apply (withDensity_absolutelyContinuous'
    _root_.GD.N0232.N0720.N1486.d015863.aemeasurable ?_).isOpenPosMeasure
  exact Filter.Eventually.of_forall fun q ↦
    (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1486.d015864 q)).ne'





def d017336 (k : ℕ) : ℝ :=
  (k : ℝ) + 2

theorem d017337 (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1485.d017336 k := by
  unfold _root_.GD.N0232.N0720.N1485.d017336
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem d017338 :
    Monotone _root_.GD.N0232.N0720.N1485.d017336 := by
  intro j k hjk
  change (j : ℝ) + 2 ≤ (k : ℝ) + 2
  calc
    (j : ℝ) + 2 = 2 + (j : ℝ) := add_comm _ _
    _ ≤ 2 + (k : ℝ) := add_le_add_right (Nat.cast_le.mpr hjk) 2
    _ = (k : ℝ) + 2 := add_comm _ _


def d017339 (k : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨(_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹, inv_pos.mpr (_root_.GD.N0232.N0720.N1485.d017337 k)⟩


def d017340 (k : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨_root_.GD.N0232.N0720.N1485.d017336 k, _root_.GD.N0232.N0720.N1485.d017337 k⟩


def d017341 (k : ℕ) : Set ℝ :=
  Set.Icc (-_root_.GD.N0232.N0720.N1485.d017336 k) (_root_.GD.N0232.N0720.N1485.d017336 k)


def d017342 (k : ℕ) : Set (Set.Ioi (0 : ℝ)) :=
  Set.Icc (_root_.GD.N0232.N0720.N1485.d017339 k) (_root_.GD.N0232.N0720.N1485.d017340 k)



def d017343 (k : ℕ) : Set _root_.GD.N0232.N0720.N1486.d015856 :=
  _root_.GD.N0232.N0720.N1485.d017341 k ×ˢ (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ Set.univ)

theorem d017344 (k : ℕ) :
    MeasurableSet (_root_.GD.N0232.N0720.N1485.d017343 k) := by
  exact measurableSet_Icc.prod
    (measurableSet_Icc.prod MeasurableSet.univ)

theorem d017345 :
    Antitone _root_.GD.N0232.N0720.N1485.d017339 := by
  intro j k hjk
  change (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ ≤ (_root_.GD.N0232.N0720.N1485.d017336 j)⁻¹
  exact (inv_le_inv₀
    (_root_.GD.N0232.N0720.N1485.d017337 k) (_root_.GD.N0232.N0720.N1485.d017337 j)).2
      (_root_.GD.N0232.N0720.N1485.d017338 hjk)

theorem d017346 :
    Monotone _root_.GD.N0232.N0720.N1485.d017340 := by
  intro j k hjk
  change _root_.GD.N0232.N0720.N1485.d017336 j ≤ _root_.GD.N0232.N0720.N1485.d017336 k
  exact _root_.GD.N0232.N0720.N1485.d017338 hjk

theorem d017347 :
    Monotone _root_.GD.N0232.N0720.N1485.d017341 := by
  intro j k hjk x hx
  constructor
  · exact (neg_le_neg (_root_.GD.N0232.N0720.N1485.d017338 hjk)).trans hx.1
  · exact hx.2.trans (_root_.GD.N0232.N0720.N1485.d017338 hjk)

theorem d017348 :
    Monotone _root_.GD.N0232.N0720.N1485.d017342 :=
  _root_.GD.N0232.N0720.N1485.d017345.Icc _root_.GD.N0232.N0720.N1485.d017346

theorem d017349 :
    Monotone _root_.GD.N0232.N0720.N1485.d017343 := by
  intro j k hjk theta htheta
  exact ⟨_root_.GD.N0232.N0720.N1485.d017347 hjk htheta.1,
    ⟨_root_.GD.N0232.N0720.N1485.d017348 hjk htheta.2.1,
      Set.mem_univ theta.2.2⟩⟩



theorem d017350 :
    (⋃ k : ℕ, _root_.GD.N0232.N0720.N1485.d017343 k) =
      (Set.univ : Set _root_.GD.N0232.N0720.N1486.d015856) := by
  apply Set.eq_univ_of_forall
  intro theta
  rw [Set.mem_iUnion]
  let b : ℝ :=
    max |theta.1|
      (max (theta.2.1 : ℝ) ((theta.2.1 : ℝ)⁻¹))
  obtain ⟨k, hk⟩ := exists_nat_gt b
  have hkRadius : (k : ℝ) < _root_.GD.N0232.N0720.N1485.d017336 k := by
    simp [_root_.GD.N0232.N0720.N1485.d017336]
  have habsRadius : |theta.1| < _root_.GD.N0232.N0720.N1485.d017336 k :=
    (le_max_left _ _).trans_lt (hk.trans hkRadius)
  have hqRadius : (theta.2.1 : ℝ) < _root_.GD.N0232.N0720.N1485.d017336 k :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt
      (hk.trans hkRadius)
  have hqInvRadius : (theta.2.1 : ℝ)⁻¹ < _root_.GD.N0232.N0720.N1485.d017336 k :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt
      (hk.trans hkRadius)
  have hlocation : theta.1 ∈ _root_.GD.N0232.N0720.N1485.d017341 k := by
    constructor
    · exact (neg_le_neg habsRadius.le).trans (neg_abs_le theta.1)
    · exact (le_abs_self theta.1).trans habsRadius.le
  have hvarianceLower :
      (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ < (theta.2.1 : ℝ) := by
    have h := (inv_lt_inv₀ (_root_.GD.N0232.N0720.N1485.d017337 k)
      (inv_pos.mpr theta.2.1.property)).2 hqInvRadius
    simpa using h
  have hvariance : theta.2.1 ∈ _root_.GD.N0232.N0720.N1485.d017342 k := by
    constructor
    · change (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ ≤ (theta.2.1 : ℝ)
      exact hvarianceLower.le
    · change (theta.2.1 : ℝ) ≤ _root_.GD.N0232.N0720.N1485.d017336 k
      exact hqRadius.le
  exact ⟨k, ⟨hlocation, ⟨hvariance, Set.mem_univ theta.2.2⟩⟩⟩



theorem d017351 (k : ℕ) :
    1 < _root_.GD.N0232.N0720.N1485.d017336 k := by
  unfold _root_.GD.N0232.N0720.N1485.d017336
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith


def d017352 (k : ℕ) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹,
    inv_pos.mpr (_root_.GD.N0232.N0720.N1485.d017337 k),
    inv_lt_one_of_one_lt₀ (_root_.GD.N0232.N0720.N1485.d017351 k)⟩


def d017353 (k : ℕ) : Set.Ioo (0 : ℝ) 1 :=
  ⟨1 - (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹,
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (_root_.GD.N0232.N0720.N1485.d017351 k)),
    sub_lt_self 1 (inv_pos.mpr (_root_.GD.N0232.N0720.N1485.d017337 k))⟩


def d017354 (k : ℕ) : Set (Set.Ioo (0 : ℝ) 1) :=
  Set.Icc (_root_.GD.N0232.N0720.N1485.d017352 k) (_root_.GD.N0232.N0720.N1485.d017353 k)

theorem d017355 :
    Antitone _root_.GD.N0232.N0720.N1485.d017352 := by
  intro j k hjk
  change (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ ≤ (_root_.GD.N0232.N0720.N1485.d017336 j)⁻¹
  exact _root_.GD.N0232.N0720.N1485.d017345 hjk

theorem d017356 :
    Monotone _root_.GD.N0232.N0720.N1485.d017353 := by
  intro j k hjk
  have h := _root_.GD.N0232.N0720.N1485.d017355 hjk
  change (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ ≤
    (_root_.GD.N0232.N0720.N1485.d017336 j)⁻¹ at h
  change 1 - (_root_.GD.N0232.N0720.N1485.d017336 j)⁻¹ ≤
    1 - (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹
  exact sub_le_sub_left h 1

theorem d017357 :
    Monotone _root_.GD.N0232.N0720.N1485.d017354 :=
  _root_.GD.N0232.N0720.N1485.d017355.Icc _root_.GD.N0232.N0720.N1485.d017356

theorem d017358 :
    (⋃ k : ℕ, _root_.GD.N0232.N0720.N1485.d017354 k) =
      (Set.univ : Set (Set.Ioo (0 : ℝ) 1)) := by
  apply Set.eq_univ_of_forall
  intro z
  rw [Set.mem_iUnion]
  let b : ℝ := max ((z : ℝ)⁻¹) ((1 - (z : ℝ))⁻¹)
  obtain ⟨k, hk⟩ := exists_nat_gt b
  have hkRadius : (k : ℝ) < _root_.GD.N0232.N0720.N1485.d017336 k := by
    simp [_root_.GD.N0232.N0720.N1485.d017336]
  have hzInvRadius : (z : ℝ)⁻¹ < _root_.GD.N0232.N0720.N1485.d017336 k :=
    (le_max_left _ _).trans_lt (hk.trans hkRadius)
  have honeSubInvRadius : (1 - (z : ℝ))⁻¹ < _root_.GD.N0232.N0720.N1485.d017336 k :=
    (le_max_right _ _).trans_lt (hk.trans hkRadius)
  have hlower : (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ < (z : ℝ) := by
    have h := (inv_lt_inv₀ (_root_.GD.N0232.N0720.N1485.d017337 k)
      (inv_pos.mpr z.property.1)).2 hzInvRadius
    simpa using h
  have hupper : (z : ℝ) < 1 - (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ := by
    have honeSubPos : 0 < 1 - (z : ℝ) := sub_pos.mpr z.property.2
    have h := (inv_lt_inv₀ (_root_.GD.N0232.N0720.N1485.d017337 k)
      (inv_pos.mpr honeSubPos)).2 honeSubInvRadius
    have h' : (_root_.GD.N0232.N0720.N1485.d017336 k)⁻¹ < 1 - (z : ℝ) := by
      simpa using h
    linarith
  exact ⟨k, ⟨hlower.le, hupper.le⟩⟩


def d017359 (k : ℕ) : Set _root_.GD.N0232.N0720.N1486.d015856 :=
  _root_.GD.N0232.N0720.N1485.d017341 k ×ˢ
    (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ _root_.GD.N0232.N0720.N1485.d017354 k)

theorem d017360 (k : ℕ) :
    MeasurableSet (_root_.GD.N0232.N0720.N1485.d017359 k) := by
  exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem d017361 :
    Monotone _root_.GD.N0232.N0720.N1485.d017359 := by
  intro j k hjk theta htheta
  exact ⟨_root_.GD.N0232.N0720.N1485.d017347 hjk htheta.1,
    ⟨_root_.GD.N0232.N0720.N1485.d017348 hjk htheta.2.1,
      _root_.GD.N0232.N0720.N1485.d017357 hjk htheta.2.2⟩⟩


theorem d017362 :
    (⋃ k : ℕ, _root_.GD.N0232.N0720.N1485.d017359 k) =
      (Set.univ : Set _root_.GD.N0232.N0720.N1486.d015856) := by
  apply Set.eq_univ_of_forall
  intro theta
  have horbit : theta ∈ ⋃ k : ℕ, _root_.GD.N0232.N0720.N1485.d017343 k := by
    rw [_root_.GD.N0232.N0720.N1485.d017350]
    exact Set.mem_univ theta
  have hz : theta.2.2 ∈ ⋃ k : ℕ, _root_.GD.N0232.N0720.N1485.d017354 k := by
    rw [_root_.GD.N0232.N0720.N1485.d017358]
    exact Set.mem_univ theta.2.2
  rw [Set.mem_iUnion] at horbit hz ⊢
  rcases horbit with ⟨j, hj⟩
  rcases hz with ⟨k, hk⟩
  refine ⟨max j k, ?_⟩
  exact ⟨_root_.GD.N0232.N0720.N1485.d017347 (Nat.le_max_left _ _) hj.1,
    ⟨_root_.GD.N0232.N0720.N1485.d017348 (Nat.le_max_left _ _) hj.2.1,
      _root_.GD.N0232.N0720.N1485.d017357 (Nat.le_max_right _ _) hk⟩⟩




def d017363 :
    Measure _root_.GD.N0232.N0720.N1486.d015856 :=
  _root_.GD.N0232.N0720.N1486.d015870 _root_.GD.N0232.N0720.N1485.d017328


def d017364 (k : ℕ) :
    Measure _root_.GD.N0232.N0720.N1486.d015856 :=
  _root_.GD.N0232.N0720.N1485.d017363.restrict (_root_.GD.N0232.N0720.N1485.d017343 k)



theorem d017365 (k : ℕ) :
    _root_.GD.N0232.N0720.N1485.d017364 k =
      (volume.restrict (_root_.GD.N0232.N0720.N1485.d017341 k)).prod
        ((_root_.GD.N0232.N0720.N1486.d015866.restrict (_root_.GD.N0232.N0720.N1485.d017342 k)).prod
          _root_.GD.N0232.N0720.N1485.d017328) := by
  unfold _root_.GD.N0232.N0720.N1485.d017364 _root_.GD.N0232.N0720.N1485.d017363
    _root_.GD.N0232.N0720.N1486.d015870 _root_.GD.N0232.N0720.N1485.d017343
  calc
    (volume.prod (_root_.GD.N0232.N0720.N1486.d015866.prod _root_.GD.N0232.N0720.N1485.d017328)).restrict
          (_root_.GD.N0232.N0720.N1485.d017341 k ×ˢ
            (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ Set.univ)) =
        (volume.restrict (_root_.GD.N0232.N0720.N1485.d017341 k)).prod
          ((_root_.GD.N0232.N0720.N1486.d015866.prod _root_.GD.N0232.N0720.N1485.d017328).restrict
            (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ Set.univ)) :=
      (Measure.prod_restrict
        (_root_.GD.N0232.N0720.N1485.d017341 k)
        (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ Set.univ)).symm
    _ = (volume.restrict (_root_.GD.N0232.N0720.N1485.d017341 k)).prod
          ((_root_.GD.N0232.N0720.N1486.d015866.restrict (_root_.GD.N0232.N0720.N1485.d017342 k)).prod
            _root_.GD.N0232.N0720.N1485.d017328) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]



noncomputable instance d017366 (k : ℕ) :
    IsFiniteMeasure
      (_root_.GD.N0232.N0720.N1486.d015866.restrict (_root_.GD.N0232.N0720.N1485.d017342 k)) := by
  rw [isFiniteMeasure_restrict]
  have hcompact : IsCompact (_root_.GD.N0232.N0720.N1485.d017342 k) := by
    rw [Subtype.isCompact_iff]
    have himage :
        ((↑) '' _root_.GD.N0232.N0720.N1485.d017342 k : Set ℝ) =
          Set.Icc ((_root_.GD.N0232.N0720.N1485.d017339 k : Set.Ioi (0 : ℝ)) : ℝ)
            ((_root_.GD.N0232.N0720.N1485.d017340 k : Set.Ioi (0 : ℝ)) : ℝ) := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hx
        have hxpos : 0 < x :=
          (_root_.GD.N0232.N0720.N1485.d017339 k).property.trans_le hx.1
        exact ⟨⟨x, hxpos⟩, hx, rfl⟩
    rw [himage]
    exact isCompact_Icc
  exact hcompact.measure_ne_top


noncomputable instance d017367 (k : ℕ) :
    IsFiniteMeasure (volume.restrict (_root_.GD.N0232.N0720.N1485.d017341 k)) := by
  rw [isFiniteMeasure_restrict]
  exact measure_Icc_lt_top.ne


noncomputable instance d017368 (k : ℕ) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1485.d017364 k) := by
  rw [_root_.GD.N0232.N0720.N1485.d017365]
  infer_instance

theorem d017369
    (k : ℕ) {s : Set _root_.GD.N0232.N0720.N1486.d015856}
    (hs : MeasurableSet s) :
    _root_.GD.N0232.N0720.N1485.d017364 k s =
      _root_.GD.N0232.N0720.N1485.d017363 (s ∩ _root_.GD.N0232.N0720.N1485.d017343 k) := by
  exact Measure.restrict_apply hs

theorem d017370 :
    Monotone _root_.GD.N0232.N0720.N1485.d017364 := by
  intro j k hjk
  exact Measure.restrict_mono_set _root_.GD.N0232.N0720.N1485.d017363
    (_root_.GD.N0232.N0720.N1485.d017349 hjk)



noncomputable local instance d017371 :
    _root_.GD.N0232.N0720.N1485.d017363.IsOpenPosMeasure := by
  unfold _root_.GD.N0232.N0720.N1485.d017363 _root_.GD.N0232.N0720.N1486.d015870
  infer_instance




theorem d017372 :
    _root_.GD.N0232.N0720.N1111.d016605 _root_.GD.N0232.N0720.N1485.d017364 := by
  intro theta U hU
  rcases mem_nhds_iff.1 hU with ⟨V, hVU, hVopen, hthetaV⟩
  have hVpos : 0 < _root_.GD.N0232.N0720.N1485.d017363 V :=
    hVopen.measure_pos _root_.GD.N0232.N0720.N1485.d017363
      ⟨theta, hthetaV⟩
  have hVcover :
      (⋃ k : ℕ, V ∩ _root_.GD.N0232.N0720.N1485.d017343 k) = V := by
    rw [← inter_iUnion, _root_.GD.N0232.N0720.N1485.d017350, inter_univ]
  obtain ⟨N, hNpos⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null
      (μ := _root_.GD.N0232.N0720.N1485.d017363)
      (s := fun k : ℕ ↦ V ∩ _root_.GD.N0232.N0720.N1485.d017343 k) (by
        rw [hVcover]
        exact hVpos.ne')
  let a : ℝ := (_root_.GD.N0232.N0720.N1485.d017364 N V).toReal
  have hcutoffNpos : 0 < _root_.GD.N0232.N0720.N1485.d017364 N V := by
    rw [_root_.GD.N0232.N0720.N1485.d017369 N hVopen.measurableSet]
    exact hNpos
  have ha : 0 < a := by
    exact ENNReal.toReal_pos hcutoffNpos.ne'
      (measure_ne_top (_root_.GD.N0232.N0720.N1485.d017364 N) V)
  refine ⟨a, ha, N, ?_⟩
  intro k hk
  have hmeasure :
      _root_.GD.N0232.N0720.N1485.d017364 N V ≤ _root_.GD.N0232.N0720.N1485.d017364 k U := by
    calc
      _root_.GD.N0232.N0720.N1485.d017364 N V ≤ _root_.GD.N0232.N0720.N1485.d017364 k V :=
        (_root_.GD.N0232.N0720.N1485.d017370 hk) V
      _ ≤ _root_.GD.N0232.N0720.N1485.d017364 k U := measure_mono hVU
  exact (ENNReal.toReal_le_toReal
    (measure_ne_top (_root_.GD.N0232.N0720.N1485.d017364 N) V)
    (measure_ne_top (_root_.GD.N0232.N0720.N1485.d017364 k) U)).2 hmeasure





def d017373
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) (k : ℕ) :
    Measure _root_.GD.N0232.N0720.N1486.d015856 :=
  (_root_.GD.N0232.N0720.N1486.d015870 rho).restrict (_root_.GD.N0232.N0720.N1485.d017359 k)


theorem d017374
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SFinite rho] (k : ℕ) :
    _root_.GD.N0232.N0720.N1485.d017373 rho k =
      (volume.restrict (_root_.GD.N0232.N0720.N1485.d017341 k)).prod
        ((_root_.GD.N0232.N0720.N1486.d015866.restrict (_root_.GD.N0232.N0720.N1485.d017342 k)).prod
          (rho.restrict (_root_.GD.N0232.N0720.N1485.d017354 k))) := by
  unfold _root_.GD.N0232.N0720.N1485.d017373
    _root_.GD.N0232.N0720.N1486.d015870 _root_.GD.N0232.N0720.N1485.d017359
  calc
    (volume.prod (_root_.GD.N0232.N0720.N1486.d015866.prod rho)).restrict
          (_root_.GD.N0232.N0720.N1485.d017341 k ×ˢ
            (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ _root_.GD.N0232.N0720.N1485.d017354 k)) =
        (volume.restrict (_root_.GD.N0232.N0720.N1485.d017341 k)).prod
          ((_root_.GD.N0232.N0720.N1486.d015866.prod rho).restrict
            (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ _root_.GD.N0232.N0720.N1485.d017354 k)) :=
      (Measure.prod_restrict
        (_root_.GD.N0232.N0720.N1485.d017341 k)
        (_root_.GD.N0232.N0720.N1485.d017342 k ×ˢ _root_.GD.N0232.N0720.N1485.d017354 k)).symm
    _ = (volume.restrict (_root_.GD.N0232.N0720.N1485.d017341 k)).prod
          ((_root_.GD.N0232.N0720.N1486.d015866.restrict (_root_.GD.N0232.N0720.N1485.d017342 k)).prod
            (rho.restrict (_root_.GD.N0232.N0720.N1485.d017354 k))) := by
      rw [← Measure.prod_restrict]



noncomputable instance d017375
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [IsFiniteMeasure rho] (k : ℕ) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1485.d017373 rho k) := by
  rw [_root_.GD.N0232.N0720.N1485.d017374]
  infer_instance

theorem d017376
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) (k : ℕ)
    {s : Set _root_.GD.N0232.N0720.N1486.d015856} (hs : MeasurableSet s) :
    _root_.GD.N0232.N0720.N1485.d017373 rho k s =
      _root_.GD.N0232.N0720.N1486.d015870 rho
        (s ∩ _root_.GD.N0232.N0720.N1485.d017359 k) := by
  exact Measure.restrict_apply hs

theorem d017377
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) :
    Monotone (_root_.GD.N0232.N0720.N1485.d017373 rho) := by
  intro j k hjk
  exact Measure.restrict_mono_set (_root_.GD.N0232.N0720.N1486.d015870 rho)
    (_root_.GD.N0232.N0720.N1485.d017361 hjk)





theorem d017378
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    [IsFiniteMeasure rho] [rho.IsOpenPosMeasure] :
    _root_.GD.N0232.N0720.N1111.d016605
      (_root_.GD.N0232.N0720.N1485.d017373 rho) := by
  letI : (_root_.GD.N0232.N0720.N1486.d015870 rho).IsOpenPosMeasure := by
    unfold _root_.GD.N0232.N0720.N1486.d015870
    infer_instance
  intro theta U hU
  rcases mem_nhds_iff.1 hU with ⟨V, hVU, hVopen, hthetaV⟩
  have hVpos : 0 < _root_.GD.N0232.N0720.N1486.d015870 rho V :=
    hVopen.measure_pos (_root_.GD.N0232.N0720.N1486.d015870 rho)
      ⟨theta, hthetaV⟩
  have hVcover :
      (⋃ k : ℕ, V ∩ _root_.GD.N0232.N0720.N1485.d017359 k) = V := by
    rw [← inter_iUnion, _root_.GD.N0232.N0720.N1485.d017362, inter_univ]
  obtain ⟨N, hNpos⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null
      (μ := _root_.GD.N0232.N0720.N1486.d015870 rho)
      (s := fun k : ℕ ↦ V ∩ _root_.GD.N0232.N0720.N1485.d017359 k) (by
        rw [hVcover]
        exact hVpos.ne')
  let a : ℝ :=
    (_root_.GD.N0232.N0720.N1485.d017373 rho N V).toReal
  have hcutoffNpos :
      0 < _root_.GD.N0232.N0720.N1485.d017373 rho N V := by
    rw [_root_.GD.N0232.N0720.N1485.d017376 rho N
      hVopen.measurableSet]
    exact hNpos
  have ha : 0 < a := by
    exact ENNReal.toReal_pos hcutoffNpos.ne'
      (measure_ne_top
        (_root_.GD.N0232.N0720.N1485.d017373 rho N) V)
  refine ⟨a, ha, N, ?_⟩
  intro k hk
  have hmeasure :
      _root_.GD.N0232.N0720.N1485.d017373 rho N V ≤
        _root_.GD.N0232.N0720.N1485.d017373 rho k U := by
    calc
      _root_.GD.N0232.N0720.N1485.d017373 rho N V ≤
          _root_.GD.N0232.N0720.N1485.d017373 rho k V :=
        (_root_.GD.N0232.N0720.N1485.d017377 rho hk) V
      _ ≤ _root_.GD.N0232.N0720.N1485.d017373 rho k U :=
        measure_mono hVU
  exact (ENNReal.toReal_le_toReal
    (measure_ne_top
      (_root_.GD.N0232.N0720.N1485.d017373 rho N) V)
    (measure_ne_top
      (_root_.GD.N0232.N0720.N1485.d017373 rho k) U)).2 hmeasure

end

end N1485
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1485.d017365
#print axioms _root_.GD.N0232.N0720.N1485.d017372
#print axioms _root_.GD.N0232.N0720.N1485.d017374
#print axioms _root_.GD.N0232.N0720.N1485.d017378
