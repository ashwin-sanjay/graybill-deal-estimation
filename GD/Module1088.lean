import GD.Module1086
import GD.Module1087
import Mathlib.MeasureTheory.Function.LocallyIntegrable





























open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0720
namespace N1166

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1177
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1485
open _root_.GD.N0232.N0720.N1490
open _root_.GD.N0232.N0720.N1491
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1494
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602

attribute [local instance] Measure.Subtype.measureSpace

noncomputable local instance d017430 :
    (volume : Measure (Set.Ioi (0 : ℝ))).IsOpenPosMeasure := by
  exact Measure.IsOpenPosMeasure.comap
    (volume : Measure ℝ) isOpen_Ioi.isOpenEmbedding_subtypeVal

noncomputable local instance d017431 :
    _root_.GD.N0232.N0720.N1486.d015866.IsOpenPosMeasure := by
  apply (withDensity_absolutelyContinuous'
    _root_.GD.N0232.N0720.N1486.d015863.aemeasurable ?_).isOpenPosMeasure
  exact Filter.Eventually.of_forall fun q ↦
    (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1486.d015864 q)).ne'




def d017432 (k : ℕ) : _root_.GD.N0232.N0720.N1173.d015933 → ℝ :=
  _root_.GD.N0232.N0720.N1491.d017379 (k + 1)


def d017433 (k : ℕ) : Measure _root_.GD.N0232.N0720.N1173.d015933 :=
  _root_.GD.N0232.N0720.N1494.d017426 (k + 1)

@[simp]
theorem d017434 (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    _root_.GD.N0232.N0720.N1166.d017432 k theta = _root_.GD.N0232.N0720.N1491.d017379 (k + 1) theta := rfl

@[simp]
theorem d017435 (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    _root_.GD.N0232.N0720.N1166.d017432 k theta ^ 2 = _root_.GD.N0232.N0720.N1166.d017432 k theta := by
  by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 (k + 1)
  · simp [_root_.GD.N0232.N0720.N1166.d017432, _root_.GD.N0232.N0720.N1491.d017379, htheta]
  · simp [_root_.GD.N0232.N0720.N1166.d017432, _root_.GD.N0232.N0720.N1491.d017379, htheta]

theorem d017436 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1166.d017432 k) :=
  _root_.GD.N0232.N0720.N1491.d017380 (k + 1)

theorem d017437 (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    0 ≤ _root_.GD.N0232.N0720.N1166.d017432 k theta :=
  _root_.GD.N0232.N0720.N1491.d017381 (k + 1) theta

theorem d017438 (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    _root_.GD.N0232.N0720.N1166.d017432 k theta ≤ 1 :=
  _root_.GD.N0232.N0720.N1491.d017382 (k + 1) theta



theorem d017439 (k : ℕ) :
    _root_.GD.N0232.N0720.N1166.d017433 k =
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104).restrict
        (_root_.GD.N0232.N0720.N1485.d017359 (k + 1)) := by
  rfl



theorem d017440 (k : ℕ) :
    _root_.GD.N0232.N0720.N1166.d017433 k =
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104).withDensity
        (fun theta ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1166.d017432 k theta ^ 2)) := by
  rw [_root_.GD.N0232.N0720.N1166.d017439]
  have hdensity :
      (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1166.d017432 k theta ^ 2)) =
        (_root_.GD.N0232.N0720.N1485.d017359 (k + 1)).indicator (1 : _root_.GD.N0232.N0720.N1173.d015933 → ℝ≥0∞) := by
    funext theta
    by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 (k + 1)
    · simp [_root_.GD.N0232.N0720.N1166.d017432, _root_.GD.N0232.N0720.N1491.d017379, htheta]
    · simp [_root_.GD.N0232.N0720.N1166.d017432, _root_.GD.N0232.N0720.N1491.d017379, htheta]
  rw [hdensity, ← withDensity_indicator_one
    (_root_.GD.N0232.N0720.N1485.d017360 (k + 1))]

noncomputable instance d017441 (k : ℕ) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1166.d017433 k) := by
  unfold _root_.GD.N0232.N0720.N1166.d017433
  infer_instance




theorem d017442 :
    _root_.GD.N0232.N0720.N1111.d016605 _root_.GD.N0232.N0720.N1166.d017433 := by
  intro theta U hU
  obtain ⟨a, ha, N, hN⟩ :=
    _root_.GD.N0232.N0720.N1494.d017428 theta U hU
  refine ⟨a, ha, N, ?_⟩
  intro k hk
  exact hN (k + 1) (hk.trans (Nat.le_add_right k 1))




theorem d017443 :
    Measurable (Function.uncurry _root_.GD.N0232.N0720.N1173.d015937) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · intro x
    exact _root_.GD.N0232.N0720.N1490.d016350 x
  · intro theta
    unfold _root_.GD.N0232.N0720.N1173.d015937
    exact _root_.GD.N0232.N0720.N1499.d015002 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta)




theorem d017444 (k : ℕ) :
    Measurable (Function.uncurry
      (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1491.d017379 k))) := by
  unfold _root_.GD.N0232.N0720.N1173.d015939
  exact _root_.GD.N0232.N0720.N1166.d017443.mul
    ((_root_.GD.N0232.N0720.N1491.d017380 k).comp measurable_fst)


theorem d017445 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1491.d017379 k)) := by
  letI : SigmaFinite
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
    unfold _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088
  exact (_root_.GD.N0232.N0720.N1166.d017444 k).stronglyMeasurable
    |>.integral_prod_left'.measurable


theorem d017446 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1491.d017379 k)) := by
  letI : SigmaFinite
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
    unfold _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  unfold _root_.GD.N0232.N0720.N1173.d015942
  have hjoint : Measurable (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015936 ↦
      _root_.GD.N0232.N0720.N1173.d015938 z.1 *
        _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1491.d017379 k) z.1 z.2) := by
    exact (measurable_fst.comp measurable_fst).mul
      (_root_.GD.N0232.N0720.N1166.d017444 k)
  exact hjoint.stronglyMeasurable.integral_prod_left'.measurable


theorem d017447 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1491.d017379 k)) := by
  unfold _root_.GD.N0232.N0720.N1173.d015943
  exact (_root_.GD.N0232.N0720.N1166.d017446 k).div
    (_root_.GD.N0232.N0720.N1166.d017445 k)

theorem d017448 (k : ℕ) :
    Measurable (Function.uncurry
      (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k))) := by
  exact _root_.GD.N0232.N0720.N1166.d017444 (k + 1)

theorem d017449 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1166.d017432 k)) := by
  exact _root_.GD.N0232.N0720.N1166.d017445 (k + 1)

theorem d017450 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1166.d017432 k)) := by
  exact _root_.GD.N0232.N0720.N1166.d017446 (k + 1)

theorem d017451 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1166.d017432 k)) := by
  exact _root_.GD.N0232.N0720.N1166.d017447 (k + 1)



private theorem d017452
    (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    ‖_root_.GD.N0232.N0720.N1491.d017379 k theta‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (_root_.GD.N0232.N0720.N1491.d017381 k theta)]
  exact _root_.GD.N0232.N0720.N1491.d017382 k theta

theorem d017453
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1491.d017379 k) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  have hfull := _root_.GD.N0232.N0720.N1490.d016352 x ht
  have h := hfull.mul_bdd
    (_root_.GD.N0232.N0720.N1491.d017380 k).aestronglyMeasurable
    (ae_of_all _ (_root_.GD.N0232.N0720.N1166.d017452 k))
  simpa only [_root_.GD.N0232.N0720.N1173.d015939] using h

theorem d017454
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta *
        _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1491.d017379 k) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  have hfull := _root_.GD.N0232.N0720.N1490.d016354 x ht
  have h := hfull.mul_bdd
    (_root_.GD.N0232.N0720.N1491.d017380 k).aestronglyMeasurable
    (ae_of_all _ (_root_.GD.N0232.N0720.N1166.d017452 k))
  simpa only [_root_.GD.N0232.N0720.N1173.d015939, mul_assoc] using h

theorem d017455
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 *
        _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1491.d017379 k) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  have hfull :=
    _root_.GD.N0232.N0720.N1490.d016353 x ht
  have h := hfull.mul_bdd
    (_root_.GD.N0232.N0720.N1491.d017380 k).aestronglyMeasurable
    (ae_of_all _ (_root_.GD.N0232.N0720.N1166.d017452 k))
  simpa only [_root_.GD.N0232.N0720.N1173.d015939, mul_assoc] using h

theorem d017456
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
  _root_.GD.N0232.N0720.N1166.d017453 (k + 1) x ht

theorem d017457
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta *
        _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
  _root_.GD.N0232.N0720.N1166.d017454 (k + 1) x ht

theorem d017458
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 *
        _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
  _root_.GD.N0232.N0720.N1166.d017455 (k + 1) x ht





private def d017459 : _root_.GD.N0232.N0720.N1173.d015933 :=
  (0, (⟨1, by norm_num⟩, ⟨1 / 2, by norm_num, by norm_num⟩))

private theorem d017460 (k : ℕ) :
    _root_.GD.N0232.N0720.N1166.d017459 ∈ interior (_root_.GD.N0232.N0720.N1485.d017359 (k + 1)) := by
  let R : ℝ := _root_.GD.N0232.N0720.N1485.d017336 (k + 1)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hRtwo : 2 < R := by
    dsimp [R, _root_.GD.N0232.N0720.N1485.d017336]
    push_cast
    linarith
  have hRpos : 0 < R := lt_trans (by norm_num) hRtwo
  have hRone : 1 < R := lt_trans (by norm_num) hRtwo
  have hinvOne : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hRone
  have hinvHalf : R⁻¹ < (1 / 2 : ℝ) := by
    have h := (inv_lt_inv₀ hRpos (by norm_num : (0 : ℝ) < 2)).2 hRtwo
    simpa using h
  rw [_root_.GD.N0232.N0720.N1485.d017359, interior_prod_eq, interior_prod_eq,
    _root_.GD.N0232.N0720.N1485.d017341, _root_.GD.N0232.N0720.N1485.d017342, _root_.GD.N0232.N0720.N1485.d017354,
    interior_Icc, interior_Icc, interior_Icc]
  have hcoordinates :
    -R < (0 : ℝ) ∧ (0 : ℝ) < R ∧
      (R⁻¹ < (1 : ℝ) ∧ (1 : ℝ) < R) ∧
      (R⁻¹ < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 - R⁻¹) :=
    ⟨by linarith, hRpos, ⟨hinvOne, hRone⟩, ⟨hinvHalf, by linarith⟩⟩
  simpa [_root_.GD.N0232.N0720.N1166.d017459, R, _root_.GD.N0232.N0720.N1485.d017339,
    _root_.GD.N0232.N0720.N1485.d017340, _root_.GD.N0232.N0720.N1485.d017352, _root_.GD.N0232.N0720.N1485.d017353] using
      hcoordinates




theorem d017461 (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1485.d017359 (k + 1)) := by
  letI : (_root_.GD.N0232.N0720.N1173.d015934
      _root_.GD.N0232.N0720.N1493.d016104).IsOpenPosMeasure := by
    unfold _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1486.d015870
    infer_instance
  have hinterior :
      0 < _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104
        (interior (_root_.GD.N0232.N0720.N1485.d017359 (k + 1))) :=
    isOpen_interior.measure_pos
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104)
      ⟨_root_.GD.N0232.N0720.N1166.d017459,
        _root_.GD.N0232.N0720.N1166.d017460 k⟩
  exact hinterior.trans_le (measure_mono interior_subset)



private theorem d017462
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 ≤ _root_.GD.N0232.N0720.N1173.d015937 theta x := by
  exact _root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x

private theorem d017463
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 < _root_.GD.N0232.N0720.N1173.d015937 theta x := by
  exact _root_.GD.N0232.N0720.N1499.d015005 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x



theorem d017464
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1166.d017432 k) x := by
  have hint :=
    _root_.GD.N0232.N0720.N1166.d017456 k x ht
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088
  apply (integral_pos_iff_support_of_nonneg
    (fun theta ↦ mul_nonneg (_root_.GD.N0232.N0720.N1166.d017462 theta x)
      (_root_.GD.N0232.N0720.N1166.d017437 k theta)) hint).2
  have hsubset : _root_.GD.N0232.N0720.N1485.d017359 (k + 1) ⊆
      Function.support
        (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x) := by
    intro theta htheta
    simpa [Function.support, _root_.GD.N0232.N0720.N1173.d015939, _root_.GD.N0232.N0720.N1166.d017432,
      _root_.GD.N0232.N0720.N1491.d017379, htheta] using (_root_.GD.N0232.N0720.N1166.d017463 theta x).ne'
  exact (_root_.GD.N0232.N0720.N1166.d017461 k).trans_le
    (measure_mono hsubset)



theorem d017465
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    _root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k) x ∈
      Set.Icc (-_root_.GD.N0232.N0720.N1485.d017336 (k + 1))
        (_root_.GD.N0232.N0720.N1485.d017336 (k + 1)) := by
  let R : ℝ := _root_.GD.N0232.N0720.N1485.d017336 (k + 1)
  let W : _root_.GD.N0232.N0720.N1173.d015933 → ℝ :=
    fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x
  have hW : Integrable W
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
    _root_.GD.N0232.N0720.N1166.d017456 k x ht
  have hM : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * W theta)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
    _root_.GD.N0232.N0720.N1166.d017457 k x ht
  have hWnonneg : ∀ theta, 0 ≤ W theta := by
    intro theta
    exact mul_nonneg (_root_.GD.N0232.N0720.N1166.d017462 theta x)
      (_root_.GD.N0232.N0720.N1166.d017437 k theta)
  have hlowerPoint : ∀ theta, -R * W theta ≤ _root_.GD.N0232.N0720.N1173.d015938 theta * W theta := by
    intro theta
    by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 (k + 1)
    · exact mul_le_mul_of_nonneg_right htheta.1.1 (hWnonneg theta)
    · simp [W, _root_.GD.N0232.N0720.N1173.d015939, _root_.GD.N0232.N0720.N1166.d017432,
        _root_.GD.N0232.N0720.N1491.d017379, htheta]
  have hupperPoint : ∀ theta, _root_.GD.N0232.N0720.N1173.d015938 theta * W theta ≤ R * W theta := by
    intro theta
    by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 (k + 1)
    · exact mul_le_mul_of_nonneg_right htheta.1.2 (hWnonneg theta)
    · simp [W, _root_.GD.N0232.N0720.N1173.d015939, _root_.GD.N0232.N0720.N1166.d017432,
        _root_.GD.N0232.N0720.N1491.d017379, htheta]
  have hlowerInt :
      -R * (∫ theta, W theta
          ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) ≤
        ∫ theta, _root_.GD.N0232.N0720.N1173.d015938 theta * W theta
          ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104 := by
    rw [← integral_const_mul]
    exact integral_mono (hW.const_mul (-R)) hM hlowerPoint
  have hupperInt :
      (∫ theta, _root_.GD.N0232.N0720.N1173.d015938 theta * W theta
          ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) ≤
        R * ∫ theta, W theta
          ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104 := by
    rw [← integral_const_mul]
    exact integral_mono hM (hW.const_mul R) hupperPoint
  have hE : 0 < ∫ theta, W theta
      ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104 := by
    simpa [W, _root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088] using
      _root_.GD.N0232.N0720.N1166.d017464 k x ht
  unfold _root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088
  change (∫ theta, _root_.GD.N0232.N0720.N1173.d015938 theta * W theta
      ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) /
      (∫ theta, W theta
        ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) ∈ Set.Icc (-R) R
  exact ⟨(le_div_iff₀ hE).2 hlowerInt, (div_le_iff₀ hE).2 hupperInt⟩



private theorem d017466
    (a b : Set.Ioi (0 : ℝ)) : IsCompact (Set.Icc a b) := by
  let lift : Set.Icc (a : ℝ) (b : ℝ) → Set.Ioi (0 : ℝ) :=
    fun x ↦ ⟨x, lt_of_lt_of_le a.property x.property.1⟩
  have hlift : Continuous lift :=
    Continuous.subtype_mk continuous_subtype_val _
  have himage : lift '' Set.univ = Set.Icc a b := by
    ext q
    constructor
    · rintro ⟨x, -, rfl⟩
      exact x.property
    · intro hq
      let x : Set.Icc (a : ℝ) (b : ℝ) := ⟨q, hq⟩
      exact ⟨x, Set.mem_univ x, Subtype.ext rfl⟩
  rw [← himage]
  exact isCompact_univ.image hlift

private theorem d017467
    (a b : Set.Ioo (0 : ℝ) 1) : IsCompact (Set.Icc a b) := by
  let lift : Set.Icc (a : ℝ) (b : ℝ) → Set.Ioo (0 : ℝ) 1 :=
    fun x ↦ ⟨x, lt_of_lt_of_le a.property.1 x.property.1,
      lt_of_le_of_lt x.property.2 b.property.2⟩
  have hlift : Continuous lift :=
    Continuous.subtype_mk continuous_subtype_val _
  have himage : lift '' Set.univ = Set.Icc a b := by
    ext z
    constructor
    · rintro ⟨x, -, rfl⟩
      exact x.property
    · intro hz
      let x : Set.Icc (a : ℝ) (b : ℝ) := ⟨z, hz⟩
      exact ⟨x, Set.mem_univ x, Subtype.ext rfl⟩
  rw [← himage]
  exact isCompact_univ.image hlift

private theorem d017468 (k : ℕ) :
    IsCompact (_root_.GD.N0232.N0720.N1485.d017359 k) := by
  unfold _root_.GD.N0232.N0720.N1485.d017359 _root_.GD.N0232.N0720.N1485.d017341 _root_.GD.N0232.N0720.N1485.d017342
    _root_.GD.N0232.N0720.N1485.d017354
  exact isCompact_Icc.prod
    ((_root_.GD.N0232.N0720.N1166.d017466 _ _).prod
      (_root_.GD.N0232.N0720.N1166.d017467 _ _))

private theorem d017469 (k : ℕ) :
    _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1485.d017359 (k + 1)) ≠ ∞ := by
  have hfinite := measure_ne_top (_root_.GD.N0232.N0720.N1166.d017433 k) Set.univ
  rw [_root_.GD.N0232.N0720.N1166.d017439] at hfinite
  simpa [Measure.restrict_apply,
    _root_.GD.N0232.N0720.N1485.d017360] using hfinite



theorem d017470 (k : ℕ) :
    Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1166.d017432 k theta *
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1177.d017413).toReal)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  let profile : _root_.GD.N0232.N0720.N1173.d015933 → ℝ := fun theta ↦
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1177.d017413).toReal
  have hprofile : Continuous profile := by
    exact
      (_root_.GD.N0232.N0720.N1111.d016606 2 2
        _root_.GD.N0232.N0720.N1177.d017413
        _root_.GD.N0232.N0720.N1177.d017416).comp
          (_root_.GD.N0232.N0720.N1486.d015877
            2 2 (by norm_num) (by norm_num))
  have hon : IntegrableOn profile (_root_.GD.N0232.N0720.N1485.d017359 (k + 1))
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
    hprofile.continuousOn.integrableOn_of_subset_isCompact
      (_root_.GD.N0232.N0720.N1166.d017468 (k + 1))
      (_root_.GD.N0232.N0720.N1485.d017360 (k + 1))
      Subset.rfl
      (_root_.GD.N0232.N0720.N1166.d017469 k)
  have hindicator := hon.integrable_indicator
    (_root_.GD.N0232.N0720.N1485.d017360 (k + 1))
  refine hindicator.congr
    (ae_of_all (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104)
      fun theta ↦ ?_)
  by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 (k + 1)
  · simp [profile, _root_.GD.N0232.N0720.N1166.d017432, _root_.GD.N0232.N0720.N1491.d017379, htheta]
  · simp [profile, _root_.GD.N0232.N0720.N1166.d017432, _root_.GD.N0232.N0720.N1491.d017379, htheta]

private theorem d017471
    (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    Integrable
      (fun x ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x *
        (_root_.GD.N0232.N0720.N1177.d017406 x - _root_.GD.N0232.N0720.N1173.d015938 theta) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  have hphysical :=
    (_root_.GD.N0232.N0720.N1177.d017409 (_root_.GD.N0232.N0720.N1173.d015935 theta)).integrable_sq
  rw [_root_.GD.N0232.N0720.N1499.d015006 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta),
    integrable_withDensity_iff_integrable_smul'
      (_root_.GD.N0232.N0720.N1499.d015002 2 2
        (_root_.GD.N0232.N0720.N1173.d015935 theta)).ennreal_ofReal
      (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun _ ↦ ENNReal.ofReal_lt_top)]
      at hphysical
  refine hphysical.congr (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun x ↦ ?_)
  change
    (ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1499.d015001 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x)).toReal •
        (_root_.GD.N0232.N0720.N1177.d017406 x - (_root_.GD.N0232.N0720.N1173.d015935 theta).location) ^ 2 =
      _root_.GD.N0232.N0720.N1173.d015937 theta x *
        (_root_.GD.N0232.N0720.N1177.d017406 x - _root_.GD.N0232.N0720.N1173.d015938 theta) ^ 2
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x)]
  simp only [smul_eq_mul]
  rfl

private theorem d017472
    (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1177.d017413).toReal =
      ∫ x, _root_.GD.N0232.N0720.N1173.d015937 theta x *
        (_root_.GD.N0232.N0720.N1177.d017406 x - _root_.GD.N0232.N0720.N1173.d015938 theta) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
  rw [_root_.GD.N0232.N0720.N1177.d017415]
  have hnonneg : 0 ≤
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta))
        (fun x ↦ _root_.GD.N0232.N0720.N1177.d017406 x - (_root_.GD.N0232.N0720.N1173.d015935 theta).location) := by
    unfold _root_.GD.N0141.d006684
    exact integral_nonneg fun _ ↦ sq_nonneg _
  rw [ENNReal.toReal_ofReal hnonneg]
  unfold _root_.GD.N0141.d006684
  rw [_root_.GD.N0232.N0720.N1499.d015006 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta),
    integral_withDensity_eq_integral_toReal_smul
      (_root_.GD.N0232.N0720.N1499.d015002 2 2
        (_root_.GD.N0232.N0720.N1173.d015935 theta)).ennreal_ofReal
      (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x)]
  simp only [smul_eq_mul]
  rfl



theorem d017473 (k : ℕ) :
    Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
          _root_.GD.N0232.N0720.N1177.d017406).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104).prod
        (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  have htarget : Measurable _root_.GD.N0232.N0720.N1173.d015938 := by
    unfold _root_.GD.N0232.N0720.N1173.d015938
    fun_prop
  have hjoint : Measurable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
          _root_.GD.N0232.N0720.N1177.d017406).uncurry :=
    _root_.GD.N0230.N0589.d000073
      (_root_.GD.N0232.N0720.N1166.d017448 k)
      htarget _root_.GD.N0232.N0720.N1177.d017407
  apply (integrable_prod_iff hjoint.aestronglyMeasurable).2
  constructor
  · filter_upwards with theta
    have hbase :=
      _root_.GD.N0232.N0720.N1166.d017471 theta
    have hscaled := hbase.const_mul (_root_.GD.N0232.N0720.N1166.d017432 k theta)
    refine hscaled.congr (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 2 2) fun x ↦ ?_)
    unfold _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1173.d015939
    dsimp only [Function.uncurry_apply_pair]
    ring
  · have hprofile :=
      _root_.GD.N0232.N0720.N1166.d017470 k
    refine hprofile.congr
      (ae_of_all (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104)
        fun theta ↦ ?_)
    change
      _root_.GD.N0232.N0720.N1166.d017432 k theta *
          (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1177.d017413).toReal =
        ∫ x,
          ‖_root_.GD.N0230.N0589.d000071
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
              _root_.GD.N0232.N0720.N1177.d017406 theta x‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
    rw [show
      (∫ x,
        ‖_root_.GD.N0230.N0589.d000071
          (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
            _root_.GD.N0232.N0720.N1177.d017406 theta x‖ ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        ∫ x,
          _root_.GD.N0230.N0589.d000071
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
              _root_.GD.N0232.N0720.N1177.d017406 theta x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 by
        apply integral_congr_ae
        filter_upwards with x
        exact Real.norm_of_nonneg (by
          apply _root_.GD.N0230.N0589.d000075
          intro eta y
          exact mul_nonneg
            (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 eta) y)
            (_root_.GD.N0232.N0720.N1166.d017437 k eta))]
    rw [show
      (∫ x,
        _root_.GD.N0230.N0589.d000071
          (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
            _root_.GD.N0232.N0720.N1177.d017406 theta x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        _root_.GD.N0232.N0720.N1166.d017432 k theta *
          ∫ x, _root_.GD.N0232.N0720.N1173.d015937 theta x *
            (_root_.GD.N0232.N0720.N1177.d017406 x - _root_.GD.N0232.N0720.N1173.d015938 theta) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        unfold _root_.GD.N0230.N0589.d000071 _root_.GD.N0232.N0720.N1173.d015939
        ring]
    rw [← _root_.GD.N0232.N0720.N1166.d017472 theta]



theorem d017474 (k : ℕ) :
    Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104).prod
        (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  have hraw := _root_.GD.N0232.N0720.N1166.d017473 k
  have haction :
      _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
        _root_.GD.N0232.N0720.N1177.d017406 := by
    filter_upwards [_root_.GD.N0232.N0720.N1491.d017394] with x hx
    exact _root_.GD.N0232.N0720.N1177.d017408 x hx
  have hactionProd :
      (fun z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015936 ↦
        _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 z.2) =ᵐ[
          (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104).prod
            (_root_.GD.N0232.N0720.N1080.d014172 2 2)]
        (fun z ↦ _root_.GD.N0232.N0720.N1177.d017406 z.2) :=
    (Measure.quasiMeasurePreserving_snd
      (μ := _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104)
      (ν := _root_.GD.N0232.N0720.N1080.d014172 2 2)).ae_eq_comp haction
  refine hraw.congr ?_
  filter_upwards [hactionProd] with z hz
  unfold _root_.GD.N0230.N0589.d000071
  change
    _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) z.1 z.2 *
        (_root_.GD.N0232.N0720.N1177.d017406 z.2 - _root_.GD.N0232.N0720.N1173.d015938 z.1) ^ 2 =
      _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) z.1 z.2 *
        (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 z.2 - _root_.GD.N0232.N0720.N1173.d015938 z.1) ^ 2
  rw [hz]




def d017475 (k : ℕ) : _root_.GD.N0232.N0720.N1173.d015936 → ℝ :=
  _root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1166.d017432 k)

theorem d017476 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1166.d017475 k) :=
  _root_.GD.N0232.N0720.N1166.d017451 k

theorem d017477
    (k : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (_root_.GD.N0232.N0720.N1166.d017475 k) 2 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
    unfold _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  apply memLp_of_bounded
    (a := -_root_.GD.N0232.N0720.N1485.d017336 (k + 1))
    (b := _root_.GD.N0232.N0720.N1485.d017336 (k + 1))
  · filter_upwards [_root_.GD.N0232.N0720.N1177.d017410 theta] with x hx
    exact _root_.GD.N0232.N0720.N1166.d017465 k x hx
  · exact (_root_.GD.N0232.N0720.N1166.d017476 k).aestronglyMeasurable

theorem d017478
    (k : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (fun x ↦ _root_.GD.N0232.N0720.N1166.d017475 k x - theta.location) 2
      (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta) := by
    unfold _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  exact (_root_.GD.N0232.N0720.N1166.d017477 k theta).sub
    (memLp_const theta.location)



def d017479
    (k : ℕ) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1166.d017475 k) (by
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1166.d017478 k _root_.GD.N0232.N0720.N1080.d014169)

@[simp]
theorem d017480 (k : ℕ) :
    (fun x ↦ _root_.GD.N0232.N0720.N1166.d017479 k x) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2]
      _root_.GD.N0232.N0720.N1166.d017475 k := by
  exact (by
    simpa [_root_.GD.N0232.N0720.N1166.d017479] using
      (show MemLp (_root_.GD.N0232.N0720.N1166.d017475 k) 2 (_root_.GD.N0232.N0720.N1080.d014172 2 2) by
        simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          _root_.GD.N0232.N0720.N1166.d017478 k _root_.GD.N0232.N0720.N1080.d014169).coeFn_toLp)


theorem d017481
    (k : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 theta (_root_.GD.N0232.N0720.N1166.d017479 k) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
          (fun x ↦ _root_.GD.N0232.N0720.N1166.d017475 k x - theta.location)) := by
  apply _root_.GD.N0232.N0720.N1080.d014183
    2 2 (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta)
  exact _root_.GD.N0232.N0720.N1166.d017478 k theta



theorem d017482 (k : ℕ) :
    _root_.GD.N0232.N0720.N1159.d014637 2 2 (_root_.GD.N0232.N0720.N1166.d017479 k) := by
  intro theta
  rw [_root_.GD.N0232.N0720.N1166.d017481 k theta]
  exact ENNReal.ofReal_ne_top






theorem d017483
    (k : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q) :
    Integrable
      (fun theta ↦ (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) q).toReal)
      (_root_.GD.N0232.N0720.N1166.d017433 k) := by
  let profile : _root_.GD.N0232.N0720.N1173.d015933 → ℝ := fun theta ↦
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) q).toReal
  have hprofile : Continuous profile :=
    (_root_.GD.N0232.N0720.N1111.d016606 2 2 q hq).comp
      (_root_.GD.N0232.N0720.N1486.d015877
        2 2 (by norm_num) (by norm_num))
  have hon : IntegrableOn profile (_root_.GD.N0232.N0720.N1485.d017359 (k + 1))
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
    hprofile.continuousOn.integrableOn_of_subset_isCompact
      (_root_.GD.N0232.N0720.N1166.d017468 (k + 1))
      (_root_.GD.N0232.N0720.N1485.d017360 (k + 1))
      Subset.rfl
      (_root_.GD.N0232.N0720.N1166.d017469 k)
  rw [_root_.GD.N0232.N0720.N1166.d017439]
  exact hon





theorem d017484
    (k : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q) :
    _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 _root_.GD.N0232.N0720.N1166.d017433 k q =
      _root_.GD.N0230.N0589.d000084 (_root_.GD.N0232.N0720.N1166.d017433 k) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        _root_.GD.N0232.N0720.N1173.d015937 _root_.GD.N0232.N0720.N1173.d015938 (fun x ↦ q x) := by
  unfold _root_.GD.N0232.N0720.N1111.d016604 _root_.GD.N0230.N0589.d000084
  apply integral_congr_ae
  filter_upwards with theta
  rw [_root_.GD.N0232.N0720.N1126.d016430
    (_root_.GD.N0232.N0720.N1173.d015935 theta) q (hq (_root_.GD.N0232.N0720.N1173.d015935 theta))]
  rfl

end

end N1166
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1166.d017440
#print axioms _root_.GD.N0232.N0720.N1166.d017442
#print axioms _root_.GD.N0232.N0720.N1166.d017464
#print axioms _root_.GD.N0232.N0720.N1166.d017482
#print axioms _root_.GD.N0232.N0720.N1166.d017474
#print axioms _root_.GD.N0232.N0720.N1166.d017484
