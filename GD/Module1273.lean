import GD.Module1253
import GD.Module1243
import GD.Module1246











open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace GD.N0232.N0720.N1395

noncomputable section

open _root_.GD.N0232.N0720.N1290 _root_.GD.N0232.N0720.N1271
open _root_.GD.N0232.N0720.N1368 _root_.GD.N0232.N0720.N1359
open _root_.GD.N0232.N0720.N1264 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1352 _root_.GD.N0232.N0720.N1351
open _root_.GD.N0232.N0720.N1270 _root_.GD.N0232.N0720.N1265
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1401
open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1389 _root_.GD.N0232.N0720.N1387
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1437 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441

abbrev d020552 := _root_.GD.N0232.N0720.N1393.d004492

def d020553 (x : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1351.d002812 :=
  ![x.1, 1 - x.1, x.2]

theorem d020554 : Continuous _root_.GD.N0232.N0720.N1395.d020553 := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1395.d020553] <;> fun_prop

theorem d020555 {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1395.d020553 x ∈ _root_.GD.N0232.N0720.N1292.d004155 :=
  _root_.GD.N0232.N0720.N1292.d004160 hx.1.1 (sub_pos.mpr hx.1.2) hx.2.le

theorem d020556 (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1292.d004153 (_root_.GD.N0232.N0720.N1395.d020553 x) = _root_.GD.N0232.N0720.N1271.d013404 x := by
  funext t
  simp only [_root_.GD.N0232.N0720.N1292.d004153, _root_.GD.N0232.N0720.N1395.d020553, _root_.GD.N0232.N0720.N1271.d013404,
    _root_.GD.N0232.N0720.N1271.d013403,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

def d020557 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) mu

theorem d020558 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContinuousOn (_root_.GD.N0232.N0720.N1395.d020557 mu) _root_.GD.N0232.N0720.N1436.d013218 := by
  have hD := (_root_.GD.N0232.N0720.N1292.d004173 (5 / 2) continuous_const mu
    (phi := fun _ ↦ 1)).continuousOn.comp _root_.GD.N0232.N0720.N1395.d020554.continuousOn
      (fun _ hx ↦ _root_.GD.N0232.N0720.N1395.d020555 hx)
  have hT := (_root_.GD.N0232.N0720.N1292.d004173 (5 / 2) continuous_subtype_val mu).continuousOn.comp
    _root_.GD.N0232.N0720.N1395.d020554.continuousOn (fun _ hx ↦ _root_.GD.N0232.N0720.N1395.d020555 hx)
  apply (hT.div hD (fun x hx ↦ (_root_.GD.N0232.N0720.N1264.d020248 (5 / 2) mu (_root_.GD.N0232.N0720.N1395.d020555 hx)).ne')).congr
  intro x hx
  simp only [Pi.div_apply, _root_.GD.N0232.N0720.N1395.d020557, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139,
    _root_.GD.N0232.N0720.N1292.d004162, _root_.GD.N0232.N0720.N1292.d004161, _root_.GD.N0232.N0720.N1395.d020556, Function.comp_apply, one_mul]

def d020559 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1436.d013217 → ℝ := by
  classical
  exact _root_.GD.N0232.N0720.N1436.d013218.piecewise (_root_.GD.N0232.N0720.N1395.d020557 mu) (fun _ ↦ 0)

theorem d020560 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    Measurable (_root_.GD.N0232.N0720.N1395.d020559 mu) := by
  classical
  exact (_root_.GD.N0232.N0720.N1395.d020558 mu).measurable_piecewise continuousOn_const
    _root_.GD.N0232.N0720.N1436.d013219

theorem d020561 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (x : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1395.d020559 mu x ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218
  · rw [_root_.GD.N0232.N0720.N1395.d020559, piecewise_eq_of_mem _ _ _ hx]
    exact _root_.GD.N0232.N0720.N1359.d004246 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x)
      (_root_.GD.N0232.N0720.N1271.d013405.comp (continuous_const.prodMk continuous_id))
      (_root_.GD.N0232.N0720.N1271.d013407 hx) mu (ae_of_all _ fun t ↦ t.2)
  · simp [_root_.GD.N0232.N0720.N1395.d020559, hx]

theorem d020562 {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ}
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : _root_.GD.N0232.N0720.N1398.d019601 d =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] _root_.GD.N0232.N0720.N1395.d020557 mu) :
    _root_.GD.N0232.N0720.N1395.d020559 mu =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] _root_.GD.N0232.N0720.N1398.d019601 d := by
  filter_upwards [hpost, _root_.GD.N0232.N0720.N1265.d020140] with x hx hdom
  simpa [_root_.GD.N0232.N0720.N1395.d020559, hdom] using hx.symm



theorem d020563 {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : _root_.GD.N0232.N0720.N1398.d019601 d =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] _root_.GD.N0232.N0720.N1395.d020557 mu)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1395.d020559 mu) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 theta]
      _root_.GD.N0232.N0720.N1425.d014719 2 2 (_root_.GD.N0232.N0720.N1398.d019601 d) := by
  have hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1395.d020559 mu) t.1 ≤ _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1 := by
    intro t
    apply le_of_eq
    apply integral_congr_ae
    filter_upwards [(_root_.GD.N0232.N0720.N1441.d013682
      (by omega : 2 ≤ 2) (by omega : 2 ≤ 2) t).ae_le
      (_root_.GD.N0232.N0720.N1395.d020562 mu hpost)] with x hx
    rw [hx]
  have hs := hd.2.2.2 _ (_root_.GD.N0232.N0720.N1398.d019599 2 2 (_root_.GD.N0232.N0720.N1395.d020560 mu))
    (_root_.GD.N0232.N0720.N1398.d019619 hd (_root_.GD.N0232.N0720.N1395.d020560 mu)
      (_root_.GD.N0232.N0720.N1395.d020561 mu) hdom)
  exact (hs theta).trans (_root_.GD.N0232.N0720.N1398.d019606 hd theta)



theorem d020564 {f g : _root_.GD.N0232.N0720.N1395.d020552 → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : f ∘ _root_.GD.N0232.N0720.N1389.d012529 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2] g ∘ _root_.GD.N0232.N0720.N1389.d012529) :
    f =ᵐ[volume] g := by
  have hmap : (_root_.GD.N0232.N0720.N1080.d014172 2 2).map _root_.GD.N0232.N0720.N1389.d012529 =
      volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004523 _root_.GD.N0232.N0720.N1372.d004566 x)) := by
    have h := _root_.GD.N0232.N0720.N1389.d012531 _root_.GD.N0232.N0720.N1372.d004566
    have hfirst : _root_.GD.N0232.N0720.N1389.d012523 _root_.GD.N0232.N0720.N1372.d004566 = 1 := by
      norm_num [_root_.GD.N0232.N0720.N1389.d012523, _root_.GD.N0232.N0720.N1372.d004566]
    have hsecond : _root_.GD.N0232.N0720.N1389.d012524 _root_.GD.N0232.N0720.N1372.d004566 = 1 := by
      norm_num [_root_.GD.N0232.N0720.N1389.d012524, _root_.GD.N0232.N0720.N1372.d004566]
    rw [hfirst, hsecond] at h
    simpa only [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0720.N1372.d004566] using h
  have hm : f =ᵐ[(_root_.GD.N0232.N0720.N1080.d014172 2 2).map _root_.GD.N0232.N0720.N1389.d012529] g :=
    (ae_map_iff _root_.GD.N0232.N0720.N1389.d012530.aemeasurable (measurableSet_eq_fun hf hg)).2 hfg
  rw [hmap] at hm
  have hh := (ae_withDensity_iff (_root_.GD.N0232.N0720.N1389.d012533 _root_.GD.N0232.N0720.N1372.d004566).ennreal_ofReal).1 hm
  filter_upwards [hh] with x hx
  apply hx
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  have hv := _root_.GD.N0232.N0720.N1372.d004524 _root_.GD.N0232.N0720.N1372.d004566
  unfold _root_.GD.N0232.N0720.N1372.d004523
  positivity

theorem d020565 {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : _root_.GD.N0232.N0720.N1398.d019601 d =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] _root_.GD.N0232.N0720.N1395.d020557 mu) :
    _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) =ᵐ[volume]
      _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1395.d020559 mu) := by
  apply _root_.GD.N0232.N0720.N1395.d020564
    (_root_.GD.N0232.N0720.N1401.d020151 (_root_.GD.N0232.N0720.N1398.d019602 hd.1))
    (_root_.GD.N0232.N0720.N1401.d020151 (_root_.GD.N0232.N0720.N1395.d020560 mu))
  have h := (_root_.GD.N0232.N0720.N1395.d020563 hd mu hpost _root_.GD.N0232.N0720.N1080.d014169).symm
  filter_upwards [h] with x hx
  simpa only [Function.comp_apply, _root_.GD.N0232.N0720.N1401.d020156] using hx

def d020566 (x : _root_.GD.N0232.N0720.N1395.d020552) : _root_.GD.N0232.N0720.N1352.d002739 :=
  ![x 0, x 2, x 1 ^ 2 / 2, x 3 ^ 2 / 2]

def d020567 : Set _root_.GD.N0232.N0720.N1395.d020552 := {x | x 1 ≠ 0 ∧ x 3 ≠ 0}

theorem d020568 : ContDiff ℝ ∞ _root_.GD.N0232.N0720.N1395.d020566 := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1395.d020566] <;> fun_prop

theorem d020569 {x : _root_.GD.N0232.N0720.N1395.d020552} (hx : x ∈ _root_.GD.N0232.N0720.N1395.d020567) :
    _root_.GD.N0232.N0720.N1395.d020566 x ∈ _root_.GD.N0232.N0720.N1270.d020224 := by
  exact ⟨div_pos (sq_pos_of_ne_zero hx.1) (by norm_num),
    div_pos (sq_pos_of_ne_zero hx.2) (by norm_num)⟩

def d020570 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1395.d020552) : ℝ :=
  _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1270.d020230 mu ∘ _root_.GD.N0232.N0720.N1351.d002814) (_root_.GD.N0232.N0720.N1395.d020566 x)

theorem d020571 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1270.d020230 mu ∘ _root_.GD.N0232.N0720.N1351.d002814)) _root_.GD.N0232.N0720.N1270.d020224 := by
  have hG := (_root_.GD.N0232.N0720.N1264.d020251 mu).comp _root_.GD.N0232.N0720.N1351.d002818.contDiffOn
    (fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020252 hx)
  exact (show ContDiffOn ℝ ∞ (fun x : _root_.GD.N0232.N0720.N1352.d002739 ↦ x 0) _root_.GD.N0232.N0720.N1270.d020224 by fun_prop).add
    (_root_.GD.N0232.N0720.N1352.d002748.contDiffOn.mul hG)

theorem d020572 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContinuousOn (_root_.GD.N0232.N0720.N1395.d020570 mu) _root_.GD.N0232.N0720.N1395.d020567 := by
  exact (_root_.GD.N0232.N0720.N1395.d020571 mu).continuousOn.comp _root_.GD.N0232.N0720.N1395.d020568.continuous.continuousOn
    (fun _ hx ↦ _root_.GD.N0232.N0720.N1395.d020569 hx)

theorem d020573 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ t, 0 ≤ P t) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0232.N0720.N1290.d004140 q (fun t ↦ c * P t) mu = _root_.GD.N0232.N0720.N1290.d004140 q P mu := by
  have hpow : ∀ t, (c * P t) ^ (-q) = c ^ (-q) * P t ^ (-q) :=
    fun t ↦ Real.mul_rpow hc.le (hP t)
  have hN : (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ) * (c ^ (-q) * P t ^ (-q))) =
      fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ c ^ (-q) * ((t : ℝ) * P t ^ (-q)) := by funext t; ring
  unfold _root_.GD.N0232.N0720.N1290.d004140 _root_.GD.N0232.N0720.N1290.d004139
  simp_rw [hpow]
  rw [hN, integral_const_mul, integral_const_mul]
  exact mul_div_mul_left _ _ (ne_of_gt (Real.rpow_pos_of_pos hc (-q)))

def d020574 (x : _root_.GD.N0232.N0720.N1395.d020552) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (x 3 ^ 2 / (x 1 ^ 2 + x 3 ^ 2), (x 0 - x 2) ^ 2 / (x 1 ^ 2 + x 3 ^ 2))

theorem d020575 {x : _root_.GD.N0232.N0720.N1395.d020552} (hx : x ∈ _root_.GD.N0232.N0720.N1395.d020567)
    (hd : x 0 ≠ x 2) : _root_.GD.N0232.N0720.N1395.d020574 x ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  have hR := sq_pos_of_ne_zero hx.1
  have hS := sq_pos_of_ne_zero hx.2
  have hE := add_pos hR hS
  refine ⟨⟨div_pos hS hE, (div_lt_one hE).2 (by linarith)⟩, ?_⟩
  exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hd)) hE

theorem d020576 {x : _root_.GD.N0232.N0720.N1395.d020552}
    (hx : x ∈ _root_.GD.N0232.N0720.N1395.d020567) :
    _root_.GD.N0232.N0720.N1368.d020208 (x 3 ^ 2 / 2) (x 1 ^ 2 / 2) ((x 2 - x 0) ^ 2 / 2) =
      fun t ↦ ((x 1 ^ 2 + x 3 ^ 2) / 2) * _root_.GD.N0232.N0720.N1271.d013404 (_root_.GD.N0232.N0720.N1395.d020574 x) t := by
  have hE : x 1 ^ 2 + x 3 ^ 2 ≠ 0 :=
    ne_of_gt (add_pos (sq_pos_of_ne_zero hx.1) (sq_pos_of_ne_zero hx.2))
  funext t
  simp only [_root_.GD.N0232.N0720.N1368.d020208, _root_.GD.N0232.N0720.N1271.d013404, _root_.GD.N0232.N0720.N1395.d020574,
    _root_.GD.N0232.N0720.N1271.d013403]
  field_simp [hE] <;> ring



theorem d020577 {x : _root_.GD.N0232.N0720.N1395.d020552}
    (hx : x ∈ _root_.GD.N0232.N0720.N1395.d020567) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1395.d020559 mu) x = _root_.GD.N0232.N0720.N1395.d020570 mu x := by
  classical
  by_cases hd : x 0 = x 2
  · simp [_root_.GD.N0232.N0720.N1401.d020150, _root_.GD.N0232.N0720.N1437.d002998, _root_.GD.N0232.N0720.N1395.d020570,
      _root_.GD.N0232.N0720.N1352.d002804, _root_.GD.N0232.N0720.N1395.d020566, _root_.GD.N0232.N0720.N1352.d002742, hd]
  have hproj := _root_.GD.N0232.N0720.N1395.d020575 hx hd
  have hc : 0 < (x 1 ^ 2 + x 3 ^ 2) / 2 :=
    div_pos (add_pos (sq_pos_of_ne_zero hx.1) (sq_pos_of_ne_zero hx.2)) (by norm_num)
  have hprior : _root_.GD.N0232.N0720.N1270.d020230 mu (_root_.GD.N0232.N0720.N1351.d002814 (_root_.GD.N0232.N0720.N1395.d020566 x)) =
      1 - _root_.GD.N0232.N0720.N1395.d020557 mu (_root_.GD.N0232.N0720.N1395.d020574 x) := by
    change 1 - _root_.GD.N0232.N0720.N1290.d004140 (5 / 2)
      (_root_.GD.N0232.N0720.N1368.d020208 (x 3 ^ 2 / 2) (x 1 ^ 2 / 2) ((x 2 - x 0) ^ 2 / 2)) mu =
        1 - _root_.GD.N0232.N0720.N1395.d020557 mu (_root_.GD.N0232.N0720.N1395.d020574 x)
    rw [_root_.GD.N0232.N0720.N1395.d020576 hx,
      _root_.GD.N0232.N0720.N1395.d020573 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 (_root_.GD.N0232.N0720.N1395.d020574 x))
        (fun t ↦ (_root_.GD.N0232.N0720.N1271.d013407 hproj t).le) mu hc]
    rfl
  change x 2 + (x 0 - x 2) * _root_.GD.N0232.N0720.N1395.d020559 mu (_root_.GD.N0232.N0720.N1395.d020574 x) = _
  rw [_root_.GD.N0232.N0720.N1395.d020559, piecewise_eq_of_mem _ _ _ hproj]
  simp only [_root_.GD.N0232.N0720.N1395.d020570, _root_.GD.N0232.N0720.N1352.d002804, Function.comp_apply, hprior]
  change x 2 + (x 0 - x 2) * _root_.GD.N0232.N0720.N1395.d020557 mu (_root_.GD.N0232.N0720.N1395.d020574 x) =
    x 0 + (x 2 - x 0) * (1 - _root_.GD.N0232.N0720.N1395.d020557 mu (_root_.GD.N0232.N0720.N1395.d020574 x))
  ring



theorem d020578 {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : _root_.GD.N0232.N0720.N1398.d019601 d =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2] _root_.GD.N0232.N0720.N1395.d020557 mu) :
    ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1395.d020552), x ∈ _root_.GD.N0232.N0720.N1395.d020567 →
      _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) x =
        _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1270.d020230 mu ∘ _root_.GD.N0232.N0720.N1351.d002814) (_root_.GD.N0232.N0720.N1395.d020566 x) := by
  filter_upwards [_root_.GD.N0232.N0720.N1395.d020565 hd mu hpost] with x hx
  intro hregular
  exact hx.trans (_root_.GD.N0232.N0720.N1395.d020577 hregular mu)

theorem d020579 {x : _root_.GD.N0232.N0720.N1395.d020552}
    (hx : x ∈ _root_.GD.N0232.N0720.N1394.d020169) :
    x ∈ _root_.GD.N0232.N0720.N1395.d020567 := by
  change 0 < x 1 ^ 2 / 2 ∧ 0 < x 3 ^ 2 / 2 at hx
  constructor
  · intro h
    have hp := hx.1
    simp [h] at hp
  · intro h
    have hp := hx.2
    simp [h] at hp


theorem d020580 {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : _root_.GD.N0232.N0720.N1398.d019601 d =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 2 2]
      fun x ↦ _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) mu) :
    ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1395.d020552),
      x ∈ _root_.GD.N0232.N0720.N1394.d020169 →
        _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) x =
          _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1270.d020230 mu ∘ _root_.GD.N0232.N0720.N1351.d002814) (_root_.GD.N0232.N0720.N1394.d020168 x) := by
  filter_upwards [_root_.GD.N0232.N0720.N1395.d020578 hd mu hpost] with x hx
  intro hphysical
  exact hx (_root_.GD.N0232.N0720.N1395.d020579 hphysical)

theorem d020581 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContinuousOn (_root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1270.d020230 mu ∘ _root_.GD.N0232.N0720.N1351.d002814))
      _root_.GD.N0232.N0720.N1382.d004652 :=
  (_root_.GD.N0232.N0720.N1395.d020571 mu).continuousOn

end
end GD.N0232.N0720.N1395

#print axioms _root_.GD.N0232.N0720.N1395.d020565
#print axioms _root_.GD.N0232.N0720.N1395.d020572
#print axioms _root_.GD.N0232.N0720.N1395.d020580
