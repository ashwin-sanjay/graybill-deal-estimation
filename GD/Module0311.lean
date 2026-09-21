import GD.Module0310
import GD.Module0210
import GD.Module0048
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure


















open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0232.N0720.N1371

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1376
open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0622

noncomputable section

def d004569 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) : _root_.GD.N0232.N0720.N1393.d004495 →L[ℝ] _root_.GD.N0232.N0720.N1393.d004495 :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL _root_.GD.N0232.N0720.N1393.d004494 ∞ 2 2
    (ContinuousMap.toLp ∞ _root_.GD.N0232.N0720.N1393.d004494 ℝ a)

theorem d004570 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1371.d004569 a h = _root_.GD.N0232.N0720.N1372.d004548 a h := rfl

theorem d004571 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h k : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004548 a (h - k) = _root_.GD.N0232.N0720.N1372.d004548 a h - _root_.GD.N0232.N0720.N1372.d004548 a k :=
  (_root_.GD.N0232.N0720.N1371.d004569 a).map_sub h k

theorem d004572 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h k : _root_.GD.N0232.N0720.N1393.d004495) :
    inner ℝ (_root_.GD.N0232.N0720.N1372.d004548 a h) k = inner ℝ h (_root_.GD.N0232.N0720.N1372.d004548 a k) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1372.d004549 a h, _root_.GD.N0232.N0720.N1372.d004549 a k] with u hu ku
  simp [hu, ku, mul_comm, mul_left_comm]

def d004573 (a b : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (ha : ∀ u, 0 < a u) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) where
  toFun u := b u / a u
  continuous_toFun := b.continuous.div a.continuous (fun u ↦ (ha u).ne')

def d004574 (a b : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (ha : ∀ u, 0 < a u) : _root_.GD.N0232.N0720.N1393.d004495 :=
  ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ (_root_.GD.N0232.N0720.N1371.d004573 a b ha)

theorem d004575 (a b : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (ha : ∀ u, 0 < a u) :
    _root_.GD.N0232.N0720.N1371.d004574 a b ha =ᵐ[_root_.GD.N0232.N0720.N1393.d004494] fun u ↦ b u / a u :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _root_.GD.N0232.N0720.N1393.d004494 (_root_.GD.N0232.N0720.N1371.d004573 a b ha)


theorem d004576 (a b : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (ha : ∀ u, 0 < a u) :
    _root_.GD.N0232.N0720.N1372.d004548 a (_root_.GD.N0232.N0720.N1371.d004574 a b ha) = ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ b := by
  apply Lp.ext
  filter_upwards [_root_.GD.N0232.N0720.N1372.d004549 a (_root_.GD.N0232.N0720.N1371.d004574 a b ha), _root_.GD.N0232.N0720.N1371.d004575 a b ha,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _root_.GD.N0232.N0720.N1393.d004494 b] with u hu hm hb
  rw [hu, hm, hb]
  exact mul_div_cancel₀ (b u) (ha u).ne'

def d004577 (a b : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) : ℝ :=
  _root_.GD.N0232.N0720.N1372.d004551 a h - 2 * _root_.GD.N0232.N0720.N1372.d004552 b h


theorem d004578 (a b : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ))
    (ha : ∀ u, 0 < a u) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1371.d004577 a b h = _root_.GD.N0232.N0720.N1371.d004577 a b (_root_.GD.N0232.N0720.N1371.d004574 a b ha) +
      _root_.GD.N0232.N0720.N1372.d004551 a (h - _root_.GD.N0232.N0720.N1371.d004574 a b ha) := by
  have hnormal := _root_.GD.N0232.N0720.N1371.d004576 a b ha
  have hcross : inner ℝ (_root_.GD.N0232.N0720.N1372.d004548 a h) (_root_.GD.N0232.N0720.N1371.d004574 a b ha) =
      inner ℝ (ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ b) h := by
    rw [_root_.GD.N0232.N0720.N1371.d004572, hnormal, real_inner_comm]
  unfold _root_.GD.N0232.N0720.N1371.d004577 _root_.GD.N0232.N0720.N1372.d004551 _root_.GD.N0232.N0720.N1372.d004552
  simp only [_root_.GD.N0232.N0720.N1371.d004571, inner_sub_left, inner_sub_right,
    hnormal, hcross]
  ring

theorem d004579 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (ha : ∀ u, 0 ≤ a u) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    0 ≤ _root_.GD.N0232.N0720.N1372.d004551 a h := by
  rw [_root_.GD.N0232.N0720.N1372.d004563 a ha]
  exact sq_nonneg _

theorem d004580 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (ha : ∀ u, 0 < a u)
    (h : _root_.GD.N0232.N0720.N1393.d004495) : _root_.GD.N0232.N0720.N1372.d004551 a h = 0 ↔ h = 0 := by
  constructor
  · intro hzero
    rw [_root_.GD.N0232.N0720.N1372.d004563 a (fun u ↦ (ha u).le)] at hzero
    have hz : _root_.GD.N0232.N0720.N1372.d004548 (_root_.GD.N0232.N0720.N1372.d004562 a) h = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    apply Lp.ext
    filter_upwards [_root_.GD.N0232.N0720.N1372.d004549 (_root_.GD.N0232.N0720.N1372.d004562 a) h,
      Lp.coeFn_zero ℝ 2 _root_.GD.N0232.N0720.N1393.d004494] with u hu h0
    rw [hz, h0] at hu
    have hroot : Real.sqrt (a u) ≠ 0 := (Real.sqrt_pos.2 (ha u)).ne'
    have hh : h u = 0 := (mul_eq_zero.mp hu.symm).resolve_left hroot
    exact hh.trans h0.symm
  · rintro rfl
    simp [_root_.GD.N0232.N0720.N1372.d004551, _root_.GD.N0232.N0720.N1372.d004548]

theorem d004581 (a b : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ))
    (ha : ∀ u, 0 < a u) {h : _root_.GD.N0232.N0720.N1393.d004495}
    (hmin : _root_.GD.N0232.N0720.N1371.d004577 a b h ≤ _root_.GD.N0232.N0720.N1371.d004577 a b (_root_.GD.N0232.N0720.N1371.d004574 a b ha)) :
    h = _root_.GD.N0232.N0720.N1371.d004574 a b ha := by
  rw [_root_.GD.N0232.N0720.N1371.d004578 a b ha h] at hmin
  have hz : _root_.GD.N0232.N0720.N1372.d004551 a (h - _root_.GD.N0232.N0720.N1371.d004574 a b ha) = 0 :=
    le_antisymm (by linarith) (_root_.GD.N0232.N0720.N1371.d004579 a (fun u ↦ (ha u).le) _)
  exact sub_eq_zero.mp ((_root_.GD.N0232.N0720.N1371.d004580 a ha _).mp hz)

def d004582 (h : _root_.GD.N0232.N0720.N1393.d004495) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ h).comp
    (((ContinuousLinearMap.mul ℝ ℝ).holderL _root_.GD.N0232.N0720.N1393.d004494 ∞ 2 2).flip h |>.comp
      (ContinuousMap.toLp ∞ _root_.GD.N0232.N0720.N1393.d004494 ℝ))

def d004583 (h : _root_.GD.N0232.N0720.N1393.d004495) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ h).comp (ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ)

theorem d004584 (h : _root_.GD.N0232.N0720.N1393.d004495) (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) :
    _root_.GD.N0232.N0720.N1371.d004582 h a = _root_.GD.N0232.N0720.N1372.d004551 a h := by
  change inner ℝ h (_root_.GD.N0232.N0720.N1372.d004548 a h) = inner ℝ (_root_.GD.N0232.N0720.N1372.d004548 a h) h
  exact real_inner_comm _ _

theorem d004585 (h : _root_.GD.N0232.N0720.N1393.d004495) (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) :
    _root_.GD.N0232.N0720.N1371.d004583 h a = _root_.GD.N0232.N0720.N1372.d004552 a h := by
  change inner ℝ h (ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ a) =
    inner ℝ (ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ a) h
  exact real_inner_comm _ _

variable {I : Type*} [Fintype I]

def d004586 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1372.d004522 (q i)) • _root_.GD.N0232.N0720.N1372.d004534 5 (q i)

def d004587 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1372.d004522 (q i) * (q i).1) • _root_.GD.N0232.N0720.N1372.d004534 4 (q i)

def d004588 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) : ℝ :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1372.d004522 (q i) * (q i).1 ^ 2) *
    (∫ u, _root_.GD.N0232.N0720.N1372.d004534 3 (q i) u ∂_root_.GD.N0232.N0720.N1393.d004494)

def d004589 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1393.d004495) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0720.N1372.d004546 (q i) h

theorem d004590 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1393.d004493) :
    _root_.GD.N0232.N0720.N1371.d004586 q w u =
      ∑ i, w i * _root_.GD.N0232.N0720.N1372.d004522 (q i) *
        _root_.GD.N0232.N0720.N1377.d002852 5 (_root_.GD.N0232.N0720.N1372.d004520 (q i) u) (_root_.GD.N0232.N0720.N1372.d004521 (q i) u) := by
  simp [_root_.GD.N0232.N0720.N1371.d004586, _root_.GD.N0232.N0720.N1372.d004534, smul_eq_mul]

theorem d004591 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1393.d004493) :
    _root_.GD.N0232.N0720.N1371.d004587 q w u =
      ∑ i, w i * _root_.GD.N0232.N0720.N1372.d004522 (q i) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 4 (_root_.GD.N0232.N0720.N1372.d004520 (q i) u) (_root_.GD.N0232.N0720.N1372.d004521 (q i) u) := by
  simp [_root_.GD.N0232.N0720.N1371.d004587, _root_.GD.N0232.N0720.N1372.d004534, smul_eq_mul]

theorem d004592 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (u : _root_.GD.N0232.N0720.N1393.d004493) :
    0 < _root_.GD.N0232.N0720.N1371.d004586 q w u := by
  rw [_root_.GD.N0232.N0720.N1371.d004590]
  obtain ⟨j, hj⟩ := hpositive
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (hw i) (_root_.GD.N0232.N0720.N1372.d004525 (q i)).le)
      (_root_.GD.N0232.N0720.N1377.d002861 5 (_root_.GD.N0232.N0720.N1372.d004528 (q i) u) (_root_.GD.N0232.N0720.N1372.d004521 (q i) u)).le
  · exact ⟨j, Finset.mem_univ j,
      mul_pos (mul_pos hj (_root_.GD.N0232.N0720.N1372.d004525 (q j)))
        (_root_.GD.N0232.N0720.N1377.d002861 5 (_root_.GD.N0232.N0720.N1372.d004528 (q j) u) (_root_.GD.N0232.N0720.N1372.d004521 (q j) u))⟩

theorem d004593 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004551 (_root_.GD.N0232.N0720.N1371.d004586 q w) h =
      ∑ i, (w i * _root_.GD.N0232.N0720.N1372.d004522 (q i)) * _root_.GD.N0232.N0720.N1372.d004551 (_root_.GD.N0232.N0720.N1372.d004534 5 (q i)) h := by
  rw [← _root_.GD.N0232.N0720.N1371.d004584, _root_.GD.N0232.N0720.N1371.d004586, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, _root_.GD.N0232.N0720.N1371.d004584]
  rfl

theorem d004594 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004552 (_root_.GD.N0232.N0720.N1371.d004587 q w) h =
      ∑ i, (w i * _root_.GD.N0232.N0720.N1372.d004522 (q i) * (q i).1) *
        _root_.GD.N0232.N0720.N1372.d004552 (_root_.GD.N0232.N0720.N1372.d004534 4 (q i)) h := by
  rw [← _root_.GD.N0232.N0720.N1371.d004585, _root_.GD.N0232.N0720.N1371.d004587, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, _root_.GD.N0232.N0720.N1371.d004585]
  rfl



theorem d004595 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1371.d004589 q w h =
      _root_.GD.N0232.N0720.N1371.d004577 (_root_.GD.N0232.N0720.N1371.d004586 q w) (_root_.GD.N0232.N0720.N1371.d004587 q w) h +
        _root_.GD.N0232.N0720.N1371.d004588 q w := by
  unfold _root_.GD.N0232.N0720.N1371.d004577
  rw [_root_.GD.N0232.N0720.N1371.d004593, _root_.GD.N0232.N0720.N1371.d004594]
  unfold _root_.GD.N0232.N0720.N1371.d004589 _root_.GD.N0232.N0720.N1371.d004588
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1372.d004558]
  ring

def d004596 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) : _root_.GD.N0232.N0720.N1393.d004495 :=
  _root_.GD.N0232.N0720.N1371.d004574 (_root_.GD.N0232.N0720.N1371.d004586 q w) (_root_.GD.N0232.N0720.N1371.d004587 q w)
    (_root_.GD.N0232.N0720.N1371.d004592 q w hw hpositive)

theorem d004597 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) :
    _root_.GD.N0232.N0720.N1371.d004596 q w hw hpositive =ᵐ[_root_.GD.N0232.N0720.N1393.d004494] fun u ↦
      _root_.GD.N0232.N0720.N1371.d004587 q w u / _root_.GD.N0232.N0720.N1371.d004586 q w u :=
  _root_.GD.N0232.N0720.N1371.d004575 _ _ _

theorem d004598 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : _root_.GD.N0232.N0720.N1393.d004495)
    (hmin : ∀ k, _root_.GD.N0232.N0720.N1371.d004589 q w h ≤ _root_.GD.N0232.N0720.N1371.d004589 q w k) :
    h = _root_.GD.N0232.N0720.N1371.d004596 q w hw hpositive := by
  apply _root_.GD.N0232.N0720.N1371.d004581
  have hm := hmin (_root_.GD.N0232.N0720.N1371.d004596 q w hw hpositive)
  rw [_root_.GD.N0232.N0720.N1371.d004595, _root_.GD.N0232.N0720.N1371.d004595] at hm
  simpa only [_root_.GD.N0232.N0720.N1371.d004596] using!
    (add_le_add_iff_right (_root_.GD.N0232.N0720.N1371.d004588 q w)).mp hm

def d004599 (q : I → _root_.GD.N0232.N0720.N1372.d004518) : Option I → _root_.GD.N0232.N0720.N1372.d004518
  | none => _root_.GD.N0232.N0720.N1372.d004566
  | some i => q i

def d004600 (w : I → ℝ) : Option I → ℝ
  | none => 1
  | some i => w i

omit [Fintype I] in
theorem d004601 (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1371.d004600 w i := by
  intro i
  cases i with
  | none => exact zero_le_one
  | some i => exact hw i

omit [Fintype I] in
theorem d004602 (w : I → ℝ) : ∃ i, 0 < _root_.GD.N0232.N0720.N1371.d004600 w i :=
  ⟨none, zero_lt_one⟩

theorem d004603 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1371.d004589 (_root_.GD.N0232.N0720.N1371.d004599 q) (_root_.GD.N0232.N0720.N1371.d004600 w) h =
      _root_.GD.N0232.N0720.N1372.d004546 _root_.GD.N0232.N0720.N1372.d004566 h + ∑ i, w i * _root_.GD.N0232.N0720.N1372.d004546 (q i) h := by
  simp [_root_.GD.N0232.N0720.N1371.d004589, Fintype.sum_option, _root_.GD.N0232.N0720.N1371.d004599, _root_.GD.N0232.N0720.N1371.d004600]



theorem d004604 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1393.d004495)
    (hbayes : _root_.GD.N0230.N0622.d000607 univ _root_.GD.N0232.N0720.N1372.d004546 _root_.GD.N0232.N0720.N1372.d004566 q w h) :
    h = _root_.GD.N0232.N0720.N1371.d004596 (_root_.GD.N0232.N0720.N1371.d004599 q) (_root_.GD.N0232.N0720.N1371.d004600 w)
      (_root_.GD.N0232.N0720.N1371.d004601 w hbayes.1) (_root_.GD.N0232.N0720.N1371.d004602 w) := by
  apply _root_.GD.N0232.N0720.N1371.d004598
  intro k
  rw [_root_.GD.N0232.N0720.N1371.d004603, _root_.GD.N0232.N0720.N1371.d004603]
  exact hbayes.2 k (mem_univ k)

local instance : Nonempty _root_.GD.N0232.N0720.N1372.d004518 := ⟨_root_.GD.N0232.N0720.N1372.d004566⟩

def d004605 : ℕ → _root_.GD.N0232.N0720.N1372.d004518 := TopologicalSpace.denseSeq _root_.GD.N0232.N0720.N1372.d004518

theorem d004606 : DenseRange _root_.GD.N0232.N0720.N1371.d004605 :=
  TopologicalSpace.denseRange_denseSeq _root_.GD.N0232.N0720.N1372.d004518

def d004607 (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem d004608 (n : ℕ) : 0 < _root_.GD.N0232.N0720.N1371.d004607 n := by unfold _root_.GD.N0232.N0720.N1371.d004607; positivity

theorem d004609 : Antitone _root_.GD.N0232.N0720.N1371.d004607 := by
  intro m n hmn
  apply one_div_le_one_div_of_le (show (0 : ℝ) < (m : ℝ) + 1 by positivity)
  exact add_le_add (Nat.cast_le.mpr hmn) le_rfl

theorem d004610 : Tendsto _root_.GD.N0232.N0720.N1371.d004607 atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat




theorem d004611 (h : _root_.GD.N0232.N0720.N1393.d004495)
    (hadmissible : _root_.GD.N0230.N0556.d000031 _root_.GD.N0232.N0720.N1372.d004546 h) :
    ∃ (p : ℕ → _root_.GD.N0232.N0720.N1393.d004495) (w : ∀ n, Fin n → ℝ),
      Tendsto p atTop (𝓝 h) ∧ (∀ n i, 0 ≤ w n i) ∧ ∀ n,
        p n =ᵐ[_root_.GD.N0232.N0720.N1393.d004494] fun u ↦
          _root_.GD.N0232.N0720.N1371.d004587 (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin n ↦ _root_.GD.N0232.N0720.N1371.d004605 i))
              (_root_.GD.N0232.N0720.N1371.d004600 (w n)) u /
            _root_.GD.N0232.N0720.N1371.d004586 (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin n ↦ _root_.GD.N0232.N0720.N1371.d004605 i))
              (_root_.GD.N0232.N0720.N1371.d004600 (w n)) u := by
  have hadmissible' : _root_.GD.N0230.N0556.d000031 (fun q (d : (univ : Set _root_.GD.N0232.N0720.N1393.d004495)) ↦ _root_.GD.N0232.N0720.N1372.d004546 q d)
      ⟨h, mem_univ h⟩ := by
    rintro ⟨d, hweak, q, hstrict⟩
    exact hadmissible ⟨d.1, hweak, q, hstrict⟩
  obtain ⟨p, w, hlimit, hcertificate⟩ :=
    _root_.GD.N0230.N0622.d000623 univ _root_.GD.N0232.N0720.N1372.d004546 _root_.GD.N0232.N0720.N1371.d004605
      _root_.GD.N0232.N0720.N1372.d004566 h (mem_univ h) isClosed_univ convex_univ
      _root_.GD.N0232.N0720.N1372.d004560 _root_.GD.N0232.N0720.N1372.d004565
      (fun d _ ↦ _root_.GD.N0232.N0720.N1372.d004561 d) _root_.GD.N0232.N0720.N1371.d004606
      _root_.GD.N0232.N0720.N1393.d004506 0 _root_.GD.N0232.N0720.N1393.d004507
      (fun d _ ↦ by simpa only [add_zero] using _root_.GD.N0232.N0720.N1372.d004568 d)
      hadmissible' _root_.GD.N0232.N0720.N1371.d004607 _root_.GD.N0232.N0720.N1371.d004608 _root_.GD.N0232.N0720.N1371.d004609 _root_.GD.N0232.N0720.N1371.d004610
  refine ⟨p, w, hlimit, fun n ↦ (hcertificate n).2.1, fun n ↦ ?_⟩
  have heq := _root_.GD.N0232.N0720.N1371.d004604
    (fun i : Fin n ↦ _root_.GD.N0232.N0720.N1371.d004605 i) (w n) (p n) (hcertificate n).2
  rw [heq]
  exact _root_.GD.N0232.N0720.N1371.d004597 _ _ _ _



theorem d004612 (h : _root_.GD.N0232.N0720.N1393.d004495)
    (hadmissible : _root_.GD.N0230.N0556.d000031 _root_.GD.N0232.N0720.N1372.d004546 h) :
    ∃ (w : ∀ n, Fin n → ℝ) (ns : ℕ → ℕ),
      (∀ n i, 0 ≤ w n i) ∧ StrictMono ns ∧ ∀ᵐ u ∂_root_.GD.N0232.N0720.N1393.d004494,
        Tendsto (fun j ↦
          _root_.GD.N0232.N0720.N1371.d004587 (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i))
              (_root_.GD.N0232.N0720.N1371.d004600 (w (ns j))) u /
            _root_.GD.N0232.N0720.N1371.d004586 (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i))
              (_root_.GD.N0232.N0720.N1371.d004600 (w (ns j))) u)
          atTop (𝓝 (h u)) := by
  obtain ⟨p, w, hlimit, hw, hratio⟩ := _root_.GD.N0232.N0720.N1371.d004611 h hadmissible
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlimit).exists_seq_tendsto_ae
  refine ⟨w, ns, hw, hns, ?_⟩
  have hratios : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1393.d004494, ∀ n,
      p n u = _root_.GD.N0232.N0720.N1371.d004587
          (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin n ↦ _root_.GD.N0232.N0720.N1371.d004605 i)) (_root_.GD.N0232.N0720.N1371.d004600 (w n)) u /
        _root_.GD.N0232.N0720.N1371.d004586
          (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin n ↦ _root_.GD.N0232.N0720.N1371.d004605 i)) (_root_.GD.N0232.N0720.N1371.d004600 (w n)) u :=
    ae_all_iff.mpr hratio
  filter_upwards [hpoint, hratios] with u hu huratio
  simpa only [huratio] using hu





def d004613 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ := (Real.sqrt (_root_.GD.N0232.N0720.N1372.d004519 q))⁻¹

def d004614 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ := q.1 * _root_.GD.N0232.N0720.N1371.d004613 q

def d004615 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ :=
  _root_.GD.N0232.N0720.N1372.d004522 q * (_root_.GD.N0232.N0720.N1371.d004613 q ^ 6)⁻¹ * 8

theorem d004616 (q : _root_.GD.N0232.N0720.N1372.d004518) : 0 < _root_.GD.N0232.N0720.N1371.d004613 q :=
  inv_pos.mpr (Real.sqrt_pos.2 (_root_.GD.N0232.N0720.N1372.d004524 q))

theorem d004617 (q : _root_.GD.N0232.N0720.N1372.d004518) : _root_.GD.N0232.N0720.N1371.d004613 q ^ 2 = 1 / _root_.GD.N0232.N0720.N1372.d004519 q := by
  unfold _root_.GD.N0232.N0720.N1371.d004613
  rw [inv_pow, Real.sq_sqrt (_root_.GD.N0232.N0720.N1372.d004524 q).le]
  simp only [one_div]

theorem d004618 (q : _root_.GD.N0232.N0720.N1372.d004518) : 0 < _root_.GD.N0232.N0720.N1371.d004615 q := by
  exact mul_pos
    (mul_pos (_root_.GD.N0232.N0720.N1372.d004525 q) (inv_pos.mpr (pow_pos (_root_.GD.N0232.N0720.N1371.d004616 q) 6)))
    (by norm_num)

def d004619 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  _root_.GD.N0232.N0720.N1376.d002892 q.2.1 (x 0) (x 2) (x 1 ^ 2 / 2) (x 3 ^ 2 / 2)

def d004620 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ := _root_.GD.N0232.N0720.N1376.d002893 q.2.1 (x 0) (x 2)

theorem d004621 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1372.d004520 q x = _root_.GD.N0232.N0720.N1371.d004613 q ^ 2 * _root_.GD.N0232.N0720.N1371.d004619 q x := by
  rw [_root_.GD.N0232.N0720.N1371.d004617]
  unfold _root_.GD.N0232.N0720.N1372.d004520 _root_.GD.N0232.N0720.N1371.d004619 _root_.GD.N0232.N0720.N1376.d002892 _root_.GD.N0232.N0720.N1372.d004519
  field_simp [q.2.2.1.ne', (sub_pos.mpr q.2.2.2).ne']

theorem d004622 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1372.d004521 q x = _root_.GD.N0232.N0720.N1371.d004613 q * (_root_.GD.N0232.N0720.N1371.d004620 q x * _root_.GD.N0232.N0720.N1371.d004614 q) := by
  calc
    _root_.GD.N0232.N0720.N1372.d004521 q x = _root_.GD.N0232.N0720.N1371.d004613 q ^ 2 * _root_.GD.N0232.N0720.N1371.d004620 q x * q.1 := by
      rw [_root_.GD.N0232.N0720.N1371.d004617]
      unfold _root_.GD.N0232.N0720.N1372.d004521 _root_.GD.N0232.N0720.N1371.d004620 _root_.GD.N0232.N0720.N1376.d002893 _root_.GD.N0232.N0720.N1372.d004519
      field_simp [q.2.2.1.ne', (sub_pos.mpr q.2.2.2).ne']
    _ = _ := by unfold _root_.GD.N0232.N0720.N1371.d004614; ring

theorem d004623 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1372.d004522 q * _root_.GD.N0232.N0720.N1377.d002852 5 (_root_.GD.N0232.N0720.N1372.d004520 q x) (_root_.GD.N0232.N0720.N1372.d004521 q x) =
      _root_.GD.N0232.N0720.N1371.d004615 q *
        _root_.GD.N0232.N0720.N1376.d002894 (_root_.GD.N0232.N0720.N1371.d004614 q) q.2.1 (x 0) (x 2) (x 1 ^ 2 / 2) (x 3 ^ 2 / 2) := by
  rw [_root_.GD.N0232.N0720.N1371.d004621, _root_.GD.N0232.N0720.N1371.d004622,
    _root_.GD.N0232.N0720.N1377.d002866 5 (_root_.GD.N0232.N0720.N1371.d004619 q x) (_root_.GD.N0232.N0720.N1371.d004620 q x * _root_.GD.N0232.N0720.N1371.d004614 q) (_root_.GD.N0232.N0720.N1371.d004616 q)]
  simp only [_root_.GD.N0232.N0720.N1371.d004615, _root_.GD.N0232.N0720.N1376.d002894, _root_.GD.N0232.N0720.N1371.d004619, _root_.GD.N0232.N0720.N1371.d004620, Nat.reduceAdd]
  ring

theorem d004624 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1372.d004522 q * q.1 * _root_.GD.N0232.N0720.N1377.d002852 4 (_root_.GD.N0232.N0720.N1372.d004520 q x) (_root_.GD.N0232.N0720.N1372.d004521 q x) =
      _root_.GD.N0232.N0720.N1371.d004615 q *
        _root_.GD.N0232.N0720.N1376.d002895 (_root_.GD.N0232.N0720.N1371.d004614 q) q.2.1 (x 0) (x 2) (x 1 ^ 2 / 2) (x 3 ^ 2 / 2) := by
  rw [_root_.GD.N0232.N0720.N1371.d004621, _root_.GD.N0232.N0720.N1371.d004622,
    _root_.GD.N0232.N0720.N1377.d002866 4 (_root_.GD.N0232.N0720.N1371.d004619 q x) (_root_.GD.N0232.N0720.N1371.d004620 q x * _root_.GD.N0232.N0720.N1371.d004614 q) (_root_.GD.N0232.N0720.N1371.d004616 q)]
  simp only [_root_.GD.N0232.N0720.N1371.d004615, _root_.GD.N0232.N0720.N1376.d002895, _root_.GD.N0232.N0720.N1371.d004619, _root_.GD.N0232.N0720.N1371.d004620, Nat.reduceAdd]
  unfold _root_.GD.N0232.N0720.N1371.d004614
  field_simp [(_root_.GD.N0232.N0720.N1371.d004616 q).ne']

theorem d004625 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1393.d004493) :
    _root_.GD.N0232.N0720.N1371.d004586 q w u = ∑ i, (w i * _root_.GD.N0232.N0720.N1371.d004615 (q i)) *
      _root_.GD.N0232.N0720.N1376.d002894 (_root_.GD.N0232.N0720.N1371.d004614 (q i)) (q i).2.1
        ((u : _root_.GD.N0232.N0720.N1393.d004492) 0) ((u : _root_.GD.N0232.N0720.N1393.d004492) 2)
        ((u : _root_.GD.N0232.N0720.N1393.d004492) 1 ^ 2 / 2) ((u : _root_.GD.N0232.N0720.N1393.d004492) 3 ^ 2 / 2) := by
  rw [_root_.GD.N0232.N0720.N1371.d004590]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, _root_.GD.N0232.N0720.N1371.d004623]
  ring

theorem d004626 (q : I → _root_.GD.N0232.N0720.N1372.d004518) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1393.d004493) :
    _root_.GD.N0232.N0720.N1371.d004587 q w u = ∑ i, (w i * _root_.GD.N0232.N0720.N1371.d004615 (q i)) *
      _root_.GD.N0232.N0720.N1376.d002895 (_root_.GD.N0232.N0720.N1371.d004614 (q i)) (q i).2.1
        ((u : _root_.GD.N0232.N0720.N1393.d004492) 0) ((u : _root_.GD.N0232.N0720.N1393.d004492) 2)
        ((u : _root_.GD.N0232.N0720.N1393.d004492) 1 ^ 2 / 2) ((u : _root_.GD.N0232.N0720.N1393.d004492) 3 ^ 2 / 2) := by
  rw [_root_.GD.N0232.N0720.N1371.d004591]
  apply Finset.sum_congr rfl
  intro i _
  calc
    w i * _root_.GD.N0232.N0720.N1372.d004522 (q i) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 4 (_root_.GD.N0232.N0720.N1372.d004520 (q i) u) (_root_.GD.N0232.N0720.N1372.d004521 (q i) u) =
      w i * (_root_.GD.N0232.N0720.N1372.d004522 (q i) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 4 (_root_.GD.N0232.N0720.N1372.d004520 (q i) u) (_root_.GD.N0232.N0720.N1372.d004521 (q i) u)) := by ring
    _ = _ := by rw [_root_.GD.N0232.N0720.N1371.d004624]; ring



theorem d004627 (h : _root_.GD.N0232.N0720.N1393.d004495) (hadmissible : _root_.GD.N0230.N0556.d000031 _root_.GD.N0232.N0720.N1372.d004546 h) :
    ∃ (w : ∀ n, Fin n → ℝ) (ns : ℕ → ℕ),
      (∀ n i, 0 ≤ w n i) ∧ StrictMono ns ∧ ∀ᵐ (u : _root_.GD.N0232.N0720.N1393.d004493) ∂_root_.GD.N0232.N0720.N1393.d004494,
        Tendsto (fun j ↦
          (∑ i : Option (Fin (ns j)),
            (_root_.GD.N0232.N0720.N1371.d004600 (w (ns j)) i *
              _root_.GD.N0232.N0720.N1371.d004615 (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i) i)) *
              _root_.GD.N0232.N0720.N1376.d002895 (_root_.GD.N0232.N0720.N1371.d004614 (_root_.GD.N0232.N0720.N1371.d004599
                (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i) i))
                (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i) i).2.1
                ((u : _root_.GD.N0232.N0720.N1393.d004492) 0) ((u : _root_.GD.N0232.N0720.N1393.d004492) 2)
                ((u : _root_.GD.N0232.N0720.N1393.d004492) 1 ^ 2 / 2) ((u : _root_.GD.N0232.N0720.N1393.d004492) 3 ^ 2 / 2)) /
          (∑ i : Option (Fin (ns j)),
            (_root_.GD.N0232.N0720.N1371.d004600 (w (ns j)) i *
              _root_.GD.N0232.N0720.N1371.d004615 (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i) i)) *
              _root_.GD.N0232.N0720.N1376.d002894 (_root_.GD.N0232.N0720.N1371.d004614 (_root_.GD.N0232.N0720.N1371.d004599
                (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i) i))
                (_root_.GD.N0232.N0720.N1371.d004599 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1371.d004605 i) i).2.1
                ((u : _root_.GD.N0232.N0720.N1393.d004492) 0) ((u : _root_.GD.N0232.N0720.N1393.d004492) 2)
                ((u : _root_.GD.N0232.N0720.N1393.d004492) 1 ^ 2 / 2) ((u : _root_.GD.N0232.N0720.N1393.d004492) 3 ^ 2 / 2)))
          atTop (𝓝 (h u)) := by
  obtain ⟨w, ns, hw, hns, hlimit⟩ := _root_.GD.N0232.N0720.N1371.d004612 h hadmissible
  exact ⟨w, ns, hw, hns, by
    simpa only [_root_.GD.N0232.N0720.N1371.d004626, _root_.GD.N0232.N0720.N1371.d004625] using hlimit⟩

end

end GD.N0232.N0720.N1371

#print axioms _root_.GD.N0232.N0720.N1371.d004578
#print axioms _root_.GD.N0232.N0720.N1371.d004598
#print axioms _root_.GD.N0232.N0720.N1371.d004611
#print axioms _root_.GD.N0232.N0720.N1371.d004612
#print axioms _root_.GD.N0232.N0720.N1371.d004627
