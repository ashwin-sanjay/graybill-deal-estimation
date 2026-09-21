import GD.Module1216
import GD.Module0048
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure













open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0232.N0720.N1314

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0622

noncomputable section

section Hilbert
variable {d : ℕ}

def d019681 (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) : (_root_.GD.N0232.N0720.N1341.d004417 d) →L[ℝ] (_root_.GD.N0232.N0720.N1341.d004417 d) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (_root_.GD.N0232.N0720.N1341.d004416 d) ∞ 2 2
    (ContinuousMap.toLp ∞ (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ a)

theorem d019682 (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    _root_.GD.N0232.N0720.N1314.d019681 a h = _root_.GD.N0232.N0720.N1316.d004471 a h := rfl

theorem d019683 (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (h k : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    _root_.GD.N0232.N0720.N1316.d004471 a (h - k) = _root_.GD.N0232.N0720.N1316.d004471 a h - _root_.GD.N0232.N0720.N1316.d004471 a k :=
  (_root_.GD.N0232.N0720.N1314.d019681 a).map_sub h k

theorem d019684 (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (h k : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    inner ℝ (_root_.GD.N0232.N0720.N1316.d004471 a h) k = inner ℝ h (_root_.GD.N0232.N0720.N1316.d004471 a k) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1316.d004472 a h, _root_.GD.N0232.N0720.N1316.d004472 a k] with u hu ku
  simp [hu, ku, mul_comm, mul_left_comm]

def d019685 (a b : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (ha : ∀ u, 0 < a u) : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ) where
  toFun u := b u / a u
  continuous_toFun := b.continuous.div a.continuous (fun u ↦ (ha u).ne')

def d019686 (a b : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (ha : ∀ u, 0 < a u) : (_root_.GD.N0232.N0720.N1341.d004417 d) :=
  ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0720.N1314.d019685 a b ha)

theorem d019687 (a b : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (ha : ∀ u, 0 < a u) :
    _root_.GD.N0232.N0720.N1314.d019686 a b ha =ᵐ[(_root_.GD.N0232.N0720.N1341.d004416 d)] fun u ↦ b u / a u :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (_root_.GD.N0232.N0720.N1341.d004416 d) (_root_.GD.N0232.N0720.N1314.d019685 a b ha)


theorem d019688 (a b : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (ha : ∀ u, 0 < a u) :
    _root_.GD.N0232.N0720.N1316.d004471 a (_root_.GD.N0232.N0720.N1314.d019686 a b ha) = ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ b := by
  apply Lp.ext
  filter_upwards [_root_.GD.N0232.N0720.N1316.d004472 a (_root_.GD.N0232.N0720.N1314.d019686 a b ha), _root_.GD.N0232.N0720.N1314.d019687 a b ha,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (_root_.GD.N0232.N0720.N1341.d004416 d) b] with u hu hm hb
  rw [hu, hm, hb]
  exact mul_div_cancel₀ (b u) (ha u).ne'

def d019689 (a b : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004474 a h - 2 * _root_.GD.N0232.N0720.N1316.d004475 b h


theorem d019690 (a b : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ))
    (ha : ∀ u, 0 < a u) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    _root_.GD.N0232.N0720.N1314.d019689 a b h = _root_.GD.N0232.N0720.N1314.d019689 a b (_root_.GD.N0232.N0720.N1314.d019686 a b ha) +
      _root_.GD.N0232.N0720.N1316.d004474 a (h - _root_.GD.N0232.N0720.N1314.d019686 a b ha) := by
  have hnormal := _root_.GD.N0232.N0720.N1314.d019688 a b ha
  have hcross : inner ℝ (_root_.GD.N0232.N0720.N1316.d004471 a h) (_root_.GD.N0232.N0720.N1314.d019686 a b ha) =
      inner ℝ (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ b) h := by
    rw [_root_.GD.N0232.N0720.N1314.d019684, hnormal, real_inner_comm]
  unfold _root_.GD.N0232.N0720.N1314.d019689 _root_.GD.N0232.N0720.N1316.d004474 _root_.GD.N0232.N0720.N1316.d004475
  simp only [_root_.GD.N0232.N0720.N1314.d019683, inner_sub_left, inner_sub_right,
    hnormal, hcross]
  ring

theorem d019691 (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (ha : ∀ u, 0 ≤ a u) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    0 ≤ _root_.GD.N0232.N0720.N1316.d004474 a h := by
  rw [_root_.GD.N0232.N0720.N1316.d004486 a ha]
  exact sq_nonneg _

theorem d019692 (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) (ha : ∀ u, 0 < a u)
    (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) : _root_.GD.N0232.N0720.N1316.d004474 a h = 0 ↔ h = 0 := by
  constructor
  · intro hzero
    rw [_root_.GD.N0232.N0720.N1316.d004486 a (fun u ↦ (ha u).le)] at hzero
    have hz : _root_.GD.N0232.N0720.N1316.d004471 (_root_.GD.N0232.N0720.N1316.d004485 a) h = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    apply Lp.ext
    filter_upwards [_root_.GD.N0232.N0720.N1316.d004472 (_root_.GD.N0232.N0720.N1316.d004485 a) h,
      Lp.coeFn_zero ℝ 2 (_root_.GD.N0232.N0720.N1341.d004416 d)] with u hu h0
    rw [hz, h0] at hu
    have hroot : Real.sqrt (a u) ≠ 0 := (Real.sqrt_pos.2 (ha u)).ne'
    have hh : h u = 0 := (mul_eq_zero.mp hu.symm).resolve_left hroot
    exact hh.trans h0.symm
  · rintro rfl
    simp [_root_.GD.N0232.N0720.N1316.d004474, _root_.GD.N0232.N0720.N1316.d004471]

theorem d019693 (a b : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ))
    (ha : ∀ u, 0 < a u) {h : (_root_.GD.N0232.N0720.N1341.d004417 d)}
    (hmin : _root_.GD.N0232.N0720.N1314.d019689 a b h ≤ _root_.GD.N0232.N0720.N1314.d019689 a b (_root_.GD.N0232.N0720.N1314.d019686 a b ha)) :
    h = _root_.GD.N0232.N0720.N1314.d019686 a b ha := by
  rw [_root_.GD.N0232.N0720.N1314.d019690 a b ha h] at hmin
  have hz : _root_.GD.N0232.N0720.N1316.d004474 a (h - _root_.GD.N0232.N0720.N1314.d019686 a b ha) = 0 :=
    le_antisymm (by linarith) (_root_.GD.N0232.N0720.N1314.d019691 a (fun u ↦ (ha u).le) _)
  exact sub_eq_zero.mp ((_root_.GD.N0232.N0720.N1314.d019692 a ha _).mp hz)

def d019694 (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ h).comp
    (((ContinuousLinearMap.mul ℝ ℝ).holderL (_root_.GD.N0232.N0720.N1341.d004416 d) ∞ 2 2).flip h |>.comp
      (ContinuousMap.toLp ∞ (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ))

def d019695 (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ h).comp (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ)

theorem d019696 (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) :
    _root_.GD.N0232.N0720.N1314.d019694 h a = _root_.GD.N0232.N0720.N1316.d004474 a h := by
  change inner ℝ h (_root_.GD.N0232.N0720.N1316.d004471 a h) = inner ℝ (_root_.GD.N0232.N0720.N1316.d004471 a h) h
  exact real_inner_comm _ _

theorem d019697 (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) (a : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ)) :
    _root_.GD.N0232.N0720.N1314.d019695 h a = _root_.GD.N0232.N0720.N1316.d004475 a h := by
  change inner ℝ h (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ a) =
    inner ℝ (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ a) h
  exact real_inner_comm _ _

end Hilbert

section FinitePosterior
variable {d : ℕ}

variable {I : Type*} [Fintype I]

def d019698 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ) :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1316.d004444 (q i)) • _root_.GD.N0232.N0720.N1316.d004457 (d + 2) (q i)

def d019699 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) : C((_root_.GD.N0232.N0720.N1341.d004415 d), ℝ) :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1316.d004444 (q i) * (q i).1) • _root_.GD.N0232.N0720.N1316.d004457 (d + 1) (q i)

def d019700 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) : ℝ :=
  ∑ i, (w i * _root_.GD.N0232.N0720.N1316.d004444 (q i) * (q i).1 ^ 2) *
    (∫ u, _root_.GD.N0232.N0720.N1316.d004457 d (q i) u ∂(_root_.GD.N0232.N0720.N1341.d004416 d))

def d019701 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0720.N1316.d004469 (q i) h

theorem d019702 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) (u : (_root_.GD.N0232.N0720.N1341.d004415 d)) :
    _root_.GD.N0232.N0720.N1314.d019698 q w u =
      ∑ i, w i * _root_.GD.N0232.N0720.N1316.d004444 (q i) *
        _root_.GD.N0232.N0720.N1377.d002852 (d + 2) (_root_.GD.N0232.N0720.N1316.d004441 (q i) u) (_root_.GD.N0232.N0720.N1316.d004442 (q i) u) := by
  simp [_root_.GD.N0232.N0720.N1314.d019698, _root_.GD.N0232.N0720.N1316.d004457, smul_eq_mul]

theorem d019703 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) (u : (_root_.GD.N0232.N0720.N1341.d004415 d)) :
    _root_.GD.N0232.N0720.N1314.d019699 q w u =
      ∑ i, w i * _root_.GD.N0232.N0720.N1316.d004444 (q i) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1316.d004441 (q i) u) (_root_.GD.N0232.N0720.N1316.d004442 (q i) u) := by
  simp [_root_.GD.N0232.N0720.N1314.d019699, _root_.GD.N0232.N0720.N1316.d004457, smul_eq_mul]

theorem d019704 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (u : (_root_.GD.N0232.N0720.N1341.d004415 d)) :
    0 < _root_.GD.N0232.N0720.N1314.d019698 q w u := by
  rw [_root_.GD.N0232.N0720.N1314.d019702]
  obtain ⟨j, hj⟩ := hpositive
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (hw i) (_root_.GD.N0232.N0720.N1316.d004447 (q i)).le)
      (_root_.GD.N0232.N0720.N1377.d002861 (d + 2) (_root_.GD.N0232.N0720.N1316.d004454 (q i) u) (_root_.GD.N0232.N0720.N1316.d004442 (q i) u)).le
  · exact ⟨j, Finset.mem_univ j,
      mul_pos (mul_pos hj (_root_.GD.N0232.N0720.N1316.d004447 (q j)))
        (_root_.GD.N0232.N0720.N1377.d002861 (d + 2) (_root_.GD.N0232.N0720.N1316.d004454 (q j) u) (_root_.GD.N0232.N0720.N1316.d004442 (q j) u))⟩

theorem d019705 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    _root_.GD.N0232.N0720.N1316.d004474 (_root_.GD.N0232.N0720.N1314.d019698 q w) h =
      ∑ i, (w i * _root_.GD.N0232.N0720.N1316.d004444 (q i)) * _root_.GD.N0232.N0720.N1316.d004474 (_root_.GD.N0232.N0720.N1316.d004457 (d + 2) (q i)) h := by
  rw [← _root_.GD.N0232.N0720.N1314.d019696, _root_.GD.N0232.N0720.N1314.d019698, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, _root_.GD.N0232.N0720.N1314.d019696]
  rfl

theorem d019706 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    _root_.GD.N0232.N0720.N1316.d004475 (_root_.GD.N0232.N0720.N1314.d019699 q w) h =
      ∑ i, (w i * _root_.GD.N0232.N0720.N1316.d004444 (q i) * (q i).1) *
        _root_.GD.N0232.N0720.N1316.d004475 (_root_.GD.N0232.N0720.N1316.d004457 (d + 1) (q i)) h := by
  rw [← _root_.GD.N0232.N0720.N1314.d019697, _root_.GD.N0232.N0720.N1314.d019699, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, _root_.GD.N0232.N0720.N1314.d019697]
  rfl



theorem d019707 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ) (h : (_root_.GD.N0232.N0720.N1341.d004417 d)) :
    _root_.GD.N0232.N0720.N1314.d019701 q w h =
      _root_.GD.N0232.N0720.N1314.d019689 (_root_.GD.N0232.N0720.N1314.d019698 q w) (_root_.GD.N0232.N0720.N1314.d019699 q w) h +
        _root_.GD.N0232.N0720.N1314.d019700 q w := by
  unfold _root_.GD.N0232.N0720.N1314.d019689
  rw [_root_.GD.N0232.N0720.N1314.d019705, _root_.GD.N0232.N0720.N1314.d019706]
  unfold _root_.GD.N0232.N0720.N1314.d019701 _root_.GD.N0232.N0720.N1314.d019700
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1316.d004481]
  ring

def d019708 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) : (_root_.GD.N0232.N0720.N1341.d004417 d) :=
  _root_.GD.N0232.N0720.N1314.d019686 (_root_.GD.N0232.N0720.N1314.d019698 q w) (_root_.GD.N0232.N0720.N1314.d019699 q w)
    (_root_.GD.N0232.N0720.N1314.d019704 q w hw hpositive)

theorem d019709 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) :
    _root_.GD.N0232.N0720.N1314.d019708 q w hw hpositive =ᵐ[(_root_.GD.N0232.N0720.N1341.d004416 d)] fun u ↦
      _root_.GD.N0232.N0720.N1314.d019699 q w u / _root_.GD.N0232.N0720.N1314.d019698 q w u :=
  _root_.GD.N0232.N0720.N1314.d019687 _ _ _

theorem d019710 (q : I → (_root_.GD.N0232.N0720.N1316.d004440 d)) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i) (h : (_root_.GD.N0232.N0720.N1341.d004417 d))
    (hmin : ∀ k, _root_.GD.N0232.N0720.N1314.d019701 q w h ≤ _root_.GD.N0232.N0720.N1314.d019701 q w k) :
    h = _root_.GD.N0232.N0720.N1314.d019708 q w hw hpositive := by
  apply _root_.GD.N0232.N0720.N1314.d019693
  have hm := hmin (_root_.GD.N0232.N0720.N1314.d019708 q w hw hpositive)
  rw [_root_.GD.N0232.N0720.N1314.d019707, _root_.GD.N0232.N0720.N1314.d019707] at hm
  simpa only [_root_.GD.N0232.N0720.N1314.d019708] using!
    (add_le_add_iff_right (_root_.GD.N0232.N0720.N1314.d019700 q w)).mp hm

end FinitePosterior



def d019711 (m n d : ℕ) (hdim : m + n = d + 1)
    (q : _root_.GD.N0232.N0720.N1329.d019646) (h : _root_.GD.N0232.N0720.N1341.d004417 d) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004469 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) h

def d019712 : _root_.GD.N0232.N0720.N1329.d019646 :=
  (0, ⟨1 / 2, by constructor <;> norm_num⟩)

section TwoBlock

variable {m n d : ℕ} (hdim : m + n = d + 1)

theorem d019713 : Continuous (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim) := by
  apply Continuous.prodMk continuous_fst
  apply continuous_pi
  intro i
  cases hi : (_root_.GD.N0232.N0720.N1329.d019647 m n d hdim).symm i with
  | inl j =>
      simpa only [_root_.GD.N0232.N0720.N1329.d019660, hi, Sum.elim_inl] using
        (continuous_snd : Continuous (fun q : _root_.GD.N0232.N0720.N1329.d019646 ↦ q.2))
  | inr j =>
      simp only [Sum.elim_inr]
      unfold _root_.GD.N0232.N0720.N1329.d019659
      fun_prop

theorem d019714 :
    _root_.GD.N0232.N0720.N1329.d019660 m n d hdim _root_.GD.N0232.N0720.N1314.d019712 = _root_.GD.N0232.N0720.N1316.d004489 d := by
  apply Prod.ext
  · rfl
  funext i
  cases hi : (_root_.GD.N0232.N0720.N1329.d019647 m n d hdim).symm i with
  | inl j =>
      simp only [_root_.GD.N0232.N0720.N1329.d019660, _root_.GD.N0232.N0720.N1314.d019712, _root_.GD.N0232.N0720.N1316.d004489, hi, Sum.elim_inl]
  | inr j =>
      apply Subtype.ext
      norm_num [_root_.GD.N0232.N0720.N1329.d019660, _root_.GD.N0232.N0720.N1314.d019712, _root_.GD.N0232.N0720.N1316.d004489, hi,
        _root_.GD.N0232.N0720.N1329.d019659]

theorem d019715 (q : _root_.GD.N0232.N0720.N1329.d019646) :
    Continuous (_root_.GD.N0232.N0720.N1314.d019711 m n d hdim q) :=
  _root_.GD.N0232.N0720.N1316.d004483 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q)

theorem d019716 (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Continuous (fun q ↦ _root_.GD.N0232.N0720.N1314.d019711 m n d hdim q h) := by
  simpa only [_root_.GD.N0232.N0720.N1314.d019711, Function.comp_def] using!
    (_root_.GD.N0232.N0720.N1316.d004484 h).comp
      (_root_.GD.N0232.N0720.N1314.d019713 hdim)

theorem d019717 (q : _root_.GD.N0232.N0720.N1329.d019646) :
    ConvexOn ℝ univ (_root_.GD.N0232.N0720.N1314.d019711 m n d hdim q) :=
  _root_.GD.N0232.N0720.N1316.d004488 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q)

theorem d019718 (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0720.N1314.d019711 m n d hdim _root_.GD.N0232.N0720.N1314.d019712 h =
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * _root_.GD.N0232.N0720.N1341.d004428 d) * ‖h‖ ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1314.d019711
  rw [_root_.GD.N0232.N0720.N1314.d019714 hdim, _root_.GD.N0232.N0720.N1316.d004491]

variable {I : Type*} [Fintype I]



def d019719 (q : I → _root_.GD.N0232.N0720.N1329.d019646) : Option I → _root_.GD.N0232.N0720.N1316.d004440 d
  | none => _root_.GD.N0232.N0720.N1329.d019660 m n d hdim _root_.GD.N0232.N0720.N1314.d019712
  | some i => _root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)

def d019720 (w : I → ℝ) : Option I → ℝ
  | none => 1
  | some i => w i

omit [Fintype I] in
theorem d019721 (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1314.d019720 w i := by
  intro i
  cases i with
  | none => exact zero_le_one
  | some i => exact hw i

omit [Fintype I] in
theorem d019722 (w : I → ℝ) : ∃ i, 0 < _root_.GD.N0232.N0720.N1314.d019720 w i :=
  ⟨none, zero_lt_one⟩

theorem d019723 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0720.N1314.d019701 (_root_.GD.N0232.N0720.N1314.d019719 hdim q) (_root_.GD.N0232.N0720.N1314.d019720 w) h =
      _root_.GD.N0232.N0720.N1314.d019711 m n d hdim _root_.GD.N0232.N0720.N1314.d019712 h +
        ∑ i, w i * _root_.GD.N0232.N0720.N1314.d019711 m n d hdim (q i) h := by
  simp [_root_.GD.N0232.N0720.N1314.d019701, Fintype.sum_option, _root_.GD.N0232.N0720.N1314.d019719, _root_.GD.N0232.N0720.N1314.d019720, _root_.GD.N0232.N0720.N1314.d019711]

theorem d019724 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hbayes : _root_.GD.N0230.N0622.d000607 univ (_root_.GD.N0232.N0720.N1314.d019711 m n d hdim)
      _root_.GD.N0232.N0720.N1314.d019712 q w h) :
    h = _root_.GD.N0232.N0720.N1314.d019708 (_root_.GD.N0232.N0720.N1314.d019719 hdim q) (_root_.GD.N0232.N0720.N1314.d019720 w)
      (_root_.GD.N0232.N0720.N1314.d019721 w hbayes.1) (_root_.GD.N0232.N0720.N1314.d019722 w) := by
  apply _root_.GD.N0232.N0720.N1314.d019710
  intro z
  rw [_root_.GD.N0232.N0720.N1314.d019723, _root_.GD.N0232.N0720.N1314.d019723]
  exact hbayes.2 z (mem_univ z)

end TwoBlock

local instance : Nonempty _root_.GD.N0232.N0720.N1329.d019646 := ⟨_root_.GD.N0232.N0720.N1314.d019712⟩

def d019725 : ℕ → _root_.GD.N0232.N0720.N1329.d019646 := TopologicalSpace.denseSeq _root_.GD.N0232.N0720.N1329.d019646

theorem d019726 : DenseRange _root_.GD.N0232.N0720.N1314.d019725 :=
  TopologicalSpace.denseRange_denseSeq _root_.GD.N0232.N0720.N1329.d019646

def d019727 (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem d019728 (n : ℕ) : 0 < _root_.GD.N0232.N0720.N1314.d019727 n := by unfold _root_.GD.N0232.N0720.N1314.d019727; positivity

theorem d019729 : Antitone _root_.GD.N0232.N0720.N1314.d019727 := by
  intro m n hmn
  apply one_div_le_one_div_of_le (show (0 : ℝ) < (m : ℝ) + 1 by positivity)
  exact add_le_add (Nat.cast_le.mpr hmn) le_rfl

theorem d019730 : Tendsto _root_.GD.N0232.N0720.N1314.d019727 atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

section Approximation

variable {m n d : ℕ} (hdim : m + n = d + 1)

set_option maxHeartbeats 800000 in




theorem d019731 (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1314.d019711 m n d hdim) h) :
    ∃ (p : ℕ → _root_.GD.N0232.N0720.N1341.d004417 d) (w : ∀ j, Fin j → ℝ),
      Tendsto p atTop (𝓝 h) ∧ (∀ j i, 0 ≤ w j i) ∧ ∀ j,
        p j =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] fun u ↦
          _root_.GD.N0232.N0720.N1314.d019699 (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin j ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
              (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u /
            _root_.GD.N0232.N0720.N1314.d019698 (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin j ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
              (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u := by
  have hadmissible' : _root_.GD.N0230.N0556.d000031
      (fun q (z : (univ : Set (_root_.GD.N0232.N0720.N1341.d004417 d))) ↦ _root_.GD.N0232.N0720.N1314.d019711 m n d hdim q z)
      ⟨h, mem_univ h⟩ := by
    rintro ⟨z, hweak, q, hstrict⟩
    exact hadmissible ⟨z.1, hweak, q, hstrict⟩
  have hscale : 0 < _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * _root_.GD.N0232.N0720.N1341.d004428 d :=
    mul_pos (_root_.GD.N0232.N0720.N1316.d004446 _) (_root_.GD.N0232.N0720.N1341.d004429 d)
  obtain ⟨p, w, hlimit, hcertificate⟩ :=
    _root_.GD.N0230.N0622.d000623
      (H := _root_.GD.N0232.N0720.N1341.d004417 d) (Θ := _root_.GD.N0232.N0720.N1329.d019646)
      (univ : Set (_root_.GD.N0232.N0720.N1341.d004417 d)) (_root_.GD.N0232.N0720.N1314.d019711 m n d hdim) _root_.GD.N0232.N0720.N1314.d019725
      _root_.GD.N0232.N0720.N1314.d019712 h (mem_univ h) isClosed_univ convex_univ
      (_root_.GD.N0232.N0720.N1314.d019715 hdim) (_root_.GD.N0232.N0720.N1314.d019717 hdim)
      (fun z _ ↦ _root_.GD.N0232.N0720.N1314.d019716 hdim z) _root_.GD.N0232.N0720.N1314.d019726
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * _root_.GD.N0232.N0720.N1341.d004428 d) 0 hscale
      (fun z _ ↦ by simpa only [add_zero] using _root_.GD.N0232.N0720.N1314.d019718 hdim z)
      hadmissible' _root_.GD.N0232.N0720.N1314.d019727 _root_.GD.N0232.N0720.N1314.d019728 _root_.GD.N0232.N0720.N1314.d019729 _root_.GD.N0232.N0720.N1314.d019730
  refine ⟨p, w, hlimit, fun j ↦ (hcertificate j).2.1, fun j ↦ ?_⟩
  have heq := _root_.GD.N0232.N0720.N1314.d019724 hdim
    (fun i : Fin j ↦ _root_.GD.N0232.N0720.N1314.d019725 i) (w j) (p j) (hcertificate j).2
  rw [heq]
  exact _root_.GD.N0232.N0720.N1314.d019709 _ _ _ _




theorem d019732 (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1314.d019711 m n d hdim) h) :
    ∃ (w : ∀ j, Fin j → ℝ) (ns : ℕ → ℕ),
      (∀ j i, 0 ≤ w j i) ∧ StrictMono ns ∧ ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
        Tendsto (fun j ↦
          _root_.GD.N0232.N0720.N1314.d019699 (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
              (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u /
            _root_.GD.N0232.N0720.N1314.d019698 (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
              (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u)
          atTop (𝓝 (h u)) := by
  obtain ⟨p, w, hlimit, hw, hratio⟩ :=
    _root_.GD.N0232.N0720.N1314.d019731 hdim h hadmissible
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlimit).exists_seq_tendsto_ae
  refine ⟨w, ns, hw, hns, ?_⟩
  have hratios : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, ∀ j,
      p j u = _root_.GD.N0232.N0720.N1314.d019699
          (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin j ↦ _root_.GD.N0232.N0720.N1314.d019725 i)) (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u /
        _root_.GD.N0232.N0720.N1314.d019698
          (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin j ↦ _root_.GD.N0232.N0720.N1314.d019725 i)) (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u :=
    ae_all_iff.mpr hratio
  filter_upwards [hpoint, hratios] with u hu huratio
  simpa only [huratio] using hu

end Approximation

end
end GD.N0232.N0720.N1314

#print axioms _root_.GD.N0232.N0720.N1314.d019690
#print axioms _root_.GD.N0232.N0720.N1314.d019710
#print axioms _root_.GD.N0232.N0720.N1314.d019731
#print axioms _root_.GD.N0232.N0720.N1314.d019732
