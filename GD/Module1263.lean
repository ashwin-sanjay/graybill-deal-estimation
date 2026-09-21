import GD.Module0667
import GD.Module0665
import GD.Module1223
import GD.Module1262

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace GD.N0213.N0477

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0230.N0615

variable {k d : ℕ} (sizes : Fin k → ℕ)
  (hdim : (∑ i, sizes i) = (d + 1) + 1)

abbrev d020377 (k : ℕ) := {a : Fin k → ℝ // ∀ i, 0 < a i}

abbrev d020378 (d : ℕ) :=
  {a : _root_.GD.N0232.N0719.N0977.d009764 d // ∀ i, 0 < a i}

def d020379 (z : _root_.GD.N0232.N0719.N0977.d009764 d) : _root_.GD.N0232.N0719.N0997.d019804 sizes :=
  fun i j => z (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩)

def d020380 (a : _root_.GD.N0213.N0477.d020377 k) : _root_.GD.N0213.N0477.d020378 d :=
  ⟨fun j => a.1 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j), fun j => a.2 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j)⟩

def d020381 (a : _root_.GD.N0213.N0477.d020377 k) : ℝ := ∑ i, (sizes i : ℝ) * a.1 i

theorem d020382 (f : Fin ((d + 1) + 1) → ℝ) :
    (∑ j, f j) = ∑ i, ∑ j : Fin (sizes i), f (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i,j⟩) := by
  rw [← (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim).sum_comp f, Fintype.sum_sigma]

theorem d020383 (a : _root_.GD.N0213.N0477.d020377 k) :
    _root_.GD.N0230.N0615.d000151 (_root_.GD.N0213.N0477.d020380 sizes hdim a).1 = _root_.GD.N0213.N0477.d020381 sizes a := by
  unfold _root_.GD.N0230.N0615.d000151
  rw [_root_.GD.N0213.N0477.d020382 sizes hdim]
  simp [_root_.GD.N0213.N0477.d020380, _root_.GD.N0232.N0719.N0997.d019806, _root_.GD.N0213.N0477.d020381]

include hdim in
theorem d020384 (a : _root_.GD.N0213.N0477.d020377 k) : 0 < _root_.GD.N0213.N0477.d020381 sizes a := by
  rw [← _root_.GD.N0213.N0477.d020383 sizes hdim]
  exact _root_.GD.N0232.N0719.N0977.d009779 d _ (_root_.GD.N0213.N0477.d020380 sizes hdim a).2

def d020385 (a : _root_.GD.N0213.N0477.d020377 k) : _root_.GD.N0232.N0719.N0983.d009709 k := by
  refine ⟨fun i => ⟨(sizes i : ℝ) * a.1 i / _root_.GD.N0213.N0477.d020381 sizes a, ?_⟩, ?_⟩
  · have ht := _root_.GD.N0213.N0477.d020384 sizes hdim a
    constructor
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (a.2 i).le) ht.le
    · apply (div_le_one ht).2
      exact Finset.single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _) (a.2 j).le)
        (Finset.mem_univ i)
  · change (∑ i, (sizes i : ℝ) * a.1 i / _root_.GD.N0213.N0477.d020381 sizes a) = 1
    rw [← Finset.sum_div]
    exact div_self (_root_.GD.N0213.N0477.d020384 sizes hdim a).ne'

theorem d020386 (a : _root_.GD.N0213.N0477.d020377 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0983.d009710 i (_root_.GD.N0213.N0477.d020385 sizes hdim a) : ℝ) =
      (sizes i : ℝ) * a.1 i / _root_.GD.N0213.N0477.d020381 sizes a := rfl

theorem d020387 (hn : ∀ i, 0 < sizes i) (a : _root_.GD.N0213.N0477.d020377 k) (i : Fin k) :
    0 < (_root_.GD.N0232.N0719.N0983.d009710 i (_root_.GD.N0213.N0477.d020385 sizes hdim a) : ℝ) :=
  div_pos (mul_pos (Nat.cast_pos.mpr (hn i)) (a.2 i)) (_root_.GD.N0213.N0477.d020384 sizes hdim a)

theorem d020388 (a : _root_.GD.N0213.N0477.d020377 k)
    (z : _root_.GD.N0232.N0719.N0977.d009764 d) (hn : ∀ i, 0 < sizes i) :
    _root_.GD.N0230.N0615.d000152 (_root_.GD.N0213.N0477.d020380 sizes hdim a).1 z =
      _root_.GD.N0232.N0719.N0983.d009713 (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) (_root_.GD.N0213.N0477.d020385 sizes hdim a) := by
  unfold _root_.GD.N0230.N0615.d000152
  rw [_root_.GD.N0213.N0477.d020383, _root_.GD.N0213.N0477.d020382 sizes hdim]
  unfold _root_.GD.N0232.N0719.N0983.d009713
  simp_rw [_root_.GD.N0213.N0477.d020386]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hn0 : (sizes i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hn i)).ne'
  simp only [_root_.GD.N0213.N0477.d020380, _root_.GD.N0232.N0719.N0997.d019806, Equiv.symm_apply_apply]
  rw [← Finset.mul_sum]
  unfold _root_.GD.N0232.N0719.N0986.d020360 _root_.GD.N0213.N0477.d020379
  field_simp [hn0]

theorem d020389 (x : _root_.GD.N0232.N0719.N0997.d019804 sizes) (mu : ℝ)
    (i : Fin k) (hn : 0 < sizes i) :
    (∑ j, (x i j - mu) ^ 2) =
      (sizes i : ℝ) * (2 * _root_.GD.N0232.N0719.N0986.d020361 sizes x i + (_root_.GD.N0232.N0719.N0986.d020360 sizes x i - mu) ^ 2) := by
  have hn0 : (sizes i : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hT : _root_.GD.N0230.N0615.d000151 (fun _ : Fin (sizes i) => (1 : ℝ)) = sizes i := by
    simp [_root_.GD.N0230.N0615.d000151]
  have hM : _root_.GD.N0230.N0615.d000152 (fun _ : Fin (sizes i) => (1 : ℝ)) (x i) =
      _root_.GD.N0232.N0719.N0986.d020360 sizes x i := by simp [_root_.GD.N0230.N0615.d000152, _root_.GD.N0230.N0615.d000151, _root_.GD.N0232.N0719.N0986.d020360]
  have h := _root_.GD.N0230.N0615.d000158 (fun _ : Fin (sizes i) => (1 : ℝ)) (x i) mu
    (by simpa only [hT] using hn0)
  simp only [one_mul, hT, hM] at h
  rw [h]
  unfold _root_.GD.N0232.N0719.N0986.d020361
  field_simp [hn0]
  ring

theorem d020390 (a : _root_.GD.N0213.N0477.d020377 k)
    (u : _root_.GD.N0232.N0720.N1341.d004415 d)
    (hn : ∀ i, 0 < sizes i) :
    _root_.GD.N0232.N0719.N0977.d009778 d (_root_.GD.N0213.N0477.d020380 sizes hdim a).1 u =
      _root_.GD.N0213.N0477.d020381 sizes a * _root_.GD.N0232.N0719.N0983.d009714
        (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
        (_root_.GD.N0213.N0477.d020385 sizes hdim a) := by
  let x := _root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)
  let p := _root_.GD.N0213.N0477.d020385 sizes hdim a
  let m := _root_.GD.N0232.N0719.N0983.d009713 (_root_.GD.N0232.N0719.N0986.d020360 sizes x) p
  unfold _root_.GD.N0232.N0719.N0977.d009778
  rw [_root_.GD.N0213.N0477.d020388 sizes hdim a _ hn, _root_.GD.N0213.N0477.d020382 sizes hdim]
  have hs : (∑ i, ∑ j : Fin (sizes i),
      (_root_.GD.N0213.N0477.d020380 sizes hdim a).1 (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i,j⟩) *
      (_root_.GD.N0232.N0719.N0977.d009773 d u (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i,j⟩) - m) ^ 2) =
      ∑ i, a.1 i * ((sizes i : ℝ) *
        (2 * _root_.GD.N0232.N0719.N0986.d020361 sizes x i + (_root_.GD.N0232.N0719.N0986.d020360 sizes x i - m) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [_root_.GD.N0213.N0477.d020380, _root_.GD.N0232.N0719.N0997.d019806, Equiv.symm_apply_apply]
    rw [← Finset.mul_sum]
    congr 1
    exact _root_.GD.N0213.N0477.d020389 sizes x m i (hn i)
  change (1 / 2 : ℝ) * (∑ i, ∑ j : Fin (sizes i),
      (_root_.GD.N0213.N0477.d020380 sizes hdim a).1 (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i,j⟩) *
      (_root_.GD.N0232.N0719.N0977.d009773 d u (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i,j⟩) - m) ^ 2) = _
  rw [hs]
  change (1 / 2 : ℝ) * (∑ i, a.1 i * ((sizes i : ℝ) *
        (2 * _root_.GD.N0232.N0719.N0986.d020361 sizes x i + (_root_.GD.N0232.N0719.N0986.d020360 sizes x i - m) ^ 2))) =
    _root_.GD.N0213.N0477.d020381 sizes a * _root_.GD.N0232.N0719.N0983.d009714 (_root_.GD.N0232.N0719.N0986.d020360 sizes x) (_root_.GD.N0232.N0719.N0986.d020361 sizes x) p
  unfold _root_.GD.N0232.N0719.N0983.d009714
  rw [mul_add]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [p, m]
  simp only [_root_.GD.N0213.N0477.d020386]
  field_simp [(_root_.GD.N0213.N0477.d020384 sizes hdim a).ne']

def d020391 (d : ℕ) : ℝ := ((d : ℝ) + 3) / 2

def d020392 (d : ℕ) (a : _root_.GD.N0213.N0477.d020377 k) : ℝ :=
  Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0213.N0477.d020381 sizes a)) * (1 / 2 : ℝ) *
    (1 / _root_.GD.N0213.N0477.d020381 sizes a) ^ _root_.GD.N0213.N0477.d020391 d * Real.Gamma (_root_.GD.N0213.N0477.d020391 d)

def d020393 (a : _root_.GD.N0213.N0477.d020377 k)
    (u : _root_.GD.N0232.N0720.N1341.d004415 d) : ℝ :=
  Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0230.N0615.d000151 (_root_.GD.N0213.N0477.d020380 sizes hdim a).1)) *
    _root_.GD.N0232.N0719.N0985.d009755 ((d : ℝ) + 2)
      (_root_.GD.N0232.N0719.N0977.d009778 d (_root_.GD.N0213.N0477.d020380 sizes hdim a).1 u)

include hdim in
theorem d020394 (a : _root_.GD.N0213.N0477.d020377 k) : 0 < _root_.GD.N0213.N0477.d020392 sizes d a := by
  have hT := _root_.GD.N0213.N0477.d020384 sizes hdim a
  have hq : 0 < _root_.GD.N0213.N0477.d020391 d := by unfold _root_.GD.N0213.N0477.d020391; positivity
  unfold _root_.GD.N0213.N0477.d020392
  exact mul_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr (by positivity)) (by norm_num))
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.Gamma_pos_of_pos hq)

theorem d020395 (a : _root_.GD.N0213.N0477.d020377 k)
    (u : _root_.GD.N0232.N0720.N1341.d004415 d)
    (hn : ∀ i, 0 < sizes i) :
    _root_.GD.N0213.N0477.d020393 sizes hdim a u = _root_.GD.N0213.N0477.d020392 sizes d a * _root_.GD.N0232.N0719.N0983.d009720 (_root_.GD.N0213.N0477.d020391 d)
      (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
      (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
      (_root_.GD.N0213.N0477.d020385 sizes hdim a) := by
  let x := _root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)
  let E := _root_.GD.N0232.N0719.N0983.d009714 (_root_.GD.N0232.N0719.N0986.d020360 sizes x) (_root_.GD.N0232.N0719.N0986.d020361 sizes x) (_root_.GD.N0213.N0477.d020385 sizes hdim a)
  let T := _root_.GD.N0213.N0477.d020381 sizes a
  have hT : 0 < T := _root_.GD.N0213.N0477.d020384 sizes hdim a
  have hE : 0 < E := by
    have h := _root_.GD.N0232.N0719.N0977.d009780 d
      (_root_.GD.N0213.N0477.d020380 sizes hdim a).1 (_root_.GD.N0213.N0477.d020380 sizes hdim a).2 u
    rw [_root_.GD.N0213.N0477.d020390 sizes hdim a u hn] at h
    exact (mul_pos_iff_of_pos_left hT).mp h
  have hpow : (1 / (T * E)) ^ _root_.GD.N0213.N0477.d020391 d =
      (1 / T) ^ _root_.GD.N0213.N0477.d020391 d * E ^ (-_root_.GD.N0213.N0477.d020391 d) := by
    rw [show 1 / (T * E) = (1 / T) * (1 / E) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    rw [one_div E, ← Real.rpow_neg_eq_inv_rpow]
  unfold _root_.GD.N0213.N0477.d020393
  rw [_root_.GD.N0213.N0477.d020383, _root_.GD.N0213.N0477.d020390 sizes hdim a u hn]
  change Real.sqrt (2 * Real.pi * (1 / T)) *
    _root_.GD.N0232.N0719.N0985.d009755 ((d : ℝ) + 2) (T * E) =
    _root_.GD.N0213.N0477.d020392 sizes d a * E ^ (-_root_.GD.N0213.N0477.d020391 d)
  unfold _root_.GD.N0232.N0719.N0985.d009755
  rw [show ((d : ℝ) + 2 + 1) / 2 = _root_.GD.N0213.N0477.d020391 d by unfold _root_.GD.N0213.N0477.d020391; ring, hpow]
  unfold _root_.GD.N0213.N0477.d020392
  change _ = Real.sqrt (2 * Real.pi * (1 / T)) * (1 / 2 : ℝ) *
    (1 / T) ^ _root_.GD.N0213.N0477.d020391 d * Real.Gamma (_root_.GD.N0213.N0477.d020391 d) * E ^ (-_root_.GD.N0213.N0477.d020391 d)
  ring

open _root_.GD.N0232.N0719.N0984
open _root_.GD.N0232.N0719.N0928

variable {J : Type*} [Fintype J]

def d020396 (a : J → _root_.GD.N0213.N0477.d020377 k) (w : J → ℝ) (j : J) : ℝ :=
  w j * _root_.GD.N0213.N0477.d020392 sizes d (a j) /
    _root_.GD.N0232.N0719.N0928.d009409 (fun _ : Fin k => 0)
      (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i (_root_.GD.N0213.N0477.d020385 sizes hdim (a j)) : ℝ))

omit [Fintype J] in
theorem d020397
    (a : J → _root_.GD.N0213.N0477.d020377 k) (w : J → ℝ) (hn : ∀ i, 0 < sizes i) (j : J) :
    _root_.GD.N0232.N0719.N0984.d009739 (fun _ : Fin k => 0) (fun j => _root_.GD.N0213.N0477.d020385 sizes hdim (a j))
      (_root_.GD.N0213.N0477.d020396 sizes hdim a w) j = w j * _root_.GD.N0213.N0477.d020392 sizes d (a j) := by
  unfold _root_.GD.N0232.N0719.N0984.d009739 _root_.GD.N0213.N0477.d020396
  exact div_mul_cancel₀ _ (_root_.GD.N0232.N0719.N0928.d009438 _ _
    (fun i => _root_.GD.N0213.N0477.d020387 sizes hdim hn (a j) i)).ne'

omit [Fintype J] in
theorem d020398 (a : J → _root_.GD.N0213.N0477.d020377 k) (w : J → ℝ)
    (hn : ∀ i, 0 < sizes i) (hw : ∀ j, 0 ≤ w j) (j : J) :
    0 ≤ _root_.GD.N0213.N0477.d020396 sizes hdim a w j :=
  div_nonneg (mul_nonneg (hw j) (_root_.GD.N0213.N0477.d020394 sizes hdim (a j)).le)
    (_root_.GD.N0232.N0719.N0928.d009438 _ _
      (fun i => _root_.GD.N0213.N0477.d020387 sizes hdim hn (a j) i)).le

omit [Fintype J] in
theorem d020399 (a : J → _root_.GD.N0213.N0477.d020377 k) (w : J → ℝ)
    (hn : ∀ i, 0 < sizes i) (hwpos : ∃ j, 0 < w j) :
    ∃ j, 0 < _root_.GD.N0213.N0477.d020396 sizes hdim a w j := by
  obtain ⟨j, hj⟩ := hwpos
  exact ⟨j, div_pos (mul_pos hj (_root_.GD.N0213.N0477.d020394 sizes hdim (a j)))
    (_root_.GD.N0232.N0719.N0928.d009438 _ _
      (fun i => _root_.GD.N0213.N0477.d020387 sizes hdim hn (a j) i))⟩

variable [NeZero k]

def d020400 (a : J → _root_.GD.N0213.N0477.d020377 k) (w : J → ℝ) : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k) :=
  _root_.GD.N0232.N0719.N0984.d009744 (fun _ : Fin k => 0) (fun j => _root_.GD.N0213.N0477.d020385 sizes hdim (a j))
    (_root_.GD.N0213.N0477.d020396 sizes hdim a w)

theorem d020401
    (a : J → _root_.GD.N0213.N0477.d020377 k) (w : J → ℝ)
    (hn : ∀ i, 0 < sizes i) (hw : ∀ j, 0 ≤ w j) (hwpos : ∃ j, 0 < w j)
    (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    (∑ j, w j * _root_.GD.N0213.N0477.d020393 sizes hdim (a j) u *
      _root_.GD.N0230.N0615.d000152 (_root_.GD.N0213.N0477.d020380 sizes hdim (a j)).1 (_root_.GD.N0232.N0719.N0977.d009773 d u)) /
      (∑ j, w j * _root_.GD.N0213.N0477.d020393 sizes hdim (a j) u) =
    _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
      (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
      (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
      (_root_.GD.N0213.N0477.d020400 sizes hdim a w : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  have hp := fun j i => _root_.GD.N0213.N0477.d020387 sizes hdim hn (a j) i
  have hpos := _root_.GD.N0213.N0477.d020399 sizes hdim a w hn hwpos
  have hnonneg := _root_.GD.N0213.N0477.d020398 sizes hdim a w hn hw
  unfold _root_.GD.N0213.N0477.d020400
  rw [_root_.GD.N0232.N0719.N0984.d009746 _ _ _ hp hpos]
  unfold _root_.GD.N0232.N0719.N0983.d009724 _root_.GD.N0232.N0719.N0983.d009723
  rw [_root_.GD.N0232.N0719.N0984.d009745 _ _ _ hnonneg hp, _root_.GD.N0232.N0719.N0984.d009745 _ _ _ hnonneg hp]
  simp_rw [_root_.GD.N0213.N0477.d020397 sizes hdim a w hn,
    _root_.GD.N0213.N0477.d020395 sizes hdim _ u hn,
    _root_.GD.N0213.N0477.d020388 sizes hdim _ _ hn]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype J] in
theorem d020402
    {Index : ℕ → Type*} [∀ j, Fintype (Index j)]
    (a : ∀ j, Index j → _root_.GD.N0213.N0477.d020377 k) (w : ∀ j, Index j → ℝ)
    (hn : ∀ i, 0 < sizes i) (hw : ∀ j i, 0 ≤ w j i) (hwpos : ∀ j, ∃ i, 0 < w j i)
    (g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ)
    (hr : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes
        (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) i)
    (hlim : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      Tendsto (fun j =>
        (∑ i, w j i * _root_.GD.N0213.N0477.d020393 sizes hdim (a j i) u *
          _root_.GD.N0230.N0615.d000152 (_root_.GD.N0213.N0477.d020380 sizes hdim (a j i)).1 (_root_.GD.N0232.N0719.N0977.d009773 d u)) /
          (∑ i, w j i * _root_.GD.N0213.N0477.d020393 sizes hdim (a j i) u)) atTop (𝓝 (g u))) :
    ∃ pi : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k),
      g =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] fun u =>
        _root_.GD.N0232.N0719.N0983.d009724 (_root_.GD.N0213.N0477.d020391 d)
          (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (pi : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  apply _root_.GD.N0232.N0719.N0983.d009737
    (_root_.GD.N0232.N0720.N1341.d004416 d)
    (_root_.GD.N0213.N0477.d020391 d)
    (fun u => _root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
    (fun u => _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
    g (fun j => _root_.GD.N0213.N0477.d020400 sizes hdim (a j) (w j)) hr
  filter_upwards [hlim] with u hu
  simpa only [_root_.GD.N0213.N0477.d020401 sizes hdim _ _ hn (hw _) (hwpos _)] using hu

end
end GD.N0213.N0477

#print axioms _root_.GD.N0213.N0477.d020388
#print axioms _root_.GD.N0213.N0477.d020390
#print axioms _root_.GD.N0213.N0477.d020395
#print axioms _root_.GD.N0213.N0477.d020401
#print axioms _root_.GD.N0213.N0477.d020402
