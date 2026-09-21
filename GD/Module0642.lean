import GD.Module0267
import GD.Module0640















open MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0232.N0719.N0857

noncomputable section


abbrev d009377 (k : ℕ) := Fin (k - 1) → ℝ


def d009378 (x : ℝ) : ℝ :=
  max (-1) (min 1 x)

theorem d009379 (x : ℝ) :
    _root_.GD.N0232.N0719.N0857.d009378 x ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

@[simp]
theorem d009380 : _root_.GD.N0232.N0719.N0857.d009378 0 = 0 := by
  norm_num [_root_.GD.N0232.N0719.N0857.d009378]

theorem d009381 {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    _root_.GD.N0232.N0719.N0857.d009378 x = x := by
  simp [_root_.GD.N0232.N0719.N0857.d009378, hx.1, hx.2]

@[fun_prop]
theorem d009382 : Continuous _root_.GD.N0232.N0719.N0857.d009378 := by
  unfold _root_.GD.N0232.N0719.N0857.d009378
  fun_prop


def d009383 (k : ℕ) : Set (_root_.GD.N0232.N0719.N0857.d009377 k) :=
  Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1)

theorem d009384 (k : ℕ) :
    IsCompact (_root_.GD.N0232.N0719.N0857.d009383 k) := by
  exact isCompact_Icc

theorem d009385 (k : ℕ) :
    (0 : _root_.GD.N0232.N0719.N0857.d009377 k) ∈ interior (_root_.GD.N0232.N0719.N0857.d009383 k) := by
  rw [mem_interior_iff_mem_nhds]
  exact
    pi_Icc_mem_nhds
      (a := fun _ : Fin (k - 1) => (-1 : ℝ))
      (b := fun _ : Fin (k - 1) => (1 : ℝ))
      (x := (0 : _root_.GD.N0232.N0719.N0857.d009377 k))
      (fun _ => by norm_num)
      (fun _ => by norm_num)


def d009386 (k : ℕ) : ℝ :=
  1 / (100 * (k : ℝ) ^ 2)

theorem d009387 {k : ℕ} (hk : 0 < k) :
    0 < _root_.GD.N0232.N0719.N0857.d009386 k := by
  unfold _root_.GD.N0232.N0719.N0857.d009386
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  positivity





def d009388 {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) (u : _root_.GD.N0232.N0719.N0857.d009377 k) (i : Fin k) : ℝ :=
  match (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i with
  | Sum.inl j =>
      anchor i + _root_.GD.N0232.N0719.N0857.d009386 k * _root_.GD.N0232.N0719.N0857.d009378 (u j)
  | Sum.inr _ =>
      anchor i - _root_.GD.N0232.N0719.N0857.d009386 k * ∑ j, _root_.GD.N0232.N0719.N0857.d009378 (u j)

@[simp]
theorem d009389 {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0857.d009388 hk anchor 0 = anchor := by
  funext i
  unfold _root_.GD.N0232.N0719.N0857.d009388
  split <;> simp

@[fun_prop]
theorem d009390
    {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) (i : Fin k) :
    Continuous (fun u : _root_.GD.N0232.N0719.N0857.d009377 k => _root_.GD.N0232.N0719.N0857.d009388 hk anchor u i) := by
  unfold _root_.GD.N0232.N0719.N0857.d009388
  split <;> fun_prop


theorem d009391
    {k : ℕ} (hk : 0 < k)
    {anchor : Fin k → ℝ}
    (hanchor : ∑ i, anchor i = 1)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    ∑ i, _root_.GD.N0232.N0719.N0857.d009388 hk anchor u i = 1 := by
  let e := _root_.GD.N0232.N0719.N0954.d009344 k hk
  rw [show
      (∑ i : Fin k, _root_.GD.N0232.N0719.N0857.d009388 hk anchor u i) =
        ∑ j : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          _root_.GD.N0232.N0719.N0857.d009388 hk anchor u (e j) by
    symm
    exact Fintype.sum_equiv e _ _ fun _ => rfl]
  rw [Fintype.sum_sum_type]
  simp only [_root_.GD.N0232.N0719.N0857.d009388, e, Equiv.symm_apply_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hanchorReindex :
      (∑ j : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          anchor (e j)) = 1 := by
    rw [← hanchor]
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  rw [Fintype.sum_sum_type, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero] at hanchorReindex
  rw [← hanchorReindex]
  ring


theorem d009392 (x : ℝ) :
    |_root_.GD.N0232.N0719.N0857.d009378 x| ≤ 1 := by
  exact (abs_le).2 (_root_.GD.N0232.N0719.N0857.d009379 x)





theorem d009393
    {k : ℕ} (hk : 0 < k)
    (anchor : Fin k → ℝ) (u : _root_.GD.N0232.N0719.N0857.d009377 k) (i : Fin k) :
    |_root_.GD.N0232.N0719.N0857.d009388 hk anchor u i - anchor i| ≤
      1 / (100 * (k : ℝ)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold _root_.GD.N0232.N0719.N0857.d009388
  generalize
    (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i = c
  cases c with
  | inl j =>
    have hclip := _root_.GD.N0232.N0719.N0857.d009392 (u j)
    rw [add_sub_cancel_left, abs_mul]
    have hr := (_root_.GD.N0232.N0719.N0857.d009387 hk).le
    rw [abs_of_nonneg hr]
    calc
      _root_.GD.N0232.N0719.N0857.d009386 k * |_root_.GD.N0232.N0719.N0857.d009378 (u j)| ≤ _root_.GD.N0232.N0719.N0857.d009386 k * 1 :=
        mul_le_mul_of_nonneg_left hclip hr
      _ ≤ 1 / (100 * (k : ℝ)) := by
        rw [mul_one]
        unfold _root_.GD.N0232.N0719.N0857.d009386
        exact
          one_div_le_one_div_of_le
            (by positivity)
            (by
              have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast hk
              nlinarith)
  | inr j =>
    rw [sub_sub_cancel_left, abs_neg]
    have hsum :
        |∑ j, _root_.GD.N0232.N0719.N0857.d009378 (u j)| ≤ (k - 1 : ℕ) := by
      calc
        |∑ j, _root_.GD.N0232.N0719.N0857.d009378 (u j)| ≤ ∑ j, |_root_.GD.N0232.N0719.N0857.d009378 (u j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (k - 1), (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => _root_.GD.N0232.N0719.N0857.d009392 (u j)
        _ = (k - 1 : ℕ) := by simp
    rw [abs_mul, abs_of_nonneg (_root_.GD.N0232.N0719.N0857.d009387 hk).le]
    have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.sub_le k 1
    calc
      _root_.GD.N0232.N0719.N0857.d009386 k * |∑ j, _root_.GD.N0232.N0719.N0857.d009378 (u j)| ≤
          _root_.GD.N0232.N0719.N0857.d009386 k * (k : ℝ) :=
        mul_le_mul_of_nonneg_left
          (hsum.trans hkm1) (_root_.GD.N0232.N0719.N0857.d009387 hk).le
      _ = 1 / (100 * (k : ℝ)) := by
        unfold _root_.GD.N0232.N0719.N0857.d009386
        field_simp [hkR.ne']





theorem d009394
    {k : ℕ} (hk : 0 < k)
    {anchor : Fin k → ℝ}
    (hcore :
      ∀ i,
        4 / (5 * (k : ℝ)) ≤ anchor i ∧
          anchor i ≤ 6 / (5 * (k : ℝ)))
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0857.d009388 hk anchor u) := by
  intro i
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hdev := _root_.GD.N0232.N0719.N0857.d009393 hk anchor u i
  have hdev' :
      -(1 / (100 * (k : ℝ))) ≤
          _root_.GD.N0232.N0719.N0857.d009388 hk anchor u i - anchor i ∧
        _root_.GD.N0232.N0719.N0857.d009388 hk anchor u i - anchor i ≤
          1 / (100 * (k : ℝ)) :=
    (abs_le).1 hdev
  unfold _root_.GD.N0232.N0719.N0951.d003578 _root_.GD.N0232.N0719.N0951.d003579
  constructor
  · have hc := (hcore i).1
    field_simp [hkR.ne'] at hdev' hc ⊢
    nlinarith [hdev'.1]
  · have hc := (hcore i).2
    field_simp [hkR.ne'] at hdev' hc ⊢
    nlinarith [hdev'.2]

theorem d009395
    {k : ℕ} (hk : 0 < k) :
    ∀ i,
      4 / (5 * (k : ℝ)) ≤ _root_.GD.N0232.N0719.N0854.d003821 k i ∧
        _root_.GD.N0232.N0719.N0854.d003821 k i ≤ 6 / (5 * (k : ℝ)) := by
  intro i
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold _root_.GD.N0232.N0719.N0854.d003821
  constructor <;> field_simp [hkR.ne'] <;> nlinarith

theorem d009396
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    ∀ i,
      4 / (5 * (k : ℝ)) ≤ _root_.GD.N0232.N0719.N0854.d003822 triangle i ∧
        _root_.GD.N0232.N0719.N0854.d003822 triangle i ≤ 6 / (5 * (k : ℝ)) := by
  intro i
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold _root_.GD.N0232.N0719.N0854.d003822
  by_cases h0 : i = triangle 0
  · have h1 : i ≠ triangle 1 := by
      rw [h0]
      exact _root_.GD.N0232.N0719.N0854.d003823 triangle
    simp [h0, h1]
    constructor <;> field_simp [hkR.ne'] <;> nlinarith
  · by_cases h1 : i = triangle 1
    · simp [h0, h1]
      constructor <;> field_simp [hkR.ne'] <;> nlinarith
    · simp [h0, h1]
      constructor <;> field_simp [hkR.ne'] <;> nlinarith

theorem d009397
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0951.d003580
      (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) :=
  _root_.GD.N0232.N0719.N0857.d009394 hk
    (_root_.GD.N0232.N0719.N0857.d009395 hk) u

theorem d009398
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0951.d003580
      (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) :=
  _root_.GD.N0232.N0719.N0857.d009394 hk
    (_root_.GD.N0232.N0719.N0857.d009396 hk triangle) u

theorem d009399
    {k : ℕ} (hk : 0 < k) (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    ∑ i, _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u i = 1 :=
  _root_.GD.N0232.N0719.N0857.d009391 hk (_root_.GD.N0232.N0719.N0854.d003829 hk) u

theorem d009400
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    ∑ i, _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u i = 1 :=
  _root_.GD.N0232.N0719.N0857.d009391 hk (_root_.GD.N0232.N0719.N0854.d003830 hk triangle) u






def d009401 (k : ℕ) : ℝ :=
  (_root_.GD.N0232.N0719.N0857.d009386 k) ^ (k - 1)

theorem d009402 {k : ℕ} (hk : 0 < k) :
    0 < _root_.GD.N0232.N0719.N0857.d009401 k := by
  unfold _root_.GD.N0232.N0719.N0857.d009401
  exact pow_pos (_root_.GD.N0232.N0719.N0857.d009387 hk) _


theorem d009403 {k : ℕ} :
    0 < volume (_root_.GD.N0232.N0719.N0857.d009383 k) := by
  rw [_root_.GD.N0232.N0719.N0857.d009383, Real.volume_Icc_pi]
  rw [pos_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)

theorem d009404 {k : ℕ} :
    volume (_root_.GD.N0232.N0719.N0857.d009383 k) ≠ ∞ := by
  rw [_root_.GD.N0232.N0719.N0857.d009383, Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top

end

end GD.N0232.N0719.N0857
