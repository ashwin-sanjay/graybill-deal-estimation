import GD.Module0239



















namespace GD
namespace N0229
namespace N0550

open scoped BigOperators

variable {ι X : Type*} [Fintype ι]





theorem d003502
    {κ : Type*} [Fintype κ]
    (rowScale : κ → ℝ) (columnScale w : ι → ℝ)
    (charge : ι → κ → ℝ)
    (hrow : ∀ k, 0 < rowScale k) :
    (∀ k, ∑ i, (w i / columnScale i) * charge i k = 0) ↔
      (∀ k, ∑ i, w i *
        (rowScale k * charge i k / columnScale i) = 0) := by
  constructor
  · intro h k
    calc
      ∑ i, w i * (rowScale k * charge i k / columnScale i) =
          rowScale k *
            ∑ i, (w i / columnScale i) * charge i k := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = 0 := by rw [h k]; ring
  · intro h k
    have hk :
        rowScale k * ∑ i, (w i / columnScale i) * charge i k = 0 := by
      calc
        rowScale k * ∑ i, (w i / columnScale i) * charge i k =
            ∑ i, w i * (rowScale k * charge i k / columnScale i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := h k
    exact (mul_eq_zero.mp hk).resolve_left (ne_of_gt (hrow k))

omit [Fintype ι] in
theorem d003503
    (columnScale w : ι → ℝ)
    (hcolumn : ∀ i, 0 < columnScale i)
    (hw : ∀ i, 0 < w i) :
    ∀ i, 0 < w i / columnScale i := by
  intro i
  exact div_pos (hw i) (hcolumn i)

omit [Fintype ι] in



theorem d003504
    (center exact : ι → ℝ) (error : ℝ)
    (hcenter : ∀ i, error < center i)
    (herror : ∀ i, |exact i - center i| ≤ error) :
    ∀ i, 0 < exact i := by
  intro i
  have hlow : -error ≤ exact i - center i := (abs_le.mp (herror i)).1
  linarith [hcenter i]



theorem d003505
    (w : ι → ℝ)
    (hwsum : ∑ i, w i = 1) :
    ∃ i, 0 < w i := by
  by_contra hz
  push Not at hz
  have hnonpos : (∑ i, w i) ≤ 0 :=
    Finset.sum_nonpos fun i hi ↦ hz i
  rw [hwsum] at hnonpos
  norm_num at hnonpos



theorem d003506
    (w charge : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hbalance : ∑ i, w i * charge i = 0) :
    ∃ i, 0 ≤ charge i := by
  by_contra h
  push Not at h
  have hex : ∃ i, 0 < w i := _root_.GD.N0229.N0550.d003505 w hwsum
  have hsumneg : ∑ i, w i * charge i < 0 := by
    apply Finset.sum_neg'
    · intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (hw i) (h i).le
    · obtain ⟨i, hwi⟩ := hex
      exact ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg hwi (h i)⟩
  rw [hbalance] at hsumneg
  exact (lt_irrefl 0) hsumneg




theorem d003507
    (w : ι → ℝ) (charge energy : ι → X → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (henergy : ∀ i x, 0 ≤ energy i x) :
    ¬ ∃ x, ∀ i, 2 * charge i x + energy i x < 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨i, hi⟩ :=
    _root_.GD.N0229.N0550.d003506 w (fun j ↦ charge j x) hw hwsum (hbalance x)
  have hnonneg : 0 ≤ 2 * charge i x + energy i x := by
    exact add_nonneg (mul_nonneg (by norm_num) hi) (henergy i x)
  exact (not_lt_of_ge hnonneg) (hx i)



theorem d003508
    (w : ι → ℝ) (charge energy : ι → X → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (henergy : ∀ i x, 0 ≤ energy i x)
    (x : X) :
    ∃ i, 0 ≤ 2 * charge i x + energy i x := by
  obtain ⟨i, hi⟩ :=
    _root_.GD.N0229.N0550.d003506 w (fun j ↦ charge j x) hw hwsum (hbalance x)
  exact ⟨i, add_nonneg (mul_nonneg (by norm_num) hi) (henergy i x)⟩



theorem d003509
    (w : ι → ℝ) (charge energy : ι → X → ℝ)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (x : X) :
    ∑ i, w i * (2 * charge i x + energy i x) =
      ∑ i, w i * energy i x := by
  calc
    ∑ i, w i * (2 * charge i x + energy i x) =
        2 * (∑ i, w i * charge i x) + ∑ i, w i * energy i x := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ i, w i * energy i x := by rw [hbalance x]; ring




theorem d003510
    (zero : X)
    (w : ι → ℝ) (charge energy : ι → X → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (henergy : ∀ i x, 0 ≤ energy i x)
    (henergy_strict : ∀ i x, x ≠ zero → 0 < energy i x)
    (x : X) (hx : x ≠ zero) :
    ∃ i, 0 < 2 * charge i x + energy i x := by
  have hex : ∃ i, 0 < w i := _root_.GD.N0229.N0550.d003505 w hwsum
  have henergySum : 0 < ∑ i, w i * energy i x := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hw i) (henergy i x)
    · obtain ⟨i, hwi⟩ := hex
      exact ⟨i, Finset.mem_univ i,
        mul_pos hwi (henergy_strict i x hx)⟩
  by_contra h
  push Not at h
  have hincrementSum :
      (∑ i, w i * (2 * charge i x + energy i x)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hw i) (h i)
  rw [_root_.GD.N0229.N0550.d003509 w charge energy hbalance x]
    at hincrementSum
  exact (not_lt_of_ge hincrementSum) henergySum



theorem d003511
    (zero : X)
    (w : ι → ℝ) (charge energy : ι → X → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (henergy : ∀ i x, 0 ≤ energy i x)
    (henergy_strict : ∀ i x, x ≠ zero → 0 < energy i x) :
    ¬ ∃ x, x ≠ zero ∧ ∀ i, 2 * charge i x + energy i x ≤ 0 := by
  rintro ⟨x, hx, hall⟩
  obtain ⟨i, hi⟩ := _root_.GD.N0229.N0550.d003510 zero w charge energy hw hwsum
    hbalance henergy henergy_strict x hx
  exact (not_lt_of_ge (hall i)) hi




theorem d003512
    [Nonempty ι]
    (zero : X)
    (w : ι → ℝ) (charge energy : ι → X → ℝ)
    (hw : ∀ i, 0 < w i)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (henergy : ∀ i x, 0 ≤ energy i x)
    (henergy_strict : ∀ i x, x ≠ zero → 0 < energy i x)
    (x : X) (hx : x ≠ zero) :
    ∃ i, 0 < 2 * charge i x + energy i x := by
  have henergySum : 0 < ∑ i, w i * energy i x := by
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hw i).le (henergy i x)
    · let i : ι := Classical.choice (inferInstance : Nonempty ι)
      exact ⟨i, Finset.mem_univ i,
        mul_pos (hw i) (henergy_strict i x hx)⟩
  by_contra h
  push Not at h
  have hincrementSum :
      (∑ i, w i * (2 * charge i x + energy i x)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hw i).le (h i)
  rw [_root_.GD.N0229.N0550.d003509 w charge energy hbalance x]
    at hincrementSum
  exact (not_lt_of_ge hincrementSum) henergySum



theorem d003513
    [Nonempty ι]
    (zero : X)
    (w : ι → ℝ) (charge energy : ι → X → ℝ)
    (hw : ∀ i, 0 < w i)
    (hbalance : ∀ x, ∑ i, w i * charge i x = 0)
    (henergy : ∀ i x, 0 ≤ energy i x)
    (henergy_strict : ∀ i x, x ≠ zero → 0 < energy i x) :
    ¬ ∃ x, x ≠ zero ∧ ∀ i, 2 * charge i x + energy i x ≤ 0 := by
  rintro ⟨x, hx, hall⟩
  obtain ⟨i, hi⟩ :=
    _root_.GD.N0229.N0550.d003512 zero w charge energy hw
      hbalance henergy henergy_strict x hx
  exact (not_lt_of_ge (hall i)) hi

end N0550
end N0229
end GD
