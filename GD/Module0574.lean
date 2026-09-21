import GD.Module0035

set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators

namespace GD.N0213.N0525
noncomputable section
variable {I : Type*} [Fintype I]

theorem d008426 (a r : I → ℝ) (ℓ : ℝ) :
    (∑ i, a i * (r i - ℓ) ^ 2) = (∑ i, a i * r i ^ 2) -
      2 * ℓ * (∑ i, a i * r i) + ℓ ^ 2 * (∑ i, a i) := by
  calc
    _ = ∑ i, (a i * r i ^ 2 - 2 * ℓ * (a i * r i) + ℓ ^ 2 * a i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem d008427 (a r : I → ℝ) (ha : ∑ i, a i ≠ 0) :
    (∑ i, a i * (r i - (∑ j, a j * r j) / (∑ j, a j)) ^ 2) =
      (∑ i, a i * r i ^ 2) - (∑ i, a i * r i) ^ 2 / (∑ i, a i) := by
  rw [_root_.GD.N0213.N0525.d008426]
  field_simp
  ring

theorem d008428 (a r : I → ℝ) :
    (∑ i, ∑ j, a i * a j * (r i - r j) ^ 2) =
      2 * (∑ i, a i) * (∑ i, a i * r i ^ 2) - 2 * (∑ i, a i * r i) ^ 2 := by
  have hrow (i : I) : (∑ j, a i * a j * (r i - r j) ^ 2) =
      a i * ((∑ j, a j * r j ^ 2) - 2 * r i * (∑ j, a j * r j) +
        r i ^ 2 * (∑ j, a j)) := by
    rw [← _root_.GD.N0213.N0525.d008426 a r (r i), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hrow]
  calc
    _ = (∑ i, a i) * (∑ i, a i * r i ^ 2) -
        2 * (∑ i, a i * r i) * (∑ i, a i * r i) +
        (∑ i, a i * r i ^ 2) * (∑ i, a i) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      congr 2
      · rw [Finset.sum_mul]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = _ := by ring

theorem d008429 (a r : I → ℝ) (ha : ∑ i, a i ≠ 0) :
    (∑ i, a i * r i ^ 2) - (∑ i, a i * r i) ^ 2 / (∑ i, a i) =
      (∑ i, ∑ j, a i * a j * (r i - r j) ^ 2) / (2 * ∑ i, a i) := by
  rw [_root_.GD.N0213.N0525.d008428]
  field_simp

theorem d008430 (a r : I → ℝ) (ha : ∑ i, a i ≠ 0) (ℓ : ℝ) :
    (∑ i, a i * (r i - ℓ) ^ 2) =
      (∑ i, ∑ j, a i * a j * (r i - r j) ^ 2) / (2 * ∑ i, a i) +
        (∑ i, a i) * (ℓ - (∑ i, a i * r i) / (∑ i, a i)) ^ 2 := by
  rw [← _root_.GD.N0213.N0525.d008429 a r ha, _root_.GD.N0213.N0525.d008426]
  field_simp
  ring

theorem d008431 {a r d : ℝ} (ha : 0 < a) :
    -a * d ^ 2 + r * d ≤ r ^ 2 / (4 * a) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * a)).mpr
  nlinarith [sq_nonneg (2 * a * d - r)]

theorem d008432 (r d : I → ℝ) (hd : ∑ i, d i = 0) (ℓ : ℝ) :
    (∑ i, (r i - ℓ) * d i) = ∑ i, r i * d i := by
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hd, mul_zero, sub_zero]

theorem d008433 (a r d : I → ℝ)
    (ha : ∀ i, 0 < a i) (hd : ∑ i, d i = 0) (ℓ : ℝ) :
    (∑ i, (-a i * d i ^ 2 + r i * d i)) ≤
      (∑ i, (a i)⁻¹ * (r i - ℓ) ^ 2) / 4 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    _root_.GD.N0213.N0525.d008431 (a := a i) (r := r i - ℓ) (d := d i) (ha i))
  have heq : (∑ i, (-a i * d i ^ 2 + (r i - ℓ) * d i)) =
      (∑ i, (-a i * d i ^ 2 + r i * d i)) := by
    simp only [Finset.sum_add_distrib, _root_.GD.N0213.N0525.d008432 r d hd ℓ]
  rw [heq] at h
  apply h.trans_eq
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d008434 [Nonempty I] (a r d : I → ℝ)
    (ha : ∀ i, 0 < a i) (hd : ∑ i, d i = 0) :
    (∑ i, (-a i * d i ^ 2 + r i * d i)) ≤
      (∑ i, ∑ j, (a i)⁻¹ * (a j)⁻¹ * (r i - r j) ^ 2) /
        (8 * ∑ i, (a i)⁻¹) := by
  have hsum : ∑ i, (a i)⁻¹ ≠ 0 :=
    (Finset.sum_pos (fun i _ => inv_pos.mpr (ha i)) Finset.univ_nonempty).ne'
  have h := _root_.GD.N0213.N0525.d008433 a r d ha hd
    ((∑ i, (a i)⁻¹ * r i) / (∑ i, (a i)⁻¹))
  rw [_root_.GD.N0213.N0525.d008427 _ _ hsum, _root_.GD.N0213.N0525.d008429 _ _ hsum] at h
  convert h using 1
  ring

theorem d008435 [Nonempty I] (a r : I → ℝ)
    (ha : ∀ i, 0 < a i) (ℓ : ℝ) :
    (∑ i, ∑ j, a i * a j * (r i - r j) ^ 2) / (2 * ∑ i, a i) ≤
      ∑ i, a i * (r i - ℓ) ^ 2 := by
  have hsum : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  rw [_root_.GD.N0213.N0525.d008430 a r hsum.ne' ℓ]
  exact le_add_of_nonneg_right (mul_nonneg hsum.le (sq_nonneg _))

theorem d008436 (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (i j : I) (hij : i ≠ j) :
    a i + a j ≤ a i * a j * (∑ l, (a l)⁻¹) := by
  classical
  have hsum : (a i)⁻¹ + (a j)⁻¹ ≤ ∑ l, (a l)⁻¹ := by
    calc
      _ = ∑ l ∈ ({i, j} : Finset I), (a l)⁻¹ := by simp [hij]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _ => (inv_pos.mpr (ha l)).le)
  calc
    a i + a j = a i * a j * ((a i)⁻¹ + (a j)⁻¹) := by
      field_simp [(ha i).ne', (ha j).ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_pos (ha i) (ha j)).le

theorem d008437 [Nonempty I] (a r d : I → ℝ)
    (ha : ∀ i, 0 < a i) (hd : ∑ i, d i = 0) :
    (∑ i, (-a i * d i ^ 2 + r i * d i)) ≤
      ∑ i, ∑ j, (r i - r j) ^ 2 / (8 * (a i + a j)) := by
  apply (_root_.GD.N0213.N0525.d008434 a r d ha hd).trans
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, le_refl]
  · have heq : (a i)⁻¹ * (a j)⁻¹ * (r i - r j) ^ 2 / (8 * ∑ l, (a l)⁻¹) =
        (r i - r j) ^ 2 / (8 * (a i * a j * (∑ l, (a l)⁻¹))) := by ring
    rw [heq]
    exact div_le_div_of_nonneg_left (sq_nonneg _)
      (mul_pos (by norm_num) (add_pos (ha i) (ha j)))
      (mul_le_mul_of_nonneg_left (_root_.GD.N0213.N0525.d008436 a ha i j hij) (by norm_num))

end
end GD.N0213.N0525

#print axioms _root_.GD.N0213.N0525.d008430
#print axioms _root_.GD.N0213.N0525.d008429
#print axioms _root_.GD.N0213.N0525.d008434
#print axioms _root_.GD.N0213.N0525.d008435
#print axioms _root_.GD.N0213.N0525.d008437
