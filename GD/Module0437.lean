import GD.Module0035

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace GD.N0101.N0406
noncomputable section

open _root_.GD.N0230.N0665

variable {k : ℕ} [NeZero k]

theorem d006756 {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) (i : Fin k) :
    0 < _root_.GD.N0230.N0665.d000407 t i :=
  div_pos (inv_pos.mpr (ht i)) (_root_.GD.N0230.N0665.d000408 ht)

theorem d006757 {t : Fin k → ℝ} (ht : ∀ i, 0 < t i) (i : Fin k) :
    _root_.GD.N0230.N0665.d000407 t i ≤ 1 := by
  apply (div_le_one (_root_.GD.N0230.N0665.d000408 ht)).mpr
  exact Finset.single_le_sum (fun j _ => (inv_pos.mpr (ht j)).le) (Finset.mem_univ i)


theorem d006758 {t : Fin k → ℝ} (ht : ∀ i, 0 < t i)
    (i j : Fin k) :
    t i * _root_.GD.N0230.N0665.d000407 t i ^ 2 = t j * _root_.GD.N0230.N0665.d000407 t i * _root_.GD.N0230.N0665.d000407 t j := by
  calc
    _ = (t i * _root_.GD.N0230.N0665.d000407 t i) * _root_.GD.N0230.N0665.d000407 t i := by ring
    _ = (t j * _root_.GD.N0230.N0665.d000407 t j) * _root_.GD.N0230.N0665.d000407 t i := by
      rw [_root_.GD.N0230.N0665.d000410 ht i, _root_.GD.N0230.N0665.d000410 ht j]
    _ = _ := by ring


theorem d006759
    {a t : Fin k → ℝ} (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (i j : Fin k) :
    _root_.GD.N0230.N0665.d000407 t i ^ 2 * ((1 + a i * t i) / (1 + a j * t j)) ≤
      max 1 (a i / a j) := by
  have hpi0 := (_root_.GD.N0101.N0406.d006756 ht i).le
  have hpj0 := (_root_.GD.N0101.N0406.d006756 ht j).le
  have hpi1 := _root_.GD.N0101.N0406.d006757 ht i
  have hpj1 := _root_.GD.N0101.N0406.d006757 ht j
  have hsq : _root_.GD.N0230.N0665.d000407 t i ^ 2 ≤ 1 := by nlinarith
  have hpair : _root_.GD.N0230.N0665.d000407 t i * _root_.GD.N0230.N0665.d000407 t j ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hpi1 hpj1 hpj0 zero_le_one
  have hsecond : (a i / a j) * (_root_.GD.N0230.N0665.d000407 t i * _root_.GD.N0230.N0665.d000407 t j) ≤
      max 1 (a i / a j) := by
    calc
      _ ≤ (a i / a j) * 1 :=
        mul_le_mul_of_nonneg_left hpair (div_pos (ha i) (ha j)).le
      _ = a i / a j := mul_one _
      _ ≤ _ := le_max_right _ _
  have heq : _root_.GD.N0230.N0665.d000407 t i ^ 2 * (1 + a i * t i) =
      _root_.GD.N0230.N0665.d000407 t i ^ 2 + (a j * t j) *
        ((a i / a j) * (_root_.GD.N0230.N0665.d000407 t i * _root_.GD.N0230.N0665.d000407 t j)) := by
    calc
      _ = _root_.GD.N0230.N0665.d000407 t i ^ 2 + a i * (t i * _root_.GD.N0230.N0665.d000407 t i ^ 2) := by ring
      _ = _root_.GD.N0230.N0665.d000407 t i ^ 2 + a i *
          (t j * _root_.GD.N0230.N0665.d000407 t i * _root_.GD.N0230.N0665.d000407 t j) := by
        rw [_root_.GD.N0101.N0406.d006758 ht i j]
      _ = _ := by field_simp [(ha j).ne']
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one
    (mul_pos (ha j) (ht j)).le)).mpr
  rw [heq]
  calc
    _ ≤ max 1 (a i / a j) + (a j * t j) * max 1 (a i / a j) :=
      add_le_add (hsq.trans (le_max_left _ _))
        (mul_le_mul_of_nonneg_left hsecond (mul_pos (ha j) (ht j)).le)
    _ = _ := by ring



theorem d006760
    (a b t : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 1 < b i)
    (ht : ∀ i, 0 < t i) :
    (∑ i, _root_.GD.N0230.N0665.d000407 t i ^ 2 *
      (1 + ∑ j ∈ Finset.univ.erase i,
        (b j / (b i - 1)) * ((1 + a i * t i) / (1 + a j * t j)))) ≤
      1 + ∑ i, ∑ j ∈ Finset.univ.erase i,
        (b j / (b i - 1)) * max 1 (a i / a j) := by
  have hsq : (∑ i, _root_.GD.N0230.N0665.d000407 t i ^ 2) ≤ 1 := by
    rw [← _root_.GD.N0230.N0665.d000409 ht]
    apply Finset.sum_le_sum
    intro i _
    have h0 := (_root_.GD.N0101.N0406.d006756 ht i).le
    have h1 := _root_.GD.N0101.N0406.d006757 ht i
    nlinarith
  simp_rw [mul_add, mul_one, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  apply add_le_add hsq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [show _root_.GD.N0230.N0665.d000407 t i ^ 2 *
      ((b j / (b i - 1)) * ((1 + a i * t i) / (1 + a j * t j))) =
      (b j / (b i - 1)) *
        (_root_.GD.N0230.N0665.d000407 t i ^ 2 * ((1 + a i * t i) / (1 + a j * t j))) by ring]
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0101.N0406.d006759 ha ht i j)
    (div_pos (zero_lt_one.trans (hb j)) (sub_pos.mpr (hb i))).le

end
end GD.N0101.N0406

#print axioms _root_.GD.N0101.N0406.d006758
#print axioms _root_.GD.N0101.N0406.d006759
#print axioms _root_.GD.N0101.N0406.d006760
