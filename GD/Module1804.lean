import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace GD.N0073
noncomputable section

variable {k : ℕ}


theorem d029990 (q : Fin k → ℝ) (hq : ∀ i, 0 < q i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, q i / (q i + q j)) = (k.choose 2 : ℝ) := by
  let A : ℝ := ∑ i, ∑ j, q i / (q i + q j)
  have hswap : A = ∑ i, ∑ j, q j / (q i + q j) := by
    dsimp only [A]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [add_comm]
  have hpair (i j : Fin k) : q i / (q i + q j) + q j / (q i + q j) = 1 := by
    rw [← add_div, div_self (add_pos (hq i) (hq j)).ne']
  have htwice : A + A = (k : ℝ) * k := by
    calc
      A + A = (∑ i, ∑ j, q i / (q i + q j)) + (∑ i, ∑ j, q j / (q i + q j)) := by
        rw [← hswap]
      _ = ∑ i, ∑ j, (q i / (q i + q j) + q j / (q i + q j)) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by simp only [hpair, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
  have hdiag (i : Fin k) : q i / (q i + q i) = (1 / 2 : ℝ) := by
    field_simp [(hq i).ne']
    ring
  have herase (i : Fin k) :
      (∑ j ∈ Finset.univ.erase i, q i / (q i + q j)) =
        (∑ j, q i / (q i + q j)) - (1 / 2 : ℝ) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hdiag]
  simp_rw [herase]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change A - (k : ℝ) * (1 / 2) = (k.choose 2 : ℝ)
  rw [Nat.cast_choose_two]
  nlinarith



theorem d029991 (q : Fin k → ℝ) (hq : ∀ i, 0 < q i) (C : ℝ) :
    (∑ i, (q i / (∑ l, q l)) *
      (∑ j ∈ Finset.univ.erase i, C * (q i + q j)⁻¹)) =
      (k.choose 2 : ℝ) * C * (∑ l, q l)⁻¹ := by
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
        (C / (∑ l, q l)) * (q i / (q i + q j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [div_eq_mul_inv]
      ring
    _ = (C / (∑ l, q l)) * (∑ i, ∑ j ∈ Finset.univ.erase i, q i / (q i + q j)) := by
      simp only [Finset.mul_sum]
    _ = _ := by rw [_root_.GD.N0073.d029990 q hq]; simp only [div_eq_mul_inv]; ring

end
end GD.N0073

#print axioms _root_.GD.N0073.d029990
#print axioms _root_.GD.N0073.d029991
