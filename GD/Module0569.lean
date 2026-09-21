import GD.Module0568
import GD.Module0161







set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1750
noncomputable section

open _root_.GD.N0232.N0719.N1023

theorem d008405 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma : ι → ℝ) :
    _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma = 2 * ∑ i, (sigma i)⁻¹ := by
  simp [_root_.GD.N0106.N0428.N0770.N1750.d008368, div_eq_mul_inv, Finset.mul_sum]

theorem d008406 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma : ι → ℝ) (i : ι) :
    (2 / sigma i) / _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma = (sigma i)⁻¹ / (∑ j, (sigma j)⁻¹) := by
  rw [_root_.GD.N0106.N0428.N0770.N1750.d008405]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring



theorem d008407 {k : ℕ} (hk : 0 < k)
    {sigma : Fin k → ℝ} (hsigma : ∀ i, 0 < sigma i) :
    (∑ i, sigma i ^ 2 / 2 *
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k))) =
      _root_.GD.N0232.N0719.N1023.d001844 sigma := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hS : 0 < ∑ i, (sigma i)⁻¹ := by
    have hR := _root_.GD.N0106.N0428.N0770.N1750.d008394 hsigma
    rw [_root_.GD.N0106.N0428.N0770.N1750.d008405] at hR
    linarith
  calc
    _ = ∑ i, sigma i ^ 2 / 2 *
        (∫ u in Ioi (0 : ℝ), _root_.GD.N0232.N0719.N1023.d001842 ((sigma i)⁻¹) (∑ j, (sigma j)⁻¹) u) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [_root_.GD.N0106.N0428.N0770.N1750.d008400 hsigma i, _root_.GD.N0232.N0719.N1023.d001843 hS,
        _root_.GD.N0106.N0428.N0770.N1750.d008406]
    _ = _ := _root_.GD.N0232.N0719.N1023.d001845 sigma hsigma hS


theorem d008408 {k : ℕ} (hk : 0 < k)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∑ i : Fin k, sigma ^ 2 / 2 *
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 (fun _ : Fin k => sigma) i ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k))) =
      sigma ^ 2 * (k + 1) / (4 * k) :=
  (_root_.GD.N0106.N0428.N0770.N1750.d008407 hk (fun _ => hsigma)).trans
    (_root_.GD.N0232.N0719.N1023.d001846 hk hsigma)


theorem d008409 {r : ℝ} (hr : 0 < r) :
    (∑ i : Fin 3, (![1, 1, r] i) ^ 2 / 2 *
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 ![1, 1, r] i ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin 3))) =
      r / 8 + 3 * r * (4 * r + 1) / (8 * (2 * r + 1) ^ 2) := by
  have hsigma : ∀ i : Fin 3, 0 < ![1, 1, r] i := by
    intro i
    fin_cases i <;> simp [hr]
  exact (_root_.GD.N0106.N0428.N0770.N1750.d008407 (by norm_num) hsigma).trans
    (_root_.GD.N0232.N0719.N1023.d001849 hr)

end
end GD.N0106.N0428.N0770.N1750

#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008405
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008406
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008407
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008408
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008409
