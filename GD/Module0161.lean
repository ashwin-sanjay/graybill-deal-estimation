import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators
namespace GD.N0232.N0719.N1023
noncomputable section


def d001842 (c C u : ℝ) : ℝ :=
  (c ^ 2 * u + c) / 2 * Real.exp (-(C * u))


theorem d001843 {c C : ℝ} (hC : 0 < C) :
    (∫ u in Ioi (0 : ℝ), _root_.GD.N0232.N0719.N1023.d001842 c C u) =
      ((c / C) ^ 2 + c / C) / 2 := by
  have h0 : IntegrableOn (fun u : ℝ => Real.exp (-(C * u))) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 0) (p := 1) (b := C) (by norm_num) (by norm_num) hC)
  have h1 : IntegrableOn (fun u : ℝ => u * Real.exp (-(C * u))) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (b := C) (by norm_num) (by norm_num) hC)
  have e0 : (∫ u : ℝ in Ioi 0, Real.exp (-(C * u))) = 1 / C := by
    simpa using (Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := 1) (r := C) (by norm_num) hC)
  have e1 : (∫ u : ℝ in Ioi 0, u * Real.exp (-(C * u))) = (1 / C) ^ 2 := by
    have hg : Real.Gamma 2 = 1 := by
      norm_num
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      Real.rpow_two, hg, mul_one] using (Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := 2) (r := C) (by norm_num) hC)
  have heq : _root_.GD.N0232.N0719.N1023.d001842 c C = fun u =>
      (c ^ 2 / 2) * (u * Real.exp (-(C * u))) +
      (c / 2) * Real.exp (-(C * u)) := by
    funext u
    unfold _root_.GD.N0232.N0719.N1023.d001842
    ring
  rw [heq, integral_add (h1.const_mul _) (h0.const_mul _),
    integral_const_mul, integral_const_mul, e1, e0]
  ring



def d001844 {k : ℕ} (σ : Fin k → ℝ) : ℝ :=
  ((∑ i, σ i) / (∑ i, (σ i)⁻¹) +
    (k : ℝ) / (∑ i, (σ i)⁻¹) ^ 2) / 4

theorem d001845 {k : ℕ} (σ : Fin k → ℝ)
    (hσ : ∀ i, 0 < σ i) (hC : 0 < ∑ i, (σ i)⁻¹) :
    (∑ i, σ i ^ 2 / 2 *
      (∫ u in Ioi (0 : ℝ), _root_.GD.N0232.N0719.N1023.d001842 ((σ i)⁻¹) (∑ j, (σ j)⁻¹) u)) =
      _root_.GD.N0232.N0719.N1023.d001844 σ := by
  simp_rw [_root_.GD.N0232.N0719.N1023.d001843 hC]
  have heq : ∀ i : Fin k,
      σ i ^ 2 / 2 * ((((σ i)⁻¹ / (∑ j, (σ j)⁻¹)) ^ 2 +
        (σ i)⁻¹ / (∑ j, (σ j)⁻¹)) / 2) =
      (σ i / (∑ j, (σ j)⁻¹) + 1 / (∑ j, (σ j)⁻¹) ^ 2) / 4 := by
    intro i
    field_simp [(hσ i).ne', hC.ne']
    ring
  simp_rw [heq]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div]
  simp [_root_.GD.N0232.N0719.N1023.d001844, div_eq_mul_inv]

theorem d001846 {k : ℕ} (hk : 0 < k) {σ : ℝ} (hσ : 0 < σ) :
    _root_.GD.N0232.N0719.N1023.d001844 (fun _ : Fin k => σ) = σ ^ 2 * (k + 1) / (4 * k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [_root_.GD.N0232.N0719.N1023.d001844, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [hkR, hσ.ne']


theorem d001847 {k : ℕ} (hk : 0 < k) (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    ((k : ℝ) + 1) / 2 ≤
      (∑ i, p i ^ 2) * ((∑ i, (p i)⁻¹) + k) / 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsq : 1 / (k : ℝ) ≤ ∑ i, p i ^ 2 := by
    have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ p
      (g := fun _ => (1 : ℝ)) (by intros; norm_num)
    simpa [hsum] using h
  have hinv : (k : ℝ) ^ 2 ≤ ∑ i, (p i)⁻¹ := by
    have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun _ : Fin k => (1 : ℝ))
      (g := p) (by intro i _; exact hp i)
    simpa [hsum, one_div] using h
  have hfactor : 0 ≤ (∑ i, (p i)⁻¹) + (k : ℝ) := by nlinarith [sq_nonneg (k : ℝ)]
  have hmul := mul_le_mul_of_nonneg_right hsq hfactor
  have hmul2 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 1 / (k : ℝ))
  have hid : 1 / (k : ℝ) * ((k : ℝ) ^ 2 + k) = k + 1 := by
    field_simp
  nlinarith

theorem d001848 {k : ℕ} (hk : 0 < k) :
    (∑ _i : Fin k, (1 / (k : ℝ)) ^ 2) *
      ((∑ _i : Fin k, (1 / (k : ℝ))⁻¹) + k) / 2 = (k + 1) / 2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hkR]


theorem d001849 {r : ℝ} (hr : 0 < r) :
    _root_.GD.N0232.N0719.N1023.d001844 ![1, 1, r] =
      r / 8 + 3 * r * (4 * r + 1) / (8 * (2 * r + 1) ^ 2) := by
  have hd : 2 * r + 1 ≠ 0 := by positivity
  have hi : 1 + (1 + r⁻¹) ≠ 0 := by positivity
  norm_num [_root_.GD.N0232.N0719.N1023.d001844, Fin.sum_univ_succ]
  field_simp [hr.ne', hd, hi]
  ring


theorem d001850 {r : ℝ} (hr : 0 < r) :
    r / 8 < _root_.GD.N0232.N0719.N1023.d001844 ![1, 1, r] := by
  rw [_root_.GD.N0232.N0719.N1023.d001849 hr]
  have : 0 < 3 * r * (4 * r + 1) / (8 * (2 * r + 1) ^ 2) := by positivity
  linarith

theorem d001851 (M : ℝ) :
    ∃ r : ℝ, 0 < r ∧ M < _root_.GD.N0232.N0719.N1023.d001844 ![1, 1, r] := by
  refine ⟨8 * (|M| + 1), by positivity, ?_⟩
  have h := _root_.GD.N0232.N0719.N1023.d001850 (r := 8 * (|M| + 1)) (by positivity)
  have hm := le_abs_self M
  linarith

end
end GD.N0232.N0719.N1023
#print axioms _root_.GD.N0232.N0719.N1023.d001843
#print axioms _root_.GD.N0232.N0719.N1023.d001845
#print axioms _root_.GD.N0232.N0719.N1023.d001847

#print axioms _root_.GD.N0232.N0719.N1023.d001851
