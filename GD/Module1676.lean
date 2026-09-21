import GD.Module1511
import GD.Module1667

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0070
noncomputable section

open _root_.GD.N0033 _root_.GD.N0102.N0420
open _root_.GD.N0047

variable {k : ℕ}



theorem d028363
    (shape : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hs : 1 ≤ shape i)
    (a : ℝ) (ha : 0 < a) (B : (Fin k → ℝ) → ℝ) (hBm : Measurable B)
    (hB : ∀ᵐ b ∂_root_.GD.N0033.d028239 (fun j => shape (i.succAbove j)), 0 ≤ B b) :
    (∫⁻ q, ENNReal.ofReal (a / (a + B (fun j => q (i.succAbove j)) * q i) ^ 2)
      ∂_root_.GD.N0033.d028239 shape) ≤
      ∫⁻ q, ENNReal.ofReal (q i / (a + B (fun j => q (i.succAbove j)) * q i))
        ∂_root_.GD.N0033.d028239 shape := by
  let μ : Fin (k + 1) → Measure ℝ := fun j => gammaMeasure (shape j) (shape j)
  let ν := _root_.GD.N0033.d028239 (fun j => shape (i.succAbove j))
  let f : ℝ × (Fin k → ℝ) → ℝ≥0∞ := fun r => ENNReal.ofReal (a / (a + B r.2 * r.1) ^ 2)
  let g : ℝ × (Fin k → ℝ) → ℝ≥0∞ := fun r => ENNReal.ofReal (r.1 / (a + B r.2 * r.1))
  have hfm : Measurable f := by unfold f; fun_prop
  have hgm : Measurable g := by unfold g; fun_prop
  have hf := (measurePreserving_piFinSuccAbove μ i).lintegral_comp hfm
  have hg := (measurePreserving_piFinSuccAbove μ i).lintegral_comp hgm
  change (∫⁻ q, ENNReal.ofReal (a / (a + B (fun j => q (i.succAbove j)) * q i) ^ 2)
      ∂_root_.GD.N0033.d028239 shape) = ∫⁻ r, f r ∂((μ i).prod ν) at hf
  change (∫⁻ q, ENNReal.ofReal (q i / (a + B (fun j => q (i.succAbove j)) * q i))
      ∂_root_.GD.N0033.d028239 shape) = ∫⁻ r, g r ∂((μ i).prod ν) at hg
  rw [hf, hg, lintegral_prod_symm' _ hfm, lintegral_prod_symm' _ hgm]
  apply lintegral_mono_ae
  filter_upwards [hB] with b hb
  exact _root_.GD.N0047.d023545 a (B b) (shape i) ha hb hs



theorem d028364
    (shape p : Fin (k + 1) → ℝ) (hs : ∀ i, 1 ≤ shape i) (hp : ∀ i, 0 < p i)
    (i : Fin (k + 1)) :
    (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape) ≤
      ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028254 p q) ∂_root_.GD.N0033.d028239 shape := by
  have hs0 : ∀ i, 0 < shape i := fun i => lt_of_lt_of_le (by norm_num) (hs i)
  have hB : ∀ᵐ b ∂_root_.GD.N0033.d028239 (fun j => shape (i.succAbove j)), 0 ≤ _root_.GD.N0102.N0420.d028264 p i b := by
    filter_upwards [_root_.GD.N0033.d028240 _
      (fun j => hs0 (i.succAbove j))] with b hb
    exact _root_.GD.N0102.N0420.d028266 p i hp b hb
  have hc := _root_.GD.N0070.d028363 shape i (hs i) (p i) (hp i)
    (_root_.GD.N0102.N0420.d028264 p i) (_root_.GD.N0102.N0420.d028265 p i) hB
  have heq : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape) =
      ∫⁻ q, ENNReal.ofReal (p i / (p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i) ^ 2)
        ∂_root_.GD.N0033.d028239 shape := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0033.d028240 shape hs0] with q hq
    rw [_root_.GD.N0102.N0420.d028268 p q i hp hq]
  have heqH : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028254 p q) ∂_root_.GD.N0033.d028239 shape) =
      ∫⁻ q, ENNReal.ofReal (q i / (p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i))
        ∂_root_.GD.N0033.d028239 shape := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0033.d028240 shape hs0] with q hq
    rw [_root_.GD.N0102.N0420.d028269 p q i hq]
  rwa [heq, heqH]


theorem d028365
    (shape p : Fin (k + 1) → ℝ) (hs : ∀ i, 1 ≤ shape i) (hp : ∀ i, 0 < p i) :
    (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028256 p q) ∂_root_.GD.N0033.d028239 shape) ≤
      ENNReal.ofReal (k + 1 : ℝ) *
        ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028254 p q) ∂_root_.GD.N0033.d028239 shape := by
  have heq : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028256 p q) ∂_root_.GD.N0033.d028239 shape) =
      ∑ i, ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape := by
    calc
      _ = ∫⁻ q, ∑ i, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape := by
        apply lintegral_congr
        intro q
        exact ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          div_nonneg (div_nonneg (hp i).le (sq_nonneg _)) (sq_nonneg _))
      _ = _ := lintegral_finsetSum _ (fun i _ => ENNReal.measurable_ofReal.comp
        (_root_.GD.N0102.N0420.d028258 p i))
  rw [heq]
  calc
    _ ≤ ∑ _i : Fin (k + 1), ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028254 p q) ∂_root_.GD.N0033.d028239 shape :=
      Finset.sum_le_sum fun i _ => _root_.GD.N0070.d028364 shape p hs hp i
    _ = _ := by simp [nsmul_eq_mul, ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one]



theorem d028366
    (shape p : Fin (k + 1) → ℝ) (hs : ∀ i, 1 ≤ shape i)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028256 p q) ∂_root_.GD.N0033.d028239 shape) ≤
      ENNReal.ofReal (k + 1 : ℝ) := by
  have hs0 : ∀ i, 0 < shape i := fun i => lt_of_lt_of_le (by norm_num) (hs i)
  exact (_root_.GD.N0070.d028365 shape p hs hp).trans
    (by simpa only [mul_one] using (mul_le_mul_right
      (_root_.GD.N0102.N0420.d028261 shape p hs0 hp hsum) (ENNReal.ofReal (k + 1 : ℝ))))

end
end GD.N0070

#print axioms _root_.GD.N0070.d028363
#print axioms _root_.GD.N0070.d028364
#print axioms _root_.GD.N0070.d028365
#print axioms _root_.GD.N0070.d028366
