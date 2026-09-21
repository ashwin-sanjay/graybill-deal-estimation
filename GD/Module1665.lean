import GD.Module1664

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0420
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0033

variable {k : ℕ}

def d028253 (p q : Fin k → ℝ) : ℝ := ∑ i, p i / q i
def d028254 (p q : Fin k → ℝ) : ℝ := (_root_.GD.N0102.N0420.d028253 p q)⁻¹
def d028255 (p q : Fin k → ℝ) (i : Fin k) : ℝ :=
  (p i / q i ^ 2) / _root_.GD.N0102.N0420.d028253 p q ^ 2
def d028256 (p q : Fin k → ℝ) : ℝ := ∑ i, _root_.GD.N0102.N0420.d028255 p q i

@[fun_prop] theorem d028257 (p : Fin k → ℝ) : Measurable (_root_.GD.N0102.N0420.d028254 p) := by
  unfold _root_.GD.N0102.N0420.d028254 _root_.GD.N0102.N0420.d028253
  fun_prop

@[fun_prop] theorem d028258 (p : Fin k → ℝ) (i : Fin k) :
    Measurable (fun q => _root_.GD.N0102.N0420.d028255 p q i) := by
  unfold _root_.GD.N0102.N0420.d028255 _root_.GD.N0102.N0420.d028253
  fun_prop

theorem d028259 (p q : Fin (k + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) : 0 < _root_.GD.N0102.N0420.d028253 p q := by
  exact Finset.sum_pos (fun i _ => div_pos (hp i) (hq i)) Finset.univ_nonempty


theorem d028260 (p q : Fin (k + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) (hq : ∀ i, 0 < q i) :
    _root_.GD.N0102.N0420.d028254 p q ≤ ∑ i, p i * q i := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := p) (f := fun i => p i * q i) (g := fun i => p i / q i)
    (fun i _ => (mul_pos (hp i) (hq i)).le)
    (fun i _ => (div_pos (hp i) (hq i)).le)
    (fun i _ => by field_simp [(hq i).ne']; nlinarith [sq_nonneg (p i)])
  rw [hsum, one_pow] at hc
  exact (inv_le_iff_one_le_mul₀ (_root_.GD.N0102.N0420.d028259 p q hp hq)).mpr hc



theorem d028261
    (shape p : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028254 p q) ∂_root_.GD.N0033.d028239 shape) ≤ 1 := by
  let μ : Fin (k + 1) → Measure ℝ := fun i => gammaMeasure (shape i) (shape i)
  letI (i : Fin (k + 1)) : IsProbabilityMeasure (μ i) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  have hint (i : Fin (k + 1)) : Integrable (fun q : Fin (k + 1) → ℝ => q i) (_root_.GD.N0033.d028239 shape) :=
    (measurePreserving_eval μ i).integrable_comp_of_integrable
      (_root_.GD.N0232.N0719.N0877.d020694 (hs i) (hs i))
  have hmean (i : Fin (k + 1)) : (∫ q : Fin (k + 1) → ℝ, q i ∂_root_.GD.N0033.d028239 shape) = 1 := by
    have h := integral_comp_eval (μ := μ) (i := i) (f := fun x : ℝ => x)
      measurable_id.aestronglyMeasurable
    rw [_root_.GD.N0232.N0719.N0960.d009682 (hs i) (hs i)] at h
    simpa only [div_self (hs i).ne'] using h
  have ha : Integrable (fun q : Fin (k + 1) → ℝ => ∑ i, p i * q i) (_root_.GD.N0033.d028239 shape) :=
    integrable_finsetSum _ fun i _ => (hint i).const_mul (p i)
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal (∑ i, p i * q i) ∂_root_.GD.N0033.d028239 shape := by
      apply lintegral_mono_ae
      filter_upwards [_root_.GD.N0033.d028240 shape hs] with q hq
      exact ENNReal.ofReal_le_ofReal (_root_.GD.N0102.N0420.d028260 p q hp hsum hq)
    _ = ENNReal.ofReal (∫ q, ∑ i, p i * q i ∂_root_.GD.N0033.d028239 shape) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal ha
      filter_upwards [_root_.GD.N0033.d028240 shape hs] with q hq
      exact Finset.sum_nonneg fun i _ => (mul_pos (hp i) (hq i)).le
    _ = 1 := by
      rw [integral_finsetSum _ (fun i _ => (hint i).const_mul (p i))]
      simp_rw [integral_const_mul, hmean, mul_one]
      rw [hsum, ENNReal.ofReal_one]




def d028262 (s : ℝ) : Prop := ∀ a B : ℝ, 0 < a → 0 ≤ B →
  (∫⁻ x, ENNReal.ofReal (a / (a + B * x) ^ 2) ∂gammaMeasure s s) ≤
    ENNReal.ofReal s * ∫⁻ x, ENNReal.ofReal (x / (a + B * x)) ∂gammaMeasure s s



theorem d028263
    (shape : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hscalar : _root_.GD.N0102.N0420.d028262 (shape i))
    (a : ℝ) (ha : 0 < a) (B : (Fin k → ℝ) → ℝ) (hBm : Measurable B)
    (hB : ∀ᵐ b ∂_root_.GD.N0033.d028239 (fun j => shape (i.succAbove j)), 0 ≤ B b) :
    (∫⁻ q, ENNReal.ofReal (a / (a + B (fun j => q (i.succAbove j)) * q i) ^ 2)
      ∂_root_.GD.N0033.d028239 shape) ≤
    ENNReal.ofReal (shape i) *
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
  rw [hf, hg, lintegral_prod_symm' _ hfm, lintegral_prod_symm' _ hgm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hB] with b hb
  exact hscalar a (B b) ha hb

end
end GD.N0102.N0420

#print axioms _root_.GD.N0102.N0420.d028260
#print axioms _root_.GD.N0102.N0420.d028261
#print axioms _root_.GD.N0102.N0420.d028263
