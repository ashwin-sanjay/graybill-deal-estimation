import GD.Module1668
import GD.Module1325
import GD.Module1323

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace GD.N0089
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0072 _root_.GD.N0021

variable {k : ℕ}

def d028310 (a x : ℝ) : ℝ := a / (1 + x) ^ (a + 1)



theorem d028311 (a x p : ℝ) (ha : 0 < a)
    (hx : 0 ≤ x) (hp : 0 < p) :
    gammaPDFReal a 1 p * gammaPDFReal 1 p x =
      _root_.GD.N0089.d028310 a x * gammaPDFReal (a + 1) (1 + x) p := by
  have hA : 0 < 1 + x := by linarith
  have hg : Real.Gamma (a + 1) = a * Real.Gamma a := Real.Gamma_add_one ha.ne'
  have hpow : p ^ (a - 1) * p = p ^ a := by
    calc
      _ = p ^ (a - 1) * p ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = p ^ ((a - 1) + 1) := (Real.rpow_add hp _ _).symm
      _ = _ := by ring_nf
  have he : Real.exp (-(1 * p)) * Real.exp (-(p * x)) =
      Real.exp (-((1 + x) * p)) := by rw [← Real.exp_add]; congr 1; ring
  simp only [gammaPDFReal, if_pos hp.le, if_pos hx, Real.one_rpow,
    Real.rpow_one, sub_self, Real.rpow_zero, Real.Gamma_one, div_one,
    mul_one, add_sub_cancel_right, _root_.GD.N0089.d028310, hg]
  calc
    _ = (p ^ (a - 1) * p) *
        (Real.exp (-(1 * p)) * Real.exp (-(p * x))) / Real.Gamma a := by ring
    _ = p ^ a * Real.exp (-((1 + x) * p)) / Real.Gamma a := by rw [hpow, he]
    _ = _ := by field_simp [ha.ne', (Real.Gamma_pos_of_pos ha).ne',
        (Real.rpow_pos_of_pos hA (a + 1)).ne']



theorem d028312 (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    (∫⁻ p, gammaPDF a 1 p * gammaPDF 1 p x) = ENNReal.ofReal (_root_.GD.N0089.d028310 a x) := by
  have hA : 0 < 1 + x := by linarith
  calc
    _ = ∫⁻ p, ENNReal.ofReal (_root_.GD.N0089.d028310 a x) * gammaPDF (a + 1) (1 + x) p := by
      apply lintegral_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with p hp
      rcases lt_or_gt_of_ne hp with hneg | hpos
      · simp [gammaPDF_of_neg hneg]
      · rw [gammaPDF, gammaPDF, ← ENNReal.ofReal_mul
          (gammaPDFReal_nonneg ha (by norm_num) p), _root_.GD.N0089.d028311 a x p ha hx hpos,
          ENNReal.ofReal_mul (by unfold _root_.GD.N0089.d028310; positivity), gammaPDF]
    _ = ENNReal.ofReal (_root_.GD.N0089.d028310 a x) * ∫⁻ p, gammaPDF (a + 1) (1 + x) p :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [lintegral_gammaPDF_eq_one (by linarith) hA, mul_one]

def d028313 (a : ℝ) (x : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (a + 1) (1 + x i)



theorem d028314 (a : ℝ) (ha : 0 < a)
    (x w : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∫ p, _root_.GD.N0072.d007621 (fun i => (p i)⁻¹) w ∂_root_.GD.N0089.d028313 a x) =
      _root_.GD.N0072.d007621 (fun i => x i + 1) w / a := by
  let μ : Fin k → Measure ℝ := fun i => gammaMeasure (a + 1) (1 + x i)
  have hA : ∀ i, 0 < 1 + x i := fun i => by have := hx i; linarith
  letI (i : Fin k) : IsProbabilityMeasure (μ i) :=
    isProbabilityMeasure_gammaMeasure (by linarith) (hA i)
  have hint (i : Fin k) : Integrable (fun p : Fin k → ℝ => (p i)⁻¹)
      (_root_.GD.N0089.d028313 a x) :=
    (measurePreserving_eval μ i).integrable_comp_of_integrable
      (_root_.GD.N0232.N0719.N0876.d020682 (by linarith) (hA i))
  have hmean (i : Fin k) : (∫ p : Fin k → ℝ, (p i)⁻¹
      ∂_root_.GD.N0089.d028313 a x) = (1 + x i) / a := by
    have hh := integral_comp_eval (μ := μ) (i := i) (f := fun p : ℝ => p⁻¹)
      measurable_inv.aestronglyMeasurable
    rw [_root_.GD.N0023.N0257.d021615 (by linarith) (hA i)] at hh
    simpa only [_root_.GD.N0089.d028313, μ, add_sub_cancel_right] using hh
  unfold _root_.GD.N0072.d007621
  rw [integral_finsetSum _ (fun i _ => (hint i).const_mul (w i ^ 2))]
  simp_rw [integral_const_mul, hmean, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm]



theorem d028315 (hk : 0 < k)
    (a : ℝ) (ha : 0 < a) (x w : Fin k → ℝ)
    (hx : ∀ i, 0 < x i) (hw : ∑ i, w i = 1) :
    (∫ p, _root_.GD.N0072.d007621 (fun i => (p i)⁻¹) (_root_.GD.N0021.d023313 x) ∂_root_.GD.N0089.d028313 a x) ≤
      (∫ p, _root_.GD.N0072.d007621 (fun i => (p i)⁻¹) w ∂_root_.GD.N0089.d028313 a x) + 1 / a := by
  rw [_root_.GD.N0089.d028314 a ha x _ (fun i => (hx i).le),
    _root_.GD.N0089.d028314 a ha x _ (fun i => (hx i).le), ← add_div]
  exact div_le_div_of_nonneg_right (_root_.GD.N0089.d028305 hk x w hx hw 1 (by norm_num)) ha.le

end
end GD.N0089

#print axioms _root_.GD.N0089.d028311
#print axioms _root_.GD.N0089.d028312
#print axioms _root_.GD.N0089.d028314
#print axioms _root_.GD.N0089.d028315
