import GD.Module1472










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0358
noncomputable section

open _root_.GD.N0101.N0357
open _root_.GD.N0232.N0719.N0954

variable {k : ℕ}

def d023210 (b r : Fin k → ℝ) : ℝ :=
  ∏ i, (r i / (r i + 1)) ^ b i

theorem d023211 (b r : Fin k → ℝ) (hr : ∀ i, 0 < r i) :
    0 < _root_.GD.N0101.N0358.d023210 b r := by
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (div_pos (hr i) (by linarith [hr i])) _


theorem d023212 {b r : ℝ} (hb : 0 < b) (hr : 0 < r) (x : ℝ) :
    gammaPDFReal b r x * Real.exp (-x) =
      (r / (r + 1)) ^ b * gammaPDFReal b (r + 1) x := by
  have hr1 : 0 < r + 1 := by linarith
  by_cases hx : 0 ≤ x
  · simp only [gammaPDFReal, if_pos hx]
    rw [Real.div_rpow hr.le hr1.le]
    have he : Real.exp (-((r + 1) * x)) = Real.exp (-(r * x)) * Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    field_simp [(Real.rpow_pos_of_pos hr1 b).ne', (Real.Gamma_pos_of_pos hb).ne']
  · simp only [gammaPDFReal, if_neg hx, zero_mul, mul_zero]

theorem d023213 (b r : Fin k → ℝ)
    (hb : ∀ i, 0 < b i) (hr : ∀ i, 0 < r i) (β : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0954.d009343 b r β * Real.exp (-(∑ i, β i)) =
      _root_.GD.N0101.N0358.d023210 b r * _root_.GD.N0232.N0719.N0954.d009343 b (fun i => r i + 1) β := by
  unfold _root_.GD.N0232.N0719.N0954.d009343 _root_.GD.N0101.N0358.d023210
  rw [← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => _root_.GD.N0101.N0358.d023212 (hb i) (hr i) (β i)



theorem d023214 (b r : Fin k → ℝ)
    (hb : ∀ i, 0 < b i) (hr : ∀ i, 0 < r i) :
    (_root_.GD.N0232.N0719.N0954.d009342 b r).withDensity (fun β => ENNReal.ofReal (Real.exp (-(∑ i, β i)))) =
      ENNReal.ofReal (_root_.GD.N0101.N0358.d023210 b r) • _root_.GD.N0232.N0719.N0954.d009342 b (fun i => r i + 1) := by
  have hr1 : ∀ i, 0 < r i + 1 := fun i => by linarith [hr i]
  have he : Measurable (fun β : Fin k → ℝ => ENNReal.ofReal (Real.exp (-(∑ i, β i)))) := by
    fun_prop
  rw [_root_.GD.N0232.N0719.N0954.d009363 hb hr,
    ← withDensity_mul volume (_root_.GD.N0101.N0357.d023168 b r).ennreal_ofReal he,
    _root_.GD.N0232.N0719.N0954.d009363 hb hr1]
  rw [← withDensity_smul' (ENNReal.ofReal (_root_.GD.N0101.N0358.d023210 b r)) _ ENNReal.ofReal_ne_top]
  apply congrArg (fun f : (Fin k → ℝ) → ℝ≥0∞ => volume.withDensity f)
  funext β
  have hpdf : 0 ≤ _root_.GD.N0232.N0719.N0954.d009343 b r β :=
    Finset.prod_nonneg fun i _ => gammaPDFReal_nonneg (hb i) (hr i) (β i)
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hpdf, _root_.GD.N0101.N0358.d023213 b r hb hr,
    ENNReal.ofReal_mul (_root_.GD.N0101.N0358.d023211 b r hr).le]



theorem d023215 (b r : Fin k → ℝ)
    (hb : ∀ i, 0 < b i) (hr : ∀ i, 0 < r i)
    (F : (Fin k → ℝ) → ℝ≥0∞) :
    (∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) * F β ∂_root_.GD.N0232.N0719.N0954.d009342 b r) =
      ENNReal.ofReal (_root_.GD.N0101.N0358.d023210 b r) * ∫⁻ β, F β ∂_root_.GD.N0232.N0719.N0954.d009342 b (fun i => r i + 1) := by
  have he : Measurable (fun β : Fin k → ℝ => ENNReal.ofReal (Real.exp (-(∑ i, β i)))) := by
    fun_prop
  calc
    _ = ∫⁻ β, F β ∂(_root_.GD.N0232.N0719.N0954.d009342 b r).withDensity
        (fun β => ENNReal.ofReal (Real.exp (-(∑ i, β i)))) :=
      (lintegral_withDensity_eq_lintegral_mul_non_measurable _ he
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) F).symm
    _ = _ := by rw [_root_.GD.N0101.N0358.d023214 b r hb hr, lintegral_smul_measure, smul_eq_mul]

theorem d023216 (b r : Fin k → ℝ)
    (hb : ∀ i, 0 < b i) (hr : ∀ i, 0 < r i) :
    (∫⁻ β, ENNReal.ofReal (Real.exp (-(∑ i, β i))) ∂_root_.GD.N0232.N0719.N0954.d009342 b r) =
      ENNReal.ofReal (_root_.GD.N0101.N0358.d023210 b r) := by
  letI (i : Fin k) := isProbabilityMeasure_gammaMeasure (hb i)
    (show 0 < r i + 1 by linarith [hr i])
  have h := _root_.GD.N0101.N0358.d023215 b r hb hr (fun _ => 1)
  simpa only [mul_one, lintegral_one, _root_.GD.N0232.N0719.N0954.d009342, measure_univ] using h

end
end GD.N0101.N0358

#print axioms _root_.GD.N0101.N0358.d023212
#print axioms _root_.GD.N0101.N0358.d023213
#print axioms _root_.GD.N0101.N0358.d023214
#print axioms _root_.GD.N0101.N0358.d023215
#print axioms _root_.GD.N0101.N0358.d023216
