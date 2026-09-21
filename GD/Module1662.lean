import GD.Module0640
import GD.Module0223
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0213.N0527

noncomputable section

def d028204 (e a C x : ℝ) : ℝ :=
  e * a ^ 2 / (x + e * a + e * C * x) ^ 2

def d028205 (e a C u : ℝ) : ℝ :=
  Real.exp (-(e * a * u)) / (1 + (1 + e * C) * u) ^ 2

theorem d028206 (e a C x : ℝ) (hx : x ≠ 0) :
    e * (a / x) ^ 2 / (1 + e * (a / x + C)) ^ 2 = _root_.GD.N0213.N0527.d028204 e a C x := by
  unfold _root_.GD.N0213.N0527.d028204
  field_simp
  ring

theorem d028207 (e a C u : ℝ) : 0 ≤ _root_.GD.N0213.N0527.d028205 e a C u := by
  unfold _root_.GD.N0213.N0527.d028205
  positivity

theorem d028208 (e a C u : ℝ)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hC : 0 ≤ C) (hu : 0 ≤ u) :
    _root_.GD.N0213.N0527.d028205 e a C u ≤ 1 / (1 + u) ^ 2 := by
  have hden : 0 < (1 + (1 + e * C) * u) ^ 2 := by positivity
  have hbase : 0 < (1 + u) ^ 2 := by positivity
  have hexp : Real.exp (-(e * a * u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg he ha) hu))
  have hsq : (1 + u) ^ 2 ≤ (1 + (1 + e * C) * u) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_nonneg he hC, mul_nonneg (mul_nonneg he hC) hu]
  unfold _root_.GD.N0213.N0527.d028205
  exact (div_le_div_of_nonneg_right hexp hden.le).trans
    (div_le_div_of_nonneg_left (by norm_num) hbase hsq)

theorem d028209 :
    IntegrableOn (fun u : ℝ => 1 / (1 + u) ^ 2) (Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt
    (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ)) (by norm_num) (by norm_num)
  apply h.congr_fun _ measurableSet_Ioi
  intro u hu
  have hu' : 0 < u := hu
  change (u + 1) ^ (-2 : ℝ) = 1 / (1 + u) ^ 2
  rw [Real.rpow_neg (by linarith : 0 ≤ u + 1), Real.rpow_two]
  simp [one_div, add_comm]

theorem d028210 :
    (∫ u in Ioi (0 : ℝ), 1 / (1 + u) ^ 2) = 1 := by
  have h := _root_.GD.N0232.N0720.N1050.d003164
    1 1 (by norm_num) (by norm_num)
  norm_num [ProbabilityTheory.beta, Real.Gamma_add_one] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  norm_num [one_div, Real.rpow_two]
  rfl

theorem d028211 (a C u : ℝ) (hu : 0 ≤ u)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0213.N0527.d028205 (e n) a C u) atTop (𝓝 (1 / (1 + u) ^ 2)) := by
  have hnum : Tendsto (fun n => Real.exp (-(e n * a * u))) atTop (𝓝 1) := by
    have hz : Tendsto (fun n => -(e n * a * u)) atTop (𝓝 0) := by
      simpa using ((he.mul_const a).mul_const u).neg
    have hh := (Real.continuous_exp.tendsto 0).comp hz
    simpa only [Function.comp_def, Real.exp_zero] using hh
  have hden : Tendsto (fun n => (1 + (1 + e n * C) * u) ^ 2)
      atTop (𝓝 ((1 + u) ^ 2)) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add
      (((tendsto_const_nhds (x := (1 : ℝ))).add (he.mul_const C)).mul_const u)).pow 2)
  exact hnum.div hden (by positivity)

theorem d028212 (a C : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u in Ioi (0 : ℝ), _root_.GD.N0213.N0527.d028205 (e n) a C u)
      atTop (𝓝 1) := by
  rw [← _root_.GD.N0213.N0527.d028210]
  apply tendsto_integral_of_dominated_convergence (fun u : ℝ => 1 / (1 + u) ^ 2)
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold _root_.GD.N0213.N0527.d028205
    fun_prop
  · exact _root_.GD.N0213.N0527.d028209
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0213.N0527.d028207 _ _ _ _)]
    exact _root_.GD.N0213.N0527.d028208 _ _ _ _ (he n) ha hC hu.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact _root_.GD.N0213.N0527.d028211 a C u hu.le e he0

theorem d028213 (e a C : ℝ) (he : 0 < e) (ha : 0 < a) :
    (∫ x, _root_.GD.N0213.N0527.d028204 e a C x ∂gammaMeasure 1 1) =
      a * ∫ u in Ioi (0 : ℝ), _root_.GD.N0213.N0527.d028205 e a C u := by
  rw [_root_.GD.N0232.N0719.N0954.d009351
    (by norm_num) (by norm_num)]
  have hrestrict : (∫ x, gammaPDFReal 1 1 x * _root_.GD.N0213.N0527.d028204 e a C x) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-x) * _root_.GD.N0213.N0527.d028204 e a C x := by
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (s := Ioi (0 : ℝ))]
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxpos : 0 < x := hx
      simp [gammaPDFReal, hxpos.le]
    · filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx
      intro hxnot
      have hxneg : x < 0 := lt_of_le_of_ne (not_lt.mp hxnot) hx
      simp [gammaPDFReal, not_le.mpr hxneg]
  rw [hrestrict]
  have hscale := integral_comp_mul_left_Ioi
    (fun x => Real.exp (-x) * _root_.GD.N0213.N0527.d028204 e a C x) 0 (mul_pos he ha)
  simp only [mul_zero, smul_eq_mul] at hscale
  have hrecover : (∫ x in Ioi (0 : ℝ), Real.exp (-x) * _root_.GD.N0213.N0527.d028204 e a C x) =
      (e * a) * ∫ u in Ioi (0 : ℝ),
        Real.exp (-(e * a * u)) * _root_.GD.N0213.N0527.d028204 e a C (e * a * u) := by
    rw [hscale]
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero he.ne' ha.ne'), one_mul]
  rw [hrecover, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  unfold _root_.GD.N0213.N0527.d028204 _root_.GD.N0213.N0527.d028205
  dsimp only []
  have hden : e * a * u + e * a + e * C * (e * a * u) =
      (e * a) * (1 + (1 + e * C) * u) := by ring
  rw [hden, mul_pow]
  field_simp

theorem d028214 (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, _root_.GD.N0213.N0527.d028204 (e n) a C x ∂gammaMeasure 1 1)
      atTop (𝓝 a) := by
  have h := (_root_.GD.N0213.N0527.d028212 a C ha.le hC e
    (fun n => (he n).le) he0).const_mul a
  simpa only [_root_.GD.N0213.N0527.d028213 _ _ _ (he _) ha, mul_one] using h

theorem d028215
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    ¬ Tendsto (fun n => ∫ x, _root_.GD.N0213.N0527.d028204 (e n) a C x ∂gammaMeasure 1 1)
      atTop (𝓝 0) := by
  intro hzero
  exact ha.ne (tendsto_nhds_unique hzero
    (_root_.GD.N0213.N0527.d028214 a C ha hC e he he0))

theorem d028216 (e a C : ℝ)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hC : 0 ≤ C) :
    (∫ u in Ioi (0 : ℝ), _root_.GD.N0213.N0527.d028205 e a C u) ≤ 1 := by
  have hmeas : AEStronglyMeasurable (_root_.GD.N0213.N0527.d028205 e a C) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold _root_.GD.N0213.N0527.d028205
    fun_prop
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ‖_root_.GD.N0213.N0527.d028205 e a C u‖ ≤ 1 / (1 + u) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0213.N0527.d028207 _ _ _ _)]
    exact _root_.GD.N0213.N0527.d028208 e a C u he ha hC hu.le
  rw [← _root_.GD.N0213.N0527.d028210]
  apply integral_mono_ae (_root_.GD.N0213.N0527.d028209.mono' hmeas hbound)
    _root_.GD.N0213.N0527.d028209
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact _root_.GD.N0213.N0527.d028208 e a C u he ha hC hu.le

theorem d028217 (e a C : ℝ)
    (he : 0 < e) (ha : 0 < a) (hC : 0 ≤ C) :
    (∫ x, _root_.GD.N0213.N0527.d028204 e a C x ∂gammaMeasure 1 1) ≤ a := by
  rw [_root_.GD.N0213.N0527.d028213 e a C he ha]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (_root_.GD.N0213.N0527.d028216 e a C he.le ha.le hC) ha.le

theorem d028218
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a C : Ω → ℝ) (ha : Measurable a) (hC : Measurable C)
    (hpositive : ∀ᵐ ω ∂μ, 0 < a ω ∧ 0 ≤ C ω) (hint : Integrable a μ)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ∫ x, _root_.GD.N0213.N0527.d028204 (e n) (a ω) (C ω) x
      ∂gammaMeasure 1 1 ∂μ) atTop (𝓝 (∫ ω, a ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence a
  · intro n
    have hm : StronglyMeasurable (fun p : Ω × ℝ => _root_.GD.N0213.N0527.d028204 (e n) (a p.1) (C p.1) p.2) := by
      unfold _root_.GD.N0213.N0527.d028204
      fun_prop
    exact hm.integral_prod_right'.aestronglyMeasurable
  · exact hint
  · intro n
    filter_upwards [hpositive] with ω hω
    have hnonneg : 0 ≤ ∫ x, _root_.GD.N0213.N0527.d028204 (e n) (a ω) (C ω) x ∂gammaMeasure 1 1 := by
      apply integral_nonneg
      intro x
      unfold _root_.GD.N0213.N0527.d028204
      exact div_nonneg (mul_nonneg (he n).le (sq_nonneg _)) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact _root_.GD.N0213.N0527.d028217 _ _ _ (he n) hω.1 hω.2
  · filter_upwards [hpositive] with ω hω
    exact _root_.GD.N0213.N0527.d028214 (a ω) (C ω) hω.1 hω.2 e he he0

end
end GD.N0213.N0527

#print axioms _root_.GD.N0213.N0527.d028206
#print axioms _root_.GD.N0213.N0527.d028207
#print axioms _root_.GD.N0213.N0527.d028208
#print axioms _root_.GD.N0213.N0527.d028209
#print axioms _root_.GD.N0213.N0527.d028210
#print axioms _root_.GD.N0213.N0527.d028211
#print axioms _root_.GD.N0213.N0527.d028212
#print axioms _root_.GD.N0213.N0527.d028213
#print axioms _root_.GD.N0213.N0527.d028214
#print axioms _root_.GD.N0213.N0527.d028215
#print axioms _root_.GD.N0213.N0527.d028216
#print axioms _root_.GD.N0213.N0527.d028217
#print axioms _root_.GD.N0213.N0527.d028218
