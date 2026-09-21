import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0213.N0495
noncomputable section

def d007174 (L r : ℝ) : ℝ := Real.exp (-(Real.log r / L) ^ 2)

def d007175 (L r : ℝ) : ℝ :=
  -2 * Real.log r / (L ^ 2 * r) * _root_.GD.N0213.N0495.d007174 L r

theorem d007176 (L r : ℝ) : 0 < _root_.GD.N0213.N0495.d007174 L r := Real.exp_pos _

theorem d007177 (L r : ℝ) : _root_.GD.N0213.N0495.d007174 L r ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

theorem d007178 {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    HasDerivAt (_root_.GD.N0213.N0495.d007174 L) (_root_.GD.N0213.N0495.d007175 L r) r := by
  have h := ((((Real.hasDerivAt_log hr.ne').div_const L).pow 2).neg).exp
  convert h using 1
  · rfl
  · unfold _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174
    simp only [Pi.neg_apply, Pi.pow_apply]
    field_simp [hL.ne', hr.ne']
    ring_nf
    field_simp

theorem d007179 : Real.exp '' (univ : Set ℝ) = Ioi 0 := by
  ext r
  constructor
  · rintro ⟨x, _, rfl⟩
    exact Real.exp_pos x
  · intro hr
    exact ⟨Real.log r, mem_univ _, Real.exp_log hr⟩

theorem d007180 (f : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), f r) = ∫ x, Real.exp x * f (Real.exp x) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn f
  simpa only [_root_.GD.N0213.N0495.d007179, Measure.restrict_univ, abs_of_pos (Real.exp_pos _), smul_eq_mul] using h

theorem d007181 (f : ℝ → ℝ) :
    IntegrableOn f (Ioi (0 : ℝ)) ↔ Integrable (fun x => Real.exp x * f (Real.exp x)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn f
  simpa only [_root_.GD.N0213.N0495.d007179, integrableOn_univ, abs_of_pos (Real.exp_pos _), smul_eq_mul] using h

theorem d007182 (L x : ℝ) :
    _root_.GD.N0213.N0495.d007174 L (Real.exp x) ^ 2 = Real.exp (-2 * (x / L) ^ 2) := by
  simp only [_root_.GD.N0213.N0495.d007174, Real.log_exp, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem d007183 {L : ℝ} (hL : 0 < L) (q : ℝ) :
    IntegrableOn (fun r => r ^ q * _root_.GD.N0213.N0495.d007174 L r ^ 2) (Ioi (0 : ℝ)) := by
  rw [_root_.GD.N0213.N0495.d007181]
  have heq : (fun x => Real.exp x * ((Real.exp x) ^ q * _root_.GD.N0213.N0495.d007174 L (Real.exp x) ^ 2)) =
      fun x => Real.exp ((q + 1) * x - 2 * (x / L) ^ 2) := by
    funext x
    rw [_root_.GD.N0213.N0495.d007182, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  have hi := (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / L ^ 2)).const_mul
    (Real.exp ((q + 1) ^ 2 * L ^ 2 / 4))
  apply hi.mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := sq_nonneg (x - (q + 1) * L ^ 2 / 2)
  field_simp
  nlinarith

theorem d007184 {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun r => _root_.GD.N0213.N0495.d007174 L r ^ 2) (Ioi (0 : ℝ)) := by
  simpa only [Real.rpow_zero, one_mul] using _root_.GD.N0213.N0495.d007183 hL 0

theorem d007185 {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun r => _root_.GD.N0213.N0495.d007174 L r ^ 2 / r) (Ioi (0 : ℝ)) := by
  simpa only [Real.rpow_neg_one, div_eq_mul_inv, mul_comm] using
    _root_.GD.N0213.N0495.d007183 hL (-1)

def d007186 : ℝ := ∫ u : ℝ, u ^ 2 * Real.exp (-2 * u ^ 2)

theorem d007187 :
    Integrable (fun u : ℝ => u ^ 2 * Real.exp (-2 * u ^ 2)) := by
  simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (-1 : ℝ) < 2)

theorem d007188 {L : ℝ} (hL : 0 < L) (x : ℝ) :
    Real.exp x * (Real.exp x * _root_.GD.N0213.N0495.d007175 L (Real.exp x) ^ 2) =
      (4 / L ^ 2) * ((x / L) ^ 2 * Real.exp (-2 * (x / L) ^ 2)) := by
  simp only [_root_.GD.N0213.N0495.d007175, Real.log_exp, mul_pow, _root_.GD.N0213.N0495.d007182]
  field_simp
  ring

theorem d007189 {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun r => r * _root_.GD.N0213.N0495.d007175 L r ^ 2) (Ioi (0 : ℝ)) := by
  rw [_root_.GD.N0213.N0495.d007181]
  simp_rw [_root_.GD.N0213.N0495.d007188 hL]
  exact (_root_.GD.N0213.N0495.d007187.comp_div hL.ne').const_mul _

theorem d007190 {L : ℝ} (hL : 0 < L) :
    (∫ r in Ioi (0 : ℝ), r * _root_.GD.N0213.N0495.d007175 L r ^ 2) = 4 * _root_.GD.N0213.N0495.d007186 / L := by
  rw [_root_.GD.N0213.N0495.d007180]
  simp_rw [_root_.GD.N0213.N0495.d007188 hL]
  rw [integral_const_mul, Measure.integral_comp_div
    (fun u : ℝ => u ^ 2 * Real.exp (-2 * u ^ 2)) L, abs_of_pos hL, smul_eq_mul]
  unfold _root_.GD.N0213.N0495.d007186
  field_simp
  simp only [mul_comm]

theorem d007191 :
    Tendsto (fun n : ℕ => ∫ r in Ioi (0 : ℝ),
      r * _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) r ^ 2) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * _root_.GD.N0213.N0495.d007186)
  have heq (n : ℕ) := _root_.GD.N0213.N0495.d007190 (L := (n : ℝ) + 1) (by positivity)
  simp_rw [heq]
  simpa only [mul_zero, mul_one_div] using h

theorem d007192 (r : ℝ) :
    Tendsto (fun n : ℕ => _root_.GD.N0213.N0495.d007174 ((n : ℝ) + 1) r) atTop (𝓝 1) := by
  have hz : Tendsto (fun n : ℕ => Real.log r / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.log r)
  have hh := Real.continuous_exp.continuousAt.tendsto.comp (hz.pow 2).neg
  simpa only [Function.comp_def, _root_.GD.N0213.N0495.d007174, zero_pow (by decide : 2 ≠ 0), neg_zero, Real.exp_zero] using hh

end
end GD.N0213.N0495

#print axioms _root_.GD.N0213.N0495.d007178
#print axioms _root_.GD.N0213.N0495.d007180
#print axioms _root_.GD.N0213.N0495.d007183
#print axioms _root_.GD.N0213.N0495.d007184
#print axioms _root_.GD.N0213.N0495.d007185
#print axioms _root_.GD.N0213.N0495.d007190
#print axioms _root_.GD.N0213.N0495.d007191
#print axioms _root_.GD.N0213.N0495.d007192
