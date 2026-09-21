import GD.Module1754
import GD.Module0593
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp



















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1684
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1683
open scoped BigOperators

def d029071 : ℝ := ∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1683.d029050 x

def d029072 : ℝ := 16 * ∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1683.d029050 (1 + 16 * (k : ℝ))

def d029073 : ℝ := ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1683.d029052 x‖

def d029074 : ℝ := ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1683.d029053 x‖

theorem d029075 : Measurable _root_.GD.N0106.N0428.N0765.N1683.d029049 := by
  unfold _root_.GD.N0106.N0428.N0765.N1683.d029049 _root_.GD.N0106.N0428.N0765.N1683.d029048
  fun_prop

theorem d029076 : Measurable _root_.GD.N0106.N0428.N0765.N1683.d029050 := by
  unfold _root_.GD.N0106.N0428.N0765.N1683.d029050
  fun_prop

theorem d029077 : Measurable _root_.GD.N0106.N0428.N0765.N1683.d029052 := by
  unfold _root_.GD.N0106.N0428.N0765.N1683.d029052
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  exact _root_.GD.N0106.N0428.N0765.N1684.d029075.comp (by fun_prop)

theorem d029078 : Measurable _root_.GD.N0106.N0428.N0765.N1683.d029053 := by
  unfold _root_.GD.N0106.N0428.N0765.N1683.d029053
  apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
  exact _root_.GD.N0106.N0428.N0765.N1684.d029075.comp (by fun_prop)

theorem d029079 (C : ℝ) :
    Integrable (fun x : ℝ => C * Real.exp (-x ^ 2)) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  exact hg.const_mul C

theorem d029080 (C : ℝ) :
    (∫ x : ℝ, C * Real.exp (-x ^ 2)) = C * Real.sqrt Real.pi := by
  rw [integral_const_mul]
  congr 1
  simpa using integral_gaussian (1 : ℝ)

theorem d029081 : Integrable _root_.GD.N0106.N0428.N0765.N1683.d029050 := by
  apply (_root_.GD.N0106.N0428.N0765.N1684.d029079 (Real.exp 8)).mono'
    _root_.GD.N0106.N0428.N0765.N1684.d029076.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (_root_.GD.N0106.N0428.N0765.N1683.d029057 x)]
  exact _root_.GD.N0106.N0428.N0765.N1683.d029058 x

theorem d029082 : Integrable _root_.GD.N0106.N0428.N0765.N1683.d029052 := by
  exact (_root_.GD.N0106.N0428.N0765.N1684.d029079 (Real.exp (3 / 2))).mono'
    _root_.GD.N0106.N0428.N0765.N1684.d029077.aestronglyMeasurable
    (Filter.Eventually.of_forall _root_.GD.N0106.N0428.N0765.N1683.d029064)

theorem d029083 : Integrable _root_.GD.N0106.N0428.N0765.N1683.d029053 := by
  exact (_root_.GD.N0106.N0428.N0765.N1684.d029079 (Real.exp (3 / 2))).mono'
    _root_.GD.N0106.N0428.N0765.N1684.d029078.aestronglyMeasurable
    (Filter.Eventually.of_forall _root_.GD.N0106.N0428.N0765.N1683.d029065)

theorem d029084 : _root_.GD.N0106.N0428.N0765.N1684.d029071 ≤ Real.exp 8 * Real.sqrt Real.pi := by
  exact (integral_mono _root_.GD.N0106.N0428.N0765.N1684.d029081 (_root_.GD.N0106.N0428.N0765.N1684.d029079 (Real.exp 8))
    _root_.GD.N0106.N0428.N0765.N1683.d029058).trans_eq (_root_.GD.N0106.N0428.N0765.N1684.d029080 (Real.exp 8))

theorem d029085 : _root_.GD.N0106.N0428.N0765.N1684.d029073 ≤ Real.exp (3 / 2) * Real.sqrt Real.pi := by
  exact (integral_mono _root_.GD.N0106.N0428.N0765.N1684.d029082.norm
    (_root_.GD.N0106.N0428.N0765.N1684.d029079 (Real.exp (3 / 2)))
    _root_.GD.N0106.N0428.N0765.N1683.d029064).trans_eq (_root_.GD.N0106.N0428.N0765.N1684.d029080 (Real.exp (3 / 2)))

theorem d029086 : _root_.GD.N0106.N0428.N0765.N1684.d029074 ≤ Real.exp (3 / 2) * Real.sqrt Real.pi := by
  exact (integral_mono _root_.GD.N0106.N0428.N0765.N1684.d029083.norm
    (_root_.GD.N0106.N0428.N0765.N1684.d029079 (Real.exp (3 / 2)))
    _root_.GD.N0106.N0428.N0765.N1683.d029065).trans_eq (_root_.GD.N0106.N0428.N0765.N1684.d029080 (Real.exp (3 / 2)))

theorem d029087 (k : ℤ) : |(k : ℝ)| ≤ (1 + 16 * (k : ℝ)) ^ 2 := by
  by_cases hk : 0 ≤ k
  · have hx : 0 ≤ (k : ℝ) := by exact_mod_cast hk
    rw [abs_of_nonneg hx]
    nlinarith [sq_nonneg (k : ℝ)]
  · have hk' : k ≤ -1 := by omega
    have hx : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
    rw [abs_of_nonpos (by linarith : (k : ℝ) ≤ 0)]
    nlinarith [sq_nonneg ((k : ℝ) + 1)]

theorem d029088 :
    Summable (fun k : ℤ => _root_.GD.N0106.N0428.N0765.N1683.d029050 (1 + 16 * (k : ℝ))) := by
  have hg : Summable (fun k : ℤ => Real.exp (-|(k : ℝ)|)) := by
    simpa using _root_.GD.N0106.N0428.N0765.N1660.d008566 (k := 1) (by norm_num)
  apply (hg.mul_left (Real.exp 8)).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_pos (_root_.GD.N0106.N0428.N0765.N1683.d029057 _)]
  exact (_root_.GD.N0106.N0428.N0765.N1683.d029058 _).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (_root_.GD.N0106.N0428.N0765.N1684.d029087 k))) (Real.exp_pos 8).le)

theorem d029089 : 16 * Real.exp 7 ≤ _root_.GD.N0106.N0428.N0765.N1684.d029072 := by
  have h0 : _root_.GD.N0106.N0428.N0765.N1683.d029050 1 ≤ ∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1683.d029050 (1 + 16 * (k : ℝ)) := by
    simpa only [Finset.sum_singleton, Int.cast_zero, mul_zero, add_zero] using
      _root_.GD.N0106.N0428.N0765.N1684.d029088.sum_le_tsum ({0} : Finset ℤ)
        (fun k _ => (_root_.GD.N0106.N0428.N0765.N1683.d029057 (1 + 16 * (k : ℝ))).le)
  change 16 * Real.exp 7 ≤ 16 * ∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1683.d029050 (1 + 16 * (k : ℝ))
  rw [← _root_.GD.N0106.N0428.N0765.N1683.d029059]
  exact mul_le_mul_of_nonneg_left h0 (by norm_num)



theorem d029090 :
    (_root_.GD.N0106.N0428.N0765.N1684.d029074 + _root_.GD.N0106.N0428.N0765.N1684.d029073) / (Real.exp (Real.pi / 8) - 1) <
      |_root_.GD.N0106.N0428.N0765.N1684.d029071 - _root_.GD.N0106.N0428.N0765.N1684.d029072| :=
  _root_.GD.N0106.N0428.N0765.N1683.d029070 _root_.GD.N0106.N0428.N0765.N1684.d029084 _root_.GD.N0106.N0428.N0765.N1684.d029089 _root_.GD.N0106.N0428.N0765.N1684.d029086 _root_.GD.N0106.N0428.N0765.N1684.d029085

theorem d029091 :
    (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1683.d029049 (x : ℂ)) = (_root_.GD.N0106.N0428.N0765.N1684.d029071 : ℂ) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1683.d029056]
  exact integral_complex_ofReal

theorem d029092 :
    (16 : ℂ) * (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1683.d029049 ((1 + 16 * (k : ℝ) : ℝ) : ℂ)) =
      (_root_.GD.N0106.N0428.N0765.N1684.d029072 : ℂ) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1683.d029056]
  rw [← Complex.ofReal_tsum]
  unfold _root_.GD.N0106.N0428.N0765.N1684.d029072
  push_cast <;> rfl




theorem d029093 :
    ((∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1683.d029053 x‖) + (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1683.d029052 x‖)) /
        (Real.exp (2 * Real.pi / 16) - 1) <
      ‖(∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1683.d029049 (x : ℂ)) -
        (16 : ℂ) * (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1683.d029049 ((1 + 16 * (k : ℝ) : ℝ) : ℂ))‖ := by
  rw [_root_.GD.N0106.N0428.N0765.N1684.d029091, _root_.GD.N0106.N0428.N0765.N1684.d029092, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have he : (2 * Real.pi / 16 : ℝ) = Real.pi / 8 := by ring
  rw [he]
  exact _root_.GD.N0106.N0428.N0765.N1684.d029090

end
end GD.N0106.N0428.N0765.N1684

#print axioms _root_.GD.N0106.N0428.N0765.N1684.d029081
#print axioms _root_.GD.N0106.N0428.N0765.N1684.d029082
#print axioms _root_.GD.N0106.N0428.N0765.N1684.d029083
#print axioms _root_.GD.N0106.N0428.N0765.N1684.d029088
#print axioms _root_.GD.N0106.N0428.N0765.N1684.d029090
#print axioms _root_.GD.N0106.N0428.N0765.N1684.d029093
