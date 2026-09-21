import GD.Module1670
import GD.Module1671
import Mathlib.MeasureTheory.Group.LIntegral

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0089
noncomputable section

def d028371 (a x : ℝ) : ℝ≥0∞ := paretoPDF 1 a (x + 1)
def d028372 (a : ℝ) : Measure ℝ := volume.withDensity (_root_.GD.N0089.d028371 a)

@[fun_prop] theorem d028373 (a : ℝ) :
    Measurable (_root_.GD.N0089.d028371 a) := by
  unfold _root_.GD.N0089.d028371 paretoPDF
  fun_prop

theorem d028374 (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (_root_.GD.N0089.d028372 a) where
  measure_univ := by
    rw [_root_.GD.N0089.d028372, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change (∫⁻ x, paretoPDF 1 a (x + 1)) = 1
    rw [lintegral_add_right_eq_self, lintegral_paretoPDF_eq_one (by norm_num) ha]

theorem d028375 (a : ℝ) :
    MeasurePreserving (fun x : ℝ => x + 1) (_root_.GD.N0089.d028372 a) (paretoMeasure 1 a) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop), _root_.GD.N0089.d028372,
    lintegral_withDensity_eq_lintegral_mul _ (_root_.GD.N0089.d028373 a)
      (show Measurable (fun x : ℝ => f (x + 1)) by fun_prop), paretoMeasure,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (paretoPDF 1 a) by unfold paretoPDF; fun_prop) hf]
  exact lintegral_add_right_eq_self (fun z => paretoPDF 1 a z * f z) 1

theorem d028376 (a x : ℝ) (hx : 0 ≤ x) :
    _root_.GD.N0089.d028371 a x = ENNReal.ofReal (_root_.GD.N0089.d028310 a x) := by
  rw [_root_.GD.N0089.d028371, paretoPDF_of_le (by linarith : 1 ≤ x + 1),
    Real.one_rpow, mul_one, _root_.GD.N0089.d028310, Real.rpow_neg (by positivity : 0 ≤ x + 1)]
  congr 1
  rw [add_comm x 1]
  rfl



theorem d028377 (a x p : ℝ) (ha : 0 < a) :
    gammaPDF a 1 p * gammaPDF 1 p x =
      _root_.GD.N0089.d028371 a x * gammaPDF (a + 1) (x + 1) p := by
  by_cases hx : 0 ≤ x
  · rcases lt_trichotomy p 0 with hp | rfl | hp
    · simp [gammaPDF_of_neg hp]
    · simp [gammaPDF, gammaPDFReal, ha.ne']
    · rw [_root_.GD.N0089.d028376 a x hx]
      have heq := _root_.GD.N0089.d028311 a x p ha hx hp
      have hh := congrArg ENNReal.ofReal heq
      rw [ENNReal.ofReal_mul (gammaPDFReal_nonneg ha (by norm_num) p),
        ENNReal.ofReal_mul (by unfold _root_.GD.N0089.d028310; positivity)] at hh
      simpa only [gammaPDF, add_comm x 1] using hh
  · have hm : _root_.GD.N0089.d028371 a x = 0 :=
      paretoPDF_of_lt (by linarith : x + 1 < 1)
    rw [gammaPDF_of_neg (lt_of_not_ge hx), mul_zero, hm, zero_mul]

end
end GD.N0089

#print axioms _root_.GD.N0089.d028374
#print axioms _root_.GD.N0089.d028375
#print axioms _root_.GD.N0089.d028377
