import GD.Module1707





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0417
noncomputable section

open _root_.GD.N0213.N0509
open _root_.GD.N0213.N0508
open _root_.GD.N0213.N0522
open _root_.GD.N0101.N0397
open _root_.GD.N0217
open _root_.GD.N0220

def d028646 : Measure (ℝ × ℝ) :=
  _root_.GD.N0217.d008090.withDensity (fun z =>
    ENNReal.ofReal (_root_.GD.N0219.d008142 z.1))

def d028647 (z : ℝ × ℝ) : ℝ :=
  _root_.GD.N0213.N0509.d023108 _root_.GD.N0220.d028624 (_root_.GD.N0101.N0397.d028118.symm z) ^ 2

@[fun_prop] theorem d028648 : Measurable _root_.GD.N0101.N0417.d028647 :=
  ((_root_.GD.N0213.N0509.d023110 _root_.GD.N0220.d028624).comp _root_.GD.N0101.N0397.d028118.symm.measurable).pow_const 2

@[fun_prop] theorem d028649 :
    Measurable _root_.GD.N0219.d008142 := by
  unfold _root_.GD.N0219.d008142
  exact measurable_const.mul (continuous_sigmoid.measurable.pow_const 2)



theorem d028650 :
    (_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624).map _root_.GD.N0101.N0397.d028118 =
      _root_.GD.N0217.d008089.withDensity (fun z => ENNReal.ofReal (_root_.GD.N0101.N0417.d028647 z)) := by
  rw [_root_.GD.N0213.N0508.d028429, _root_.GD.N0213.N0522.d008018, _root_.GD.N0220.d028632]
  rfl

theorem d028651 (z : ℝ × ℝ) :
    (2 * Real.exp (2 * z.1)) * _root_.GD.N0101.N0417.d028647 (_root_.GD.N0217.d008091 z) =
      _root_.GD.N0219.d008142 z.1 := by
  change (2 * Real.exp (2 * z.1)) *
    _root_.GD.N0213.N0509.d023108 _root_.GD.N0220.d028624 (_root_.GD.N0220.d028625 z) ^ 2 = _
  rw [_root_.GD.N0220.d028630, _root_.GD.N0219.d008143]
  simp only [inv_pow, div_eq_mul_inv]

theorem d028652 :
    _root_.GD.N0101.N0417.d028646.map _root_.GD.N0217.d008091 = (_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624).map _root_.GD.N0101.N0397.d028118 := by
  rw [_root_.GD.N0101.N0417.d028650]
  have h := _root_.GD.N0217.d008099 _root_.GD.N0101.N0417.d028647 _root_.GD.N0101.N0417.d028648
  simp_rw [_root_.GD.N0101.N0417.d028651] at h
  exact h


theorem d028653 :
    _root_.GD.N0101.N0417.d028646.map _root_.GD.N0220.d028625 = _root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624 := by
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => _root_.MeasureTheory.Measure.map _root_.GD.N0101.N0397.d028118.symm μ)
    _root_.GD.N0101.N0417.d028652
  rw [Measure.map_map _root_.GD.N0101.N0397.d028118.symm.measurable _root_.GD.N0217.d008092,
    Measure.map_map _root_.GD.N0101.N0397.d028118.symm.measurable _root_.GD.N0101.N0397.d028118.measurable] at h
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply] at h
  change _root_.GD.N0101.N0417.d028646.map _root_.GD.N0220.d028625 = (_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624).map id at h
  rwa [Measure.map_id] at h



theorem d028654 (g : (Fin 2 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ β, g β ∂_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624) =
      ∫⁻ z, g (_root_.GD.N0220.d028625 z) ∂_root_.GD.N0101.N0417.d028646 := by
  rw [← _root_.GD.N0101.N0417.d028653]
  exact lintegral_map hg _root_.GD.N0220.d028626

theorem d028655
    (g : (Fin 2 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ β, g β ∂_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624) =
      ∫⁻ z, ENNReal.ofReal (_root_.GD.N0219.d008142 z.1) *
        g (_root_.GD.N0220.d028625 z) ∂_root_.GD.N0217.d008090 := by
  rw [_root_.GD.N0101.N0417.d028654 g hg, _root_.GD.N0101.N0417.d028646,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

theorem d028656
    (g : (Fin 2 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ β, g β ∂_root_.GD.N0213.N0508.d028429 _root_.GD.N0220.d028624) =
      ∫⁻ s : ℝ, ∫⁻ v : ℝ,
        ENNReal.ofReal (_root_.GD.N0219.d008142 s) *
          g (_root_.GD.N0220.d028625 (s, v)) := by
  rw [_root_.GD.N0101.N0417.d028655 g hg]
  exact lintegral_prod _ (by fun_prop)

end
end GD.N0101.N0417

#print axioms _root_.GD.N0101.N0417.d028650
#print axioms _root_.GD.N0101.N0417.d028651
#print axioms _root_.GD.N0101.N0417.d028652
#print axioms _root_.GD.N0101.N0417.d028653
#print axioms _root_.GD.N0101.N0417.d028654
#print axioms _root_.GD.N0101.N0417.d028655
#print axioms _root_.GD.N0101.N0417.d028656
