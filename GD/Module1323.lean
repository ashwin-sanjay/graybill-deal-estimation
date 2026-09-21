import GD.Module0659
import Mathlib.MeasureTheory.Integral.Prod





set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GD.N0232.N0719.N0876
noncomputable section
theorem d020682
    {a r : ℝ} (ha : 1 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x⁻¹) (gammaMeasure a r) := by
  have ha0 : 0 < a := by linarith
  rw [gammaMeasure]
  change Integrable (fun x : ℝ ↦ x⁻¹)
    (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have hkernel :
      IntegrableOn
        (fun x : ℝ ↦
          (r ^ a / Real.Gamma a) *
            (x ^ (a - 2) * Real.exp (-(r * x))))
        (Set.Ioi 0) := by
    have hbase :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := a - 2) (b := r)
        (by linarith) (by norm_num) hr
    have hbase' :
        IntegrableOn
          (fun x : ℝ ↦ x ^ (a - 2) * Real.exp (-(r * x)))
          (Set.Ioi 0) := by
      simpa only [Real.rpow_one, neg_mul] using hbase
    exact hbase'.const_mul _
  have hkernelActual :
      IntegrableOn
        (fun x : ℝ ↦ gammaPDFReal a r x * x⁻¹)
        (Set.Ioi 0) := by
    apply hkernel.congr_fun
    · intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x⁻¹ = x ^ (a - 2) := by
        rw [← Real.rpow_neg_one x]
        calc
          x ^ (a - 1) * x ^ (-1 : ℝ) =
              x ^ ((a - 1) + (-1 : ℝ)) :=
                (Real.rpow_add hxpos (a - 1) (-1 : ℝ)).symm
          _ = x ^ (a - 2) := by ring_nf
      symm
      calc
        gammaPDFReal a r x * x⁻¹ =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x⁻¹) * Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ (a - 2) * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    · exact measurableSet_Ioi
  have hdensity :
      Integrable (fun x : ℝ ↦ gammaPDFReal a r x * x⁻¹) := by
    apply hkernelActual.integrable_of_forall_notMem_eq_zero
    intro x hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]
  apply hdensity.congr'
  · fun_prop
  filter_upwards with x
  have hpdf : 0 ≤ gammaPDFReal a r x :=
    gammaPDFReal_nonneg ha0 hr x
  simp only [smul_eq_mul,
    ENNReal.toReal_ofReal hpdf]


end
end GD.N0232.N0719.N0876

#print axioms _root_.GD.N0232.N0719.N0876.d020682
