import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Pi






set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GD.N0106.N0428.N0770.N1700
noncomputable section

variable {ι : Type*} [Fintype ι]



theorem d006089 (m w : ι → ℝ) (v : ι → ℝ≥0) :
    MemLp (fun y : ι → ℝ => ∑ i, w i * y i) 2
      (Measure.pi (fun i => gaussianReal (m i) (v i))) := by
  apply memLp_finsetSum
  intro i _
  have hi := (memLp_id_gaussianReal (μ := m i) (v := v i) 2).const_mul (w i)
  exact hi.comp_measurePreserving (measurePreserving_eval _ i)


theorem d006090 (m w : ι → ℝ) (v : ι → ℝ≥0) :
    (∫ y : ι → ℝ, (∑ i, w i * y i)
      ∂Measure.pi (fun i => gaussianReal (m i) (v i))) = ∑ i, w i * m i := by
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_eval, integral_id_gaussianReal]
  · intro i _
    have hi := (memLp_id_gaussianReal (μ := m i) (v := v i) 2).const_mul (w i)
    exact (hi.comp_measurePreserving (measurePreserving_eval _ i)).integrable (by norm_num)


theorem d006091 (m w : ι → ℝ) (v : ι → ℝ≥0) :
    Var[fun y : ι → ℝ => ∑ i, w i * y i;
      Measure.pi (fun i => gaussianReal (m i) (v i))] =
        ∑ i, (w i) ^ 2 * (v i : ℝ) := by
  calc
    _ = Var[∑ i, (fun y : ι → ℝ => w i * id (y i));
      Measure.pi (fun i => gaussianReal (m i) (v i))] := by
        congr 1
        ext y
        simp
    _ = ∑ i, Var[fun x : ℝ => w i * id x; gaussianReal (m i) (v i)] :=
      variance_sum_pi
        (fun i => (memLp_id_gaussianReal (μ := m i) (v := v i) 2).const_mul (w i))
    _ = _ := by simp only [variance_const_mul, variance_id_gaussianReal]


theorem d006092 (m w : ι → ℝ) (v : ι → ℝ≥0) :
    Integrable (fun y : ι → ℝ => ((∑ i, w i * y i) - ∑ i, w i * m i) ^ 2)
      (Measure.pi (fun i => gaussianReal (m i) (v i))) := by
  exact ((_root_.GD.N0106.N0428.N0770.N1700.d006089 m w v).sub (memLp_const _)).integrable_sq



theorem d006093 (m w : ι → ℝ) (v : ι → ℝ≥0) :
    (∫ y : ι → ℝ, ((∑ i, w i * y i) - ∑ i, w i * m i) ^ 2
      ∂Measure.pi (fun i => gaussianReal (m i) (v i))) =
        ∑ i, (w i) ^ 2 * (v i : ℝ) := by
  have h := variance_eq_integral (_root_.GD.N0106.N0428.N0770.N1700.d006089 m w v).aemeasurable
  rw [_root_.GD.N0106.N0428.N0770.N1700.d006090] at h
  exact h.symm.trans (_root_.GD.N0106.N0428.N0770.N1700.d006091 m w v)


theorem d006094 (m w : ι → ℝ) (v : ι → ℝ≥0) :
    (∫ y : ι → ℝ, (∑ i, w i * (y i - m i)) ^ 2
      ∂Measure.pi (fun i => gaussianReal (m i) (v i))) =
        ∑ i, (w i) ^ 2 * (v i : ℝ) := by
  simpa only [mul_sub, Finset.sum_sub_distrib] using
    _root_.GD.N0106.N0428.N0770.N1700.d006093 m w v



theorem d006095 (μ : ℝ) (w : ι → ℝ) (v : ι → ℝ≥0)
    (hw : ∑ i, w i = 1) :
    Integrable (fun y : ι → ℝ => ((∑ i, w i * y i) - μ) ^ 2)
      (Measure.pi (fun i => gaussianReal μ (v i))) := by
  simpa only [← Finset.sum_mul, hw, one_mul] using
    _root_.GD.N0106.N0428.N0770.N1700.d006092 (fun _ => μ) w v



theorem d006096 (μ : ℝ) (w : ι → ℝ) (v : ι → ℝ≥0)
    (hw : ∑ i, w i = 1) :
    (∫ y : ι → ℝ, ((∑ i, w i * y i) - μ) ^ 2
      ∂Measure.pi (fun i => gaussianReal μ (v i))) =
        ∑ i, (w i) ^ 2 * (v i : ℝ) := by
  simpa only [← Finset.sum_mul, hw, one_mul] using
    _root_.GD.N0106.N0428.N0770.N1700.d006093 (fun _ => μ) w v

end
end GD.N0106.N0428.N0770.N1700

#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006089
#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006090
#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006091
#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006092
#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006093
#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006094
#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006095
#print axioms _root_.GD.N0106.N0428.N0770.N1700.d006096
