import GD.Module0463
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter
open scoped ENNReal

namespace GD.N0101.N0407

noncomputable section

open _root_.GD.N0213.N0495


def d007197 (L : ℝ) : ℝ := (2 / L) * Real.exp ((L + 1) ^ 2 / 4)

theorem d007198 {L : ℝ} (hL : 0 < L) : 0 < _root_.GD.N0101.N0407.d007197 L := by
  unfold _root_.GD.N0101.N0407.d007197
  positivity

theorem d007199 {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    |x| * Real.exp (-x ^ 2 - L * x) ≤ Real.exp ((L + 1) ^ 2 / 4) := by
  have habs : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  calc
    _ ≤ Real.exp |x| * Real.exp (-x ^ 2 - L * x) :=
      mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ = Real.exp (|x| - x ^ 2 - L * x) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hlin := mul_le_mul_of_nonneg_left (neg_le_abs x) hL
      nlinarith [sq_nonneg (|x| - (L + 1) / 2), sq_abs x]

theorem d007200 {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ‖_root_.GD.N0213.N0495.d007175 L r‖ ≤ _root_.GD.N0101.N0407.d007197 L := by
  by_cases hr : r = 0
  · subst r
    simpa [_root_.GD.N0213.N0495.d007175] using (_root_.GD.N0101.N0407.d007198 hL).le
  have heq : ‖_root_.GD.N0213.N0495.d007175 L r‖ =
      (2 / L) * (|Real.log r / L| *
        Real.exp (-(Real.log r / L) ^ 2 - L * (Real.log r / L))) := by
    rw [show L * (Real.log r / L) = Real.log r by field_simp]
    rw [Real.exp_sub, Real.exp_log_eq_abs hr]
    unfold _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174
    simp only [norm_mul, norm_div, norm_pow, Real.norm_eq_abs,
      abs_of_pos hL, abs_of_pos (Real.exp_pos _), abs_div]
    norm_num
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0101.N0407.d007199 hL.le _)
    (by positivity)

theorem d007201 {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ‖_root_.GD.N0213.N0495.d007175 L r ^ 2‖ ≤ _root_.GD.N0101.N0407.d007197 L ^ 2 := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (_root_.GD.N0101.N0407.d007200 hL r) 2

theorem d007202 {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ‖_root_.GD.N0213.N0495.d007174 L r * _root_.GD.N0213.N0495.d007175 L r‖ ≤ _root_.GD.N0101.N0407.d007197 L := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (_root_.GD.N0213.N0495.d007176 L r)]
  calc
    _root_.GD.N0213.N0495.d007174 L r * ‖_root_.GD.N0213.N0495.d007175 L r‖ ≤ 1 * _root_.GD.N0101.N0407.d007197 L :=
      mul_le_mul (_root_.GD.N0213.N0495.d007177 L r) (_root_.GD.N0101.N0407.d007200 hL r)
        (norm_nonneg _) zero_le_one
    _ = _root_.GD.N0101.N0407.d007197 L := one_mul _

theorem d007203 (L : ℝ) : Measurable (_root_.GD.N0213.N0495.d007174 L) := by
  unfold _root_.GD.N0213.N0495.d007174
  fun_prop

theorem d007204 (L : ℝ) : Measurable (_root_.GD.N0213.N0495.d007175 L) := by
  unfold _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174
  fun_prop

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {L : ℝ} {R : α → ℝ}


theorem d007205 (hL : 0 < L) (hR : Measurable R) (p : ℝ≥0∞) :
    MemLp (fun x => _root_.GD.N0213.N0495.d007175 L (R x)) p μ := by
  exact MemLp.of_bound ((_root_.GD.N0101.N0407.d007204 L).comp hR).aestronglyMeasurable
    (_root_.GD.N0101.N0407.d007197 L) (Filter.Eventually.of_forall fun x => _root_.GD.N0101.N0407.d007200 hL (R x))

theorem d007206 (hL : 0 < L) (hR : Measurable R) :
    Integrable (fun x => _root_.GD.N0213.N0495.d007175 L (R x)) μ :=
  memLp_one_iff_integrable.mp (_root_.GD.N0101.N0407.d007205 hL hR 1)

theorem d007207 (hL : 0 < L) (hR : Measurable R) (p : ℝ≥0∞) :
    MemLp (fun x => _root_.GD.N0213.N0495.d007175 L (R x) ^ 2) p μ := by
  exact MemLp.of_bound (((_root_.GD.N0101.N0407.d007204 L).comp hR).pow_const 2).aestronglyMeasurable
    (_root_.GD.N0101.N0407.d007197 L ^ 2)
    (Filter.Eventually.of_forall fun x => _root_.GD.N0101.N0407.d007201 hL (R x))

theorem d007208 (hL : 0 < L) (hR : Measurable R) :
    Integrable (fun x => _root_.GD.N0213.N0495.d007175 L (R x) ^ 2) μ :=
  memLp_one_iff_integrable.mp (_root_.GD.N0101.N0407.d007207 hL hR 1)

theorem d007209 (hL : 0 < L) (hR : Measurable R)
    (p : ℝ≥0∞) : MemLp (fun x => _root_.GD.N0213.N0495.d007174 L (R x) * _root_.GD.N0213.N0495.d007175 L (R x)) p μ := by
  exact MemLp.of_bound (((_root_.GD.N0101.N0407.d007203 L).comp hR).mul
    ((_root_.GD.N0101.N0407.d007204 L).comp hR)).aestronglyMeasurable (_root_.GD.N0101.N0407.d007197 L)
    (Filter.Eventually.of_forall fun x => _root_.GD.N0101.N0407.d007202 hL (R x))

theorem d007210 (hL : 0 < L) (hR : Measurable R) :
    Integrable (fun x => _root_.GD.N0213.N0495.d007174 L (R x) * _root_.GD.N0213.N0495.d007175 L (R x)) μ :=
  memLp_one_iff_integrable.mp (_root_.GD.N0101.N0407.d007209 hL hR 1)

end
end GD.N0101.N0407

#print axioms _root_.GD.N0101.N0407.d007200
#print axioms _root_.GD.N0101.N0407.d007201
#print axioms _root_.GD.N0101.N0407.d007202
#print axioms _root_.GD.N0101.N0407.d007205
#print axioms _root_.GD.N0101.N0407.d007206
#print axioms _root_.GD.N0101.N0407.d007207
#print axioms _root_.GD.N0101.N0407.d007208
#print axioms _root_.GD.N0101.N0407.d007209
#print axioms _root_.GD.N0101.N0407.d007210
