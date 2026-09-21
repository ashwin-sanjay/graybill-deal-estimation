import GD.Module0539

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0225.N0542

noncomputable section

open _root_.GD.N0225.N0539
open _root_.GD.N0213.N0495

variable {k : ℕ}

theorem d008165 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => (∑ i, β i) * _root_.GD.N0213.N0495.d007175 L (∑ i, β i) ^ 2) (_root_.GD.N0225.N0539.d008044 α) := by
  have hm : Measurable (fun β : Fin k → ℝ => ∑ i, β i) := by fun_prop
  have hf : Measurable (fun r => r * _root_.GD.N0213.N0495.d007175 L r ^ 2) := by
    dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]
    fun_prop
  apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp
  rw [_root_.GD.N0225.N0539.d008056 α hα hsum]
  exact (_root_.GD.N0213.N0495.d007189 hL).smul_measure (_root_.GD.N0225.N0539.d008055 α hα)

theorem d008166 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L)
    (i : Fin k) :
    Integrable (fun β => β i * _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2) (_root_.GD.N0225.N0539.d008044 α) := by
  apply (_root_.GD.N0225.N0542.d008165 α hα hsum hL).mono'
    (by dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]; fun_prop)
  filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hβ i).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Finset.single_le_sum (fun j _ => (hβ j).le) (Finset.mem_univ i)

theorem d008167 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L)
    (i : Fin k) :
    0 ≤ (∫ β, β i * _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) ∧
      (∫ β, β i * _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) ≤
        (∫ β, (∑ j, β j) * _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
    exact mul_nonneg (hβ i).le (sq_nonneg _)
  · apply integral_mono_ae (_root_.GD.N0225.N0542.d008166 α hα hsum hL i)
      (_root_.GD.N0225.N0542.d008165 α hα hsum hL)
    filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => (hβ j).le) (Finset.mem_univ i)) (sq_nonneg _)

theorem d008168 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) (i : Fin k) :
    Tendsto (fun n : ℕ => ∫ β, β i *
      _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ j, β j) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n : ℕ =>
    (_root_.GD.N0225.N0542.d008167 α hα hsum (L := (n : ℝ) + 1) (by positivity) i).1)
    (Eventually.of_forall fun n : ℕ =>
    (_root_.GD.N0225.N0542.d008167 α hα hsum (L := (n : ℝ) + 1) (by positivity) i).2)
  exact _root_.GD.N0225.N0539.d008061 α hα hsum

theorem d008169 (α c : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    Tendsto (fun n : ℕ => ∫ β, ∑ i,
      c i * (β i * _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ j, β j) ^ 2) ∂_root_.GD.N0225.N0539.d008044 α)
      atTop (𝓝 0) := by
  have heq (n : ℕ) :
      (∫ β, ∑ i, c i * (β i * _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ j, β j) ^ 2) ∂_root_.GD.N0225.N0539.d008044 α) =
        ∑ i, c i * (∫ β, β i * _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ j, β j) ^ 2 ∂_root_.GD.N0225.N0539.d008044 α) := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (_root_.GD.N0225.N0542.d008166 α hα hsum (by positivity) i).const_mul (c i))]
    simp only [integral_const_mul]
  simp_rw [heq]
  simpa only [mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ =>
      (_root_.GD.N0225.N0542.d008168 α hα hsum i).const_mul (c i))

end
end GD.N0225.N0542

#print axioms _root_.GD.N0225.N0542.d008165
#print axioms _root_.GD.N0225.N0542.d008166
#print axioms _root_.GD.N0225.N0542.d008167
#print axioms _root_.GD.N0225.N0542.d008168
#print axioms _root_.GD.N0225.N0542.d008169
