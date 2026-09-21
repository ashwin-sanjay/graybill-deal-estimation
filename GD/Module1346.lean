import GD.Module1345





set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GD.N0106.N0428.N0762
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0880 _root_.GD.N0232.N0719.N0885
open _root_.GD.N0106.N0428.N0770.N1748

theorem d021784 {k : ℕ} (v : Fin k → ℝ≥0) (t : Fin k → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0880.d020684 v t := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (v i).property)

theorem d021785 {k : ℕ} (hk : 0 < k)
    (v : Fin k → ℝ≥0) (t : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0880.d020684 v t ≤ ∑ i, (v i : ℝ) := by
  unfold _root_.GD.N0232.N0719.N0880.d020684
  apply Finset.sum_le_sum
  intro i _
  have hw : _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i ^ 2 ≤ 1 :=
    pow_le_one₀ (_root_.GD.N0232.N0719.N0900.d009132 hk _ i)
      (_root_.GD.N0232.N0719.N0900.d009133 hk _ i)
  change _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i ^ 2 *
    (v i : ℝ) ≤ (v i : ℝ)
  calc
    _ ≤ 1 * (v i : ℝ) := mul_le_mul_of_nonneg_right hw (v i).property
    _ = _ := one_mul _

theorem d021786 {k : ℕ} (hk : 0 < k)
    (v : Fin k → ℝ≥0) (hv : ∀ i, 0 < v i) (t : Fin k → ℝ) :
    0 < _root_.GD.N0232.N0719.N0880.d020684 v t := by
  let s := _root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)
  have hex : ∃ i, _root_.GD.N0232.N0719.N0900.d009108 s i ≠ 0 := by
    by_contra! hzero
    have hs := _root_.GD.N0232.N0719.N0900.d009131 hk s
    simp only [hzero, Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨i, hi⟩ := hex
  have hterm : 0 < _root_.GD.N0232.N0719.N0900.d009108 s i ^ 2 * (v i : ℝ) :=
    mul_pos (sq_pos_of_ne_zero hi) (hv i)
  exact hterm.trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (sq_nonneg _) (v j).property) (Finset.mem_univ i))

theorem d021787 {k : ℕ} (hk : 0 < k)
    (v : Fin k → ℝ≥0) (μ : Measure (Fin k → ℝ)) [IsFiniteMeasure μ] :
    Integrable (_root_.GD.N0232.N0719.N0880.d020684 v) μ := by
  apply (integrable_const (∑ i, (v i : ℝ))).mono'
    (_root_.GD.N0106.N0428.N0770.N1748.d021779 v).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0762.d021784 v t)]
  exact _root_.GD.N0106.N0428.N0762.d021785 hk v t



theorem d021788 {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0972.d012340 k sizes theta := by
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021780 hk sizes hn theta]
  rw [_root_.GD.N0232.N0719.N0880.d020686 sizes hk hn
    ⟨0, theta.scale, theta.scale_pos⟩ rfl]
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes theta.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn theta.scale
  let v := _root_.GD.N0232.N0719.N0885.d009329 sizes theta.scale
  have hv : ∀ i, 0 < v i := _root_.GD.N0232.N0719.N0885.d009330 sizes hn theta.scale theta.scale_pos
  rw [integral_pos_iff_support_of_nonneg (_root_.GD.N0106.N0428.N0762.d021784 v)
    (_root_.GD.N0106.N0428.N0762.d021787 hk v _)]
  have hs : Function.support (_root_.GD.N0232.N0719.N0880.d020684 v) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact (_root_.GD.N0106.N0428.N0762.d021786 hk v hv t).ne'
  rw [hs]
  simp

end
end GD.N0106.N0428.N0762

#print axioms _root_.GD.N0106.N0428.N0762.d021784
#print axioms _root_.GD.N0106.N0428.N0762.d021785
#print axioms _root_.GD.N0106.N0428.N0762.d021786
#print axioms _root_.GD.N0106.N0428.N0762.d021787
#print axioms _root_.GD.N0106.N0428.N0762.d021788
