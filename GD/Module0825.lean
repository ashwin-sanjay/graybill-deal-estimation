import GD.Module0664

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0463

open _root_.GD.N0232.N0719.N0983

noncomputable section
variable {k : ℕ}

theorem d012583 (y : Fin k → ℝ) (a b : ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009713 (fun i => b + a * y i) p = b + a * _root_.GD.N0232.N0719.N0983.d009713 y p := by
  unfold _root_.GD.N0232.N0719.N0983.d009713
  calc
    _ = (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * b) +
        a * (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.sum_mul, _root_.GD.N0232.N0719.N0983.d009712, one_mul]

theorem d012584 (y r : Fin k → ℝ) (a b : ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009714 (fun i => b + a * y i) (fun i => a ^ 2 * r i) p =
      a ^ 2 * _root_.GD.N0232.N0719.N0983.d009714 y r p := by
  unfold _root_.GD.N0232.N0719.N0983.d009714
  rw [_root_.GD.N0212.N0463.d012583]
  have hfirst : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (a ^ 2 * r i)) =
      a ^ 2 * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * r i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) *
      (b + a * y i - (b + a * _root_.GD.N0232.N0719.N0983.d009713 y p)) ^ 2) =
      a ^ 2 * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (y i - _root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst, hsecond]
  ring

theorem d012585 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (a b : ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009720 q (fun i => b + a * y i) (fun i => a ^ 2 * r i) p =
      (a ^ 2) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009720 q y r p := by
  unfold _root_.GD.N0232.N0719.N0983.d009720
  rw [_root_.GD.N0212.N0463.d012584, Real.mul_rpow (sq_nonneg a)
    (_root_.GD.N0232.N0719.N0983.d009717 y r (fun i => (hr i).le) p)]

theorem d012586 (q : ℝ) (y r : Fin k → ℝ)
    (hr : ∀ i, 0 < r i) (a b : ℝ) (ha : 0 < a) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0983.d009725 q (fun i => b + a * y i) (fun i => a ^ 2 * r i) μ i =
      _root_.GD.N0232.N0719.N0983.d009725 q y r μ i := by
  let C : ℝ := (a ^ 2) ^ (-q)
  have hC : C ≠ 0 := (Real.rpow_pos_of_pos (sq_pos_of_pos ha) _).ne'
  have hnum : (fun p : _root_.GD.N0232.N0719.N0983.d009709 k => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) *
      _root_.GD.N0232.N0719.N0983.d009720 q (fun i => b + a * y i) (fun i => a ^ 2 * r i) p) =
      (fun p => C * ((_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * _root_.GD.N0232.N0719.N0983.d009720 q y r p)) := by
    funext p
    rw [_root_.GD.N0212.N0463.d012585 q y r hr a b p]
    dsimp [C]
    ring
  have hden : (fun p : _root_.GD.N0232.N0719.N0983.d009709 k =>
      _root_.GD.N0232.N0719.N0983.d009720 q (fun i => b + a * y i) (fun i => a ^ 2 * r i) p) =
      (fun p => C * _root_.GD.N0232.N0719.N0983.d009720 q y r p) := by
    funext p
    exact _root_.GD.N0212.N0463.d012585 q y r hr a b p
  simp only [_root_.GD.N0232.N0719.N0983.d009725, _root_.GD.N0232.N0719.N0983.d009723]
  rw [hnum, hden, integral_const_mul, integral_const_mul]
  exact mul_div_mul_left _ _ hC



theorem d012587 (q : ℝ) (y r : Fin k → ℝ)
    (hr : ∀ i, 0 < r i) (a b : ℝ) (ha : 0 < a)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ] :
    _root_.GD.N0232.N0719.N0983.d009724 q (fun i => b + a * y i) (fun i => a ^ 2 * r i) μ =
      b + a * _root_.GD.N0232.N0719.N0983.d009724 q y r μ := by
  have hr' : ∀ i, 0 < a ^ 2 * r i := fun i => mul_pos (sq_pos_of_pos ha) (hr i)
  rw [_root_.GD.N0232.N0719.N0983.d009730 q _ _ hr' μ, _root_.GD.N0232.N0719.N0983.d009730 q y r hr μ]
  simp_rw [_root_.GD.N0212.N0463.d012586 q y r hr a b ha μ]
  calc
    _ = b * (∑ i, _root_.GD.N0232.N0719.N0983.d009725 q y r μ i) +
        a * (∑ i, _root_.GD.N0232.N0719.N0983.d009725 q y r μ i * y i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [_root_.GD.N0232.N0719.N0983.d009729 q y r hr μ, mul_one]

end
end GD.N0212.N0463

#print axioms _root_.GD.N0212.N0463.d012586
#print axioms _root_.GD.N0212.N0463.d012587
