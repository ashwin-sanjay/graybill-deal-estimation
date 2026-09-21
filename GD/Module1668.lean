import GD.Module1667

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0089
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0102.N0422

variable {k : ℕ}

def d028298 (x : Fin k → ℝ) : ℝ := (_root_.GD.N0102.N0422.d028281 x)⁻¹

theorem d028299 (hk : 0 < k) (x : Fin k → ℝ) (hx : ∀ i, 0 < x i) :
    0 < _root_.GD.N0089.d028298 x := inv_pos.mpr (_root_.GD.N0102.N0422.d028283 hk x hx)



theorem d028300 (hk : 0 < k) (x w : Fin k → ℝ)
    (hx : ∀ i, 0 < x i) (hw : ∑ i, w i = 1) :
    _root_.GD.N0089.d028298 x ≤ _root_.GD.N0072.d007621 x w := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := w) (f := fun i => x i * w i ^ 2) (g := fun i => (x i)⁻¹)
    (fun i _ => mul_nonneg (hx i).le (sq_nonneg _))
    (fun i _ => (inv_pos.mpr (hx i)).le)
    (fun i _ => by field_simp [(hx i).ne']; exact le_rfl)
  rw [hw, one_pow] at hc
  apply (inv_le_iff_one_le_mul₀ (_root_.GD.N0102.N0422.d028283 hk x hx)).mpr
  simpa only [_root_.GD.N0072.d007621, _root_.GD.N0102.N0422.d028281, mul_comm] using hc

theorem d028301 (hk : 0 < k) (x : Fin k → ℝ)
    (hx : ∀ i, 0 < x i) : _root_.GD.N0072.d007621 x (_root_.GD.N0021.d023313 x) = _root_.GD.N0089.d028298 x := by
  have hP := _root_.GD.N0102.N0422.d028283 hk x hx
  unfold _root_.GD.N0072.d007621 _root_.GD.N0089.d028298
  simp_rw [_root_.GD.N0102.N0422.d028289 hk x hx]
  calc
    _ = ∑ i, (x i)⁻¹ / _root_.GD.N0102.N0422.d028281 x ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hx i).ne', hP.ne']
    _ = _root_.GD.N0102.N0422.d028281 x / _root_.GD.N0102.N0422.d028281 x ^ 2 := by rw [← Finset.sum_div]; rfl
    _ = _ := by field_simp [hP.ne']

theorem d028302 (hk : 0 < k) (x : Fin k → ℝ) :
    ∑ i, _root_.GD.N0021.d023313 x i ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ i, _root_.GD.N0021.d023313 x i := by
      apply Finset.sum_le_sum
      intro i _
      have h0 := _root_.GD.N0232.N0719.N0900.d009132 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), x)) i
      have h1 := _root_.GD.N0232.N0719.N0900.d009133 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), x)) i
      change _root_.GD.N0021.d023313 x i ≥ 0 at h0
      change _root_.GD.N0021.d023313 x i ≤ 1 at h1
      nlinarith
    _ = 1 := _root_.GD.N0232.N0719.N0900.d009131 hk _

theorem d028303 (hk : 0 < k) (x y : Fin k → ℝ)
    (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i) :
    _root_.GD.N0089.d028298 x ≤ _root_.GD.N0089.d028298 y := by
  have hy : ∀ i, 0 < y i := fun i => (hx i).trans_le (hxy i)
  apply inv_anti₀ (_root_.GD.N0102.N0422.d028283 hk y hy)
  exact Finset.sum_le_sum fun i _ => inv_anti₀ (hx i) (hxy i)




theorem d028304 (hk : 0 < k)
    (x : Fin k → ℝ) (hx : ∀ i, 0 < x i) (b : ℝ) (hb : 0 ≤ b) :
    _root_.GD.N0072.d007621 (fun i => x i + b) (_root_.GD.N0021.d023313 x) ≤
      _root_.GD.N0089.d028298 (fun i => x i + b) + b := by
  have heq : _root_.GD.N0072.d007621 (fun i => x i + b) (_root_.GD.N0021.d023313 x) =
      _root_.GD.N0089.d028298 x + b * ∑ i, _root_.GD.N0021.d023313 x i ^ 2 := by
    rw [← _root_.GD.N0089.d028301 hk x hx]
    unfold _root_.GD.N0072.d007621
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  rw [heq]
  exact add_le_add
    (_root_.GD.N0089.d028303 hk x _ hx (fun _ => le_add_of_nonneg_right hb))
    (mul_le_of_le_one_right hb (_root_.GD.N0089.d028302 hk x))

theorem d028305 (hk : 0 < k)
    (x w : Fin k → ℝ) (hx : ∀ i, 0 < x i) (hw : ∑ i, w i = 1)
    (b : ℝ) (hb : 0 ≤ b) :
    _root_.GD.N0072.d007621 (fun i => x i + b) (_root_.GD.N0021.d023313 x) ≤ _root_.GD.N0072.d007621 (fun i => x i + b) w + b :=
  (_root_.GD.N0089.d028304 hk x hx b hb).trans
    (add_le_add (_root_.GD.N0089.d028300 hk _ w
      (fun i => (hx i).trans_le (le_add_of_nonneg_right hb)) hw) le_rfl)

end
end GD.N0089

#print axioms _root_.GD.N0089.d028300
#print axioms _root_.GD.N0089.d028304
#print axioms _root_.GD.N0089.d028305
