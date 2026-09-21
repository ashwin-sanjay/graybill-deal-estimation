import GD.Module1484
import GD.Module1324
import GD.Module1325
import GD.Module0802

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0021
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0072
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962

variable {k : ℕ}

def d023313 (t : Fin k → ℝ) : Fin k → ℝ :=
  fun i => _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i

theorem d023314 : Measurable (_root_.GD.N0021.d023313 (k := k)) := by
  apply measurable_pi_lambda
  intro i
  exact (_root_.GD.N0232.N0719.N0900.d009119 i).comp ((_root_.GD.N0232.N0719.N0933.d009306 k).comp
    (measurable_const.prodMk measurable_id))

theorem d023315 (sizes : Fin k → ℕ) :
    _root_.GD.N0232.N0719.N0900.d009111 k sizes = _root_.GD.N0072.d023291 sizes _root_.GD.N0021.d023313 := by
  rfl

def d023316 (q : Fin k → ℝ) : ℝ := ∑ i, ∑ j, q i / q j

theorem d023317 (hk : 0 < k) (t q : Fin k → ℝ)
    (hq : ∀ i, 0 < q i) :
    (∑ i, _root_.GD.N0021.d023313 t i * q i) * (∑ j, _root_.GD.N0021.d023313 t j / q j) ≤
      _root_.GD.N0021.d023316 q := by
  rw [Finset.sum_mul]
  unfold _root_.GD.N0021.d023316
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hi0 := _root_.GD.N0232.N0719.N0900.d009132 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i
  have hj0 := _root_.GD.N0232.N0719.N0900.d009132 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) j
  have hi1 := _root_.GD.N0232.N0719.N0900.d009133 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) i
  have hj1 := _root_.GD.N0232.N0719.N0900.d009133 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) j
  have hprod : _root_.GD.N0021.d023313 t i * _root_.GD.N0021.d023313 t j ≤ 1 := by
    exact (mul_le_mul hi1 hj1 hj0 (by norm_num)).trans_eq (by norm_num)
  calc
    _root_.GD.N0021.d023313 t i * q i * (_root_.GD.N0021.d023313 t j / q j) =
      (_root_.GD.N0021.d023313 t i * _root_.GD.N0021.d023313 t j) * (q i / q j) := by ring
    _ ≤ 1 * (q i / q j) := mul_le_mul_of_nonneg_right hprod (div_pos (hq i) (hq j)).le
    _ = q i / q j := one_mul _

theorem d023318 (hk : 0 < k) (v q : Fin k → ℝ)
    (hv : ∀ i, 0 < v i) (hq : ∀ i, 0 < q i) :
    _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)) * (∑ i, (v i)⁻¹) =
      (∑ i, _root_.GD.N0021.d023313 (fun i => v i * q i) i * q i) *
        (∑ i, _root_.GD.N0021.d023313 (fun i => v i * q i) i / q i) := by
  let t := fun i => v i * q i
  let S : ℝ := ∑ i, (t i)⁻¹
  have ht (i : Fin k) : 0 < t i := mul_pos (hv i) (hq i)
  have hS : 0 < S := Finset.sum_pos (fun i _ => inv_pos.mpr (ht i))
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk))
  have hw (i : Fin k) : _root_.GD.N0021.d023313 t i = (t i)⁻¹ / S := by
    unfold _root_.GD.N0021.d023313 _root_.GD.N0232.N0719.N0900.d009108
    have htotal : _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) = S := by
      unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0232.N0719.N0900.d009106
      apply Finset.sum_congr rfl
      intro j _
      exact _root_.GD.N0232.N0719.N0900.d009127 (ht j)
    rw [htotal, if_neg hS.ne']
    congr 1
    exact _root_.GD.N0232.N0719.N0900.d009127 (ht i)
  have hfirst : (∑ i, _root_.GD.N0021.d023313 t i * q i) * S = ∑ i, (v i)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hw]
    dsimp [t]
    field_simp [(hv i).ne', (hq i).ne', hS.ne']
  have hsecond : _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 t) * S = ∑ i, _root_.GD.N0021.d023313 t i / q i := by
    unfold _root_.GD.N0072.d007621
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hw]
    dsimp [t]
    field_simp [(hv i).ne', (hq i).ne', hS.ne']
  change _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 t) * _ = _
  rw [← hfirst, ← hsecond]
  ring

theorem d023319 (hk : 0 < k) (v q : Fin k → ℝ)
    (hv : ∀ i, 0 < v i) (hq : ∀ i, 0 < q i) :
    _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)) ≤
      _root_.GD.N0021.d023316 q * (∑ i, (v i)⁻¹)⁻¹ := by
  have hP : 0 < ∑ i, (v i)⁻¹ := Finset.sum_pos (fun i _ => inv_pos.mpr (hv i))
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk))
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hP).mpr
  change _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)) * (∑ i, (v i)⁻¹) ≤ _root_.GD.N0021.d023316 q
  rw [_root_.GD.N0021.d023318 hk v q hv hq]
  exact _root_.GD.N0021.d023317 hk _ q hq

end
end GD.N0021

#print axioms _root_.GD.N0021.d023318
#print axioms _root_.GD.N0021.d023319
