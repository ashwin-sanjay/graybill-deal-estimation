import GD.Module1340
import GD.Module1343
import GD.Module0569






set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GD.N0106.N0428.N0770.N1748
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0972
open _root_.GD.N0232.N0719.N0880 _root_.GD.N0232.N0719.N0885
open _root_.GD.N0232.N0719.N0933 _root_.GD.N0106.N0428.N0770.N1753 _root_.GD.N0106.N0428.N0770.N1750
open _root_.GD.N0232.N0719.N1023

theorem d021779 {k : ℕ} (v : Fin k → ℝ≥0) :
    Measurable (_root_.GD.N0232.N0719.N0880.d020684 v) := by
  unfold _root_.GD.N0232.N0719.N0880.d020684
  exact Finset.measurable_sum _ (fun i _ =>
    (((_root_.GD.N0232.N0719.N0900.d009119 i).comp
      ((_root_.GD.N0232.N0719.N0933.d009306 k).comp
        (measurable_const.prodMk measurable_id))).pow_const 2).mul_const (v i : ℝ))



theorem d021780 {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0972.d012340 k sizes theta =
      _root_.GD.N0232.N0719.N0972.d012340 k sizes ⟨0, theta.scale, theta.scale_pos⟩ := by
  have h := _root_.GD.N0232.N0719.N0804.d009189 k sizes hk
    (fun i => lt_of_lt_of_le (by norm_num : 0 < 2) (hn i))
    theta.location 0 1 (by norm_num) theta.scale
  simpa only [_root_.GD.N0232.N0719.N0972.d012340, _root_.GD.N0232.N0719.N0859.d010812,
    _root_.GD.N0232.N0719.N0859.d010815, one_mul,
    mul_zero, add_zero, one_pow] using h



theorem d021781 {k : ℕ} (hk : 0 < k)
    (sigma : Fin k → ℝ) (hsigma : ∀ i, 0 < sigma i) :
    (∫ t, _root_.GD.N0232.N0719.N0880.d020684 (_root_.GD.N0232.N0719.N0885.d009329 (fun _ => 2) sigma) t
      ∂_root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma) = _root_.GD.N0232.N0719.N1023.d001844 sigma := by
  rw [← _root_.GD.N0106.N0428.N0770.N1753.d021762 sigma]
  rw [integral_map_of_stronglyMeasurable (_root_.GD.N0106.N0428.N0770.N1753.d021760 sigma)
    (_root_.GD.N0106.N0428.N0770.N1748.d021779 _).stronglyMeasurable]
  calc
    _ = ∫ z, (∑ i, sigma i ^ 2 / 2 * _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i z ^ 2)
        ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k) := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0106.N0428.N0770.N1753.d021767 k] with z hz
      unfold _root_.GD.N0232.N0719.N0880.d020684
      apply Finset.sum_congr rfl
      intro i _
      rw [_root_.GD.N0106.N0428.N0770.N1753.d021765 hk sigma (fun _ => 0) z hsigma hz]
      change _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i z ^ 2 * (sigma i ^ 2 / 2) = _
      ring
    _ = ∑ i, sigma i ^ 2 / 2 *
        (∫ z, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i z ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k)) := by
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
      · intro i _
        exact (_root_.GD.N0106.N0428.N0770.N1750.d008390 sigma i 2).const_mul _
    _ = _ := _root_.GD.N0106.N0428.N0770.N1750.d008407 hk hsigma


theorem d021782 {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta = _root_.GD.N0232.N0719.N1023.d001844 theta.scale := by
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021780 hk (fun _ => 2) (fun _ => le_rfl)]
  rw [_root_.GD.N0232.N0719.N0880.d020686 (fun _ => 2) hk
    (fun _ => le_rfl) ⟨0, theta.scale, theta.scale_pos⟩ rfl]
  exact _root_.GD.N0106.N0428.N0770.N1748.d021781 hk theta.scale theta.scale_pos



theorem d021783 {k : ℕ} (hk : 0 < k) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta =
      ((∑ i, theta.scale i) / (∑ i, (theta.scale i)⁻¹) +
        k / (∑ i, (theta.scale i)⁻¹) ^ 2) / 4 := by
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021782 hk]
  rfl

end
end GD.N0106.N0428.N0770.N1748

#print axioms _root_.GD.N0106.N0428.N0770.N1748.d021780
#print axioms _root_.GD.N0106.N0428.N0770.N1748.d021781
#print axioms _root_.GD.N0106.N0428.N0770.N1748.d021782
#print axioms _root_.GD.N0106.N0428.N0770.N1748.d021783
