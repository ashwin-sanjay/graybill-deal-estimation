import GD.Module0854
import GD.Module0880




open MeasureTheory ProbabilityTheory Set

namespace GD.N0232.N0720.N1311

open _root_.GD.N0232.N0720.N1310 _root_.GD.N0232.N0720.N1309
open _root_.GD.N0232.N0720.N1313 _root_.GD.N0232.N0720.N1438

noncomputable section

theorem d013606 {epsilon : ℝ} (he : 0 < epsilon) :
    _root_.GD.N0232.N0720.N1309.d013069 (1 / epsilon) = 1 - _root_.GD.N0232.N0720.N1309.d013069 epsilon := by
  unfold _root_.GD.N0232.N0720.N1309.d013069
  have h1 : 1 + epsilon ≠ 0 := by positivity
  have h2 : 1 + 1 / epsilon ≠ 0 := by positivity
  field_simp [he.ne', h1, h2] ; ring

theorem d013607 {epsilon r : ℝ} (he : 0 < epsilon) (hr : 0 < r) :
    _root_.GD.N0232.N0720.N1310.d013058 (1 / epsilon) (1 / r) = 1 - _root_.GD.N0232.N0720.N1310.d013058 epsilon r := by
  have hs : 0 < Real.sqrt (epsilon * r) := Real.sqrt_pos.mpr (mul_pos he hr)
  have heq : (1 / epsilon) * (1 / r) = (epsilon * r)⁻¹ := by simp [mul_inv_rev, mul_comm]
  unfold _root_.GD.N0232.N0720.N1310.d013058
  rw [heq, Real.sqrt_inv]
  have hd : 1 + Real.sqrt (epsilon * r) ≠ 0 := by positivity
  have hi : 1 + (Real.sqrt (epsilon * r))⁻¹ ≠ 0 := by positivity
  field_simp [hs.ne', hd, hi] ; ring

theorem d013608 {k epsilon r : ℝ} (hk : 0 < k) (he : 0 < epsilon) (hr : 0 < r) :
    _root_.GD.N0232.N0720.N1310.d013059 (1 / k) (1 / epsilon) (1 / r) = 1 - _root_.GD.N0232.N0720.N1310.d013059 k epsilon r := by
  have hd : 1 + k * epsilon * r ≠ 0 := by positivity
  have hi : 1 + 1 / k * (1 / epsilon) * (1 / r) ≠ 0 := by positivity
  unfold _root_.GD.N0232.N0720.N1310.d013059
  field_simp [hk.ne', he.ne', hr.ne', hd, hi] ; ring

theorem d013609 {alpha beta epsilon : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : 0 < epsilon) :
    _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon = _root_.GD.N0232.N0720.N1309.d013070 beta alpha (1 / epsilon) := by
  unfold _root_.GD.N0232.N0720.N1309.d013070
  rw [← _root_.GD.N0232.N0720.N1438.d013600 ha hb]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha beta] with u hu
  have hr : 0 < u / (1 - u) := div_pos hu.1 (sub_pos.mpr hu.2)
  have hi : (1 - u) / (1 - (1 - u)) = 1 / (u / (1 - u)) := by
    field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne'] ; ring
  rw [hi, _root_.GD.N0232.N0720.N1311.d013607 he hr, _root_.GD.N0232.N0720.N1311.d013606 he]
  ring

theorem d013610 {alpha beta epsilon : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : 0 < epsilon) :
    _root_.GD.N0232.N0720.N1309.d013071 alpha beta epsilon = _root_.GD.N0232.N0720.N1309.d013071 beta alpha (1 / epsilon) := by
  unfold _root_.GD.N0232.N0720.N1309.d013071
  rw [← _root_.GD.N0232.N0720.N1438.d013600 ha hb]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha beta] with u hu
  have hr : 0 < u / (1 - u) := div_pos hu.1 (sub_pos.mpr hu.2)
  have hi : (1 - u) / (1 - (1 - u)) = 1 / (u / (1 - u)) := by
    field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne'] ; ring
  have hk : alpha / beta = 1 / (beta / alpha) := by field_simp
  rw [hi, hk, _root_.GD.N0232.N0720.N1311.d013608 (div_pos hb ha) he hr, _root_.GD.N0232.N0720.N1311.d013606 he]
  ring

theorem d013611 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 1 ≤ beta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ _root_.GD.N0232.N0720.N1309.d013071 alpha beta epsilon < _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon := by
  rcases eq_or_lt_of_le hb with h | h
  · subst beta
    exact _root_.GD.N0232.N0720.N1313.d013100 ha
  · exact _root_.GD.N0232.N0720.N1309.d013082 ha h

theorem d013612 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (h : 1 ≤ alpha ∨ 1 ≤ beta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ _root_.GD.N0232.N0720.N1309.d013071 alpha beta epsilon < _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon := by
  rcases h with h | h
  · obtain ⟨epsilon, he, hgap⟩ := _root_.GD.N0232.N0720.N1311.d013611 hb h
    refine ⟨1 / epsilon, one_div_pos.mpr he, ?_⟩
    rw [← _root_.GD.N0232.N0720.N1311.d013610 hb ha he, ← _root_.GD.N0232.N0720.N1311.d013609 hb ha he]
    exact hgap
  · exact _root_.GD.N0232.N0720.N1311.d013611 ha h

end
end GD.N0232.N0720.N1311

#print axioms _root_.GD.N0232.N0720.N1311.d013612
