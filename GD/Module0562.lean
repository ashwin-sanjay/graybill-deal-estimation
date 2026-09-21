import GD.Module0556

set_option autoImplicit false
open MeasureTheory Set

namespace GD.N0082.N0334

noncomputable section

theorem d008338 : _root_.GD.N0082.N0334.d008258 id (1 / 2) = (1 / 3 : ℝ) := by
  have heq : _root_.GD.N0082.N0334.d008258 id (1 / 2) =
      ∫ u in Ioo (0 : ℝ) 1, 4 * u ^ 2 - 4 * u + 1 := by
    unfold _root_.GD.N0082.N0334.d008258
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    dsimp [id, _root_.GD.N0082.N0334.d008256]
    have hd : u + 1 / 2 - 2 * u * (1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hd]
    ring
  rw [heq, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul (4 : ℝ) (fun x : ℝ => x)]
    norm_num [intervalIntegral.integral_const_mul, integral_pow, integral_id]
  all_goals apply Continuous.intervalIntegrable; fun_prop

theorem d008339 : _root_.GD.N0082.N0334.d008258 _root_.GD.N0082.N0334.d008257 (1 / 2) = (17 / 35 : ℝ) := by
  have heq : _root_.GD.N0082.N0334.d008258 _root_.GD.N0082.N0334.d008257 (1 / 2) =
      ∫ u in Ioo (0 : ℝ) 1,
        16 * u ^ 6 - 48 * u ^ 5 + 36 * u ^ 4 + 8 * u ^ 3 - 12 * u ^ 2 + 1 := by
    unfold _root_.GD.N0082.N0334.d008258
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    dsimp [_root_.GD.N0082.N0334.d008257, _root_.GD.N0082.N0334.d008256]
    have hd : u + 1 / 2 - 2 * u * (1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hd]
    ring
  rw [heq, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  repeat' first | rw [intervalIntegral.integral_add] | rw [intervalIntegral.integral_sub]
  all_goals try norm_num [intervalIntegral.integral_const_mul, integral_pow, integral_id]
  all_goals apply Continuous.intervalIntegrable; fun_prop

theorem d008340 : _root_.GD.N0082.N0334.d008259 (1 / 2) = (39 / 35 : ℝ) := by
  norm_num [_root_.GD.N0082.N0334.d008259, _root_.GD.N0082.N0334.d008339, _root_.GD.N0082.N0334.d008338]

theorem d008341 :
    _root_.GD.N0082.N0334.d008258 id (1 / 2) = (1 / 3 : ℝ) ∧
      _root_.GD.N0082.N0334.d008258 _root_.GD.N0082.N0334.d008257 (1 / 2) = (17 / 35 : ℝ) ∧
      _root_.GD.N0082.N0334.d008259 (1 / 2) = (39 / 35 : ℝ) ∧ 1 < _root_.GD.N0082.N0334.d008259 (1 / 2) := by
  refine ⟨_root_.GD.N0082.N0334.d008338, _root_.GD.N0082.N0334.d008339, _root_.GD.N0082.N0334.d008340, ?_⟩
  rw [_root_.GD.N0082.N0334.d008340]
  norm_num

end
end GD.N0082.N0334

#print axioms _root_.GD.N0082.N0334.d008341
