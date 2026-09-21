import GD.Module1307
import GD.Module1286








set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
namespace GD.N0106.N0428.N0765.N1584
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1661
open _root_.GD.N0235

theorem d021365 :
    Integrable (fun p : Fin 3 → ℝ => p 1 / p 2) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  refine Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1661.d021361.add (integrable_const 1))
    (((measurable_pi_apply 1).div (measurable_pi_apply 2)).aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  change |p 1 / p 2| ≤ (p 1 / p 2) ^ 2 + 1
  nlinarith [sq_nonneg (|p 1 / p 2| - 1), sq_abs (p 1 / p 2)]

theorem d021366 :
    (∫ p : Fin 3 → ℝ, p 1 / p 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = 5 / 4 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  have hfun : (fun p : Fin 3 → ℝ => (p 1 / p 2 - 1) ^ 2) =
      fun p => ((p 1 / p 2) ^ 2 - 2 * (p 1 / p 2)) + 1 := by
    funext p; ring
  have h := _root_.GD.N0106.N0428.N0765.N1661.d021359
  have hadd := integral_add (_root_.GD.N0106.N0428.N0765.N1661.d021361.sub (_root_.GD.N0106.N0428.N0765.N1584.d021365.const_mul 2))
    (integrable_const (1 : ℝ) (μ := _root_.GD.N0106.N0428.N0765.N1529.d020798))
  have hsub := integral_sub _root_.GD.N0106.N0428.N0765.N1661.d021361 (_root_.GD.N0106.N0428.N0765.N1584.d021365.const_mul 2)
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
  rw [hfun, hadd, hsub, integral_const_mul, _root_.GD.N0106.N0428.N0765.N1661.d021363] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

theorem d021367 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0765.N1521.d020862 p 1 / _root_.GD.N0106.N0428.N0765.N1521.d020862 p 2 = Real.exp p.2 := by
  change ((1 - Real.sigmoid p.1) * Real.sigmoid p.2) /
      ((1 - Real.sigmoid p.1) * (1 - Real.sigmoid p.2)) = Real.exp p.2
  have hd : 1 + Real.exp p.2 ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ (sub_pos.mpr (Real.sigmoid_lt_one p.1)).ne',
    _root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
  field_simp

theorem d021368 (p : ℝ × ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1521.d020868 p := by
  exact mul_nonneg (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) p.1).le
    (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) p.2).le

@[fun_prop] theorem d021369 : Measurable _root_.GD.N0106.N0428.N0765.N1521.d020868 := by
  exact ((_root_.GD.N0106.N0428.N0765.N1539.d005374 _ _).comp measurable_fst).mul
    ((_root_.GD.N0106.N0428.N0765.N1539.d005374 _ _).comp measurable_snd)

theorem d021370 : Integrable _root_.GD.N0106.N0428.N0765.N1521.d020868 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  have h := (_root_.GD.N0106.N0428.N0765.N1521.d020871 (fun _ => (1 : ℝ)) measurable_const).mp
    (integrable_const (1 : ℝ) (μ := _root_.GD.N0106.N0428.N0765.N1529.d020798))
  simpa only [mul_one] using h

theorem d021371 : (∫ p, _root_.GD.N0106.N0428.N0765.N1521.d020868 p) = 1 := by
  exact _root_.GD.N0106.N0428.N0765.N1521.d020874

theorem d021372 :
    Integrable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1521.d020871 (fun p => p 1 / p 2)
    ((measurable_pi_apply 1).div (measurable_pi_apply 2))).mp _root_.GD.N0106.N0428.N0765.N1584.d021365
  simpa only [_root_.GD.N0106.N0428.N0765.N1584.d021367] using h

theorem d021373 :
    Integrable (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2) ^ 2) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1521.d020871 (fun p => (p 1 / p 2) ^ 2)
    (((measurable_pi_apply 1).div (measurable_pi_apply 2)).pow_const 2)).mp
      _root_.GD.N0106.N0428.N0765.N1661.d021361
  simpa only [_root_.GD.N0106.N0428.N0765.N1584.d021367] using h

theorem d021374 :
    (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp p.2) = 5 / 4 := by
  have h := _root_.GD.N0106.N0428.N0765.N1521.d020870 (fun p => p 1 / p 2)
    ((measurable_pi_apply 1).div (measurable_pi_apply 2))
  simpa only [_root_.GD.N0106.N0428.N0765.N1584.d021366, _root_.GD.N0106.N0428.N0765.N1584.d021367] using h.symm

theorem d021375 :
    (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * (Real.exp p.2) ^ 2) = 5 / 2 := by
  have h := _root_.GD.N0106.N0428.N0765.N1521.d020870 (fun p => (p 1 / p 2) ^ 2)
    (((measurable_pi_apply 1).div (measurable_pi_apply 2)).pow_const 2)
  simpa only [_root_.GD.N0106.N0428.N0765.N1661.d021363, _root_.GD.N0106.N0428.N0765.N1584.d021367] using h.symm

theorem d021376 :
    (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1521.d020868 p * Real.exp (2 * p.2)) = 5 / 2 := by
  simpa only [two_mul, Real.exp_add, pow_two] using _root_.GD.N0106.N0428.N0765.N1584.d021375

end
end GD.N0106.N0428.N0765.N1584

#print axioms _root_.GD.N0106.N0428.N0765.N1584.d021366
#print axioms _root_.GD.N0106.N0428.N0765.N1584.d021373
#print axioms _root_.GD.N0106.N0428.N0765.N1584.d021374
#print axioms _root_.GD.N0106.N0428.N0765.N1584.d021376
