import GD.Module1788















set_option autoImplicit false
set_option warningAsError true

namespace GD.N0106.N0428.N0765.N1511
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1515 _root_.GD.N0106.N0428.N0765.N1538

theorem d029770 (x : ℝ) {h d0 d1 : ℝ}
    (hh : 0 < h) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (haxis : ((21 : ℝ) / 2) * d0 < Real.pi)
    (hmixed : ((21 : ℝ) / 2) * (d1 + d1) < Real.pi) (a₀ b₀ : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1515.d029731 x - h ^ 2 * (∑' p : ℤ × ℤ,
      _root_.GD.N0106.N0428.N0765.N1515.d029732 (Real.exp x) (a₀ + h * p.1, b₀ + h * p.2))| ≤
      (2 * _root_.GD.N0106.N0428.N0765.N1515.d029737 d0 0 + 2 * _root_.GD.N0106.N0428.N0765.N1515.d029737 0 d0) /
        (Real.exp (2 * Real.pi * d0 / h) - 1) +
      4 * _root_.GD.N0106.N0428.N0765.N1515.d029737 d1 d1 / (Real.exp (2 * Real.pi * d1 / h) - 1) ^ 2 := by
  have ha : _root_.GD.N0106.N0428.N0765.N1515.d029736 (Real.exp x) d0 0 ≤ _root_.GD.N0106.N0428.N0765.N1515.d029737 d0 0 :=
    _root_.GD.N0106.N0428.N0765.N1515.d029762 (Real.exp_pos x) (by
      simpa only [_root_.GD.N0106.N0428.N0765.N1538.d021192, abs_of_pos hd0, abs_zero, add_zero] using haxis)
  have hb : _root_.GD.N0106.N0428.N0765.N1515.d029736 (Real.exp x) 0 d0 ≤ _root_.GD.N0106.N0428.N0765.N1515.d029737 0 d0 :=
    _root_.GD.N0106.N0428.N0765.N1515.d029762 (Real.exp_pos x) (by
      simpa only [_root_.GD.N0106.N0428.N0765.N1538.d021192, abs_zero, abs_of_pos hd0, zero_add] using haxis)
  have hm : _root_.GD.N0106.N0428.N0765.N1515.d029736 (Real.exp x) d1 d1 ≤ _root_.GD.N0106.N0428.N0765.N1515.d029737 d1 d1 :=
    _root_.GD.N0106.N0428.N0765.N1515.d029762 (Real.exp_pos x) (by
      simpa only [_root_.GD.N0106.N0428.N0765.N1538.d021192, abs_of_pos hd1] using hmixed)
  have hden : 0 ≤ Real.exp (2 * Real.pi * d0 / h) - 1 := by
    apply sub_nonneg.mpr
    apply Real.one_le_exp_iff.mpr
    positivity
  apply (_root_.GD.N0106.N0428.N0765.N1515.d029768 x hh hd0 hd1 haxis hmixed a₀ b₀).trans
  unfold _root_.GD.N0106.N0428.N0765.N1515.d029738
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ hden
    exact add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
      (mul_le_mul_of_nonneg_left hb (by norm_num))
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hm (by norm_num)

end
end GD.N0106.N0428.N0765.N1511

#print axioms _root_.GD.N0106.N0428.N0765.N1511.d029770
