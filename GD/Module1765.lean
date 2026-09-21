import GD.Module1764
import GD.Module0371



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1590
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1587

theorem d029263 (a b x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1587.d029254 a b x ≤ Real.exp (-min a b * |x|) := by
  by_cases hx : x ≤ 0
  · rw [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx, abs_of_nonpos hx]
    apply Real.exp_le_exp.mpr
    calc a*x ≤ min a b*x := mul_le_mul_of_nonpos_right (min_le_left a b) hx
      _ = -min a b * -x := by ring
  · have hx' : 0 ≤ x := (lt_of_not_ge hx).le
    rw [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg hx, abs_of_nonneg hx']
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right a b)) hx')

theorem d029264 {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 ≤ h)
    (x : ℝ) (n : ℤ) :
    _root_.GD.N0106.N0428.N0765.N1587.d029254 a b (x+h*n) ≤ Real.exp (min a b * |x|) *
      Real.exp (-(min a b*h)*|(n : ℝ)|) := by
  refine (_root_.GD.N0106.N0428.N0765.N1590.d029263 a b (x+h*n)).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hk : 0 < min a b := lt_min ha hb
  have htri : h * |(n : ℝ)| ≤ |x+h*n|+|x| := by
    have ht := abs_add_le (x+h*(n : ℝ)) (-x)
    have he : x+h*(n : ℝ)+(-x) = h*(n : ℝ) := by ring
    rw [he, abs_mul, abs_of_nonneg hh, abs_neg] at ht
    exact ht
  nlinarith

theorem d029265 {k : ℝ} (hk : 0 < k) :
    Summable (fun n : ℤ => Real.exp (-k*|(n : ℝ)|)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1613.d005630 (s := fun n : ℤ =>
    ((Real.exp (-k*|(n : ℝ)|) : ℝ) : ℂ)) (C := 1) hk (by
      intro n
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, le_refl])
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h.norm

theorem d029266 {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (x : ℝ) :
    Summable (fun n : ℤ => _root_.GD.N0106.N0428.N0765.N1587.d029254 a b (x+h*n)) := by
  apply ((_root_.GD.N0106.N0428.N0765.N1590.d029265 (mul_pos (lt_min ha hb) hh)).mul_left
    (Real.exp (min a b*|x|))).of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, abs_of_pos (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _)] using _root_.GD.N0106.N0428.N0765.N1590.d029264 ha hb hh.le x n

end
end GD.N0106.N0428.N0765.N1590
#print axioms _root_.GD.N0106.N0428.N0765.N1590.d029266
