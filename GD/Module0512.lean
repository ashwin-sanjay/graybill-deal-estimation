import GD.Module0445



set_option autoImplicit false
set_option warningAsError true

open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1623

def d007722 (I J : _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

theorem d007723 {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (y : ℝ) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hax hy),
      (mul_le_mul_of_nonneg_right hxb hy).trans (le_max_right _ _)⟩
  · have hy' : y ≤ 0 := le_of_not_ge hy
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxb hy'),
      (mul_le_mul_of_nonpos_right hax hy').trans (le_max_left _ _)⟩

theorem d007724 {I J : _root_.GD.N0232.N0720.N1164.d006809} {x y : ℝ}
    (hx : I.d006810 x) (hy : J.d006810 y) : (_root_.GD.N0106.N0428.N0765.N1623.d007722 I J).d006810 (x * y) := by
  have ha : min ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)) ≤
      (I.lo : ℝ) * y ∧ (I.lo : ℝ) * y ≤
      max ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)) := by
    simpa only [mul_comm] using _root_.GD.N0106.N0428.N0765.N1623.d007723 hy.1 hy.2 (I.lo : ℝ)
  have hb : min ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ)) ≤
      (I.hi : ℝ) * y ∧ (I.hi : ℝ) * y ≤
      max ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ)) := by
    simpa only [mul_comm] using _root_.GD.N0106.N0428.N0765.N1623.d007723 hy.1 hy.2 (I.hi : ℝ)
  have hxy := _root_.GD.N0106.N0428.N0765.N1623.d007723 hx.1 hx.2 y
  unfold _root_.GD.N0106.N0428.N0765.N1623.d007722 _root_.GD.N0232.N0720.N1164.d006809.d006810
  push_cast
  constructor
  · exact (le_min ((min_le_left _ _).trans ha.1)
      ((min_le_right _ _).trans hb.1)).trans hxy.1
  · exact hxy.2.trans (max_le (ha.2.trans (le_max_left _ _))
      (hb.2.trans (le_max_right _ _)))

end GD.N0106.N0428.N0765.N1623

#print axioms _root_.GD.N0106.N0428.N0765.N1623.d007724
