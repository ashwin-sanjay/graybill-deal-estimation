import GD.Module0613
import GD.Module0601










open MeasureTheory Set
open scoped ENNReal NNReal

namespace GD.N0108

noncomputable section

open _root_.GD.N0124
open _root_.GD.N0116
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0118
open _root_.GD.N0146


def d008888
    {rho : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) : ℝ :=
  ∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
    |((((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ))| /
      ((T.width : ℝ) ^ 2)

private theorem d008889
    (c w x : ℝ) (hw : 0 < w) :
    |_root_.GD.N0118.d008582 c w x| ≤ 1 / w := by
  by_cases hL : x ∈ Ioc (c - w) c
  · have hR : x ∉ Ioc c (c + w) := by
      intro hx
      linarith [hL.2, hx.1]
    rw [show _root_.GD.N0118.d008582 c w x = _root_.GD.N0118.d008580 c w x by
      simp [_root_.GD.N0118.d008582, hL, hR]]
    unfold _root_.GD.N0118.d008580
    rw [abs_of_nonneg (div_nonneg (by linarith [hL.1])
      (sq_nonneg w))]
    rw [div_le_div_iff₀ (sq_pos_of_pos hw) hw]
    nlinarith [hL.2]
  · by_cases hR : x ∈ Ioc c (c + w)
    · rw [show _root_.GD.N0118.d008582 c w x = _root_.GD.N0118.d008581 c w x by
        simp [_root_.GD.N0118.d008582, hL, hR]]
      unfold _root_.GD.N0118.d008581
      rw [abs_of_nonneg (div_nonneg (by linarith [hR.2])
        (sq_nonneg w))]
      rw [div_le_div_iff₀ (sq_pos_of_pos hw) hw]
      nlinarith [hR.1]
    · rw [show _root_.GD.N0118.d008582 c w x = 0 by simp [_root_.GD.N0118.d008582, hL, hR], abs_zero]
      exact one_div_nonneg.mpr hw.le

private theorem d008890
    (c₁ c₂ w : ℝ) (p : ℝ × ℝ) (hw : 0 < w) :
    |_root_.GD.N0118.d008583 c₁ c₂ w p| ≤ 1 / w ^ 2 := by
  unfold _root_.GD.N0118.d008583
  rw [abs_mul]
  calc
    |_root_.GD.N0118.d008582 c₁ w p.1| * |_root_.GD.N0118.d008582 c₂ w p.2|
        ≤ (1 / w) * (1 / w) :=
      mul_le_mul
        (_root_.GD.N0108.d008889 c₁ w p.1 hw)
        (_root_.GD.N0108.d008889 c₂ w p.2 hw)
        (abs_nonneg _) (le_of_lt (one_div_pos.mpr hw))
    _ = 1 / w ^ 2 := by ring



theorem d008891
    {rho : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) (p : ℝ × ℝ) :
    |T.d008659 p| ≤ _root_.GD.N0108.d008888 T := by
  unfold _root_.GD.N0113.d008651.d008659 _root_.GD.N0108.d008888
  calc
    |∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
        ((((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ)) *
          _root_.GD.N0118.d008583 ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
            (T.width : ℝ) p|
        ≤
      ∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
        |((((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ)) *
          _root_.GD.N0118.d008583 ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
            (T.width : ℝ) p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
      ∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
        |((((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ))| /
          ((T.width : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hw : (0 : ℝ) < (T.width : ℝ) := by
        exact_mod_cast T.width_pos
      calc
        |((((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ))| *
            |_root_.GD.N0118.d008583 ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
              (T.width : ℝ) p|
            ≤
          |((((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ))| *
            (1 / ((T.width : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (_root_.GD.N0108.d008890 _ _ _ _ hw) (abs_nonneg _)
        _ =
          |((((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ))| /
            ((T.width : ℝ) ^ 2) := by ring



theorem d008892
    {rho : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    {α β e : ℝ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1) :
    IntegrableOn
      (fun p : _root_.GD.N0124.d006387 =>
        ((p.1 - e) * T.d008659 (p.1, p.2.1)) *
          (p.2.2 ^ 2 / (e * (1 - e))) *
            _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
      _root_.GD.N0124.d006389 volume :=
  _root_.GD.N0108.d008886 hα hβ he0 he1 T.d008659
    T.d008664 (_root_.GD.N0108.d008891 T)



theorem d008893
    {rho : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    {α β e : ℝ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1) :
    IntegrableOn
      (fun p : _root_.GD.N0124.d006387 =>
        T.d008659 (p.1, p.2.1) ^ 2 *
          (p.2.2 ^ 2 / (e * (1 - e))) *
            _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
      _root_.GD.N0124.d006389 volume :=
  _root_.GD.N0108.d008887 hα hβ he0 he1 T.d008659
    T.d008664 (_root_.GD.N0108.d008891 T)

end

end GD.N0108
