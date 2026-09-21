import Mathlib


















namespace GD
namespace N0230
namespace N0637

noncomputable section


def d000240 (x : ℝ) : ℝ := min 1 (max 0 x)

theorem d000241 (x : ℝ) : 0 ≤ _root_.GD.N0230.N0637.d000240 x := by
  unfold _root_.GD.N0230.N0637.d000240
  exact le_min (by norm_num) (le_max_left 0 x)

theorem d000242 (x : ℝ) : _root_.GD.N0230.N0637.d000240 x ≤ 1 := by
  unfold _root_.GD.N0230.N0637.d000240
  exact min_le_left 1 (max 0 x)

theorem d000243 (x : ℝ) : _root_.GD.N0230.N0637.d000240 x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨_root_.GD.N0230.N0637.d000241 x, _root_.GD.N0230.N0637.d000242 x⟩

@[simp]
theorem d000244 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    _root_.GD.N0230.N0637.d000240 x = x := by
  unfold _root_.GD.N0230.N0637.d000240
  rw [max_eq_right hx.1, min_eq_right hx.2]



theorem d000245
    {t x : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |_root_.GD.N0230.N0637.d000240 x - t| ≤ |x - t| := by
  rcases ht with ⟨ht0, ht1⟩
  by_cases hx0 : x < 0
  · have hclip : _root_.GD.N0230.N0637.d000240 x = 0 := by
      unfold _root_.GD.N0230.N0637.d000240
      rw [max_eq_left (le_of_lt hx0), min_eq_right (by norm_num)]
    rw [hclip, abs_of_nonpos (sub_nonpos.mpr ht0),
      abs_of_nonpos (sub_nonpos.mpr (le_trans (le_of_lt hx0) ht0))]
    linarith
  · have hx0' : 0 ≤ x := le_of_not_gt hx0
    by_cases hx1 : x ≤ 1
    · rw [_root_.GD.N0230.N0637.d000244 ⟨hx0', hx1⟩]
    · have h1x : 1 < x := lt_of_not_ge hx1
      have hclip : _root_.GD.N0230.N0637.d000240 x = 1 := by
        unfold _root_.GD.N0230.N0637.d000240
        rw [max_eq_right hx0', min_eq_left (le_of_lt h1x)]
      rw [hclip, abs_of_nonneg (sub_nonneg.mpr ht1),
        abs_of_nonneg (sub_nonneg.mpr (le_trans ht1 (le_of_lt h1x)))]
      linarith


theorem d000246
    {t x : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (_root_.GD.N0230.N0637.d000240 x - t) ^ 2 ≤ (x - t) ^ 2 := by
  have habs := _root_.GD.N0230.N0637.d000245 (t := t) (x := x) ht
  exact (sq_le_sq).2 habs


theorem d000247
    {weight t x : ℝ} (hweight : 0 ≤ weight)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    weight * (_root_.GD.N0230.N0637.d000240 x - t) ^ 2 ≤ weight * (x - t) ^ 2 :=
  mul_le_mul_of_nonneg_left (_root_.GD.N0230.N0637.d000246 ht) hweight



theorem d000248
    (t positiveBranch negativeBranch : ℝ) :
    ((positiveBranch - t) ^ 2 + (negativeBranch - t) ^ 2) / 2 =
      (((positiveBranch + negativeBranch) / 2) - t) ^ 2 +
        (positiveBranch - negativeBranch) ^ 2 / 4 := by
  ring



theorem d000249
    (t positiveBranch negativeBranch : ℝ) :
    (((positiveBranch + negativeBranch) / 2) - t) ^ 2 ≤
      ((positiveBranch - t) ^ 2 + (negativeBranch - t) ^ 2) / 2 := by
  rw [_root_.GD.N0230.N0637.d000248]
  nlinarith [sq_nonneg (positiveBranch - negativeBranch)]



theorem d000250
    (weight t positiveBranch negativeBranch : ℝ) :
    weight *
        (((positiveBranch - t) ^ 2 + (negativeBranch - t) ^ 2) / 2) =
      weight * (((positiveBranch + negativeBranch) / 2) - t) ^ 2 +
        weight * (positiveBranch - negativeBranch) ^ 2 / 4 := by
  rw [_root_.GD.N0230.N0637.d000248]
  ring



theorem d000251
    {purified seed baseline : ℝ}
    (hpurified : purified ≤ seed) (hseed : seed < baseline) :
    purified < baseline :=
  lt_of_le_of_lt hpurified hseed

end

end N0637
end N0230
end GD

#print axioms _root_.GD.N0230.N0637.d000246
#print axioms _root_.GD.N0230.N0637.d000247
#print axioms _root_.GD.N0230.N0637.d000248
#print axioms _root_.GD.N0230.N0637.d000250
