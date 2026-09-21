import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic














namespace GD.N0232.N0720.N1253










theorem d002495
    (m01 m10 m02 m11 m20 m12 m21 m30 : ℝ) :
    let score := 10 * m10 - (21 / 2) * m01
    let d01 := 10 * m11 - (23 / 2) * m02 - score * m01
    let d10 := 9 * m20 - (21 / 2) * m11 - score * m10
    let d11 := 9 * m21 - (23 / 2) * m12 - score * m11
    let d20 := 8 * m30 - (21 / 2) * m21 - score * m20
    9 * d20 - (21 / 2) * d11 - 20 * m10 * d10 +
        (21 / 2) * (d01 * m10 + m01 * d10) =
      (1 / 4) *
        (882 * m01 ^ 2 * m10 - 1680 * m01 * m10 ^ 2 -
          882 * m01 * m11 + 756 * m01 * m20 - 483 * m02 * m10 +
          800 * m10 ^ 3 + 1680 * m10 * m11 - 1080 * m10 * m20 +
          483 * m12 - 756 * m21 + 288 * m30) := by
  dsimp
  ring



theorem d002496 (a c : ℝ) :
    ((11 / 8) * a - 1) *
        (-(11 / 128) * a * (117 * a * c - 76 * a - 16 * c + 16) + 1) =
      -(14157 / 1024) * a ^ 3 * c + (2299 / 256) * a ^ 3 +
        (1529 / 128) * a ^ 2 * c - (539 / 64) * a ^ 2 -
          (11 / 8) * a * c + (11 / 4) * a - 1 := by
  ring



theorem d002497 :
    (11 / 8 : ℝ) ^ 2 * (40 / 33) -
        2 * (11 / 8) * (10 / 11) + 1 = 19 / 24 := by
  norm_num [div_eq_mul_inv]





theorem d002498 :
    -(14157 / 1024 : ℝ) * (80 / 33) * (10 / 13) +
        (2299 / 256) * (80 / 33) +
        (1529 / 128) * (40 / 33) * (10 / 13) -
        (539 / 64) * (40 / 33) -
        (11 / 8) * (10 / 11) * (10 / 13) +
        (11 / 4) * (10 / 11) - 1 = -(3173 / 1248) := by
  norm_num [div_eq_mul_inv]



theorem d002499 :
    2 * (-(35 / 4 : ℝ) + 5 / 2 + 5 / 4 - 1) = -12 := by
  norm_num


theorem d002500 :
    ((1 : ℝ) / 11) * (1 - 19 / 24) = 5 / 264 := by
  norm_num [div_eq_mul_inv]




theorem d002501 :
    ((1 : ℝ) / 11) *
        ((1 - 19 / 24) + (-12 - (-(3173 / 624)))) = -(1395 / 2288) := by
  norm_num [div_eq_mul_inv]




theorem d002502 :
    (376 : ℝ) - 1957 / 39 = 12707 / 39 := by
  norm_num [div_eq_mul_inv]




theorem d002503 :
    ((1 : ℝ) / 11) *
        (2 * (-(4315 / 624)) + 12707 / 39) = 32447 / 1144 := by
  norm_num [div_eq_mul_inv]


theorem d002504 : (0 : ℝ) < 32447 / 1144 := by
  norm_num


theorem d002505 :
    (5 / 264 : ℝ) - (1395 / 2288) * (1 / 50) = 463 / 68640 := by
  norm_num [div_eq_mul_inv]



theorem d002506
    {e : ℝ} (_he0 : 0 ≤ e) (he50 : e ≤ 1 / 50) :
    (463 / 68640 : ℝ) ≤ 5 / 264 - (1395 / 2288) * e := by
  norm_num at he50 ⊢
  linarith


theorem d002507 : (0 : ℝ) < 463 / 68640 := by
  norm_num







theorem d002508
    (K : ℝ → ℝ)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) (1 / 50)) K)
    (hvalue : K 0 = 5 / 264)
    (hderiv : HasDerivAt K (-(1395 / 2288)) 0)
    {e : ℝ} (he0 : 0 ≤ e) (he50 : e ≤ 1 / 50) :
    (463 / 68640 : ℝ) ≤ K e := by
  by_cases he : e = 0
  · subst e
    rw [hvalue]
    norm_num
  · have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm he)
    have hslope := hconv.le_slope_of_hasDerivAt
      (show (0 : ℝ) ∈ Set.Icc 0 (1 / 50) by norm_num)
      (show e ∈ Set.Icc 0 (1 / 50) from ⟨he0, he50⟩)
      hepos hderiv
    rw [slope_def_field, hvalue, sub_zero] at hslope
    have hsupport :
        (5 / 264 : ℝ) - (1395 / 2288) * e ≤ K e := by
      have hmul := (le_div_iff₀ hepos).mp hslope
      nlinarith
    exact (_root_.GD.N0232.N0720.N1253.d002506 he0 he50).trans hsupport



theorem d002509
    (K : ℝ → ℝ)
    (hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) (1 / 50)) K)
    (hvalue : K 0 = 5 / 264)
    (hderiv : HasDerivAt K (-(1395 / 2288)) 0)
    {e : ℝ} (he0 : 0 ≤ e) (he50 : e ≤ 1 / 50) :
    0 < K e := by
  exact _root_.GD.N0232.N0720.N1253.d002507.trans_le
    (_root_.GD.N0232.N0720.N1253.d002508 K hconv hvalue hderiv he0 he50)

end GD.N0232.N0720.N1253
