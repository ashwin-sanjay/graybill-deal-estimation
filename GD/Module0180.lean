import Mathlib.Data.Real.Basic
import Mathlib.Tactic










namespace GD.N0232.N0720.N1244


theorem d002158 :
    (1 : ℝ) - 2 * (11 / 8) * (10 / 11) +
        (11 / 8) ^ 2 * (120 / 99) = 19 / 24 := by
  norm_num [div_eq_mul_inv]


theorem d002159 :
    -((11 / 8 : ℝ) * (10 / 11) - (11 / 8) ^ 2 * (120 / 99)) /
        (19 / 24) = 25 / 19 := by
  norm_num [div_eq_mul_inv]



theorem d002160 :
    (10 * (3 / 88 : ℝ) *
        ((11 / 8) * 10 - (11 / 8) ^ 2 * (120 / 9))) /
        (19 / 24) = -375 / 76 := by
  norm_num [div_eq_mul_inv]



theorem d002161 :
    ((-375 / 76 : ℝ), (25 / 19 : ℝ)) =
      ((10 * (3 / 88 : ℝ) *
          ((11 / 8) * 10 - (11 / 8) ^ 2 * (120 / 9))) / (19 / 24),
       -((11 / 8 : ℝ) * (10 / 11) -
          (11 / 8) ^ 2 * (120 / 99)) / (19 / 24)) := by
  norm_num [div_eq_mul_inv]

end GD.N0232.N0720.N1244
