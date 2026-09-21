import GD.Module1296
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1560
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1562

private theorem d021070 {d : ℝ} (hd : 0 ≤ d) (hmax : d ≤ 11 / 10) :
    (1 / 4 : ℝ) ≤ Real.cos d := by
  have hsquare : d ^ 2 ≤ (11 / 10 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hd hmax 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := d)
  nlinarith

private theorem d021071 {d : ℝ} (hd : 0 ≤ d) (hmax : d ≤ 11 / 10) :
    2 * (Real.cos d) ^ (-21 / 2 : ℝ) ≤ (2 : ℝ) ^ 23 := by
  have hcos := _root_.GD.N0106.N0428.N0765.N1560.d021070 hd hmax
  have hbase : (Real.cos d) ^ (-21 / 2 : ℝ) ≤
      (1 / 4 : ℝ) ^ (-21 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hcos (by norm_num)
  have hexponent : (1 / 4 : ℝ) ^ (-21 / 2 : ℝ) ≤
      (1 / 4 : ℝ) ^ (-11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  have hinteger : (1 / 4 : ℝ) ^ (-11 : ℝ) = (4 : ℝ) ^ 11 := by
    rw [show (-11 : ℝ) = -((11 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 4), Real.rpow_natCast]
    norm_num
  calc
    2 * (Real.cos d) ^ (-21 / 2 : ℝ) ≤ 2 * (4 : ℝ) ^ 11 :=
      mul_le_mul_of_nonneg_left (hbase.trans (hexponent.trans_eq hinteger)) (by norm_num)
    _ = (2 : ℝ) ^ 23 := by norm_num

private theorem d021072 :
    (2 : ℝ) ^ 23 < Real.exp 24 - 1 := by
  have htwo : (2 : ℝ) < Real.exp 1 := by
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hpower : (2 : ℝ) ^ 24 ≤ Real.exp 1 ^ 24 :=
    pow_le_pow_left₀ (by norm_num) htwo.le 24
  have hexp : Real.exp (24 : ℝ) = Real.exp 1 ^ 24 := by
    convert Real.exp_nat_mul (1 : ℝ) 24 using 1 <;> norm_num
  rw [← hexp] at hpower
  have harithmetic : (2 : ℝ) ^ 23 + 1 < (2 : ℝ) ^ 24 := by norm_num
  linarith


theorem d021073 {d h : ℝ}
    (hd : 0 < d) (hmax : d ≤ 11 / 10) (hh : 0 < h) (hmesh : 4 * h ≤ d) :
    _root_.GD.N0106.N0428.N0765.N1562.d021061 d h < 1 := by
  have hexponent : (24 : ℝ) ≤ 2 * Real.pi * d / h := by
    apply (le_div_iff₀ hh).mpr
    have hpi := mul_lt_mul_of_pos_right Real.pi_gt_three hd
    nlinarith
  have hlarge : (2 : ℝ) ^ 23 < Real.exp (2 * Real.pi * d / h) - 1 :=
    _root_.GD.N0106.N0428.N0765.N1560.d021072.trans_le
      (sub_le_sub_right (Real.exp_le_exp.mpr hexponent) 1)
  have hden : 0 < Real.exp (2 * Real.pi * d / h) - 1 :=
    lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2 ^ 23) hlarge
  unfold _root_.GD.N0106.N0428.N0765.N1562.d021061
  apply (div_lt_iff₀ hden).mpr
  simpa only [one_mul] using (_root_.GD.N0106.N0428.N0765.N1560.d021071 hd.le hmax).trans_lt hlarge


theorem d021074 {d h : ℝ}
    (hd : 0 < d) (hmax : d ≤ 11 / 10) (hh : 0 < h) (hmesh : 4 * h ≤ d) :
    0 < _root_.GD.N0106.N0428.N0765.N1562.d021061 d h ∧ _root_.GD.N0106.N0428.N0765.N1562.d021061 d h < 1 := by
  have hdpi : d < Real.pi / 2 := by linarith [Real.pi_gt_three]
  exact ⟨_root_.GD.N0106.N0428.N0765.N1562.d021062 hd hdpi hh, _root_.GD.N0106.N0428.N0765.N1560.d021073 hd hmax hh hmesh⟩


theorem d021075 :
    0 < _root_.GD.N0106.N0428.N0765.N1562.d021061 (11 / 10) (1 / 4) ∧ _root_.GD.N0106.N0428.N0765.N1562.d021061 (11 / 10) (1 / 4) < 1 := by
  exact _root_.GD.N0106.N0428.N0765.N1560.d021074 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)


theorem d021076 :
    0 < _root_.GD.N0106.N0428.N0765.N1562.d021061 (3 / 4) (1 / 8) ∧ _root_.GD.N0106.N0428.N0765.N1562.d021061 (3 / 4) (1 / 8) < 1 := by
  exact _root_.GD.N0106.N0428.N0765.N1560.d021074 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)


theorem d021077 :
    0 < _root_.GD.N0106.N0428.N0765.N1562.d021061 (7 / 50) (1 / 40) ∧ _root_.GD.N0106.N0428.N0765.N1562.d021061 (7 / 50) (1 / 40) < 1 := by
  exact _root_.GD.N0106.N0428.N0765.N1560.d021074 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end
end GD.N0106.N0428.N0765.N1560

#print axioms _root_.GD.N0106.N0428.N0765.N1560.d021073
#print axioms _root_.GD.N0106.N0428.N0765.N1560.d021074
#print axioms _root_.GD.N0106.N0428.N0765.N1560.d021075
#print axioms _root_.GD.N0106.N0428.N0765.N1560.d021076
#print axioms _root_.GD.N0106.N0428.N0765.N1560.d021077
