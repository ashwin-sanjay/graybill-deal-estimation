import GD.Module1754
import Mathlib.Analysis.SpecialFunctions.Log.Basic



















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1685
noncomputable section

open Complex _root_.GD.N0106.N0428.N0765.N1683

theorem d029094 {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖(16 * Complex.I) / w ^ 3‖ ≤ 16 := by
  calc
    ‖(16 * Complex.I) / w ^ 3‖ = 16 / ‖w‖ ^ 3 := by
      norm_num [norm_div, norm_mul, norm_pow]
    _ ≤ 16 := div_le_self (by norm_num) (one_le_pow₀ hw)

theorem d029095 {x y : ℝ}
    (hx : 1 ≤ |x|) (hy : |y| ≤ 1) :
    (_root_.GD.N0106.N0428.N0765.N1683.d029048 ((x : ℂ) + (y : ℂ) * Complex.I)).re ≤ 33 - x ^ 2 := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hmnorm : 1 ≤ ‖z - Complex.I‖ := by
    apply hx.trans
    simpa [z] using Complex.abs_re_le_norm (z - Complex.I)
  have hpnorm : 1 ≤ ‖z + Complex.I‖ := by
    apply hx.trans
    simpa [z] using Complex.abs_re_le_norm (z + Complex.I)
  have hm : z - Complex.I ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hmnorm)
  have hp : z + Complex.I ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hpnorm)
  have hmre : -((16 * Complex.I) / (z - Complex.I) ^ 3).re ≤ 16 :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
      (_root_.GD.N0106.N0428.N0765.N1685.d029094 hmnorm))
  have hpre : ((16 * Complex.I) / (z + Complex.I) ^ 3).re ≤ 16 :=
    (Complex.re_le_norm _).trans (_root_.GD.N0106.N0428.N0765.N1685.d029094 hpnorm)
  have hre : (z ^ 2).re = x ^ 2 - y ^ 2 := by
    simp [z, pow_two, Complex.mul_re]
    <;> ring
  have hyprod : 0 ≤ (1 - y) * (1 + y) :=
    mul_nonneg (by linarith [(abs_le.mp hy).2])
      (by linarith [(abs_le.mp hy).1])
  have hysq : y ^ 2 ≤ 1 := by nlinarith
  change (_root_.GD.N0106.N0428.N0765.N1683.d029048 z).re ≤ 33 - x ^ 2
  rw [_root_.GD.N0106.N0428.N0765.N1683.d029060 hm hp, Complex.add_re,
    Complex.sub_re, Complex.neg_re, hre]
  linarith


theorem d029096 {x y : ℝ}
    (hx : 1 ≤ |x|) (hy : |y| ≤ 1) :
    ‖_root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (33 - x ^ 2) := by
  rw [_root_.GD.N0106.N0428.N0765.N1683.d029049, Complex.norm_exp]
  exact Real.exp_le_exp.mpr (_root_.GD.N0106.N0428.N0765.N1685.d029095 hx hy)

def d029097 (ε : ℝ) : ℝ := max 1 (33 - Real.log ε)

theorem d029098 (ε : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1685.d029097 ε :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem d029099 {ε x y : ℝ}
    (hε : 0 < ε) (hx : _root_.GD.N0106.N0428.N0765.N1685.d029097 ε ≤ |x|) (hy : |y| ≤ 1) :
    ‖_root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ε := by
  have hxone : 1 ≤ |x| := (le_max_left _ _).trans hx
  have hxlog : 33 - Real.log ε ≤ |x| := (le_max_right _ _).trans hx
  have hxprod : 0 ≤ (|x| - 1) * |x| :=
    mul_nonneg (sub_nonneg.mpr hxone) (abs_nonneg x)
  have hxsq : |x| ≤ x ^ 2 := by nlinarith [sq_abs x]
  calc
    ‖_root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.exp (33 - x ^ 2) :=
      _root_.GD.N0106.N0428.N0765.N1685.d029096 hxone hy
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith)
    _ = ε := Real.exp_log hε



theorem d029100 :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ x y : ℝ, R ≤ |x| → |y| ≤ 1 →
        ‖_root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ε := by
  intro ε hε
  exact ⟨_root_.GD.N0106.N0428.N0765.N1685.d029097 ε, _root_.GD.N0106.N0428.N0765.N1685.d029098 ε,
    fun _ _ hx hy => _root_.GD.N0106.N0428.N0765.N1685.d029099 hε hx hy⟩

theorem d029101 :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ x y : ℝ, R ≤ |x| → |y| < 1 →
        ‖_root_.GD.N0106.N0428.N0765.N1683.d029049 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hR, htail⟩ := _root_.GD.N0106.N0428.N0765.N1685.d029100 ε hε
  exact ⟨R, hR, fun x y hx hy => htail x y hx hy.le⟩

#print axioms _root_.GD.N0106.N0428.N0765.N1685.d029094
#print axioms _root_.GD.N0106.N0428.N0765.N1685.d029095
#print axioms _root_.GD.N0106.N0428.N0765.N1685.d029096
#print axioms _root_.GD.N0106.N0428.N0765.N1685.d029099
#print axioms _root_.GD.N0106.N0428.N0765.N1685.d029100
#print axioms _root_.GD.N0106.N0428.N0765.N1685.d029101

end
end GD.N0106.N0428.N0765.N1685
