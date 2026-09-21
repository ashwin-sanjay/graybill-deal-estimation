import GD.Module1432
import GD.Module0093

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0096.N0343

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1482
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

theorem d022821 (g : _root_.GD.N0232.N0720.N1482.d015118)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    (∫ z, _root_.GD.N0096.N0343.d022802 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) z ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      g.d009239 ^ 2 * ‖_root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ p hp - p‖ ^ 2 := by
  rw [_root_.GD.N0230.N0691.d001213]
  rw [← integral_const_mul]
  apply integral_congr_ae
  have ht := (_root_.GD.N0232.N0720.N1159.d014641 m n g⁻¹ p hp).coeFn_toLp
  change (fun z => _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ p hp z) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
    _root_.GD.N0232.N0720.N1214.d014261 m n g⁻¹ (_root_.GD.N0232.N0720.N1214.d014265 m n p) at ht
  filter_upwards [ht, _root_.GD.N0232.N0720.N1214.d014267 m n p,
    Lp.coeFn_sub (_root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ p hp) p] with z htz hpz hsz
  rw [_root_.GD.N0096.N0343.d022803, hsz, Pi.sub_apply, htz, ← hpz, mul_pow]

theorem d022822 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0096.N0343.d022808 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) =
      4 * ‖_root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130⁻¹ p hp - p‖ ^ 2 +
      9 * ‖_root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131⁻¹ p hp - p‖ ^ 2 := by
  unfold _root_.GD.N0096.N0343.d022808 _root_.GD.N0018.N0253.d005250 _root_.GD.N0018.N0253.d005249
  simp_rw [← _root_.GD.N0096.N0343.d022812, ← _root_.GD.N0096.N0343.d022813]
  rw [integral_add (_root_.GD.N0096.N0343.d022804 m n _root_.GD.N0232.N0720.N1482.d015130 p hp).integrable_sq
    (_root_.GD.N0096.N0343.d022804 m n _root_.GD.N0232.N0720.N1482.d015131 p hp).integrable_sq,
    _root_.GD.N0096.N0343.d022821 m n _root_.GD.N0232.N0720.N1482.d015130 p hp,
    _root_.GD.N0096.N0343.d022821 m n _root_.GD.N0232.N0720.N1482.d015131 p hp]
  norm_num [_root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1482.d015131, _root_.GD.N0232.N0720.N1482.d015129, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

end
end GD.N0096.N0343

#print axioms _root_.GD.N0096.N0343.d022821
#print axioms _root_.GD.N0096.N0343.d022822
