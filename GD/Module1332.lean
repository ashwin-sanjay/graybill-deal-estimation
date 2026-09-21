import GD.Module1018
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0374
noncomputable section

open _root_.GD.N0232.N0720.N1236


theorem d021688 {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    _root_.GD.N0232.N0720.N1236.d016213 u 1 r ≤ r ^ (-2 : ℝ) := by
  unfold _root_.GD.N0232.N0720.N1236.d016213 _root_.GD.N0232.N0720.N1236.d016209
  rw [one_mul]
  calc
    _ ≤ r ^ (1 / 2 : ℝ) * r ^ (-(5 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr (le_add_of_nonneg_left hu.le) (by norm_num))
        (Real.rpow_nonneg hr.le _)
    _ = _ := by rw [← Real.rpow_add hr]; norm_num


theorem d021689 {u : ℝ} (hu : 0 < u) :
    (∫ r in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1236.d016213 u 1 r) = 2 / (3 * u) := by
  simpa using _root_.GD.N0232.N0720.N1236.d016217 hu (show (0 : ℝ) < 1 by norm_num)

theorem d021690 {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    (∫ r in Ioi R, _root_.GD.N0232.N0720.N1236.d016213 u 1 r) ≤ 1 / R := by
  calc
    _ ≤ ∫ r in Ioi R, r ^ (-2 : ℝ) := by
      apply integral_mono_ae
        ((_root_.GD.N0232.N0720.N1236.d016216 hu zero_lt_one).mono_set (Ioi_subset_Ioi hR.le))
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact _root_.GD.N0101.N0374.d021688 hu (hR.trans hr)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
      norm_num [Real.rpow_neg_one, one_div]


theorem d021691 {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    2 / (3 * u) - 1 / R ≤ ∫ r in Ioo (0 : ℝ) R, _root_.GD.N0232.N0720.N1236.d016213 u 1 r := by
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (_root_.GD.N0232.N0720.N1236.d016216 hu zero_lt_one) hR.le
  rw [_root_.GD.N0101.N0374.d021689 hu, intervalIntegral.integral_of_le hR.le,
    integral_Ioc_eq_integral_Ioo] at hsplit
  rw [← hsplit]
  linarith [_root_.GD.N0101.N0374.d021690 hu hR]

end
end GD.N0101.N0374

#print axioms _root_.GD.N0101.N0374.d021688
#print axioms _root_.GD.N0101.N0374.d021689
#print axioms _root_.GD.N0101.N0374.d021690
#print axioms _root_.GD.N0101.N0374.d021691
