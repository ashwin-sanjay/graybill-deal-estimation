import GD.Module1332
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0386
noncomputable section

open _root_.GD.N0232.N0720.N1236
open _root_.GD.N0101.N0374


theorem d021704 {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    _root_.GD.N0232.N0720.N1236.d016213 u 1 r ≤ r ^ (1 / 2 : ℝ) * u ^ (-(5 / 2 : ℝ)) := by
  unfold _root_.GD.N0232.N0720.N1236.d016213 _root_.GD.N0232.N0720.N1236.d016209
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hu (le_add_of_nonneg_right hr.le) (by norm_num))
    (Real.rpow_nonneg hr.le _)


theorem d021705 {u H : ℝ} (hu : 0 < u) (hH : 0 < H) :
    (∫ r in Ioo (0 : ℝ) H, _root_.GD.N0232.N0720.N1236.d016213 u 1 r) ≤
      (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * u ^ (-(5 / 2 : ℝ)) := by
  have hp : IntegrableOn (fun r : ℝ => r ^ (1 / 2 : ℝ)) (Ioo (0 : ℝ) H) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hH).mpr (by norm_num)
  have hpow : (∫ r in Ioo (0 : ℝ) H, r ^ (1 / 2 : ℝ)) =
      (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hH.le,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    norm_num
    ring
  calc
    _ ≤ ∫ r in Ioo (0 : ℝ) H, r ^ (1 / 2 : ℝ) * u ^ (-(5 / 2 : ℝ)) := by
      apply integral_mono_ae
        ((_root_.GD.N0232.N0720.N1236.d016216 hu zero_lt_one).mono_set
          (fun _ hr => hr.1)) (hp.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact _root_.GD.N0101.N0386.d021704 hu hr.1
    _ = _ := by rw [integral_mul_const, hpow]


theorem d021706 {δ u H : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ u) (hH : 0 < H) :
    (∫ r in Ioo (0 : ℝ) H, _root_.GD.N0232.N0720.N1236.d016213 u 1 r) ≤
      (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) := by
  exact (_root_.GD.N0101.N0386.d021705 (hδ.trans_le hδu) hH).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hδ hδu (by norm_num))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hH.le _)))


theorem d021707 {u H R : ℝ}
    (hu : 0 < u) (hH : 0 < H) (hHR : H ≤ R) :
    2 / (3 * u) - (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * u ^ (-(5 / 2 : ℝ)) - 1 / R ≤
      ∫ r in Ioo H R, _root_.GD.N0232.N0720.N1236.d016213 u 1 r := by
  have hint := _root_.GD.N0232.N0720.N1236.d016216 hu zero_lt_one
  have hhead := intervalIntegral.integral_Ioi_sub_Ioi hint hH.le
  rw [_root_.GD.N0101.N0374.d021689 hu, intervalIntegral.integral_of_le hH.le,
    integral_Ioc_eq_integral_Ioo] at hhead
  have hmiddle := intervalIntegral.integral_Ioi_sub_Ioi
    (hint.mono_set (Ioi_subset_Ioi hH.le)) hHR
  rw [intervalIntegral.integral_of_le hHR, integral_Ioc_eq_integral_Ioo] at hmiddle
  linarith [_root_.GD.N0101.N0386.d021705 hu hH, _root_.GD.N0101.N0374.d021690 hu (hH.trans_le hHR)]


theorem d021708 {δ u H R : ℝ}
    (hδ : 0 < δ) (hδu : δ ≤ u) (hH : 0 < H) (hHR : H ≤ R) :
    2 / (3 * u) - (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) - 1 / R ≤
      ∫ r in Ioo H R, _root_.GD.N0232.N0720.N1236.d016213 u 1 r := by
  have hu := hδ.trans_le hδu
  have hint := _root_.GD.N0232.N0720.N1236.d016216 hu zero_lt_one
  have hhead := intervalIntegral.integral_Ioi_sub_Ioi hint hH.le
  rw [_root_.GD.N0101.N0374.d021689 hu, intervalIntegral.integral_of_le hH.le,
    integral_Ioc_eq_integral_Ioo] at hhead
  have hmiddle := intervalIntegral.integral_Ioi_sub_Ioi
    (hint.mono_set (Ioi_subset_Ioi hH.le)) hHR
  rw [intervalIntegral.integral_of_le hHR, integral_Ioc_eq_integral_Ioo] at hmiddle
  linarith [_root_.GD.N0101.N0386.d021706 hδ hδu hH, _root_.GD.N0101.N0374.d021690 hu (hH.trans_le hHR)]

end
end GD.N0101.N0386

#print axioms _root_.GD.N0101.N0386.d021704
#print axioms _root_.GD.N0101.N0386.d021705
#print axioms _root_.GD.N0101.N0386.d021706
#print axioms _root_.GD.N0101.N0386.d021707
#print axioms _root_.GD.N0101.N0386.d021708
