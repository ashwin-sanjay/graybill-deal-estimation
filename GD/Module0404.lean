






import Mathlib
import GD.Module0403

namespace GD.N0155



noncomputable def d006211 (t : ℝ) : ℝ :=
  _root_.GD.N0155.d006199 t / (4000 * (t - 1) ^ 14) + _root_.GD.N0155.d006200 t / (200 * (t - 1) ^ 15 * (t + 1)) * Real.log t

private theorem d006212 {t : ℝ} (h0 : t ≠ 0) :
    (1 / t - 1) ^ 14 = (t - 1) ^ 14 / t ^ 14 := by
  have h : 1 / t - 1 = -(t - 1) / t := by field_simp; ring
  rw [h, div_pow, Even.neg_pow (by norm_num : Even 14)]

private theorem d006213 {t : ℝ} (h0 : t ≠ 0) :
    (1 / t - 1) ^ 15 = -((t - 1) ^ 15) / t ^ 15 := by
  have h : 1 / t - 1 = -(t - 1) / t := by field_simp; ring
  rw [h, div_pow, Odd.neg_pow (by norm_num : Odd 15)]

theorem d006214 {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    _root_.GD.N0155.d006199 (1 / t) / (4000 * (1 / t - 1) ^ 14) = _root_.GD.N0155.d006199 t / (4000 * (t - 1) ^ 14) := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  rw [_root_.GD.N0155.d006212 h0, ← _root_.GD.N0155.d006209 t h0]
  field_simp

theorem d006215 {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    _root_.GD.N0155.d006200 (1 / t) / (200 * (1 / t - 1) ^ 15 * (1 / t + 1)) * Real.log (1 / t)
      = _root_.GD.N0155.d006200 t / (200 * (t - 1) ^ 15 * (t + 1)) * Real.log t := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have h2 : t + 1 ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 / t + 1 = (t + 1) / t := by field_simp; ring
  have hlog : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  rw [_root_.GD.N0155.d006213 h0, hplus, hlog, ← _root_.GD.N0155.d006210 t h0]
  field_simp


theorem d006216 {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) : _root_.GD.N0155.d006211 (1 / t) = _root_.GD.N0155.d006211 t := by
  unfold _root_.GD.N0155.d006211
  rw [_root_.GD.N0155.d006214 ht ht1, _root_.GD.N0155.d006215 ht ht1]

end GD.N0155
