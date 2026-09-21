import GD.Module1301
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0106.N0428.N0765.N1583
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521


theorem d021332 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * (∫ l in (0 : ℝ)..1, ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l‖) ≤
      ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := by
  have hk := _root_.GD.N0106.N0428.N0765.N1538.d021227 he a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)
  have hr : ContinuousOn (fun l => (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l).re)
      (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn' (continuousOn_const.mul hk)
  have hre : (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re =
      ∫ l in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l).re := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021243
    rw [← intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact (integral_re ((hk.intervalIntegrable_of_Icc zero_le_one).1.const_mul
      (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β))).symm
  have hm : _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * (∫ l in (0 : ℝ)..1, ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l‖) ≤
      (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re := by
    rw [hre, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on zero_le_one
      ((continuousOn_const.mul hk.norm).intervalIntegrable_of_Icc zero_le_one)
      (hr.intervalIntegrable_of_Icc zero_le_one)
      (fun l hl => _root_.GD.N0106.N0428.N0765.N1538.d021234 he a b α β hl hw)
  calc _root_.GD.N0106.N0428.N0765.N1538.d021231 α β * (∫ l in (0 : ℝ)..1, ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l‖)
      ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re := hm
    _ ≤ |(_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β).re| := le_abs_self _
    _ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021228 α β * _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := Complex.abs_re_le_norm _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := by rw [norm_mul, _root_.GD.N0106.N0428.N0765.N1538.d021229, one_mul]


theorem d021333 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β‖ ≤ ∫ l in (0 : ℝ)..1, ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l‖ := by
  have hk := _root_.GD.N0106.N0428.N0765.N1538.d021227 he a b α β hw
  have hn := Complex.continuous_ofReal.continuousOn.mul hk
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021244
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  apply intervalIntegral.integral_mono_on zero_le_one
    (hn.norm.intervalIntegrable_of_Icc zero_le_one)
    (hk.norm.intervalIntegrable_of_Icc zero_le_one)
  intro l hl
  change ‖(l : ℂ) * _root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l‖ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l‖
  rw [norm_mul, Complex.norm_of_nonneg hl.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hl.2


theorem d021334 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos (_root_.GD.N0106.N0428.N0765.N1538.d021232 hw) (_root_.GD.N0106.N0428.N0765.N1538.d021248 he a b))
    (_root_.GD.N0106.N0428.N0765.N1538.d021250 he a b α β hw)


theorem d021335 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β / _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹ := by
  have hs := _root_.GD.N0106.N0428.N0765.N1538.d021232 hw
  have hD := _root_.GD.N0106.N0428.N0765.N1583.d021332 he a b α β hw
  have hN := _root_.GD.N0106.N0428.N0765.N1583.d021333 he a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)
  have hDc := norm_pos_iff.mpr (_root_.GD.N0106.N0428.N0765.N1583.d021334 he a b α β hw)
  rw [norm_div, div_le_iff₀ hDc]
  calc ‖_root_.GD.N0106.N0428.N0765.N1538.d021244 e a b α β‖ ≤ ∫ l in (0 : ℝ)..1, ‖_root_.GD.N0106.N0428.N0765.N1538.d021226 e a b α β l‖ := hN
    _ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ / _root_.GD.N0106.N0428.N0765.N1538.d021231 α β := by
      apply (le_div_iff₀ hs).mpr
      simpa only [mul_comm] using hD
    _ = (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹ * ‖_root_.GD.N0106.N0428.N0765.N1538.d021243 e a b α β‖ := by ring

theorem d021336 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b 0 0 = (_root_.GD.N0106.N0428.N0765.N1538.d021245 e a b : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021243 _root_.GD.N0106.N0428.N0765.N1538.d021245
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro l hl
  rw [uIcc_of_le zero_le_one] at hl
  exact _root_.GD.N0106.N0428.N0765.N1538.d021239 he a b hl

theorem d021337 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021244 e a b 0 0 = (_root_.GD.N0106.N0428.N0765.N1538.d021246 e a b : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021244 _root_.GD.N0106.N0428.N0765.N1538.d021246
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro l hl
  rw [uIcc_of_le zero_le_one] at hl
  dsimp only
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021239 he a b hl, Complex.ofReal_mul]


theorem d021338 {e : ℝ} (he : 0 < e) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021244 e a b 0 0 / _root_.GD.N0106.N0428.N0765.N1538.d021243 e a b 0 0 =
      (_root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1583.d021337 he a b, _root_.GD.N0106.N0428.N0765.N1583.d021336 he a b, ← Complex.ofReal_div]
  congr 1
  exact mul_left_cancel₀ (inv_ne_zero he.ne') (_root_.GD.N0106.N0428.N0765.N1538.d021258 he a b)


theorem d021339 {eta : ℝ} (heta : 0 < eta) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * (|α| + |β|) < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1538.d021244 eta⁻¹ a b α β / _root_.GD.N0106.N0428.N0765.N1538.d021243 eta⁻¹ a b α β‖ ≤
      (Real.cos (((21 : ℝ) / 2) * ((|α| + |β|) / 2)))⁻¹ := by
  exact _root_.GD.N0106.N0428.N0765.N1583.d021335 (inv_pos.mpr heta) a b α β hw


theorem d021340 {eta : ℝ} (heta : 0 < eta) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021244 eta⁻¹ a b 0 0 / _root_.GD.N0106.N0428.N0765.N1538.d021243 eta⁻¹ a b 0 0 =
      (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) : ℂ) := by
  simpa only [inv_inv] using _root_.GD.N0106.N0428.N0765.N1583.d021338 (inv_pos.mpr heta) a b

end
end GD.N0106.N0428.N0765.N1583

#print axioms _root_.GD.N0106.N0428.N0765.N1583.d021332
#print axioms _root_.GD.N0106.N0428.N0765.N1583.d021333
#print axioms _root_.GD.N0106.N0428.N0765.N1583.d021334
#print axioms _root_.GD.N0106.N0428.N0765.N1583.d021335
#print axioms _root_.GD.N0106.N0428.N0765.N1583.d021338
#print axioms _root_.GD.N0106.N0428.N0765.N1583.d021339
#print axioms _root_.GD.N0106.N0428.N0765.N1583.d021340
