import Mathlib









open MeasureTheory Set

namespace GD.N0232.N0719.N0940



theorem d001776
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 ≤ z) :
    z ^ 7 / (ε + z) ^ 8 ≤ 1 / (ε + z) := by
  have hd : 0 < ε + z := by linarith
  have hzle : z ≤ ε + z := by linarith
  have hp : z ^ 7 ≤ (ε + z) ^ 7 :=
    pow_le_pow_left₀ hz hzle 7
  rw [div_le_div_iff₀ (pow_pos hd 8) hd]
  have hm := mul_le_mul_of_nonneg_right hp hd.le
  nlinarith [hm]


theorem d001777 {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z)) =
      Real.log ((ε + 1) / ε) := by
  have hint : IntervalIntegrable
      (fun z : ℝ => 1 / (ε + z)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
    intro z hz
    have hz0 : 0 ≤ z := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hz.1
    change ε + z ≠ 0
    exact ne_of_gt (by linarith)
  have hderiv : ∀ z ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => Real.log (ε + u)) (1 / (ε + z)) z := by
    intro z hz
    have hz0 : 0 ≤ z := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hz.1
    have hne : ε + z ≠ 0 := ne_of_gt (by linarith)
    simpa [one_div] using (Real.hasDerivAt_log hne).comp_const_add ε z
  calc
    (∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z)) =
        Real.log (ε + 1) - Real.log (ε + 0) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = Real.log ((ε + 1) / ε) := by
      rw [add_zero, Real.log_div (by linarith : ε + 1 ≠ 0) hε.ne']



theorem d001778 {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℝ in (0 : ℝ)..1, z ^ 7 / (ε + z) ^ 8) ≤
      Real.log ((ε + 1) / ε) := by
  have hf : IntervalIntegrable
      (fun z : ℝ => z ^ 7 / (ε + z) ^ 8) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_id.pow 7
    · exact (continuousOn_const.add continuousOn_id).pow 8
    · intro z hz
      exact pow_ne_zero 8 (ne_of_gt (by
        have hz0 : 0 ≤ z := by simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hz.1
        linarith))
  have hg : IntervalIntegrable
      (fun z : ℝ => 1 / (ε + z)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
    intro z hz
    have hz0 : 0 ≤ z := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hz.1
    change ε + z ≠ 0
    exact ne_of_gt (by linarith)
  calc
    (∫ z : ℝ in (0 : ℝ)..1, z ^ 7 / (ε + z) ^ 8) ≤
        ∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z) := by
          apply intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num) hf hg
          intro z hz
          exact _root_.GD.N0232.N0719.N0940.d001776 hε hz.1
    _ = Real.log ((ε + 1) / ε) := _root_.GD.N0232.N0719.N0940.d001777 hε

end GD.N0232.N0719.N0940
