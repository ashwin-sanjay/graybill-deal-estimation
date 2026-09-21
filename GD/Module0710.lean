import GD.Module0709
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic






















open MeasureTheory Set

namespace GD.N0232.N0719.N0920

noncomputable section




theorem d010538
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 ≤ z) :
    z ^ 3 / (ε + z) ^ 8 ≤ 1 / (ε + z) ^ 5 := by
  have hd : 0 < ε + z := by linarith
  have hzle : z ≤ ε + z := by linarith
  have hp : z ^ 3 ≤ (ε + z) ^ 3 :=
    pow_le_pow_left₀ hz hzle 3
  rw [div_le_div_iff₀ (pow_pos hd 8) (pow_pos hd 5)]
  have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hd.le 5)
  nlinarith [hm]


theorem d010539 {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z) ^ 5) =
      1 / (4 * ε ^ 4) - 1 / (4 * (ε + 1) ^ 4) := by
  have hnot : (0 : ℝ) ∉ uIcc ε (ε + 1) := by
    rw [uIcc_of_le (by linarith : ε ≤ ε + 1)]
    simp only [mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hε)
  have hzpow := integral_zpow
    (a := ε) (b := ε + 1) (n := (-5 : ℤ))
    (Or.inr ⟨by norm_num, hnot⟩)
  have htranslate :
      (∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z) ^ 5) =
        ∫ u : ℝ in ε..ε + 1, u ^ (-5 : ℤ) := by
    calc
      (∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z) ^ 5) =
          ∫ z : ℝ in (0 : ℝ)..1, (ε + z) ^ (-5 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        norm_num [zpow_neg]
        rfl
      _ = ∫ u : ℝ in ε + 0..ε + 1, u ^ (-5 : ℤ) := by
        exact intervalIntegral.integral_comp_add_left
          (fun u : ℝ => u ^ (-5 : ℤ)) ε
      _ = ∫ u : ℝ in ε..ε + 1, u ^ (-5 : ℤ) := by rw [add_zero]
  rw [htranslate, hzpow]
  norm_num [zpow_neg]
  field_simp [hε.ne', ne_of_gt (by linarith : 0 < ε + 1)]
  <;> ring



theorem d010540 {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z) ^ 5) ≤
      1 / (4 * ε ^ 4) := by
  rw [_root_.GD.N0232.N0719.N0920.d010539 hε]
  have hnonneg : 0 ≤ 1 / (4 * (ε + 1) ^ 4) := by positivity
  linarith


theorem d010541 {ε : ℝ} (hε : 0 < ε) :
    (∫ z : ℝ in (0 : ℝ)..1, z ^ 3 / (ε + z) ^ 8) ≤
      1 / (4 * ε ^ 4) := by
  have hf : IntervalIntegrable
      (fun z : ℝ => z ^ 3 / (ε + z) ^ 8) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact continuousOn_id.pow 3
    · exact (continuousOn_const.add continuousOn_id).pow 8
    · intro z hz
      have hz0 : 0 ≤ z := by
        simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hz.1
      exact pow_ne_zero 8
        (ne_of_gt (by simpa using add_pos_of_pos_of_nonneg hε hz0))
  have hg : IntervalIntegrable
      (fun z : ℝ => 1 / (ε + z) ^ 5) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_const.add continuousOn_id).pow 5)
    intro z hz
    have hz0 : 0 ≤ z := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hz.1
    exact pow_ne_zero 5
      (ne_of_gt (by simpa using add_pos_of_pos_of_nonneg hε hz0))
  calc
    (∫ z : ℝ in (0 : ℝ)..1, z ^ 3 / (ε + z) ^ 8) ≤
        ∫ z : ℝ in (0 : ℝ)..1, 1 / (ε + z) ^ 5 := by
      apply intervalIntegral.integral_mono_on
        (show (0 : ℝ) ≤ 1 by norm_num) hf hg
      intro z hz
      exact _root_.GD.N0232.N0719.N0920.d010538 hε hz.1
    _ ≤ 1 / (4 * ε ^ 4) := _root_.GD.N0232.N0719.N0920.d010540 hε



theorem d010542
    {ε C E : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hreduce : E ≤ C *
      (∫ z : ℝ in (0 : ℝ)..1, z ^ 3 / (ε + z) ^ 8)) :
    E ≤ C / (4 * ε ^ 4) := by
  calc
    E ≤ C * (∫ z : ℝ in (0 : ℝ)..1,
        z ^ 3 / (ε + z) ^ 8) := hreduce
    _ ≤ C * (1 / (4 * ε ^ 4)) :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0719.N0920.d010541 hε) hC
    _ = C / (4 * ε ^ 4) := by ring

end

end GD.N0232.N0719.N0920

#print axioms _root_.GD.N0232.N0719.N0920.d010541
#print axioms _root_.GD.N0232.N0719.N0920.d010542
