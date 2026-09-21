import GD.Module0206
import Mathlib.MeasureTheory.Function.LocallyIntegrable






open MeasureTheory Set Filter

namespace GD.N0232.N0720.N1374

open _root_.GD.N0232.N0720.N1377

noncomputable section

theorem d002867 {A l : ℝ} (hA : 0 < A) (hl : 1 < l) (b r : ℝ) :
    -A / 2 * r ^ 2 + b * r ≤
      l * b ^ 2 / (2 * A) - (A * (l - 1) / l) / 2 * r ^ 2 := by
  have hl0 : 0 < l := lt_trans zero_lt_one hl
  have hs : 0 ≤ A / (2 * l) * (r - l * b / A) ^ 2 := by positivity
  have he : A / (2 * l) * (r - l * b / A) ^ 2 =
      l * b ^ 2 / (2 * A) - (A * (l - 1) / l) / 2 * r ^ 2 -
        (-A / 2 * r ^ 2 + b * r) := by
    field_simp [hA.ne', hl0.ne']
    <;> ring
  rw [he] at hs
  linarith


theorem d002868 (n : ℕ) {A l : ℝ}
    (hA : 0 < A) (hl : 1 < l) (b : ℝ) :
    _root_.GD.N0232.N0720.N1377.d002852 n A b ≤ Real.exp (l * b ^ 2 / (2 * A)) *
      _root_.GD.N0232.N0720.N1377.d002852 n (A * (l - 1) / l) 0 := by
  have hl0 : 0 < l := lt_trans zero_lt_one hl
  have hred : 0 < A * (l - 1) / l := by positivity
  rw [_root_.GD.N0232.N0720.N1377.d002852, _root_.GD.N0232.N0720.N1377.d002852, ← integral_const_mul]
  apply integral_mono_ae (_root_.GD.N0232.N0720.N1377.d002860 n hA b)
    ((_root_.GD.N0232.N0720.N1377.d002860 n hred 0).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  unfold _root_.GD.N0232.N0720.N1377.d002851
  have h := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (_root_.GD.N0232.N0720.N1374.d002867 hA hl b r)) (pow_nonneg hr.le n)
  convert! h using 1
  simp only [zero_mul, add_zero, sub_eq_add_neg, Real.exp_add, neg_mul, neg_div]
  ring

theorem d002869 {A b r : ℝ} (hA : 0 < A)
    (hr : r ∈ Ioo (b / A) (b / A + 1)) :
    b ^ 2 / (2 * A) - A / 2 ≤ -A / 2 * r ^ 2 + b * r := by
  have h0 : 0 ≤ r - b / A := sub_nonneg.mpr hr.1.le
  have h1 : r - b / A ≤ 1 := by linarith [hr.2]
  have hs : (r - b / A) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have he : -A / 2 * r ^ 2 + b * r =
      b ^ 2 / (2 * A) - A / 2 * (r - b / A) ^ 2 := by
    field_simp [hA.ne']
    <;> ring
  rw [he]
  nlinarith


theorem d002870 (n : ℕ) {A b : ℝ}
    (hA : 0 < A) (hb : 0 ≤ b) :
    (b / A) ^ n * Real.exp (b ^ 2 / (2 * A) - A / 2) ≤ _root_.GD.N0232.N0720.N1377.d002852 n A b := by
  let c : ℝ := (b / A) ^ n * Real.exp (b ^ 2 / (2 * A) - A / 2)
  let s : Set ℝ := Ioo (b / A) (b / A + 1)
  have hcenter : 0 ≤ b / A := div_nonneg hb hA.le
  have hsub : s ⊆ Ioi 0 := fun r hr ↦ lt_of_le_of_lt hcenter hr.1
  have hcint : IntegrableOn (fun _ : ℝ ↦ c) s :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint := _root_.GD.N0232.N0720.N1377.d002860 n hA b
  have hlower : c ≤ ∫ r in s, _root_.GD.N0232.N0720.N1377.d002851 n A b r := by
    have hconst : (∫ _ : ℝ in s, c) = c := by
      rw [setIntegral_const]
      simp [s, measureReal_def, Real.volume_Ioo, smul_eq_mul]
    rw [← hconst]
    apply integral_mono_ae hcint (hint.mono_set hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_le_mul (pow_le_pow_left₀ hcenter hr.1.le n)
      (Real.exp_le_exp.mpr (_root_.GD.N0232.N0720.N1374.d002869 hA hr))
      (Real.exp_pos _).le (pow_nonneg (hsub hr).le n)
  apply hlower.trans
  apply setIntegral_mono_set hint ?_ (ae_of_all _ fun r hr ↦ hsub hr)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact _root_.GD.N0232.N0720.N1377.d002854 n A b hr.le

end

end GD.N0232.N0720.N1374
