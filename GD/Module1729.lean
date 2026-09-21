import GD.Module0899
import GD.Module0274

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory ProbabilityTheory

namespace GD.N0081.N0327

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1046

theorem d028790 (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure 1 1) = ∫ u in Ioo (0 : ℝ) 1, f u := by
  rw [_root_.GD.N0235.d004041
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)]
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · have hu' : 0 < u ∧ u < 1 := hu
    norm_num [betaPDFReal, hu', ProbabilityTheory.beta, Real.Gamma_add_one]
  · have hu' : ¬ (0 < u ∧ u < 1) := hu
    simp [betaPDFReal, hu']

theorem d028791 {ρ : ℝ} (hρ : 0 < ρ) (f : ℝ → ℝ) :
    (∫ u in Ioo (0 : ℝ) 1, f (_root_.GD.N0232.N0720.N1091.d012763 ρ u)) =
      ∫ u in Ioo (0 : ℝ) 1, (ρ / _root_.GD.N0232.N0720.N1046.d013992 ρ u ^ 2) * f u := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioo (0 : ℝ) 1) (f := _root_.GD.N0232.N0720.N1091.d012763 ρ)
    (f' := fun u => -ρ / _root_.GD.N0232.N0720.N1046.d013992 ρ u ^ 2)
    measurableSet_Ioo (fun u hu => _root_.GD.N0232.N0720.N1046.d013999 hρ hu)
    (_root_.GD.N0232.N0720.N1046.d014001 hρ) (fun u => f (_root_.GD.N0232.N0720.N1091.d012763 ρ u))
  rw [_root_.GD.N0232.N0720.N1046.d014002 hρ] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [_root_.GD.N0232.N0720.N1046.d014000 hρ hu, smul_eq_mul, _root_.GD.N0232.N0720.N1046.d014006 hρ hu]

theorem d028792 {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    (t / (1 - t)) / _root_.GD.N0232.N0720.N1046.d013992 (t / (1 - t)) u ^ 2 =
      t * (1 - t) / (u + t - 2 * u * t) ^ 2 := by
  have ht1 : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
  have hD : 0 < u + t - 2 * u * t := by
    have : 0 < u * (1 - t) + t * (1 - u) :=
      add_pos (mul_pos hu.1 (sub_pos.mpr ht.2))
        (mul_pos ht.1 (sub_pos.mpr hu.2))
    nlinarith
  have hD' := _root_.GD.N0232.N0720.N1046.d013995 (div_pos ht.1 (sub_pos.mpr ht.2)) hu.1 hu.2
  unfold _root_.GD.N0232.N0720.N1046.d013992 at *
  field_simp
  ring

theorem d028793 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (f : ℝ → ℝ) :
    (∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 (t / (1 - t)) u) ∂betaMeasure 1 1) =
      ∫ u in Ioo (0 : ℝ) 1,
        (t * (1 - t) / (u + t - 2 * u * t) ^ 2) * f u := by
  rw [_root_.GD.N0081.N0327.d028790,
    _root_.GD.N0081.N0327.d028791 (div_pos ht.1 (sub_pos.mpr ht.2))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [_root_.GD.N0081.N0327.d028792 ht hu]

theorem d028794 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (H : ℝ → ℝ) :
    (∫ u, (H (_root_.GD.N0232.N0720.N1091.d012763 (t / (1 - t)) u) - t) ^ 2 ∂betaMeasure 1 1) =
      t * (1 - t) * ∫ u in Ioo (0 : ℝ) 1,
        ((H u - t) / (u + t - 2 * u * t)) ^ 2 := by
  rw [_root_.GD.N0081.N0327.d028793 ht (fun u => (H u - t) ^ 2),
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [div_pow]
  ring

end
end GD.N0081.N0327

#print axioms _root_.GD.N0081.N0327.d028790
#print axioms _root_.GD.N0081.N0327.d028791
#print axioms _root_.GD.N0081.N0327.d028793
#print axioms _root_.GD.N0081.N0327.d028794
