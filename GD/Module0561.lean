import GD.Module0560



set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open _root_.GD.N0082.N0334
open _root_.GD.N0149.N0432 _root_.GD.N0149.N0433

namespace GD.N0157
noncomputable section



theorem d008334 (H : ℝ → ℝ) (hHm : Measurable H)
    {M : ℝ} (hM : ∀ u ∈ Ioo (0 : ℝ) 1, |H u| ≤ M)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun u => ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let m := min t (1 - t)
  have hm : 0 < m := lt_min ht.1 (sub_pos.mpr ht.2)
  apply (integrable_const ((M + 1) ^ 2 / m ^ 2)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold _root_.GD.N0082.N0334.d008256
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hd := _root_.GD.N0082.N0334.d008263 ⟨ht.1.le, ht.2.le⟩ hu
    have hdm : m ≤ _root_.GD.N0082.N0334.d008256 t u := by
      have h1 := mul_nonneg hu.1.le
        (sub_nonneg.mpr (min_le_right t (1 - t)))
      have h2 := mul_nonneg (sub_nonneg.mpr hu.2.le)
        (sub_nonneg.mpr (min_le_left t (1 - t)))
      unfold _root_.GD.N0082.N0334.d008256
      dsimp [m] at *
      nlinarith
    have hHu := abs_le.mp (hM u hu)
    have hn : (H u - t) ^ 2 ≤ (M + 1) ^ 2 := by
      have hlo : 0 ≤ (M + 1) + (H u - t) := by linarith [hHu.1, ht.2]
      have hhi : 0 ≤ (M + 1) - (H u - t) := by linarith [hHu.2, ht.1]
      nlinarith [mul_nonneg hlo hhi]
    have hd2 : m ^ 2 ≤ _root_.GD.N0082.N0334.d008256 t u ^ 2 := (sq_le_sq₀ hm.le hd.le).mpr hdm
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow]
    calc
      (H u - t) ^ 2 / _root_.GD.N0082.N0334.d008256 t u ^ 2 ≤
          (M + 1) ^ 2 / _root_.GD.N0082.N0334.d008256 t u ^ 2 :=
        div_le_div_of_nonneg_right hn (sq_nonneg _)
      _ ≤ (M + 1) ^ 2 / m ^ 2 := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (sq_pos_of_pos hm) hd2) (sq_nonneg (M + 1))



theorem d008335
    (H : ℝ → ℝ) (hHm : Measurable H) {M C : ℝ}
    (hM : ∀ u ∈ Ioo (0 : ℝ) 1, |H u| ≤ M)
    (hcap : ∀ t ∈ Ioo (0 : ℝ) 1, _root_.GD.N0082.N0334.d008258 H t ≤ C) :
    _root_.GD.N0149.N0433.d008323 H ∧ _root_.GD.N0082.N0334.d008258 H 0 ≤ C ∧ _root_.GD.N0082.N0334.d008258 H 1 ≤ C ∧
      ContinuousOn (_root_.GD.N0082.N0334.d008258 H) (Icc (0 : ℝ) 1) := by
  have hI := fun t ht => _root_.GD.N0157.d008334 H hHm hM (t := t) ht
  have hB := _root_.GD.N0006.d008332
    H hHm C hI hcap
  have hE := _root_.GD.N0006.d008333
    H hHm C hI hcap
  exact ⟨hB, hE.1, hE.2, _root_.GD.N0149.N0433.d008324 H hB⟩



theorem d008336 (H : ℝ → ℝ) (hHm : Measurable H)
    (h0 : Integrable (fun u => ((H u - 0) / _root_.GD.N0082.N0334.d008256 0 u) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)))
    (h1 : Integrable (fun u => ((H u - 1) / _root_.GD.N0082.N0334.d008256 1 u) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1))) : _root_.GD.N0149.N0433.d008323 H := by
  refine ⟨hHm, (h0.add h1).congr ?_⟩
  filter_upwards with u
  change ((H u - 0) / _root_.GD.N0082.N0334.d008256 0 u) ^ 2 +
    ((H u - 1) / _root_.GD.N0082.N0334.d008256 1 u) ^ 2 = _root_.GD.N0149.N0432.d008291 H u
  simp only [_root_.GD.N0149.N0432.d008291, _root_.GD.N0082.N0334.d008256, mul_zero, add_zero, sub_zero]
  congr 2 <;> ring


theorem d008337 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H) :
    _root_.GD.N0082.N0334.d008258 H 0 + _root_.GD.N0082.N0334.d008258 H 1 = Real.pi / 2 +
      ∫ u in Ioo (0 : ℝ) 1,
        (1 / u ^ 2 + 1 / (1 - u) ^ 2) *
          (H u - _root_.GD.N0232.N0720.N1089.d003092 u) ^ 2 := by
  rw [_root_.GD.N0149.N0433.d008329 H hH]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  simp only [_root_.GD.N0149.N0432.d008292, div_pow, div_eq_mul_inv]
  field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne']
  <;> ring

end
end GD.N0157

#print axioms _root_.GD.N0157.d008334
#print axioms _root_.GD.N0157.d008335
#print axioms _root_.GD.N0157.d008336
#print axioms _root_.GD.N0157.d008337
