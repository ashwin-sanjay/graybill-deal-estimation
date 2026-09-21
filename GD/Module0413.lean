import Mathlib










namespace GD.N0122

open MeasureTheory ProbabilityTheory Real Set

noncomputable section



def d006380 (w : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * w ^ ((1 : ℝ) / 2) *
    Real.exp (-(w / 2))

theorem d006381 {z : ℝ} (hz : 0 < z) :
    (z ^ 2) ^ ((1 : ℝ) / 2) = z := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hz]

theorem d006382 {z : ℝ} (hz : 0 < z) :
    z * _root_.GD.N0122.d006380 (z ^ 2) =
      z ^ 2 * gaussianPDFReal 0 1 z := by
  unfold _root_.GD.N0122.d006380 gaussianPDFReal
  rw [_root_.GD.N0122.d006381 hz]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  ring

theorem d006383 (f : ℝ → ℝ) :
    (∫ z in Ioi 0,
        z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2))
      =
    (1 / 2 : ℝ) *
      ∫ w in Ioi 0, _root_.GD.N0122.d006380 w * f w := by
  have h := MeasureTheory.integral_comp_rpow_Ioi_of_pos
    (g := fun w : ℝ => _root_.GD.N0122.d006380 w * f w)
    (p := (2 : ℝ)) (by norm_num)
  have h' :
      (∫ z in Ioi 0,
          2 * (z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2)))
        =
      ∫ w in Ioi 0, _root_.GD.N0122.d006380 w * f w := by
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    simp only [smul_eq_mul]
    have hz' : 0 < z := hz
    rw [show z ^ ((2 : ℝ) - 1) = z by
      norm_num]
    have hp := _root_.GD.N0122.d006382 hz'
    rw [← hp]
    simp only [mul_assoc]
    rw [Real.rpow_two]
  rw [MeasureTheory.integral_const_mul] at h'
  linarith

theorem d006384 (f : ℝ → ℝ) (z : ℝ) :
    (-z) ^ 2 * gaussianPDFReal 0 1 (-z) * f ((-z) ^ 2) =
      z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2) := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  ring_nf


theorem d006385
    (f : ℝ → ℝ)
    (hf : Integrable
      (fun z : ℝ =>
        z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2))) :
    (∫ z : ℝ,
        z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2))
      =
    ∫ w in Ioi 0, _root_.GD.N0122.d006380 w * f w := by
  let k : ℝ → ℝ :=
    fun z => z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2)
  have hnegRaw := integral_comp_neg_Ioi (0 : ℝ) k
  have hnegRaw' :
      (∫ x in Ioi 0, k (-x)) = ∫ x in Iic 0, k x := by
    simpa using hnegRaw
  have hneg :
      (∫ z in Iic 0, k z) = ∫ z in Ioi 0, k z := by
    rw [← hnegRaw']
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z _
    exact _root_.GD.N0122.d006384 f z
  have hsplit :=
    MeasureTheory.integral_add_compl (s := Ioi (0 : ℝ))
      measurableSet_Ioi (show Integrable k from hf)
  rw [compl_Ioi, hneg] at hsplit
  have hpos := _root_.GD.N0122.d006383 f
  change (∫ z : ℝ, k z) =
    ∫ w in Ioi 0, _root_.GD.N0122.d006380 w * f w
  linarith


theorem d006386
    (f : ℝ → ℝ)
    (hf : Integrable
      (fun z : ℝ =>
        z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2))) :
    (∫ z : ℝ, z ^ 2 * f (z ^ 2)
        ∂ProbabilityTheory.gaussianReal 0 1)
      =
    ∫ w in Ioi 0, _root_.GD.N0122.d006380 w * f w := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (by norm_num)]
  simp only [smul_eq_mul]
  rw [show
      (fun z : ℝ =>
        gaussianPDFReal 0 1 z * (z ^ 2 * f (z ^ 2))) =
      (fun z : ℝ =>
        z ^ 2 * gaussianPDFReal 0 1 z * f (z ^ 2)) by
    funext z
    ring]
  exact _root_.GD.N0122.d006385 f hf

end

end GD.N0122
