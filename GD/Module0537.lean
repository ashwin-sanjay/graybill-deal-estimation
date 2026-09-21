import GD.Module0534
import GD.Module0034

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set

namespace GD.N0213.N0513
noncomputable section
open _root_.GD.N0213.N0495 _root_.GD.N0213.N0519

theorem d008010 (u : ℝ) :
    |u| * Real.exp (-u ^ 2 / 2) ≤ 1 := by
  rw [show -u ^ 2 / 2 = -(u ^ 2 / 2) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have he := Real.add_one_le_exp (u ^ 2 / 2)
  nlinarith [sq_nonneg (|u| - 1), sq_abs u]

def d008011 (L : ℝ) : ℝ := (2 / L) * Real.exp (L ^ 2 / 2)

theorem d008012 {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    ‖_root_.GD.N0213.N0495.d007175 L r‖ ≤ _root_.GD.N0213.N0513.d008011 L := by
  have heq : _root_.GD.N0213.N0495.d007175 L r = -(2 / L) * (Real.log r / L) *
      Real.exp (-(Real.log r / L) ^ 2 - Real.log r) := by
    unfold _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174
    rw [Real.exp_sub, Real.exp_log hr]
    field_simp
  have hlog : Real.log r = L * (Real.log r / L) := by field_simp
  have hexp : Real.exp (-(Real.log r / L) ^ 2 - Real.log r) ≤
      Real.exp (L ^ 2 / 2) * Real.exp (-(Real.log r / L) ^ 2 / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (Real.log r / L + L)]
  rw [heq, norm_mul, norm_mul, norm_neg, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 / L), Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (2 / L) * |Real.log r / L| *
        (Real.exp (L ^ 2 / 2) * Real.exp (-(Real.log r / L) ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _root_.GD.N0213.N0513.d008011 L *
        (|Real.log r / L| * Real.exp (-(Real.log r / L) ^ 2 / 2)) := by
      unfold _root_.GD.N0213.N0513.d008011
      ring
    _ ≤ _root_.GD.N0213.N0513.d008011 L := mul_le_of_le_one_right (by unfold _root_.GD.N0213.N0513.d008011; positivity)
      (_root_.GD.N0213.N0513.d008010 _)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → ℝ) (hR : Measurable R)

include hR

theorem d008013 (L : ℝ) :
    Integrable (fun x => _root_.GD.N0213.N0495.d007174 L (R x) ^ 2) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((show Measurable (fun x => _root_.GD.N0213.N0495.d007174 L (R x) ^ 2) by unfold _root_.GD.N0213.N0495.d007174; fun_prop).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => _root_.GD.N0213.N0519.d007983 L (R x))

theorem d008014 {L : ℝ} (hL : 0 < L)
    (hpos : ∀ᵐ x ∂μ, 0 < R x) :
    Integrable (fun x => _root_.GD.N0213.N0495.d007175 L (R x) ^ 2) μ := by
  apply (integrable_const (_root_.GD.N0213.N0513.d008011 L ^ 2)).mono'
    ((show Measurable (fun x => _root_.GD.N0213.N0495.d007175 L (R x) ^ 2) by
      unfold _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174; fun_prop).aestronglyMeasurable)
  filter_upwards [hpos] with x hx
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (_root_.GD.N0213.N0513.d008012 hL hx) 2

theorem d008015 {L : ℝ} (hL : 0 < L)
    (hpos : ∀ᵐ x ∂μ, 0 < R x) :
    Integrable (fun x => _root_.GD.N0213.N0495.d007174 L (R x) * _root_.GD.N0213.N0495.d007175 L (R x)) μ := by
  apply (integrable_const (_root_.GD.N0213.N0513.d008011 L)).mono'
    ((show Measurable (fun x => _root_.GD.N0213.N0495.d007174 L (R x) * _root_.GD.N0213.N0495.d007175 L (R x)) by
      unfold _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174; fun_prop).aestronglyMeasurable)
  filter_upwards [hpos] with x hx
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (_root_.GD.N0213.N0495.d007176 L (R x))]
  exact (mul_le_mul_of_nonneg_right (_root_.GD.N0213.N0495.d007177 L (R x)) (norm_nonneg _)).trans
    (by simpa only [one_mul] using _root_.GD.N0213.N0513.d008012 hL hx)

theorem d008016 {L : ℝ} (hL : 0 < L)
    (hpos : ∀ᵐ x ∂μ, 0 < R x) :
    (∫ x, _root_.GD.N0213.N0495.d007174 L (R x) * _root_.GD.N0213.N0495.d007175 L (R x) ∂μ) ^ 2 ≤
      (∫ x, _root_.GD.N0213.N0495.d007174 L (R x) ^ 2 ∂μ) *
        (∫ x, _root_.GD.N0213.N0495.d007175 L (R x) ^ 2 ∂μ) := by
  simpa only [one_mul] using
    _root_.GD.N0230.N0658.d000405
      μ (fun _ => 1) (fun x => _root_.GD.N0213.N0495.d007174 L (R x)) (fun x => _root_.GD.N0213.N0495.d007175 L (R x))
      (Filter.Eventually.of_forall (fun _ => zero_le_one))
      (by simpa only [one_mul] using _root_.GD.N0213.N0513.d008013 μ R hR L)
      (by simpa only [one_mul] using _root_.GD.N0213.N0513.d008015 μ R hR hL hpos)
      (by simpa only [one_mul] using _root_.GD.N0213.N0513.d008014 μ R hR hL hpos)

theorem d008017 [NeZero μ] (L : ℝ) :
    0 < ∫ x, _root_.GD.N0213.N0495.d007174 L (R x) ^ 2 ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _)
    (_root_.GD.N0213.N0513.d008013 μ R hR L)).mpr
  have hs : Function.support (fun x => _root_.GD.N0213.N0495.d007174 L (R x) ^ 2) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sq_pos_of_pos (_root_.GD.N0213.N0495.d007176 L (R x))).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne μ)

end
end GD.N0213.N0513

#print axioms _root_.GD.N0213.N0513.d008012
#print axioms _root_.GD.N0213.N0513.d008016
#print axioms _root_.GD.N0213.N0513.d008017
