import GD.Module1428
import GD.Module0699
import GD.Module0658
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GD.N0051
noncomputable section

theorem d022785 {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    (1 + x) ^ r ≤ 2 ^ r * (1 + x ^ r) := by
  by_cases h : x ≤ 1
  · have hh : (1 + x) ^ r ≤ (2 : ℝ) ^ r :=
      Real.rpow_le_rpow (by positivity) (by linarith) hr
    exact hh.trans (le_mul_of_one_le_right (by positivity)
      (le_add_of_nonneg_right (Real.rpow_nonneg hx _)))
  · have hx1 : 1 ≤ x := (lt_of_not_ge h).le
    have hh : (1 + x) ^ r ≤ (2 * x) ^ r :=
      Real.rpow_le_rpow (by positivity) (by linarith) hr
    rw [Real.mul_rpow (by norm_num) hx] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num)) (by positivity))

theorem d022786 {v w x y d r : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hx : 0 < x) (hy : 0 < y) (hr : 0 ≤ r) :
    (v * x) * (1 + d ^ 2 / (w * y)) ^ r ≤
      v * 2 ^ r * (x + (d ^ 2 / w) ^ r * (x * y ^ (-r))) := by
  have hh := mul_le_mul_of_nonneg_left
    (_root_.GD.N0051.d022785 (by positivity : 0 ≤ d ^ 2 / (w * y)) hr) (mul_pos hv hx).le
  have heq : (d ^ 2 / (w * y)) ^ r = (d ^ 2 / w) ^ r * y ^ (-r) := by
    rw [← div_div, Real.div_rpow (by positivity) hy.le, Real.rpow_neg hy.le, div_eq_mul_inv]
  rw [heq] at hh
  calc
    _ ≤ (v * x) * (2 ^ r * (1 + (d ^ 2 / w) ^ r * y ^ (-r))) := hh
    _ = _ := by ring



theorem d022787 {a b v w d r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hw : 0 < w)
    (hr : 0 ≤ r) (hrb : r < b)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hbound : ∀ x y, 0 < x → 0 < y →
      0 ≤ f (x, y) ∧ f (x, y) ≤ (v * x) * (1 + d ^ 2 / (w * y)) ^ r) :
    Integrable f ((gammaMeasure a a).prod (gammaMeasure b b)) ∧
    (∫ u, f u ∂(gammaMeasure a a).prod (gammaMeasure b b)) ≤
      v * 2 ^ r * (1 + (d ^ 2 / w) ^ r * _root_.GD.N0051.d022780 b b (-r)) := by
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb hb
  have hix : Integrable (fun x : ℝ => x) (gammaMeasure a a) := by
    simpa only [Real.rpow_one] using _root_.GD.N0051.d022782 ha ha (show 0 < a + 1 by linarith)
  have hiy : Integrable (fun y : ℝ => y ^ (-r)) (gammaMeasure b b) :=
    _root_.GD.N0051.d022782 hb hb (by linarith)
  let H : ℝ × ℝ → ℝ := fun u =>
    v * 2 ^ r * (u.1 + (d ^ 2 / w) ^ r * (u.1 * u.2 ^ (-r)))
  have hH : Integrable H ((gammaMeasure a a).prod (gammaMeasure b b)) :=
    ((hix.comp_fst (gammaMeasure b b)).add ((hix.mul_prod hiy).const_mul _)).const_mul _
  have hpos : ∀ᵐ u ∂(gammaMeasure a a).prod (gammaMeasure b b), 0 < u.1 ∧ 0 < u.2 := by
    filter_upwards [
      (Measure.quasiMeasurePreserving_fst (μ := gammaMeasure a a) (ν := gammaMeasure b b)).ae
        (_root_.GD.N0232.N0719.N0910.d010286 ha ha),
      (Measure.quasiMeasurePreserving_snd (μ := gammaMeasure a a) (ν := gammaMeasure b b)).ae
        (_root_.GD.N0232.N0719.N0910.d010286 hb hb)] with u hu hv
    exact ⟨hu, hv⟩
  have hdom : ∀ᵐ u ∂(gammaMeasure a a).prod (gammaMeasure b b), f u ≤ H u := by
    filter_upwards [hpos] with u hu
    exact (hbound _ _ hu.1 hu.2).2.trans (_root_.GD.N0051.d022786 hv hw hu.1 hu.2 hr)
  have hfi : Integrable f ((gammaMeasure a a).prod (gammaMeasure b b)) := hH.mono'
    hf.aestronglyMeasurable (by
      filter_upwards [hpos, hdom] with u hu hd
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound _ _ hu.1 hu.2).1] using hd)
  refine ⟨hfi, (integral_mono_ae hfi hH hdom).trans_eq ?_⟩
  have hmean : (∫ x : ℝ, x ∂gammaMeasure a a) = 1 := by
    simpa only [div_self ha.ne'] using
      _root_.GD.N0232.N0719.N0960.d009682 ha ha
  unfold H
  rw [integral_const_mul, integral_add (hix.comp_fst (gammaMeasure b b)) ((hix.mul_prod hiy).const_mul _),
    integral_const_mul, integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y ^ (-r))]
  simp only [integral_fun_fst (fun x : ℝ => x), probReal_univ, one_smul,
    hmean, one_mul, _root_.GD.N0051.d022783 hb hb (show 0 < b + -r by linarith)]

#print axioms _root_.GD.N0051.d022785
#print axioms _root_.GD.N0051.d022786
#print axioms _root_.GD.N0051.d022787
end
end GD.N0051
