import GD.Module1431

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GD.N0051
noncomputable section

abbrev d023832 := (ℝ × ℝ) × (ℝ × ℝ)

abbrev d023833 (a b : ℝ) : Measure _root_.GD.N0051.d023832 :=
  _root_.GD.N0051.d022792.prod ((gammaMeasure a a).prod (gammaMeasure b b))

def d023834 (m v w : ℝ) (u : _root_.GD.N0051.d023832) : _root_.GD.N0051.d023832 :=
  ((m + Real.sqrt v * u.1.1, m + Real.sqrt w * u.1.2), (v * u.2.1, w * u.2.2))

def d023835 (b r : ℝ) : ℝ :=
  2 + 2 * 2 ^ r * (1 + _root_.GD.N0051.d022794 r * _root_.GD.N0051.d022780 b b (-r))

theorem d023836 {b r : ℝ} (hb : 0 < b) (hrb : r < b) : 0 < _root_.GD.N0051.d023835 b r := by
  unfold _root_.GD.N0051.d023835
  have hm := _root_.GD.N0051.d022784 hb hb (show 0 < b + -r by linarith)
  have hg := _root_.GD.N0051.d022798 r
  positivity




theorem d023837 {a b m v w r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hw : 0 < w) (hvw : v ≤ w)
    (hr : 0 ≤ r) (hrb : r < b)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f)
    (hfirst : ∀ y z s t, 0 < s → 0 < t →
      (f ((y, z), (s, t)) - y) ^ 2 ≤ s * (1 + (z - y) ^ 2 / t) ^ r) :
    Integrable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2) (_root_.GD.N0051.d023833 a b) ∧
    (∫ u, (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ∂_root_.GD.N0051.d023833 a b) ≤
      v * _root_.GD.N0051.d023835 b r := by
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb hb
  let ν : Measure (ℝ × ℝ) := (gammaMeasure a a).prod (gammaMeasure b b)
  let E : _root_.GD.N0051.d023832 → ℝ := fun u =>
    (f (_root_.GD.N0051.d023834 m v w u) - (m + Real.sqrt v * u.1.1)) ^ 2
  let Y : _root_.GD.N0051.d023832 → ℝ := fun u => (Real.sqrt v * u.1.1) ^ 2
  let M : ℝ := _root_.GD.N0051.d022780 b b (-r)
  let H : ℝ × ℝ → ℝ := fun z => v * 2 ^ r * (1 + _root_.GD.N0051.d022793 r z * M)
  have hM : 0 ≤ M := (_root_.GD.N0051.d022784 hb hb (show 0 < b + -r by linarith)).le
  have hH : Integrable H _root_.GD.N0051.d022792 :=
    ((integrable_const 1).add ((_root_.GD.N0051.d022797 hr).mul_const M)).const_mul _
  have hEm : Measurable E := by unfold E _root_.GD.N0051.d023834; fun_prop
  have hEn (u : _root_.GD.N0051.d023832) : 0 ≤ E u := sq_nonneg _
  have hsection (z : ℝ × ℝ) : Integrable (fun q => E (z, q)) ν ∧
      (∫ q, E (z, q) ∂ν) ≤ H z := by
    have hh := _root_.GD.N0051.d022787 (a := a) (b := b) (v := v) (w := w)
      (d := (m + Real.sqrt w * z.2) - (m + Real.sqrt v * z.1)) (r := r) ha hb hv hw hr hrb
      (fun q => E (z, q)) (hEm.comp (by fun_prop)) (fun x y hx hy =>
        ⟨sq_nonneg _, hfirst _ _ _ _ (mul_pos hv hx) (mul_pos hw hy)⟩)
    refine ⟨hh.1, hh.2.trans ?_⟩
    have hd : (m + Real.sqrt w * z.2) - (m + Real.sqrt v * z.1) =
        Real.sqrt w * z.2 - Real.sqrt v * z.1 := by ring
    dsimp only [H, M]
    rw [hd]
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (_root_.GD.N0051.d022799 hv hw hvw hr z) hM)) (by positivity)
  have hgi : Integrable (fun z => ∫ q, E (z, q) ∂ν) _root_.GD.N0051.d022792 :=
    hH.mono' hEm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable (by
      apply ae_of_all
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun q => hEn (z, q))]
      exact (hsection z).2)
  have hEi : Integrable E (_root_.GD.N0051.d023833 a b) := by
    apply (integrable_prod_iff hEm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ fun z => (hsection z).1, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hEn _)] using hgi
  have hEbound : (∫ u, E u ∂_root_.GD.N0051.d023833 a b) ≤
      v * 2 ^ r * (1 + _root_.GD.N0051.d022794 r * M) := by
    rw [integral_prod E hEi]
    apply (integral_mono hgi hH (fun z => (hsection z).2)).trans_eq
    unfold H _root_.GD.N0051.d022794
    rw [integral_const_mul, integral_add (integrable_const 1)
      ((_root_.GD.N0051.d022797 hr).mul_const M), integral_mul_const]
    simp
  have hZ : Integrable (fun z : ℝ × ℝ => (Real.sqrt v * z.1) ^ 2) _root_.GD.N0051.d022792 := by
    have hh := (_root_.GD.N0232.N0719.N0886.d003647 1 2).const_mul v
    have hi := hh.comp_fst (gaussianReal 0 1)
    simpa only [mul_pow, Real.sq_sqrt hv.le] using hi
  have hYi : Integrable Y (_root_.GD.N0051.d023833 a b) := hZ.comp_fst ν
  have hYeq : (∫ u, Y u ∂_root_.GD.N0051.d023833 a b) = v := by
    unfold Y _root_.GD.N0051.d023833
    rw [integral_fun_fst (fun z : ℝ × ℝ => (Real.sqrt v * z.1) ^ 2), probReal_univ, one_smul,
      integral_fun_fst (fun z : ℝ => (Real.sqrt v * z) ^ 2), probReal_univ, one_smul]
    simp only [mul_pow, Real.sq_sqrt hv.le, integral_const_mul,
      _root_.GD.N0232.N0719.N0886.d003646,
      NNReal.coe_one, mul_one]
  have hpoint (u : _root_.GD.N0051.d023832) : (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2 ≤
      2 * E u + 2 * Y u := by
    dsimp only [E, Y]
    nlinarith [sq_nonneg (f (_root_.GD.N0051.d023834 m v w u) - m - 2 * (Real.sqrt v * u.1.1))]
  have hsum : Integrable (fun u => 2 * E u + 2 * Y u) (_root_.GD.N0051.d023833 a b) :=
    (hEi.const_mul 2).add (hYi.const_mul 2)
  have hfi : Integrable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2) (_root_.GD.N0051.d023833 a b) :=
    hsum.mono' ((show Measurable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m) ^ 2) by
      unfold _root_.GD.N0051.d023834; fun_prop).aestronglyMeasurable) (by
      apply ae_of_all
      intro u
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f (_root_.GD.N0051.d023834 m v w u) - m))] using hpoint u)
  refine ⟨hfi, (integral_mono hfi hsum hpoint).trans ?_⟩
  rw [integral_add (hEi.const_mul 2) (hYi.const_mul 2), integral_const_mul, integral_const_mul, hYeq]
  unfold _root_.GD.N0051.d023835
  dsimp only [M] at hEbound
  nlinarith

#print axioms _root_.GD.N0051.d023837
end
end GD.N0051
