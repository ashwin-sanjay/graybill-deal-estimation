import GD.Module1530

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0087
noncomputable section
open _root_.GD.N0051



theorem d023866 {a b m v w K β : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hw : 0 < w) (hvw : v ≤ w)
    (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f)
    (hsection : ∀ y z : ℝ,
      (∫⁻ q, ENNReal.ofReal ((f ((y,z),(v*q.1,w*q.2)) - y)^2)
        ∂(gammaMeasure a a).prod (gammaMeasure b b)) ≤
          ENNReal.ofReal (v * (1 + K * ((z-y)^2/w)^β))) :
    Integrable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m)^2) (_root_.GD.N0051.d023833 a b) ∧
      (∫ u, (f (_root_.GD.N0051.d023834 m v w u) - m)^2 ∂_root_.GD.N0051.d023833 a b) ≤
        v * (4 + 2 * K * _root_.GD.N0051.d022794 β) := by
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb hb
  let ν : Measure (ℝ × ℝ) := (gammaMeasure a a).prod (gammaMeasure b b)
  let E : _root_.GD.N0051.d023832 → ℝ := fun u =>
    (f (_root_.GD.N0051.d023834 m v w u) - (m + Real.sqrt v * u.1.1))^2
  let Y : _root_.GD.N0051.d023832 → ℝ := fun u => (Real.sqrt v * u.1.1)^2
  let H : ℝ × ℝ → ℝ := fun z => v * (1 + K * _root_.GD.N0051.d022793 β z)
  have hEm : Measurable E := by unfold E _root_.GD.N0051.d023834; fun_prop
  have hEn (u : _root_.GD.N0051.d023832) : 0 ≤ E u := sq_nonneg _
  have hHn (z : ℝ × ℝ) : 0 ≤ H z := by dsimp [H, _root_.GD.N0051.d022793]; positivity
  have hHi : Integrable H _root_.GD.N0051.d022792 :=
    ((integrable_const 1).add ((_root_.GD.N0051.d022797 hβ).const_mul K)).const_mul v
  have hHeq : (∫ z, H z ∂_root_.GD.N0051.d022792) = v * (1 + K * _root_.GD.N0051.d022794 β) := by
    unfold H _root_.GD.N0051.d022794
    rw [integral_const_mul, integral_add (integrable_const 1)
      ((_root_.GD.N0051.d022797 hβ).const_mul K), integral_const_mul]
    simp
  have hEs (z : ℝ × ℝ) : (∫⁻ q, ENNReal.ofReal (E (z,q)) ∂ν) ≤ ENNReal.ofReal (H z) := by
    apply (hsection (m + Real.sqrt v * z.1) (m + Real.sqrt w * z.2)).trans
    apply ENNReal.ofReal_le_ofReal
    have hd : (m + Real.sqrt w * z.2) - (m + Real.sqrt v * z.1) =
        Real.sqrt w * z.2 - Real.sqrt v * z.1 := by ring
    dsimp only [H]
    rw [hd]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (_root_.GD.N0051.d022799 hv hw hvw hβ z) hK)) hv.le
  have hEbound : (∫⁻ u, ENNReal.ofReal (E u) ∂_root_.GD.N0051.d023833 a b) ≤
      ENNReal.ofReal (v * (1 + K * _root_.GD.N0051.d022794 β)) := by
    rw [lintegral_prod _ hEm.ennreal_ofReal.aemeasurable]
    apply (lintegral_mono hEs).trans_eq
    rw [← ofReal_integral_eq_lintegral_ofReal hHi (ae_of_all _ hHn), hHeq]
  have hEi : Integrable E (_root_.GD.N0051.d023833 a b) := by
    refine ⟨hEm.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ hEn)).mpr
      (hEbound.trans_lt ENNReal.ofReal_lt_top)
  have hEreal : (∫ u, E u ∂_root_.GD.N0051.d023833 a b) ≤ v * (1 + K * _root_.GD.N0051.d022794 β) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hEi (ae_of_all _ hEn)] at hEbound
    apply (ENNReal.ofReal_le_ofReal_iff (by
      have := _root_.GD.N0051.d022798 β
      positivity)).mp hEbound
  have hZ : Integrable (fun z : ℝ × ℝ => (Real.sqrt v * z.1)^2) _root_.GD.N0051.d022792 := by
    have hh := (_root_.GD.N0232.N0719.N0886.d003647 1 2).const_mul v
    have hi := hh.comp_fst (gaussianReal 0 1)
    simpa only [mul_pow, Real.sq_sqrt hv.le] using hi
  have hYi : Integrable Y (_root_.GD.N0051.d023833 a b) := hZ.comp_fst ν
  have hYeq : (∫ u, Y u ∂_root_.GD.N0051.d023833 a b) = v := by
    unfold Y _root_.GD.N0051.d023833
    rw [integral_fun_fst (fun z : ℝ × ℝ => (Real.sqrt v * z.1)^2), probReal_univ, one_smul,
      integral_fun_fst (fun z : ℝ => (Real.sqrt v * z)^2), probReal_univ, one_smul]
    simp only [mul_pow, Real.sq_sqrt hv.le, integral_const_mul,
      _root_.GD.N0232.N0719.N0886.d003646,
      NNReal.coe_one, mul_one]
  have hpoint (u : _root_.GD.N0051.d023832) : (f (_root_.GD.N0051.d023834 m v w u) - m)^2 ≤ 2 * E u + 2 * Y u := by
    dsimp only [E, Y]
    nlinarith [sq_nonneg (f (_root_.GD.N0051.d023834 m v w u) - m - 2 * (Real.sqrt v * u.1.1))]
  have hsum : Integrable (fun u => 2 * E u + 2 * Y u) (_root_.GD.N0051.d023833 a b) :=
    (hEi.const_mul 2).add (hYi.const_mul 2)
  have hfi : Integrable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m)^2) (_root_.GD.N0051.d023833 a b) :=
    hsum.mono' ((show Measurable (fun u => (f (_root_.GD.N0051.d023834 m v w u) - m)^2) by
      unfold _root_.GD.N0051.d023834; fun_prop).aestronglyMeasurable) (by
      apply ae_of_all
      intro u
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f (_root_.GD.N0051.d023834 m v w u) - m))] using hpoint u)
  refine ⟨hfi, (integral_mono hfi hsum hpoint).trans ?_⟩
  rw [integral_add (hEi.const_mul 2) (hYi.const_mul 2), integral_const_mul, integral_const_mul, hYeq]
  nlinarith


theorem d023867 {a b m v w K β : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) (hw : 0 < w) (hvw : v ≤ w)
    (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f)
    (hsection : ∀ y z : ℝ,
      (∫⁻ q, ENNReal.ofReal ((f ((y,z),(v*q.1,w*q.2)) - y)^2)
        ∂(gammaMeasure a a).prod (gammaMeasure b b)) ≤
          ENNReal.ofReal (v * (1 + K * ((z-y)^2/w)^β))) :
    (∫⁻ u, ENNReal.ofReal ((f (_root_.GD.N0051.d023834 m v w u) - m)^2) ∂_root_.GD.N0051.d023833 a b) ≤
      ENNReal.ofReal (v * (4 + 2 * K * _root_.GD.N0051.d022794 β)) := by
  have hh := _root_.GD.N0087.d023866 (m := m) ha hb hv hw hvw hK hβ f hf hsection
  rw [← ofReal_integral_eq_lintegral_ofReal hh.1 (ae_of_all _ fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hh.2

end
end GD.N0087

#print axioms _root_.GD.N0087.d023866
#print axioms _root_.GD.N0087.d023867
