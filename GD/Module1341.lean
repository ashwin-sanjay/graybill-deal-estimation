import GD.Module0663

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace GD.N0066
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0885 _root_.GD.N0232.N0719.N0980

variable {I : Type*} [Fintype I] [Nonempty I]

theorem d021733 (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i) :
    (∫ x, (_root_.GD.N0232.N0719.N0980.d009698 v x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹ := by
  have h := _root_.GD.N0232.N0719.N0885.d009328 m v hv
  change Var[_root_.GD.N0232.N0719.N0980.d009698 v; _root_.GD.N0232.N0719.N0980.d009697 m v] = _ at h
  rwa [variance_eq_integral (_root_.GD.N0232.N0719.N0980.d009699 v).aemeasurable,
    _root_.GD.N0232.N0719.N0980.d009701 m v hv] at h



theorem d021734 (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i)
    (f : (I → ℝ) → ℝ) (hf : Measurable f) (he : _root_.GD.N0232.N0719.N0980.d009696 f)
    (hL2 : MemLp f 2 (_root_.GD.N0232.N0719.N0980.d009697 m v))
    (hcap : (∫ x, (f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) ≤ (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹) :
    f =ᵐ[_root_.GD.N0232.N0719.N0980.d009697 m v] _root_.GD.N0232.N0719.N0980.d009698 v := by
  have hdec := _root_.GD.N0232.N0719.N0980.d009703 m v hv f hf he hL2
  rw [_root_.GD.N0066.d021733 m v hv] at hdec
  have hzero : (∫ x, (f x - _root_.GD.N0232.N0719.N0980.d009698 v x) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = 0 := by
    have hpos : 0 ≤ (∫ x, (f x - _root_.GD.N0232.N0719.N0980.d009698 v x) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) :=
      integral_nonneg (fun x => sq_nonneg (f x - _root_.GD.N0232.N0719.N0980.d009698 v x))
    linarith
  have hO2 : MemLp (_root_.GD.N0232.N0719.N0980.d009698 v) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    (_root_.GD.N0232.N0719.N0885.d009318 m v (_root_.GD.N0232.N0719.N0885.d009323 v)).memLp_two
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x => sq_nonneg (f x - _root_.GD.N0232.N0719.N0980.d009698 v x)) (hL2.sub hO2).integrable_sq).mp hzero
  filter_upwards [hae] with x hx
  have hx' : (f x - _root_.GD.N0232.N0719.N0980.d009698 v x) ^ 2 = 0 := hx
  nlinarith

theorem d021735 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g h : Ω → ℝ) (heq : f =ᵐ[μ] g) :
    cov[f, h; μ] = cov[g, h; μ] := by
  unfold covariance
  rw [integral_congr_ae heq]
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

omit [Nonempty I] in


theorem d021736 (m : ℝ) (u v w : I → ℝ≥0)
    (hu : ∀ i, 0 < u i) (heq : _root_.GD.N0232.N0719.N0980.d009698 v =ᵐ[_root_.GD.N0232.N0719.N0980.d009697 m u] _root_.GD.N0232.N0719.N0980.d009698 w) :
    _root_.GD.N0232.N0719.N0885.d009323 v = _root_.GD.N0232.N0719.N0885.d009323 w := by
  funext j
  have h := _root_.GD.N0066.d021735 (_root_.GD.N0232.N0719.N0980.d009697 m u) (_root_.GD.N0232.N0719.N0980.d009698 v) (_root_.GD.N0232.N0719.N0980.d009698 w)
    (fun x => x j) heq
  change cov[_root_.GD.N0232.N0719.N0885.d009311 (_root_.GD.N0232.N0719.N0885.d009323 v), fun x => x j; _root_.GD.N0232.N0719.N0980.d009697 m u] =
    cov[_root_.GD.N0232.N0719.N0885.d009311 (_root_.GD.N0232.N0719.N0885.d009323 w), fun x => x j; _root_.GD.N0232.N0719.N0980.d009697 m u] at h
  rw [_root_.GD.N0232.N0719.N0885.d009319, _root_.GD.N0232.N0719.N0885.d009319] at h
  exact mul_right_cancel₀ (ne_of_gt (show (0 : ℝ) < u j from hu j)) h




theorem d021737 (m : ℝ) (u v w : I → ℝ≥0)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i) :
    _root_.GD.N0232.N0719.N0980.d009698 v =ᵐ[_root_.GD.N0232.N0719.N0980.d009697 m u] _root_.GD.N0232.N0719.N0980.d009698 w ↔
      ∃ c : ℝ, 0 < c ∧ ∀ i, (w i : ℝ) = c * (v i : ℝ) := by
  have hPv := _root_.GD.N0232.N0719.N0885.d009324 v hv
  have hPw := _root_.GD.N0232.N0719.N0885.d009324 w hw
  constructor
  · intro heq
    have hweights := _root_.GD.N0066.d021736 m u v w hu heq
    refine ⟨_root_.GD.N0232.N0719.N0885.d009322 v / _root_.GD.N0232.N0719.N0885.d009322 w, div_pos hPv hPw, ?_⟩
    intro i
    have h := congrFun hweights i
    have hvi : (0 : ℝ) < v i := hv i
    have hwi : (0 : ℝ) < w i := hw i
    unfold _root_.GD.N0232.N0719.N0885.d009323 at h
    field_simp [hvi.ne', hwi.ne', hPv.ne', hPw.ne'] at h ⊢
    nlinarith
  · rintro ⟨c, hc, hcv⟩
    have hP : _root_.GD.N0232.N0719.N0885.d009322 w = c⁻¹ * _root_.GD.N0232.N0719.N0885.d009322 v := by
      simp only [_root_.GD.N0232.N0719.N0885.d009322, hcv, mul_inv_rev, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hweights : _root_.GD.N0232.N0719.N0885.d009323 v = _root_.GD.N0232.N0719.N0885.d009323 w := by
      funext i
      unfold _root_.GD.N0232.N0719.N0885.d009323
      rw [hcv i, hP]
      have hvi : (0 : ℝ) < v i := hv i
      field_simp [hc.ne', hPv.ne', hvi.ne']
    exact ae_of_all _ fun x => congrArg (fun p => _root_.GD.N0232.N0719.N0885.d009311 p x) hweights

end
end GD.N0066

#print axioms _root_.GD.N0066.d021734
#print axioms _root_.GD.N0066.d021736
#print axioms _root_.GD.N0066.d021737
