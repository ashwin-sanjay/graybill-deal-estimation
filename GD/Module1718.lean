import GD.Module1664
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0093
noncomputable section
open _root_.GD.N0213.N0527
open _root_.GD.N0213.N0488 (d028223)
open _root_.GD.N0232.N0719.N0954

theorem d028709 {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (M : ℝ) : ∃ δ > 0, ∀ x, 0 < x → x < δ →
      M * gammaPDFReal 1 1 x ≤ gammaPDFReal s s x := by
  let A : ℝ := s ^ s / Real.Gamma s
  have hA : 0 < A := div_pos (Real.rpow_pos_of_pos hs _) (Real.Gamma_pos_of_pos hs)
  have ht : Tendsto (fun x : ℝ => A * x ^ (s - 1)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : s - 1 < 0)).const_mul_atTop hA
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht.eventually (eventually_ge_atTop M))
  refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
  have hb : M ≤ A * x ^ (s - 1) := hbound ⟨hx, hxδ⟩
  have hexp : Real.exp (-x) ≤ Real.exp (-(s * x)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpow : 0 ≤ A * x ^ (s - 1) := by positivity
  calc
    M * gammaPDFReal 1 1 x = M * Real.exp (-x) := by simp [gammaPDFReal, hx.le]
    _ ≤ (A * x ^ (s - 1)) * Real.exp (-x) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ ≤ (A * x ^ (s - 1)) * Real.exp (-(s * x)) := mul_le_mul_of_nonneg_left hexp hpow
    _ = gammaPDFReal s s x := by simp [gammaPDFReal, hx.le, A]

theorem d028710 {e : ℝ} (he : 0 ≤ e) (a C x : ℝ) :
    0 ≤ _root_.GD.N0213.N0527.d028204 e a C x := by unfold _root_.GD.N0213.N0527.d028204; positivity

theorem d028711 {e a C δ x : ℝ}
    (he : 0 < e) (ha : 0 < a) (hC : 0 ≤ C) (hδ : 0 < δ) (hx : δ ≤ x) :
    _root_.GD.N0213.N0527.d028204 e a C x ≤ e * a ^ 2 / δ ^ 2 := by
  have hx0 : 0 ≤ x := hδ.le.trans hx
  have hd : δ ≤ x + e * a + e * C * x := by
    nlinarith [mul_nonneg (mul_nonneg he.le hC) hx0, mul_pos he ha]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ)
    (pow_le_pow_left₀ hδ.le hd 2)

theorem d028712 {s e a C : ℝ}
    (hs : 0 < s) (he : 0 < e) (ha : 0 < a) (hC : 0 ≤ C) :
    Integrable (fun x => gammaPDFReal s s x * _root_.GD.N0213.N0527.d028204 e a C x) := by
  apply ((_root_.GD.N0232.N0719.N0954.d009352 hs hs).mul_const (1 / e)).mono'
  · exact ((measurable_gammaPDFReal s s).mul (by unfold _root_.GD.N0213.N0527.d028204; fun_prop)).aestronglyMeasurable
  · apply ae_of_all
    intro x
    by_cases hx : 0 ≤ x
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gammaPDFReal_nonneg hs hs x)
        (_root_.GD.N0093.d028710 he.le _ _ _))]
      exact mul_le_mul_of_nonneg_left (_root_.GD.N0213.N0488.d028223 _ _ _ _ he ha hC hx)
        (gammaPDFReal_nonneg hs hs x)
    · simp [gammaPDFReal, hx]

theorem d028713 {s : ℝ} (hs : 0 < s) :
    (∫ x, gammaPDFReal s s x) = 1 := by
  letI := isProbabilityMeasure_gammaMeasure hs hs
  simpa using (_root_.GD.N0232.N0719.N0954.d009351 hs hs (fun _ => (1 : ℝ))).symm

theorem d028714 {s e a C M δ : ℝ}
    (hs : 0 < s) (he : 0 < e) (ha : 0 < a) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hlocal : ∀ x, 0 < x → x < δ → M * gammaPDFReal 1 1 x ≤ gammaPDFReal s s x) :
    M * (∫ x, _root_.GD.N0213.N0527.d028204 e a C x ∂gammaMeasure 1 1) ≤
      (∫ x, _root_.GD.N0213.N0527.d028204 e a C x ∂gammaMeasure s s) + M * e * a ^ 2 / δ ^ 2 := by
  have hi1 := _root_.GD.N0093.d028712 (by norm_num : (0 : ℝ) < 1) he ha hC
  have his := _root_.GD.N0093.d028712 hs he ha hC
  have hid := _root_.GD.N0232.N0719.N0954.d009352 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  have hp : ∀ᵐ x ∂(volume : Measure ℝ),
      M * (gammaPDFReal 1 1 x * _root_.GD.N0213.N0527.d028204 e a C x) ≤
        gammaPDFReal s s x * _root_.GD.N0213.N0527.d028204 e a C x +
        (M * e * a ^ 2 / δ ^ 2) * gammaPDFReal 1 1 x := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx0
    by_cases hx : 0 < x
    · by_cases hxδ : x < δ
      · have hb := mul_le_mul_of_nonneg_right (hlocal x hx hxδ) (_root_.GD.N0093.d028710 he.le a C x)
        have hn : 0 ≤ (M * e * a ^ 2 / δ ^ 2) * gammaPDFReal 1 1 x := by
          apply mul_nonneg (by positivity) (gammaPDFReal_nonneg (a := 1) (r := 1) (by norm_num) (by norm_num) x)
        nlinarith
      · have hb := mul_le_mul_of_nonneg_left
          (_root_.GD.N0093.d028711 he ha hC hδ (le_of_not_gt hxδ))
          (mul_nonneg hM (gammaPDFReal_nonneg (a := 1) (r := 1) (by norm_num) (by norm_num) x))
        have hn := mul_nonneg (gammaPDFReal_nonneg hs hs x) (_root_.GD.N0093.d028710 he.le a C x)
        have heq : M * gammaPDFReal 1 1 x * (e * a ^ 2 / δ ^ 2) =
            (M * e * a ^ 2 / δ ^ 2) * gammaPDFReal 1 1 x := by ring
        rw [heq] at hb
        nlinarith
    · have hxneg : x < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
      simp [gammaPDFReal, not_le.mpr hxneg]
  have hh := integral_mono_ae (hi1.const_mul M) (his.add (hid.const_mul (M * e * a ^ 2 / δ ^ 2))) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add his (hid.const_mul _), integral_const_mul, integral_const_mul,
    _root_.GD.N0093.d028713 (by norm_num : (0 : ℝ) < 1), mul_one] at hh
  simpa only [_root_.GD.N0232.N0719.N0954.d009351 (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1), _root_.GD.N0232.N0719.N0954.d009351 hs hs] using hh

theorem d028715 {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, _root_.GD.N0213.N0527.d028204 (e n) a C x ∂gammaMeasure s s) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let M : ℝ := (max b 0 + 1) / a
  have hM : 0 < M := div_pos (by positivity) ha
  obtain ⟨δ, hδ, hlocal⟩ := _root_.GD.N0093.d028709 hs hs1 M
  have ht : Tendsto (fun n => M * (∫ x, _root_.GD.N0213.N0527.d028204 (e n) a C x ∂gammaMeasure 1 1) -
      M * e n * a ^ 2 / δ ^ 2) atTop (𝓝 (M * a)) := by
    convert ((_root_.GD.N0213.N0527.d028214 a C ha hC e he he0).const_mul M).sub
      ((((he0.const_mul M).mul_const (a ^ 2)).div_const (δ ^ 2))) using 1; simp
  have hba : b < M * a := by dsimp [M]; rw [div_mul_cancel₀ _ ha.ne']; have := le_max_left b 0; linarith
  filter_upwards [ht.eventually (lt_mem_nhds hba)] with n hn
  have hb := _root_.GD.N0093.d028714 hs (he n) ha hC hM.le hδ hlocal
  linarith

#print axioms _root_.GD.N0093.d028709
#print axioms _root_.GD.N0093.d028714
#print axioms _root_.GD.N0093.d028715
end
end GD.N0093
