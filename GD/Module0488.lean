import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic








set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0938
noncomputable section

variable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]

def d007527 (e B : ℝ) : ℝ := (1 + e * B)⁻¹ ^ 2

def d007528 (e B q : ℝ) : ℝ := e * q ^ 2 / (1 + e * B) ^ 2


theorem d007529 {e B q : ℝ}
    (he : 0 ≤ e) (hq : 0 ≤ q) (hqB : q ≤ B) :
    _root_.GD.N0232.N0719.N0938.d007528 e B q ≤ q / 4 := by
  have hB : 0 ≤ B := hq.trans hqB
  have hd : 0 < (1 + e * B) ^ 2 := sq_pos_of_pos (by positivity)
  rw [_root_.GD.N0232.N0719.N0938.d007528, div_le_iff₀ hd]
  have hden : (1 + e * q) ^ 2 ≤ (1 + e * B) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    gcongr
  have hsq := sq_nonneg (1 - e * q)
  have hmul := mul_le_mul_of_nonneg_left hden hq
  nlinarith


def d007530 (e : ℝ) (q : I → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, q i) + ∑ i, _root_.GD.N0232.N0719.N0938.d007528 e (∑ j, q j) (q i)

theorem d007531 {e : ℝ} (he : 0 ≤ e) (q : I → ℝ) : 0 ≤ _root_.GD.N0232.N0719.N0938.d007530 e q := by
  unfold _root_.GD.N0232.N0719.N0938.d007530 _root_.GD.N0232.N0719.N0938.d007527 _root_.GD.N0232.N0719.N0938.d007528
  positivity

theorem d007532 {e : ℝ} (he : 0 ≤ e)
    (q : I → ℝ) (hq : ∀ i, 0 ≤ q i) :
    _root_.GD.N0232.N0719.N0938.d007530 e q ≤ 1 + (∑ i, q i) / 4 := by
  have hB : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => hq i
  have hret : _root_.GD.N0232.N0719.N0938.d007527 e (∑ i, q i) ≤ 1 := by
    unfold _root_.GD.N0232.N0719.N0938.d007527
    have hden : 1 ≤ 1 + e * ∑ i, q i := le_add_of_nonneg_right (mul_nonneg he hB)
    have hi : 0 ≤ (1 + e * ∑ i, q i)⁻¹ := by positivity
    have hi1 : (1 + e * ∑ i, q i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
    nlinarith
  calc
    _root_.GD.N0232.N0719.N0938.d007530 e q ≤ 1 + ∑ i, q i / 4 := add_le_add hret (Finset.sum_le_sum fun i _ =>
      _root_.GD.N0232.N0719.N0938.d007529 he (hq i)
        (Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i)))
    _ = _ := by rw [Finset.sum_div]

theorem d007533 (q : I → ℝ) (e : ℕ → ℝ)
    (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0938.d007530 (e n) q) atTop (𝓝 1) := by
  have hd : Tendsto (fun n => 1 + e n * ∑ i, q i) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (he0.mul_const (∑ i, q i))
  have hr : Tendsto (fun n => _root_.GD.N0232.N0719.N0938.d007527 (e n) (∑ i, q i)) atTop (𝓝 1) := by
    simpa [_root_.GD.N0232.N0719.N0938.d007527] using (hd.inv₀ one_ne_zero).pow 2
  have hi (i : I) : Tendsto (fun n => _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ j, q j) (q i))
      atTop (𝓝 0) := by
    have h := (he0.mul_const (q i ^ 2)).div (hd.pow 2) (by norm_num)
    convert h using 1
    · rfl
    · norm_num
  simpa [_root_.GD.N0232.N0719.N0938.d007530] using hr.add (tendsto_finsetSum Finset.univ fun i _ => hi i)



theorem d007534 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → Ω → ℝ) (hqm : ∀ i, Measurable (q i))
    (hq : ∀ᵐ x ∂μ, ∀ i, 0 ≤ q i x) (hqi : ∀ i, Integrable (q i) μ)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, _root_.GD.N0232.N0719.N0938.d007530 (e n) (fun i => q i x) ∂μ) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n => ∫ x, _root_.GD.N0232.N0719.N0938.d007530 (e n) (fun i => q i x) ∂μ)
      atTop (𝓝 (∫ _x, (1 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 1 + (∑ i, q i x) / 4)
    · intro n
      have hm : Measurable (fun x => ∑ i, q i x) := Finset.measurable_sum _ fun i _ => hqm i
      unfold _root_.GD.N0232.N0719.N0938.d007530 _root_.GD.N0232.N0719.N0938.d007527 _root_.GD.N0232.N0719.N0938.d007528
      fun_prop
    · exact (integrable_const 1).add ((integrable_finsetSum _ fun i _ => hqi i).div_const 4)
    · intro n
      filter_upwards [hq] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0719.N0938.d007531 (he n) _)]
      exact _root_.GD.N0232.N0719.N0938.d007532 (he n) _ hx
    · exact ae_of_all _ fun x => _root_.GD.N0232.N0719.N0938.d007533 (fun i => q i x) e he0
  simpa using hlim

end
end GD.N0232.N0719.N0938

#print axioms _root_.GD.N0232.N0719.N0938.d007529
#print axioms _root_.GD.N0232.N0719.N0938.d007532
#print axioms _root_.GD.N0232.N0719.N0938.d007534
