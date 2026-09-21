import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0106.N0428.N0770.N1744
noncomputable section


theorem d007145 {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (n : ℕ) :
    a ^ n * Real.exp (-(c * a)) ≤ (n.factorial : ℝ) / c ^ n := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (c * a) (mul_nonneg hc.le ha) n)
  have hexp : Real.exp (c * a) * Real.exp (-(c * a)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply (le_div_iff₀ (pow_pos hc n)).mpr
  calc
    (a ^ n * Real.exp (-(c * a))) * c ^ n =
        (c * a) ^ n * Real.exp (-(c * a)) := by rw [mul_pow]; ring
    _ ≤ (Real.exp (c * a) * (n.factorial : ℝ)) * Real.exp (-(c * a)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (n.factorial : ℝ) := by
      rw [mul_assoc, mul_comm (n.factorial : ℝ), ← mul_assoc, hexp, one_mul]

theorem d007146 {a c s : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) (hcs : c ≤ s) (n : ℕ) :
    a ^ n * Real.exp (-(s * a)) ≤ (n.factorial : ℝ) / c ^ n := by
  apply le_trans _ (_root_.GD.N0106.N0428.N0770.N1744.d007145 ha hc n)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha n)
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_right hcs ha)

theorem d007147 (a t : ℝ) (n : ℕ) :
    HasDerivAt (fun s : ℝ => a ^ n * Real.exp (-(s * a)))
      (-(a ^ (n + 1) * Real.exp (-(t * a)))) t := by
  convert! (((hasDerivAt_id t).mul_const a).neg.exp).const_mul (a ^ n) using 1
  simp only [id_eq, pow_succ, Pi.neg_apply]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {A : Ω → ℝ}


theorem d007148 (hA : Measurable A) (ha : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun ω => A ω ^ n * Real.exp (-(t * A ω))) μ := by
  apply (integrable_const ((n.factorial : ℝ) / t ^ n)).mono'
    (((hA.pow_const n).mul ((hA.const_mul t).neg.exp)).aestronglyMeasurable)
  filter_upwards [ha] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hω n) (Real.exp_pos _).le)]
  exact _root_.GD.N0106.N0428.N0770.N1744.d007145 hω ht n



theorem d007149 (hA : Measurable A) (ha : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => ∫ ω, A ω ^ n * Real.exp (-(s * A ω)) ∂μ)
      (-(∫ ω, A ω ^ (n + 1) * Real.exp (-(t * A ω)) ∂μ)) t := by
  have hc : 0 < t / 2 := by positivity
  have hs : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hm : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun ω => A ω ^ n * Real.exp (-(s * A ω))) μ := by
    filter_upwards with s
    exact ((hA.pow_const n).mul ((hA.const_mul s).neg.exp)).aestronglyMeasurable
  have hdm : AEStronglyMeasurable
      (fun ω => -(A ω ^ (n + 1) * Real.exp (-(t * A ω)))) μ :=
    (((hA.pow_const (n + 1)).mul ((hA.const_mul t).neg.exp)).neg).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂μ, ∀ s ∈ Ioi (t / 2),
      ‖-(A ω ^ (n + 1) * Real.exp (-(s * A ω)))‖ ≤
        ((n + 1).factorial : ℝ) / (t / 2) ^ (n + 1) := by
    filter_upwards [ha] with ω hω s hs'
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg hω _) (Real.exp_pos _).le)]
    exact _root_.GD.N0106.N0428.N0770.N1744.d007146 hω hc (le_of_lt hs') (n + 1)
  have hd : ∀ᵐ ω ∂μ, ∀ s ∈ Ioi (t / 2),
      HasDerivAt (fun u : ℝ => A ω ^ n * Real.exp (-(u * A ω)))
        (-(A ω ^ (n + 1) * Real.exp (-(s * A ω)))) s := by
    filter_upwards with ω s _
    exact _root_.GD.N0106.N0428.N0770.N1744.d007147 (A ω) s n
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm
    (_root_.GD.N0106.N0428.N0770.N1744.d007148 hA ha ht n) hdm hb (integrable_const _) hd).2
  simpa only [integral_neg] using h

theorem d007150 (hA : Measurable A) (ha : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ ω, Real.exp (-(s * A ω)) ∂μ)
      (-(∫ ω, A ω * Real.exp (-(t * A ω)) ∂μ)) t := by
  simpa only [pow_zero, one_mul, zero_add, pow_one] using
    _root_.GD.N0106.N0428.N0770.N1744.d007149 hA ha ht 0


theorem d007151 (hA : Measurable A) (ha : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => deriv (fun u : ℝ => ∫ ω, Real.exp (-(u * A ω)) ∂μ) s)
      (∫ ω, A ω ^ 2 * Real.exp (-(t * A ω)) ∂μ) t := by
  have h : HasDerivAt (fun s : ℝ => -(∫ ω, A ω * Real.exp (-(s * A ω)) ∂μ))
      (∫ ω, A ω ^ 2 * Real.exp (-(t * A ω)) ∂μ) t := by
    simpa only [pow_one, neg_neg, Nat.reduceAdd, Pi.neg_apply] using!
      (_root_.GD.N0106.N0428.N0770.N1744.d007149 hA ha ht 1).neg
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact (_root_.GD.N0106.N0428.N0770.N1744.d007150 hA ha hs).deriv

end
end GD.N0106.N0428.N0770.N1744

#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007145
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007148
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007149
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007150
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d007151
