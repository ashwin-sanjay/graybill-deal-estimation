import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0418

noncomputable section


theorem d029956 (x a b : ℝ) :
    (a - b) ^ 2 / 2 ≤ (x - a) ^ 2 + (x - b) ^ 2 := by
  nlinarith [sq_nonneg (2 * x - a - b)]


theorem d029957 {A B c : ℝ} (hc : 0 ≤ c)
    (hA : c ≤ A) (hB : c ≤ B) (x a b : ℝ) :
    c * (a - b) ^ 2 / 2 ≤ A * (x - a) ^ 2 + B * (x - b) ^ 2 := by
  have hsep := mul_le_mul_of_nonneg_left (_root_.GD.N0101.N0418.d029956 x a b) hc
  have hfirst := mul_le_mul_of_nonneg_right hA (sq_nonneg (x - a))
  have hsecond := mul_le_mul_of_nonneg_right hB (sq_nonneg (x - b))
  nlinarith




theorem d029958
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Set Ω) (hS : MeasurableSet S) (hfinite : μ S ≠ ⊤)
    (p q g : Ω → ℝ) (a b : ℝ)
    (hp : 0 ≤ᵐ[μ] p) (hq : 0 ≤ᵐ[μ] q)
    (hip : Integrable (fun z => p z * (g z - a) ^ 2) μ)
    (hiq : Integrable (fun z => q z * (g z - b) ^ 2) μ)
    {wp wq c : ℝ} (hwp : 0 ≤ wp) (hwq : 0 ≤ wq) (hc : 0 ≤ c)
    (hlowerp : ∀ z ∈ S, c ≤ wp * p z)
    (hlowerq : ∀ z ∈ S, c ≤ wq * q z) :
    μ.real S * (c * (a - b) ^ 2 / 2) ≤
      wp * (∫ z, p z * (g z - a) ^ 2 ∂μ) +
      wq * (∫ z, q z * (g z - b) ^ 2 ∂μ) := by
  let F : Ω → ℝ := fun z =>
    wp * (p z * (g z - a) ^ 2) + wq * (q z * (g z - b) ^ 2)
  have hi : Integrable F μ := (hip.const_mul wp).add (hiq.const_mul wq)
  have hnonneg : 0 ≤ᵐ[μ] F := by
    filter_upwards [hp, hq] with z hpz hqz
    exact add_nonneg (mul_nonneg hwp (mul_nonneg hpz (sq_nonneg _)))
      (mul_nonneg hwq (mul_nonneg hqz (sq_nonneg _)))
  have hpoint : ∀ z ∈ S, c * (a - b) ^ 2 / 2 ≤ F z := by
    intro z hz
    simpa only [F, mul_assoc] using
      _root_.GD.N0101.N0418.d029957 hc (hlowerp z hz) (hlowerq z hz) (g z) a b
  have hbound := setIntegral_mono_on
    (integrableOn_const hfinite : IntegrableOn (fun _ : Ω => c * (a - b) ^ 2 / 2) S μ)
    hi.integrableOn hS hpoint
  rw [setIntegral_const, smul_eq_mul] at hbound
  have htotal := hbound.trans (setIntegral_le_integral hi hnonneg)
  simpa only [F, integral_add (hip.const_mul wp) (hiq.const_mul wq),
    integral_const_mul] using htotal

end
end GD.N0101.N0418

#print axioms _root_.GD.N0101.N0418.d029956
#print axioms _root_.GD.N0101.N0418.d029957
#print axioms _root_.GD.N0101.N0418.d029958
