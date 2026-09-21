import GD.Module1799








set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0393

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p q : Ω → ℝ}

theorem d029959 (hp : Integrable p μ) (hq : Integrable q μ) :
    Integrable (fun x => min (p x) (q x)) μ := hp.inf hq


theorem d029960 (g : Ω → ℝ) (a b : ℝ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpa : Integrable (fun x => p x * (g x - a) ^ 2) μ)
    (hqb : Integrable (fun x => q x * (g x - b) ^ 2) μ) :
    (∫ x, min (p x) (q x) ∂μ) * (a - b) ^ 2 / 2 ≤
      (∫ x, p x * (g x - a) ^ 2 ∂μ) +
        (∫ x, q x * (g x - b) ^ 2 ∂μ) := by
  have hpoint : (fun x => min (p x) (q x) * ((a - b) ^ 2 / 2)) ≤ᵐ[μ]
      (fun x => p x * (g x - a) ^ 2 + q x * (g x - b) ^ 2) := by
    filter_upwards [hp0, hq0] with x hpx hqx
    simpa only [mul_div_assoc] using
      _root_.GD.N0101.N0418.d029957 (le_min hpx hqx)
        (min_le_left (p x) (q x)) (min_le_right (p x) (q x)) (g x) a b
  have h := integral_mono_ae ((_root_.GD.N0101.N0393.d029959 hp hq).mul_const _)
    (hpa.add hqb) hpoint
  simp only [Pi.add_apply] at h
  simpa only [integral_mul_const, integral_add hpa hqb, mul_div_assoc] using h


theorem d029961 (hμ : μ ≠ 0)
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 < p x) (hq0 : ∀ᵐ x ∂μ, 0 < q x) :
    0 < ∫ x, min (p x) (q x) ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ] (fun x => min (p x) (q x)) := by
    filter_upwards [hp0, hq0] with x hpx hqx
    exact le_min hpx.le hqx.le
  by_contra hnot
  have hz : (∫ x, min (p x) (q x) ∂μ) = 0 :=
    le_antisymm (le_of_not_gt hnot) (integral_nonneg_of_ae hnonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg (_root_.GD.N0101.N0393.d029959 hp hq)).mp hz
  haveI := ae_neBot.mpr hμ
  obtain ⟨x, hpx, hqx, hxzero⟩ := (hp0.and (hq0.and hzero)).exists
  exact (lt_min hpx hqx).ne' hxzero


theorem d029962 (hp : Integrable p μ) (hq : Integrable q μ)
    (hpnorm : (∫ x, p x ∂μ) = 1) :
    (∫ x, min (p x) (q x) ∂μ) ≤ 1 := by
  rw [← hpnorm]
  exact integral_mono (_root_.GD.N0101.N0393.d029959 hp hq) hp (fun x => min_le_left _ _)



theorem d029963 (hp : Integrable p μ) (hq : Integrable q μ)
    (hpnorm : (∫ x, p x ∂μ) = 1) (hqnorm : (∫ x, q x ∂μ) = 1) :
    (∫ x, min (p x) (q x) ∂μ) = 1 - (∫ x, |p x - q x| ∂μ) / 2 := by
  have hmin : (fun x => min (p x) (q x)) =
      (fun x => (p x + q x - |p x - q x|) / 2) := by
    funext x
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hsum : Integrable (fun x => p x + q x) μ := hp.add hq
  have habs : Integrable (fun x => |p x - q x|) μ := (hp.sub hq).abs
  rw [hmin, integral_div, integral_sub hsum habs,
    integral_add hp hq, hpnorm, hqnorm]
  ring

end
end GD.N0101.N0393

#print axioms _root_.GD.N0101.N0393.d029959
#print axioms _root_.GD.N0101.N0393.d029960
#print axioms _root_.GD.N0101.N0393.d029961
#print axioms _root_.GD.N0101.N0393.d029962
#print axioms _root_.GD.N0101.N0393.d029963
