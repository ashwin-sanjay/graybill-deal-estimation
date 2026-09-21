





























import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import GD.Module0078

namespace GD
namespace N0230
namespace N0641

open MeasureTheory
open scoped ENNReal
open _root_.GD.N0230.N0690
open _root_.GD.N0230.N0694





theorem d001049
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → Ω) (hg : Measurable g) (w : Ω → ℝ≥0∞) (hw : Measurable w)
    (hmap : μ.map g = μ.withDensity w)
    (hw0 : ∀ᵐ ω ∂μ, w ω ≠ 0) (hwtop : ∀ᵐ ω ∂μ, w ω ≠ ∞)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (g ω) * (w (g ω))⁻¹ ∂μ = ∫⁻ ω, F ω ∂μ := by
  have hFw : Measurable fun ω => F ω * (w ω)⁻¹ := hF.mul hw.inv
  have h1 : ∫⁻ ω, F (g ω) * (w (g ω))⁻¹ ∂μ
      = ∫⁻ ω, F ω * (w ω)⁻¹ ∂(μ.map g) := (lintegral_map hFw hg).symm
  rw [h1, hmap, lintegral_withDensity_eq_lintegral_mul μ hw hFw]
  refine lintegral_congr_ae ?_
  filter_upwards [hw0, hwtop] with ω h0 htop
  show w ω * (F ω * (w ω)⁻¹) = F ω
  rw [mul_comm (F ω), ← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]



theorem d001050
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → Ω) (hg : Measurable g) (w : Ω → ℝ≥0∞) (hw : Measurable w)
    (hmap : μ.map g = μ.withDensity w)
    (hw0 : ∀ᵐ ω ∂μ, w ω ≠ 0) (hwtop : ∀ᵐ ω ∂μ, w ω ≠ ∞)
    (d : Ω → ℝ) (hd : Measurable d) (c : ℝ) :
    ∫⁻ ω, ENNReal.ofReal ((d (g ω) - c) ^ 2) * (w (g ω))⁻¹ ∂μ
      = ∫⁻ ω, ENNReal.ofReal ((d ω - c) ^ 2) ∂μ :=
  _root_.GD.N0230.N0641.d001049 μ g hg w hw hmap hw0 hwtop _
    (ENNReal.measurable_ofReal.comp ((hd.sub measurable_const).pow_const 2))





theorem d001051
    {E E' : Type*} [PseudoMetricSpace E] [PseudoMetricSpace E']
    (Φ : E → E') (Ψ : E' → E) (hΨΦ : ∀ x, Ψ (Φ x) = x)
    {KΦ KΨ : ℝ} (hKΨ : 0 ≤ KΨ)
    (hΦ : ∀ x y, dist (Φ x) (Φ y) ≤ KΦ * dist x y)
    (hΨ : ∀ x y, dist (Ψ x) (Ψ y) ≤ KΨ * dist x y)
    (U : E → E) {L' : ℝ} (hL'nn : 0 ≤ L')
    (hL' : ∀ x y, dist (Φ (U (Ψ x))) (Φ (U (Ψ y))) ≤ L' * dist x y) :
    ∀ x y, dist (U x) (U y) ≤ KΨ * L' * KΦ * dist x y := by
  intro x y
  have e1 : U x = Ψ (Φ (U (Ψ (Φ x)))) := by rw [hΨΦ, hΨΦ]
  have e2 : U y = Ψ (Φ (U (Ψ (Φ y)))) := by rw [hΨΦ, hΨΦ]
  calc dist (U x) (U y)
      = dist (Ψ (Φ (U (Ψ (Φ x))))) (Ψ (Φ (U (Ψ (Φ y))))) := by rw [← e1, ← e2]
    _ ≤ KΨ * dist (Φ (U (Ψ (Φ x)))) (Φ (U (Ψ (Φ y)))) := hΨ _ _
    _ ≤ KΨ * (L' * dist (Φ x) (Φ y)) :=
        mul_le_mul_of_nonneg_left (hL' (Φ x) (Φ y)) hKΨ
    _ ≤ KΨ * (L' * (KΦ * dist x y)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hΦ x y) hL'nn) hKΨ
    _ = KΨ * L' * KΦ * dist x y := by ring




theorem d001052 {E' : Type*} [PseudoMetricSpace E']
    (Φ : lp (fun _ : ℤ => ℝ) 2 → E') (Ψ : E' → lp (fun _ : ℤ => ℝ) 2)
    (hΨΦ : ∀ x, Ψ (Φ x) = x)
    {KΦ KΨ : ℝ} (hKΦ : 0 ≤ KΦ) (hKΨ : 0 ≤ KΨ)
    (hΦ : ∀ x y, dist (Φ x) (Φ y) ≤ KΦ * dist x y)
    (hΨ : ∀ x y, dist (Ψ x) (Ψ y) ≤ KΨ * dist x y)
    (a : ℝ) (k : ℤ) {L' : ℝ} (hL'nn : 0 ≤ L')
    (hL' : ∀ x y, dist (Φ (_root_.GD.N0230.N0694.d001000 (-k) (Ψ x))) (Φ (_root_.GD.N0230.N0694.d001000 (-k) (Ψ y)))
      ≤ L' * dist x y) :
    |a| ≤ KΦ * KΨ ^ 2 *
      (L' * dist (Φ (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008))) (Φ _root_.GD.N0230.N0694.d000992)) := by
  have hadm := _root_.GD.N0230.N0641.d001051 Φ Ψ hΨΦ hKΨ hΦ hΨ (_root_.GD.N0230.N0694.d001000 (-k)) hL'nn hL'
  have h1 := _root_.GD.N0230.N0690.d001044 a k hadm
  have h2 : dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992
      ≤ KΨ * dist (Φ (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008))) (Φ _root_.GD.N0230.N0694.d000992) := by
    have h := hΨ (Φ (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008))) (Φ _root_.GD.N0230.N0694.d000992)
    rwa [hΨΦ, hΨΦ] at h
  have hnn : 0 ≤ KΨ * L' * KΦ := mul_nonneg (mul_nonneg hKΨ hL'nn) hKΦ
  calc |a| ≤ KΨ * L' * KΦ * dist (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008)) _root_.GD.N0230.N0694.d000992 := h1
    _ ≤ KΨ * L' * KΦ *
        (KΨ * dist (Φ (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008))) (Φ _root_.GD.N0230.N0694.d000992)) :=
        mul_le_mul_of_nonneg_left h2 hnn
    _ = KΦ * KΨ ^ 2 *
        (L' * dist (Φ (_root_.GD.N0230.N0694.d001000 k (_root_.GD.N0230.N0694.d000992 + a • _root_.GD.N0230.N0694.d001008))) (Φ _root_.GD.N0230.N0694.d000992)) := by ring



#print axioms _root_.GD.N0230.N0641.d001049
#print axioms _root_.GD.N0230.N0641.d001050
#print axioms _root_.GD.N0230.N0641.d001051
#print axioms _root_.GD.N0230.N0641.d001052

end N0641
end N0230
end GD
