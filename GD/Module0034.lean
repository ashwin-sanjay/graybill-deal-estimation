import Mathlib.MeasureTheory.Integral.Prod

















open MeasureTheory

namespace GD
namespace N0230
namespace N0658

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]



theorem d000405
    (mu : Measure Omega) (weight f g : Omega → ℝ)
    (hweightNonneg : 0 ≤ᵐ[mu] weight)
    (hfSq : Integrable (fun z ↦ weight z * f z ^ 2) mu)
    (hfg : Integrable (fun z ↦ weight z * (f z * g z)) mu)
    (hgSq : Integrable (fun z ↦ weight z * g z ^ 2) mu) :
    (∫ z, weight z * (f z * g z) ∂mu) ^ 2 ≤
      (∫ z, weight z * f z ^ 2 ∂mu) *
        ∫ z, weight z * g z ^ 2 ∂mu := by
  let A : ℝ := ∫ z, weight z * f z ^ 2 ∂mu
  let B : ℝ := ∫ z, weight z * (f z * g z) ∂mu
  let C : ℝ := ∫ z, weight z * g z ^ 2 ∂mu
  change B ^ 2 ≤ A * C
  have hA : 0 ≤ A := by
    dsimp [A]
    apply integral_nonneg_of_ae
    filter_upwards [hweightNonneg] with z hz
    exact mul_nonneg hz (sq_nonneg _)
  have hC : 0 ≤ C := by
    dsimp [C]
    apply integral_nonneg_of_ae
    filter_upwards [hweightNonneg] with z hz
    exact mul_nonneg hz (sq_nonneg _)
  by_cases hCzero : C = 0
  · have hweightedGSq :
        (fun z ↦ weight z * g z ^ 2) =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (by
          filter_upwards [hweightNonneg] with z hz
          exact mul_nonneg hz (sq_nonneg _)) hgSq).mp hCzero
    have hcrossZero :
        (fun z ↦ weight z * (f z * g z)) =ᵐ[mu] 0 := by
      filter_upwards [hweightedGSq] with z hz
      rcases mul_eq_zero.mp hz with hw | hg
      · simp [hw]
      · have hg0 : g z = 0 := sq_eq_zero_iff.mp hg
        simp [hg0]
    have hBzero : B = 0 := by
      dsimp [B]
      calc
        (∫ z, weight z * (f z * g z) ∂mu) =
            ∫ _z : Omega, (0 : ℝ) ∂mu := integral_congr_ae hcrossZero
        _ = 0 := by simp
    simp [hCzero, hBzero]
  · let a : ℝ := B / C
    have hcrossScaled : Integrable
        (fun z ↦ (2 * a) * (weight z * (f z * g z))) mu :=
      hfg.const_mul _
    have hgScaled : Integrable
        (fun z ↦ a ^ 2 * (weight z * g z ^ 2)) mu :=
      hgSq.const_mul _
    have hpoint :
        (fun z ↦ weight z * (f z - a * g z) ^ 2) =
          (fun z ↦
            weight z * f z ^ 2 -
              (2 * a) * (weight z * (f z * g z)) +
                a ^ 2 * (weight z * g z ^ 2)) := by
      funext z
      ring
    have hcenterNonneg :
        0 ≤ ∫ z, weight z * (f z - a * g z) ^ 2 ∂mu := by
      apply integral_nonneg_of_ae
      filter_upwards [hweightNonneg] with z hz
      exact mul_nonneg hz (sq_nonneg _)
    have hcenterExpansion :
        (∫ z, weight z * (f z - a * g z) ^ 2 ∂mu) =
          A - (2 * a) * B + a ^ 2 * C := by
      rw [hpoint]
      calc
        (∫ z,
            weight z * f z ^ 2 -
                (2 * a) * (weight z * (f z * g z)) +
              a ^ 2 * (weight z * g z ^ 2) ∂mu) =
            (∫ z,
              weight z * f z ^ 2 -
                (2 * a) * (weight z * (f z * g z)) ∂mu) +
              ∫ z, a ^ 2 * (weight z * g z ^ 2) ∂mu := by
                simpa only [Pi.add_apply, Pi.sub_apply] using
                  integral_add (hfSq.sub hcrossScaled) hgScaled
        _ = ((∫ z, weight z * f z ^ 2 ∂mu) -
              ∫ z, (2 * a) * (weight z * (f z * g z)) ∂mu) +
              ∫ z, a ^ 2 * (weight z * g z ^ 2) ∂mu := by
                rw [integral_sub hfSq hcrossScaled]
        _ = A - (2 * a) * B + a ^ 2 * C := by
              rw [integral_const_mul, integral_const_mul]
    rw [hcenterExpansion] at hcenterNonneg
    have hBC : B = a * C := by
      dsimp [a]
      field_simp [hCzero]
    have hscaled := mul_nonneg hC hcenterNonneg
    nlinarith

end

end N0658
end N0230
end GD

#print axioms _root_.GD.N0230.N0658.d000405
