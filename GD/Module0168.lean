import Mathlib

set_option warningAsError true
set_option autoImplicit false



















namespace GD.N0232.N0720.N1231

noncomputable section

open MeasureTheory




theorem d001989
    {e rho phi psi K : ℝ}
    (hrho : 0 < rho) (hK : 0 < K)
    (hpsi : psi ^ 2 ≤ K * phi) :
    2 * (e * psi) ≤ K * (e ^ 2 / rho) + rho * phi := by
  have hKrho : 0 < K * rho := mul_pos hK hrho
  have hsquare : 0 ≤ (K * e - rho * psi) ^ 2 := sq_nonneg _
  have hyoung :
      2 * (e * psi) ≤ K * (e ^ 2 / rho) + rho * (psi ^ 2 / K) := by
    field_simp [hrho.ne', hK.ne']
    nlinarith
  have habsorb : rho * (psi ^ 2 / K) ≤ rho * phi := by
    apply mul_le_mul_of_nonneg_left _ hrho.le
    exact (div_le_iff₀ hK).2 (by simpa [mul_comm] using hpsi)
  exact hyoung.trans (by gcongr)

section Integral

variable {X : Type*} [MeasurableSpace X]
variable {mu : Measure X}








theorem d001990
    {e rho phi psi : X → ℝ} {K : ℝ}
    (hK : 0 < K)
    (hrho : ∀ x, 0 < rho x)
    (hpsi : ∀ x, (psi x) ^ 2 ≤ K * phi x)
    (hErrorTest : Integrable (fun x ↦ e x * psi x) mu)
    (hEnergy : Integrable (fun x ↦ (e x) ^ 2 / rho x) mu)
    (hMass : Integrable (fun x ↦ rho x * phi x) mu)
    (hDistribution :
      ∫ x, rho x * phi x ∂mu = ∫ x, e x * psi x ∂mu) :
    (∫ x, rho x * phi x ∂mu) / K ≤
      ∫ x, (e x) ^ 2 / rho x ∂mu := by
  have hPointwise : ∀ x,
      2 * (e x * psi x) ≤
        K * ((e x) ^ 2 / rho x) + rho x * phi x :=
    fun x ↦ _root_.GD.N0232.N0720.N1231.d001989 (hrho x) hK (hpsi x)
  have hLeft : Integrable (fun x ↦ 2 * (e x * psi x)) mu :=
    hErrorTest.const_mul 2
  have hRight : Integrable
      (fun x ↦ K * ((e x) ^ 2 / rho x) + rho x * phi x) mu :=
    (hEnergy.const_mul K).add hMass
  have hIntegrated := integral_mono hLeft hRight hPointwise
  rw [integral_const_mul 2 (fun x ↦ e x * psi x),
    integral_add (hEnergy.const_mul K) hMass,
    integral_const_mul K (fun x ↦ (e x) ^ 2 / rho x),
    ← hDistribution] at hIntegrated
  exact (div_le_iff₀ hK).2 (by linarith)



theorem d001991
    {e rho rhoAnchor phi psi : X → ℝ} {K anchorMass : ℝ}
    (hK : 0 < K)
    (hrho : ∀ x, 0 < rho x)
    (hAnchor : ∀ x, rhoAnchor x ≤ rho x)
    (hphi : ∀ x, 0 ≤ phi x)
    (hpsi : ∀ x, (psi x) ^ 2 ≤ K * phi x)
    (hErrorTest : Integrable (fun x ↦ e x * psi x) mu)
    (hEnergy : Integrable (fun x ↦ (e x) ^ 2 / rho x) mu)
    (hMass : Integrable (fun x ↦ rho x * phi x) mu)
    (hAnchorMass : Integrable (fun x ↦ rhoAnchor x * phi x) mu)
    (hDistribution :
      ∫ x, rho x * phi x ∂mu = ∫ x, e x * psi x ∂mu)
    (hAnchorLower : anchorMass ≤ ∫ x, rhoAnchor x * phi x ∂mu) :
    anchorMass / K ≤ ∫ x, (e x) ^ 2 / rho x ∂mu := by
  have hMixtureMass :
      ∫ x, rhoAnchor x * phi x ∂mu ≤
        ∫ x, rho x * phi x ∂mu := by
    apply integral_mono hAnchorMass hMass
    intro x
    exact mul_le_mul_of_nonneg_right (hAnchor x) (hphi x)
  calc
    anchorMass / K
        ≤ (∫ x, rhoAnchor x * phi x ∂mu) / K :=
          div_le_div_of_nonneg_right hAnchorLower hK.le
    _ ≤ (∫ x, rho x * phi x ∂mu) / K :=
          div_le_div_of_nonneg_right hMixtureMass hK.le
    _ ≤ ∫ x, (e x) ^ 2 / rho x ∂mu :=
      _root_.GD.N0232.N0720.N1231.d001990 hK hrho hpsi hErrorTest
        hEnergy hMass hDistribution

end Integral

end

end GD.N0232.N0720.N1231

#print axioms _root_.GD.N0232.N0720.N1231.d001989
#print axioms _root_.GD.N0232.N0720.N1231.d001990
#print axioms _root_.GD.N0232.N0720.N1231.d001991
