import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0015
noncomputable section

theorem d005022 : (fun z : ℝ => z ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 0 < z ^ 2
    exact sq_pos_of_pos hz
  · intro hs
    exact ⟨Real.sqrt s, Real.sqrt_pos.mpr hs, Real.sq_sqrt hs.le⟩



theorem d005023 (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioi (0 : ℝ), f s) =
      ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (2 * z) * f (z ^ 2) := by
  have hd : ∀ z ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z : ℝ => z ^ 2) (2 * z) (Ioi (0 : ℝ)) z := by
    intro z _
    simpa using (hasDerivAt_pow 2 z).hasDerivWithinAt (s := Ioi (0 : ℝ))
  have hm : MonotoneOn (fun z : ℝ => z ^ 2) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    exact (sq_le_sq₀ hx.le hy.le).mpr hxy
  have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioi hd hm f
  rwa [_root_.GD.N0015.d005022] at h



theorem d005024 (f : ℝ → ℝ≥0∞) (w : ℝ → ℝ) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (w s) * f s) =
      ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal ((2 * z) * w (z ^ 2)) * f (z ^ 2) := by
  rw [_root_.GD.N0015.d005023]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hz.le), mul_assoc]

theorem d005025 (f : ℝ → ℝ) :
    (∫ s in Ioi (0 : ℝ), f s) = ∫ z in Ioi (0 : ℝ), (2 * z) * f (z ^ 2) := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    smul_eq_mul] using
      (integral_comp_rpow_Ioi_of_pos (g := f) (p := (2 : ℝ)) (by norm_num)).symm

theorem d005026 (f : ℝ → ℝ) :
    IntegrableOn (fun z => (2 * z) * f (z ^ 2)) (Ioi (0 : ℝ)) ↔
      IntegrableOn f (Ioi (0 : ℝ)) := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one, Real.rpow_two, smul_eq_mul] using
      (integrableOn_Ioi_comp_rpow_iff f (p := (2 : ℝ)) (by norm_num))

theorem d005027 (f w : ℝ → ℝ) :
    (∫ s in Ioi (0 : ℝ), w s * f s) =
      ∫ z in Ioi (0 : ℝ), ((2 * z) * w (z ^ 2)) * f (z ^ 2) := by
  simpa only [mul_assoc] using _root_.GD.N0015.d005025 (fun s => w s * f s)

theorem d005028 (S : Set ℝ) (f : ℝ → ℝ → ℝ≥0∞) :
    (∫⁻ u in S, ∫⁻ s in Ioi (0 : ℝ), f u s) =
      ∫⁻ u in S, ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (2 * z) * f u (z ^ 2) := by
  apply lintegral_congr
  intro u
  exact _root_.GD.N0015.d005023 (f u)

theorem d005029 (S : Set ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ u in S, ∫ s in Ioi (0 : ℝ), f u s) =
      ∫ u in S, ∫ z in Ioi (0 : ℝ), (2 * z) * f u (z ^ 2) := by
  apply integral_congr_ae
  exact ae_of_all _ (fun u => _root_.GD.N0015.d005025 (f u))

end
end GD.N0015

#print axioms _root_.GD.N0015.d005022
#print axioms _root_.GD.N0015.d005023
#print axioms _root_.GD.N0015.d005024
#print axioms _root_.GD.N0015.d005025
#print axioms _root_.GD.N0015.d005026
#print axioms _root_.GD.N0015.d005027
#print axioms _root_.GD.N0015.d005028
#print axioms _root_.GD.N0015.d005029
