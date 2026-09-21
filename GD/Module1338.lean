import GD.Module1336
import GD.Module1335

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0101.N0375
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0101.N0387 _root_.GD.N0101.N0386



theorem d021723 {u s H R a δ ε c : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) (hH : 0 < H) (hHR : H ≤ R)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδu : δ ≤ u) (he : ε < 1) (hc : 1 ≤ c)
    (hec : ε ≤ δ * (c - 1)) (haH : s * a ≤ H) (hRs : R ≤ s * ε) :
    _root_.GD.N0101.N0387.d021709 u * ((1 - ε) ^ 2 * c ^ (-(5 / 2 : ℝ))) *
        (2 / (3 * u) - (2 / 3 : ℝ) * H ^ (3 / 2 : ℝ) * δ ^ (-(5 / 2 : ℝ)) - 1 / R) ≤
      s * ∫ t in Ioo a ε, _root_.GD.N0101.N0387.d021710 u s t := by
  exact (mul_le_mul_of_nonneg_left
    (_root_.GD.N0101.N0386.d021708 hδ hδu hH hHR)
    (mul_nonneg (_root_.GD.N0101.N0387.d021711 hu).le
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hc) _)))).trans
    (_root_.GD.N0101.N0387.d021716 hu hs hH hHR ha hδu he hc hec haH hRs)



theorem d021724 (g : ℝ) {t ε : ℝ} (hte : t ≤ ε) :
    (max 0 (g - ε)) ^ 2 ≤ (g - t) ^ 2 := by
  by_cases hg : g ≤ ε
  · rw [max_eq_left (sub_nonpos.mpr hg)]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (g - t)
  · rw [max_eq_right (by linarith : 0 ≤ g - ε)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hte)
      (show 0 ≤ 2 * g - t - ε by linarith)]

theorem d021725 (g : ℝ) {t ε : ℝ} (hte : t ≤ ε) :
    (max 0 (1 - g - ε)) ^ 2 ≤ (g - (1 - t)) ^ 2 := by
  have h := _root_.GD.N0101.N0375.d021724 (1 - g) hte
  nlinarith



theorem d021726 (g : ℝ) {u ε : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (he : ε ≤ 1 / 2) :
    (1 - 2 * ε) ^ 2 ≤
      (max 0 (g - ε)) ^ 2 / u + (max 0 (1 - g - ε)) ^ 2 / (1 - u) := by
  let A := max 0 (g - ε)
  let B := max 0 (1 - g - ε)
  have hA : 0 ≤ A := le_max_left _ _
  have hB : 0 ≤ B := le_max_left _ _
  have hsum : 1 - 2 * ε ≤ A + B := by
    have ha : g - ε ≤ A := le_max_right _ _
    have hb : 1 - g - ε ≤ B := le_max_right _ _
    linarith
  have hD : 0 ≤ 1 - 2 * ε := by linarith
  have hsq : (1 - 2 * ε) ^ 2 ≤ (A + B) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsum)
      (add_nonneg (add_nonneg hA hB) hD)]
  have hid : A ^ 2 / u + B ^ 2 / (1 - u) - (A + B) ^ 2 =
      ((1 - u) * A - u * B) ^ 2 / (u * (1 - u)) := by
    field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne']
    ring
  have hnon := div_nonneg (sq_nonneg ((1 - u) * A - u * B))
    (mul_pos hu.1 (sub_pos.mpr hu.2)).le
  change _ ≤ A ^ 2 / u + B ^ 2 / (1 - u)
  linarith

end
end GD.N0101.N0375

#print axioms _root_.GD.N0101.N0375.d021723
#print axioms _root_.GD.N0101.N0375.d021724
#print axioms _root_.GD.N0101.N0375.d021725
#print axioms _root_.GD.N0101.N0375.d021726
