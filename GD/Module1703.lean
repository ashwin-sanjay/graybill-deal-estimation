import GD.Module1696

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0101.N0410
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072 _root_.GD.N0101.N0411



theorem d028603 (n s : ℕ) (hs : 3 ≤ s) :
    ∃ ρ : ℝ, ρ < 1 ∧
      (∀ i : Fin (n + 1), 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 (fun _ => s) i) ∧
      (∑ i : Fin (n + 1), (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 (fun _ => s) i)) = 1 := by
  let a : ℝ := ((s - 1 : ℕ) : ℝ) / 2
  let K : ℝ := n + 1
  have ha : 1 ≤ a := by
    have hsR : (2 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ s - 1 by omega)
    dsimp [a]
    linarith
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨(K - 1) / (K * a), ?_, ?_, ?_⟩
  · apply (div_lt_one (mul_pos hK ha0)).mpr
    have hh : K ≤ K * a := by nlinarith
    linarith
  · intro i
    have heq : 1 - (K - 1) / (K * a) * _root_.GD.N0232.N0719.N0954.d009355 (fun _ => s) i = K⁻¹ := by
      change 1 - (K - 1) / (K * a) * a = K⁻¹
      field_simp [hK.ne', ha0.ne']
      ring
    rw [heq]
    exact inv_pos.mpr hK
  · have heq (i : Fin (n + 1)) :
        1 - (K - 1) / (K * a) * _root_.GD.N0232.N0719.N0954.d009355 (fun _ => s) i = K⁻¹ := by
      change 1 - (K - 1) / (K * a) * a = K⁻¹
      field_simp [hK.ne', ha0.ne']
      ring
    simp_rw [heq]
    simp [K, hK.ne']




theorem d028604 (n s : ℕ) (hs : 3 ≤ s) :
    ¬ ∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0072.d023291 (fun _ => s) w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) (fun _ => s))) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0072.d023291 (fun _ => s) w) <
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) (fun _ => s)) := by
  obtain ⟨ρ, hρ, hα, hsum⟩ := _root_.GD.N0101.N0410.d028603 n s hs
  exact _root_.GD.N0101.N0411.d028565 (fun _ => s) (fun _ => hs)
    ρ hρ hα hsum

end
end GD.N0101.N0410

#print axioms _root_.GD.N0101.N0410.d028603
#print axioms _root_.GD.N0101.N0410.d028604
