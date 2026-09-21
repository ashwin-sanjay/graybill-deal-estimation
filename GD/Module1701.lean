import GD.Module1700
import GD.Module1502

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0149.N0435
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0101.N0411
open _root_.GD.N0225.N0538
open _root_.GD.N0225.N0537
open _root_.GD.N0149.N0434

variable {n : ℕ}

theorem d028597
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) :
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 (n + 1), w =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 (n + 1) sizes θ.scale] _root_.GD.N0021.d023313 := by
  have hadm := _root_.GD.N0149.N0434.d028591 sizes hn ρ hρ hα hsum
  rw [_root_.GD.N0021.d023315] at hadm hweak
  exact _root_.GD.N0225.N0537.d023471 sizes hn _root_.GD.N0021.d023313 w
    _root_.GD.N0021.d023314 hw (_root_.GD.N0101.N0411.d028560 (Nat.succ_pos _)) hunit
    (_root_.GD.N0225.N0538.d023463 sizes hn _root_.GD.N0021.d023313 _root_.GD.N0021.d023314
      (_root_.GD.N0101.N0411.d028560 (Nat.succ_pos _)) (_root_.GD.N0101.N0411.d028561 (Nat.succ_pos _))).2
    hadm hweak

theorem d028598
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) :
    ∀ θ, _root_.GD.N0072.d023291 sizes w =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 (n + 1) sizes θ]
      _root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes := by
  intro θ
  rw [_root_.GD.N0021.d023315]
  apply (_root_.GD.N0225.N0537.d023470 sizes hn w _root_.GD.N0021.d023313 hw _root_.GD.N0021.d023314 θ).mp
  exact _root_.GD.N0149.N0435.d028597 sizes hn ρ hρ hα hsum w hw hunit hweak θ

theorem d028599
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ (sizes 0 = 2 ∧ sizes 1 = 2))
    (w : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes)) :
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 2, w =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 2 sizes θ.scale] _root_.GD.N0021.d023313 := by
  obtain ⟨hρ, hα, hsum⟩ := _root_.GD.N0149.N0434.d028594 sizes hn hnot
  exact _root_.GD.N0149.N0435.d028597 sizes hn
    (_root_.GD.N0103.d005209 (_root_.GD.N0232.N0719.N0954.d009355 sizes)) hρ hα hsum w hw hunit hweak

end
end GD.N0149.N0435

#print axioms _root_.GD.N0149.N0435.d028597
#print axioms _root_.GD.N0149.N0435.d028598
#print axioms _root_.GD.N0149.N0435.d028599
