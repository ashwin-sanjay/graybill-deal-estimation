import GD.Module1505
import GD.Module1696
import GD.Module0352

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0149.N0434
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0101.N0356
open _root_.GD.N0101.N0411
open _root_.GD.N0103

variable {n : ℕ}

theorem d028591
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1) :
    ¬ ∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes) := by
  rw [_root_.GD.N0021.d023315]
  exact _root_.GD.N0101.N0356.d023492 sizes hn ρ hρ hα hsum
    _root_.GD.N0021.d023313 _root_.GD.N0021.d023314 (_root_.GD.N0101.N0411.d028560 (Nat.succ_pos _))
    (_root_.GD.N0101.N0411.d028561 (Nat.succ_pos _)) _root_.GD.N0101.N0411.d028562

theorem d028592
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) =
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes) := by
  intro θ
  apply le_antisymm (hweak θ)
  by_contra h
  exact _root_.GD.N0149.N0434.d028591 sizes hn ρ hρ hα hsum
    ⟨w, hw, hunit, hweak, θ, lt_of_not_ge h⟩

theorem d028593
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1) :
    ¬ ∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023292 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023292 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes) := by
  rintro ⟨w, hw, hunit, hweak, θ, hstrict⟩
  let v : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun t => w (fun i => (sizes i : ℝ) * t i)
  have hv : Measurable v := hw.comp (by fun_prop)
  have hvu : ∀ t, ∑ i, v t i = 1 := fun t => hunit (fun i => (sizes i : ℝ) * t i)
  have heq : _root_.GD.N0072.d023292 sizes w = _root_.GD.N0072.d023291 sizes v :=
    _root_.GD.N0072.d023294 sizes (fun i => by have := hn i; omega) w
  exact _root_.GD.N0149.N0434.d028591 sizes hn ρ hρ hα hsum
    ⟨v, hv, hvu, (fun η => by simpa only [heq] using hweak η), θ,
      by simpa only [heq] using hstrict⟩

theorem d028594
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ (sizes 0 = 2 ∧ sizes 1 = 2)) :
    _root_.GD.N0103.d005209 (_root_.GD.N0232.N0719.N0954.d009355 sizes) < 1 ∧
      (∀ i, 0 < _root_.GD.N0103.d005210 (_root_.GD.N0232.N0719.N0954.d009355 sizes) i) ∧
      (∑ i, _root_.GD.N0103.d005210 (_root_.GD.N0232.N0719.N0954.d009355 sizes) i) = 1 := by
  have ha := _root_.GD.N0232.N0719.N0954.d009358 hn
  have hA : 1 < _root_.GD.N0103.d005208 (_root_.GD.N0232.N0719.N0954.d009355 sizes) := by
    have hnat : 3 ≤ (sizes 0 - 1) + (sizes 1 - 1) := by
      have := hn 0
      have := hn 1
      omega
    have hreal : (3 : ℝ) ≤ ((sizes 0 - 1 : ℕ) : ℝ) + ((sizes 1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simp only [_root_.GD.N0103.d005208, Fin.sum_univ_two, _root_.GD.N0232.N0719.N0954.d009355]
    linarith
  have hApos : 0 < _root_.GD.N0103.d005208 (_root_.GD.N0232.N0719.N0954.d009355 sizes) := zero_lt_one.trans hA
  refine ⟨(_root_.GD.N0103.d005213 _ hApos).mpr (by norm_num; exact hA), ?_,
    _root_.GD.N0103.d005212 _ hApos.ne'⟩
  intro i
  apply (_root_.GD.N0103.d005214 _ hApos i).mpr
  have h0 := ha 0
  have h1 := ha 1
  fin_cases i
  · change ((2 : ℝ) - 1) * _root_.GD.N0232.N0719.N0954.d009355 sizes 0 < _
    simp only [_root_.GD.N0103.d005208, Fin.sum_univ_two]
    linarith
  · change ((2 : ℝ) - 1) * _root_.GD.N0232.N0719.N0954.d009355 sizes 1 < _
    simp only [_root_.GD.N0103.d005208, Fin.sum_univ_two]
    linarith

theorem d028595
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ (sizes 0 = 2 ∧ sizes 1 = 2)) :
    ¬ ∃ w : (Fin 2 → ℝ) → Fin 2 → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes) := by
  obtain ⟨hρ, hα, hsum⟩ := _root_.GD.N0149.N0434.d028594 sizes hn hnot
  exact _root_.GD.N0149.N0434.d028591 sizes hn
    (_root_.GD.N0103.d005209 (_root_.GD.N0232.N0719.N0954.d009355 sizes)) hρ hα hsum

theorem d028596
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ (sizes 0 = 2 ∧ sizes 1 = 2)) :
    ¬ ∃ w : (Fin 2 → ℝ) → Fin 2 → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023292 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023292 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes) := by
  obtain ⟨hρ, hα, hsum⟩ := _root_.GD.N0149.N0434.d028594 sizes hn hnot
  exact _root_.GD.N0149.N0434.d028593 sizes hn
    (_root_.GD.N0103.d005209 (_root_.GD.N0232.N0719.N0954.d009355 sizes)) hρ hα hsum

end
end GD.N0149.N0434

#print axioms _root_.GD.N0149.N0434.d028591
#print axioms _root_.GD.N0149.N0434.d028592
#print axioms _root_.GD.N0149.N0434.d028593
#print axioms _root_.GD.N0149.N0434.d028594
#print axioms _root_.GD.N0149.N0434.d028595
#print axioms _root_.GD.N0149.N0434.d028596
