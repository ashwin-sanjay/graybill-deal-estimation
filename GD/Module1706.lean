import GD.Module1700
import GD.Module1705

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0214.N0530
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0101
open _root_.GD.N0072 _root_.GD.N0021 _root_.GD.N0101.N0357
open _root_.GD.N0101.N0411
open _root_.GD.N0101.N0409
open _root_.GD.N0149.N0434

variable {n : ℕ}

theorem d028621
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hw : Measurable w)
    (hc : ContinuousOn w _root_.GD.N0101.N0357.d023158) (hu : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) :
    EqOn w _root_.GD.N0021.d023313 _root_.GD.N0101.N0357.d023158 :=
  _root_.GD.N0101.N0409.d028617 (Nat.succ_pos _) sizes hn
    (_root_.GD.N0149.N0434.d028591 sizes hn ρ hρ hα hsum) w hw hc hu hweak

theorem d028622
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hw : Measurable w)
    (hc : ContinuousOn w _root_.GD.N0101.N0357.d023158) (hu : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1)
    (t : Fin (n + 1) → ℝ) (ht : t ∈ _root_.GD.N0101.N0357.d023158) (hdiff : w t ≠ _root_.GD.N0021.d023313 t) :
    ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes) <
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) :=
  _root_.GD.N0101.N0409.d028618 (Nat.succ_pos _) sizes hn
    (_root_.GD.N0149.N0434.d028591 sizes hn ρ hρ hα hsum) w hw hc hu t ht hdiff

theorem d028623
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ (sizes 0 = 2 ∧ sizes 1 = 2))
    (w : (Fin 2 → ℝ) → Fin 2 → ℝ) (hw : Measurable w)
    (hc : ContinuousOn w _root_.GD.N0101.N0357.d023158) (hu : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 2 sizes θ (_root_.GD.N0232.N0719.N0900.d009111 2 sizes)) :
    EqOn w _root_.GD.N0021.d023313 _root_.GD.N0101.N0357.d023158 :=
  _root_.GD.N0101.N0409.d028617 (by decide) sizes hn
    (_root_.GD.N0149.N0434.d028595 sizes hn hnot) w hw hc hu hweak

end
end GD.N0214.N0530

#print axioms _root_.GD.N0214.N0530.d028621
#print axioms _root_.GD.N0214.N0530.d028622
#print axioms _root_.GD.N0214.N0530.d028623
