import GD.Module1490
import GD.Module1504
import GD.Module0353

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0356
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0230.N0665
open _root_.GD.N0072 _root_.GD.N0101.N0357
open _root_.GD.N0101.N0349 _root_.GD.N0101.N0400

variable {n : ℕ}



theorem d023492
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1)
    (p : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hp : Measurable p) (hpunit : ∀ t, ∑ i, p t i = 1) (hpnn : ∀ t i, 0 ≤ p t i)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t) :
    ¬ ∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes p) := by
  apply _root_.GD.N0101.N0400.d023491
    sizes hn ρ hρ hα hsum
    (_root_.GD.N0104.d005223 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ρ
      (_root_.GD.N0232.N0719.N0954.d009358 hn) hρ (fun i => (hα i).le) hsum)
    p hp hpunit hpnn hporacle
  intro m
  exact _root_.GD.N0101.N0349.d023345 sizes hn ρ hρ hα hsum
    p hp hpunit hporacle (by positivity)

end
end GD.N0101.N0356

#print axioms _root_.GD.N0101.N0356.d023492
