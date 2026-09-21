import GD.Module1698
import GD.Module1695
import GD.Module1543

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0224.N0533
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0213.N0485
open _root_.GD.N0213.N0486

variable {n : ℕ}

theorem d028600
    (sizes : Fin (n + 2) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hcone : _root_.GD.N0213.N0486.d028577 sizes)
    (i₀ : Fin (n + 2)) (hi₀ : sizes i₀ = 2)
    (hother : ∀ i, i ≠ i₀ → 5 ≤ sizes i) :
    _root_.GD.N0213.N0485.d028566 sizes ∧ _root_.GD.N0232.N0719.N0962.d012188 (n + 2) sizes ≠ ⊤ ∧
      ∀ w : (Fin (n + 2) → ℝ) → Fin (n + 2) → ℝ,
        Measurable w → (∀ t, ∑ i, w t i = 1) →
          _root_.GD.N0232.N0719.N0962.d012187 (n + 2) sizes (_root_.GD.N0072.d023291 sizes w) = ⊤ := by
  refine ⟨_root_.GD.N0213.N0486.d028581 sizes hn hcone, ?_, ?_⟩
  · exact (_root_.GD.N0067.d023926
      (by omega) sizes hn).mpr (Or.inr ⟨i₀, hi₀, hother⟩)
  · intro w hw hu
    exact _root_.GD.N0083.d028556
      (by omega) sizes hn i₀ hi₀ w hw hu

theorem d028601 (m : ℕ) (hm : 5 ≤ m) :
    let sizes : Fin (n + 2) → ℕ := Fin.cons 2 (fun _ => m)
    _root_.GD.N0213.N0485.d028566 sizes ∧ _root_.GD.N0232.N0719.N0962.d012188 (n + 2) sizes ≠ ⊤ ∧
      ∀ w : (Fin (n + 2) → ℝ) → Fin (n + 2) → ℝ,
        Measurable w → (∀ t, ∑ i, w t i = 1) →
          _root_.GD.N0232.N0719.N0962.d012187 (n + 2) sizes (_root_.GD.N0072.d023291 sizes w) = ⊤ := by
  dsimp only
  have hordinary : ∀ i : Fin (n + 2),
      2 ≤ (Fin.cons 2 (fun _ : Fin (n + 1) => m) : Fin (n + 2) → ℕ) i := by
    intro i
    refine Fin.cases (by simp) (fun j => ?_) i
    simpa only [Fin.cons_succ] using (by omega : 2 ≤ m)
  have hother : ∀ i : Fin (n + 2), i ≠ 0 →
      5 ≤ (Fin.cons 2 (fun _ : Fin (n + 1) => m) : Fin (n + 2) → ℕ) i := by
    intro i hi
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ j => simpa only [Fin.cons_succ] using hm
  exact _root_.GD.N0224.N0533.d028600 _ hordinary
    (_root_.GD.N0213.N0486.d028585 (by omega : 3 ≤ m)) 0 (by simp) hother

theorem d028602
    (sizes : Fin (n + 2) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hcone : _root_.GD.N0213.N0486.d028577 sizes) (i₀ : Fin (n + 2)) (hi₀ : sizes i₀ = 2)
    (hother : ∀ i, i ≠ i₀ → 5 ≤ sizes i)
    (w : (Fin (n + 2) → ℝ) → Fin (n + 2) → ℝ) (hw : Measurable w)
    (hu : ∀ t, ∑ i, w t i = 1) :
    _root_.GD.N0232.N0719.N0962.d012188 (n + 2) sizes <
      _root_.GD.N0232.N0719.N0962.d012187 (n + 2) sizes (_root_.GD.N0072.d023291 sizes w) := by
  obtain ⟨_, hf, hall⟩ := _root_.GD.N0224.N0533.d028600 sizes hn hcone i₀ hi₀ hother
  rw [hall w hw hu]
  exact lt_top_iff_ne_top.mpr hf

end
end GD.N0224.N0533

#print axioms _root_.GD.N0224.N0533.d028600
#print axioms _root_.GD.N0224.N0533.d028601
#print axioms _root_.GD.N0224.N0533.d028602
