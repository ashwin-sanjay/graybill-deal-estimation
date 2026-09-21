import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0034.N0292

noncomputable section

theorem d007211
    {α : Type*} (K : Set α) (E : α → ℝ)
    (hE : ∀ f ∈ K, 0 ≤ E f) :
    (¬ ∀ f ∈ K, E f = 0) ↔ ∃ f ∈ K, 0 < E f := by
  classical
  constructor
  · intro h
    by_contra hnone
    apply h
    intro f hf
    apply le_antisymm
    · by_contra hpos
      exact hnone ⟨f, hf, lt_of_not_ge hpos⟩
    · exact hE f hf
  · rintro ⟨f, hf, hpos⟩ hzero
    exact (ne_of_gt hpos) (hzero f hf)

variable {Ω Θ : Type*} [MeasurableSpace Ω]

def d007212 (ν : Measure Ω) (S T : Ω → Ω) (f : Ω → ℝ) : ℝ :=
  ∫ z, (f (S z) - 2 * f z) ^ 2 +
    (f (T z) - 3 * f z - 1) ^ 2 ∂ν

theorem d007213
    (ν : Measure Ω) (S T : Ω → Ω) (f : Ω → ℝ) :
    0 ≤ _root_.GD.N0034.N0292.d007212 ν S T f := by
  exact integral_nonneg fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)

def d007214
    (risk : Θ → (Ω → ℝ) → ℝ) (β denominator : Θ → ℝ) (V : ℝ) :
    Set (Ω → ℝ) :=
  {f | Measurable f ∧ ∀ θ, risk θ f ≤ min (β θ) (V / denominator θ)}

def d007215
    (ν : Measure Ω) (S T : Ω → Ω)
    (risk : Θ → (Ω → ℝ) → ℝ) (β denominator : Θ → ℝ) (V : ℝ) : Prop :=
  ∀ f ∈ _root_.GD.N0034.N0292.d007214 risk β denominator V, _root_.GD.N0034.N0292.d007212 ν S T f = 0

theorem d007216
    (ν : Measure Ω) (S T : Ω → Ω)
    (risk : Θ → (Ω → ℝ) → ℝ) (β denominator : Θ → ℝ) (V : ℝ) :
    ¬ _root_.GD.N0034.N0292.d007215 ν S T risk β denominator V ↔
      ∃ f : Ω → ℝ, Measurable f ∧
        (∀ θ, risk θ f ≤ min (β θ) (V / denominator θ)) ∧
        0 < _root_.GD.N0034.N0292.d007212 ν S T f := by
  have h := _root_.GD.N0034.N0292.d007211
    (_root_.GD.N0034.N0292.d007214 risk β denominator V) (_root_.GD.N0034.N0292.d007212 ν S T)
    (fun f _ => _root_.GD.N0034.N0292.d007213 ν S T f)
  simpa only [_root_.GD.N0034.N0292.d007215, _root_.GD.N0034.N0292.d007214, Set.mem_setOf_eq,
    and_assoc] using h

theorem d007217
    (ν : Measure Ω) (S T : Ω → Ω)
    (risk : Θ → (Ω → ℝ) → ℝ) (β denominator : Θ → ℝ) (V : ℝ)
    (hK : _root_.GD.N0034.N0292.d007214 risk β denominator V = ∅) :
    _root_.GD.N0034.N0292.d007215 ν S T risk β denominator V := by
  intro f hf
  rw [hK] at hf
  exact hf.elim

theorem d007218
    (ν : Measure Ω) (S T : Ω → Ω)
    (risk : Θ → (Ω → ℝ) → ℝ) (β denominator : Θ → ℝ) (V : ℝ)
    (h : ¬ _root_.GD.N0034.N0292.d007215 ν S T risk β denominator V) :
    (_root_.GD.N0034.N0292.d007214 risk β denominator V).Nonempty := by
  obtain ⟨f, hmeas, hcap, _⟩ := (_root_.GD.N0034.N0292.d007216 ν S T risk β denominator V).mp h
  exact ⟨f, hmeas, hcap⟩

end

end GD.N0034.N0292

#print axioms _root_.GD.N0034.N0292.d007211
#print axioms _root_.GD.N0034.N0292.d007213
#print axioms _root_.GD.N0034.N0292.d007216
#print axioms _root_.GD.N0034.N0292.d007217
#print axioms _root_.GD.N0034.N0292.d007218
