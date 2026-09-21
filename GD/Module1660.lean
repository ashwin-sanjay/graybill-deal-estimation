import GD.Module1659

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter

namespace GD.N0097

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859

noncomputable section

theorem d028192 (a b : ℤ) : (a : ℝ) ≠ 1 / 2 + (b : ℝ) := by
  intro h
  have hr : (2 : ℝ) * a = 1 + 2 * b := by linarith
  have hi : (2 : ℤ) * a = 1 + 2 * b := by exact_mod_cast hr
  omega




theorem d028193
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 0 < sizes i) :
    ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧
      (∀ z, f (fun i j => 1 + z i j) = 1 + f z) ∧
      ¬ _root_.GD.N0097.d028174 sizes f (1 / 2) := by
  let i : Fin k := ⟨0, hk⟩
  let j : Fin (sizes i) := ⟨0, hn i⟩
  let f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
    fun z => (⌊z i j⌋ : ℤ)
  refine ⟨f, ?_, ?_, ?_⟩
  · unfold f
    fun_prop
  · intro z
    change (⌊1 + z i j⌋ : ℝ) = 1 + (⌊z i j⌋ : ℝ)
    exact_mod_cast Int.floor_intCast_add (1 : ℤ) (z i j)
  · intro h
    letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
      unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
      infer_instance
    obtain ⟨z, hz⟩ := h.exists
    exact _root_.GD.N0097.d028192 ⌊1 / 2 + z i j⌋ ⌊z i j⌋ hz

end
end GD.N0097

#print axioms _root_.GD.N0097.d028192
#print axioms _root_.GD.N0097.d028193
