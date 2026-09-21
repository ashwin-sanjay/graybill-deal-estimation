import GD.Module1454

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped Topology BigOperators

namespace GD.N0212.N0467
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0962
open _root_.GD.N0156.N0444

noncomputable section
variable {k : ℕ} [NeZero k]



theorem d023018 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ t : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ,
      _root_.GD.N0232.N0719.N0896.d011131 k sizes t ∧ ∀ z, _root_.GD.N0156.N0444.d020667 sizes t z := by
  have haff : s ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes := by
    refine ⟨hs.1, ?_⟩
    intro b a ha z
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, Real.log a⟩
    have h := hs.2.1 g z
    change s (fun i j => b + Real.exp (Real.log a) * z i j) =
      b + Real.exp (Real.log a) * s z at h
    change s (fun i j => b + a * z i j) = b + a * s z
    simpa only [Real.exp_log ha] using h
  have hf : s ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes :=
    ⟨haff, fun θ => ne_top_of_lt (hs.2.2.1 θ)⟩
  obtain ⟨hc, hct, hi, hrisk⟩ := _root_.GD.N0156.N0444.d020678 sizes hn s hf hs.2.2.2
  refine ⟨_root_.GD.N0232.N0719.N0981.d020660 sizes s, ⟨hc.1.1, ?_, ?_, hct⟩, hi⟩
  · intro g z
    exact hc.1.2 g.shift g.d009239 g.d009240 z
  · intro θ
    rw [hrisk θ]
    exact hs.2.2.1 θ

theorem d023019 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ) (hs : ∀ z, _root_.GD.N0156.N0444.d020667 sizes s z)
    (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) (hz : ∀ i j, |z i j| ≤ 1) : |s z| ≤ 1 := by
  have hm (i : Fin k) : _root_.GD.N0232.N0719.N0981.d020646 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) i ∈ Icc (-1 : ℝ) 1 := by
    have hnreal : (0 : ℝ) < sizes i := by exact_mod_cast hn i
    constructor
    · apply (le_div_iff₀ hnreal).mpr
      calc
        -1 * (sizes i : ℝ) = ∑ j : Fin (sizes i), (-1 : ℝ) := by simp
        _ ≤ ∑ j : Fin (sizes i), z i j :=
          Finset.sum_le_sum fun j _ => (abs_le.mp (hz i j)).1
    · apply (div_le_iff₀ hnreal).mpr
      calc
        (∑ j : Fin (sizes i), z i j) ≤ ∑ j : Fin (sizes i), (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => (abs_le.mp (hz i j)).2
        _ = 1 * (sizes i : ℝ) := by simp
  apply abs_le.mpr
  refine ⟨le_trans ?_ (hs z).1, (hs z).2.trans ?_⟩
  · exact Finset.le_inf' _ _ fun i _ => (hm i).1
  · exact Finset.sup'_le _ _ fun i _ => (hm i).2

end
end GD.N0212.N0467

#print axioms _root_.GD.N0212.N0467.d023018
#print axioms _root_.GD.N0212.N0467.d023019
