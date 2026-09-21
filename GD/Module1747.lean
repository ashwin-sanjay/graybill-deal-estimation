import GD.Module1746
import GD.Module1464

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0465

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0982
open _root_.GD.N0232.N0719.N0986 _root_.GD.N0232.N0719.N0997
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0212.N0462

noncomputable section
variable {k : ℕ}



theorem d028992 (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ)
    (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (hrep : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      s z = _root_.GD.N0212.N0462.d020723 ((((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2)
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (_root_.GD.N0232.N0719.N0986.d020362 sizes z)) :
    ¬ _root_.GD.N0232.N0719.N0896.d011131 k sizes s := by
  intro hs
  letI : NeZero k := ⟨by omega⟩
  obtain ⟨ν, _hν, ⟨m⟩, hpost⟩ :=
    _root_.GD.N0212.N0471.d028991 sizes hn hs
  exact _root_.GD.N0212.N0473.d023080 hk sizes hn s hs.1
    (fun θ => (hs.2.2.1 θ).le) μ hrep _ m hpost

end
end GD.N0212.N0465

#print axioms _root_.GD.N0212.N0465.d028992
