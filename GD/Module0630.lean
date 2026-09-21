import GD.Module0629















open MeasureTheory ProbabilityTheory

namespace GD
namespace N0232
namespace N0719

noncomputable section

open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900


theorem d009185
    (n : ℕ) (shift dilation location scale : ℝ) :
    _root_.GD.N0107.d009018 n shift dilation ∘ _root_.GD.N0107.d009018 n location scale =
      _root_.GD.N0107.d009018 n (shift + dilation * location) (dilation * scale) := by
  funext z i
  simp [Function.comp_apply, _root_.GD.N0107.d009018]
  ring


theorem d009186
    (n : ℕ) (shift dilation location scale : ℝ) :
    (_root_.GD.N0232.N0719.d009174 n location scale).map
        (_root_.GD.N0107.d009018 n shift dilation) =
      _root_.GD.N0232.N0719.d009174 n
        (shift + dilation * location) (dilation * scale) := by
  unfold _root_.GD.N0232.N0719.d009174
  rw [Measure.map_map
    (_root_.GD.N0107.d009020 n shift dilation)
    (_root_.GD.N0107.d009020 n location scale)]
  rw [_root_.GD.N0232.N0719.d009185]


theorem d009187
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation location scale : ℝ) :
    _root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation ∘
        _root_.GD.N0232.N0719.N0900.d009095 k sizes location scale =
      _root_.GD.N0232.N0719.N0900.d009095 k sizes
        (shift + dilation * location) (dilation * scale) := by
  funext omega i j
  simp [Function.comp_apply, _root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018]
  ring





theorem d009188
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation location : ℝ) (scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation) =
      _root_.GD.N0232.N0719.d009176 k sizes
        (shift + dilation * location) (fun i ↦ dilation * scales i) := by
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N0900.d009095
  rw [Measure.pi_map_pi]
  · congr 1
    funext i
    exact _root_.GD.N0232.N0719.d009186
      (sizes i) shift dilation location (scales i)
  · intro i
    exact (_root_.GD.N0107.d009020 (sizes i) shift dilation).aemeasurable

end

end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.d009185
#print axioms _root_.GD.N0232.N0719.d009186
#print axioms _root_.GD.N0232.N0719.d009187
#print axioms _root_.GD.N0232.N0719.d009188
