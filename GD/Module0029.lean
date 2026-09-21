import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Constructions.SumProd













open Set

namespace GD
namespace N0230
namespace N0655

noncomputable section


abbrev d000349 := ℝ × Set.Ioi (0 : ℝ)


abbrev d000350 := ℚ × ℚ



def d000351 : _root_.GD.N0230.N0655.d000350 → _root_.GD.N0230.N0655.d000349 :=
  Prod.map ((↑) : ℚ → ℝ)
    (fun q ↦ Real.expOrderIso (q : ℝ))


theorem d000352 :
    DenseRange (fun q : ℚ ↦ Real.expOrderIso (q : ℝ)) := by
  exact (Real.expOrderIso.surjective.denseRange.comp
    Rat.denseRange_cast Real.expOrderIso.continuous)



theorem d000353 : DenseRange _root_.GD.N0230.N0655.d000351 := by
  exact Rat.denseRange_cast.prodMap _root_.GD.N0230.N0655.d000352

end

end N0655
end N0230
end GD

#print axioms _root_.GD.N0230.N0655.d000352
#print axioms _root_.GD.N0230.N0655.d000353
