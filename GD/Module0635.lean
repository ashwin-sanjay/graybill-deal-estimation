import GD.Module0029
import GD.Module0634
import Mathlib.Topology.Homeomorph.TransferInstance














open Set

namespace GD
namespace N0232
namespace N0719
namespace N0945

noncomputable section

open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229



noncomputable instance d009263 :
    TopologicalSpace _root_.GD.N0232.N0719.N0946.d009229 :=
  _root_.GD.N0232.N0719.N0946.d009229.d009230.topologicalSpace


def d009264 : _root_.GD.N0232.N0719.N0946.d009229 ≃ₜ ℝ × ℝ :=
  _root_.GD.N0232.N0719.N0946.d009229.d009230.homeomorph

theorem d009265 : Continuous _root_.GD.N0232.N0719.N0946.d009229.d009230 :=
  _root_.GD.N0232.N0719.N0945.d009264.continuous

theorem d009266 :
    Continuous (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦ g.logScale) := by
  exact continuous_fst.comp _root_.GD.N0232.N0719.N0945.d009265

theorem d009267 :
    Continuous (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦ g.shift) := by
  exact continuous_snd.comp _root_.GD.N0232.N0719.N0945.d009265

theorem d009268 : Continuous _root_.GD.N0232.N0719.N0946.d009229.d009239 := by
  exact Real.continuous_exp.comp _root_.GD.N0232.N0719.N0945.d009266


abbrev d009269 := ℚ × ℚ



def d009270
    (q : _root_.GD.N0232.N0719.N0945.d009269) : _root_.GD.N0232.N0719.N0946.d009229 :=
  _root_.GD.N0232.N0719.N0945.d009264.symm ((q.1 : ℝ), (q.2 : ℝ))


theorem d009271 : DenseRange _root_.GD.N0232.N0719.N0945.d009270 := by
  have hproduct : DenseRange
      (fun q : ℚ × ℚ ↦ ((q.1 : ℝ), (q.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hinverse : DenseRange
      (_root_.GD.N0232.N0719.N0945.d009264.symm : ℝ × ℝ → _root_.GD.N0232.N0719.N0946.d009229) :=
    _root_.GD.N0232.N0719.N0945.d009264.symm.surjective.denseRange
  have hcomp := hinverse.comp hproduct
    _root_.GD.N0232.N0719.N0945.d009264.symm.continuous
  change DenseRange
    (fun q : ℚ × ℚ ↦
      _root_.GD.N0232.N0719.N0945.d009264.symm ((q.1 : ℝ), (q.2 : ℝ)))
  exact hcomp

end

end N0945
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0945.d009271
