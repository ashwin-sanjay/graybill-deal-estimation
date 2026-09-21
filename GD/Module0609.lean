import Mathlib
import GD.Module0598
import GD.Module0428









open MeasureTheory

namespace GD.N0148

noncomputable section

open _root_.GD.N0147 _root_.GD.N0141

variable {Ω : Type*} [MeasurableSpace Ω]




theorem d008808
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L q : Ω → ℝ} {e : ℝ}
    {atomic smear densityError energy C M : ℝ}
    (hC : 0 < C) (hM : 0 < M)
    (hAtomic : atomic ≤ -(3 * C / 4))
    (hSmear : |smear| ≤ C / 16)
    (hDensity : |densityError| ≤ C / 16)
    (hTrace :
      _root_.GD.N0141.d006687 P D L q e = atomic + smear + densityError)
    (hEnergy :
      _root_.GD.N0141.d006688 P D q = energy)
    (hEnergyCeiling : energy ≤ M)
    (hRiskIdentity :
      _root_.GD.N0141.d006684 P
          (_root_.GD.N0141.d006686 U D L q e ((C / 2) / M))
          - _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) =
        2 * ((C / 2) / M) * _root_.GD.N0141.d006687 P D L q e
          + ((C / 2) / M) ^ 2 * _root_.GD.N0141.d006688 P D q) :
    _root_.GD.N0141.d006684 P
        (_root_.GD.N0141.d006686 U D L q e ((C / 2) / M))
      < _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) := by
  have hδ : 0 < C / 2 := by linarith
  have hTraceMargin :
      _root_.GD.N0141.d006687 P D L q e ≤ -(C / 2) := by
    rw [hTrace]
    exact _root_.GD.N0147.d008613
      atomic smear densityError C (le_of_lt hC)
      hAtomic hSmear hDensity
  have hDirect :
      2 * ((C / 2) / M) * _root_.GD.N0141.d006687 P D L q e
          + ((C / 2) / M) ^ 2 * _root_.GD.N0141.d006688 P D q < 0 := by
    rw [hEnergy]
    exact _root_.GD.N0147.d008615
      (_root_.GD.N0141.d006687 P D L q e) energy (C / 2) M
      hδ hM hTraceMargin hEnergyCeiling
  linarith

end

end GD.N0148
