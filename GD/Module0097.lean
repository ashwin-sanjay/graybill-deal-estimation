import GD.Module0014
import GD.Module0089
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0230
namespace N0712

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0708

variable {Omega Theta : Type*} [MeasurableSpace Omega]



def d001258
    (mu0 mu : Measure Omega) (target : ℝ)
    (d : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0)) : ENNReal :=
  _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target
    ((toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0)).symm d)




theorem d001259
    (mu0 mu : Measure Omega) (hmu : mu ≪ mu0)
    (target : ℝ) (c : ENNReal) :
    IsClosed
      ((_root_.GD.N0230.N0712.d001258 mu0 mu target) ⁻¹' Set.Iic c) := by
  let K : Set (_root_.GD.N0230.N0602.d000116 mu0) :=
    {d | _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target d ≤ c}
  have hKclosed : IsClosed K := by
    simpa [K, _root_.GD.N0230.N0602.d000118] using
      (_root_.GD.N0230.N0602.d000122
        (Θ := Unit) mu0 (fun _ => mu) (fun _ => target)
        (fun _ => c) (fun _ => hmu))
  have hKconvex : Convex ℝ K := by
    simpa [K, _root_.GD.N0230.N0602.d000118] using
      (_root_.GD.N0230.N0602.d000123
        (Θ := Unit) mu0 (fun _ => mu) (fun _ => target)
        (fun _ => c) (fun _ => hmu))
  have hweakClosed :
      IsClosed (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0) '' K) :=
    _root_.GD.N0230.N0708.d001175 hKconvex hKclosed
  have hset :
      (_root_.GD.N0230.N0712.d001258 mu0 mu target) ⁻¹' Set.Iic c =
        toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0) '' K := by
    ext d
    constructor
    · intro hd
      exact ⟨(toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0)).symm d, hd,
        (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0)).apply_symm_apply d⟩
    · rintro ⟨e, he, rfl⟩
      simpa [K, _root_.GD.N0230.N0712.d001258] using he
  rw [hset]
  exact hweakClosed



theorem d001260
    (mu0 mu : Measure Omega) (hmu : mu ≪ mu0)
    (target : ℝ) :
    LowerSemicontinuous (_root_.GD.N0230.N0712.d001258 mu0 mu target) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  exact _root_.GD.N0230.N0712.d001259 mu0 mu hmu target



theorem d001261
    (mu0 mu : Measure Omega) (hmu : mu ≪ mu0)
    (target : ℝ) (cap : ENNReal) (hcap0 : cap ≠ 0) :
    LowerSemicontinuous
      (fun d : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0) =>
        _root_.GD.N0230.N0712.d001258 mu0 mu target d / cap) := by
  exact (ENNReal.continuous_div_const cap hcap0).comp_lowerSemicontinuous
    (_root_.GD.N0230.N0712.d001260 mu0 mu hmu target)
    (fun _ _ h => ENNReal.div_le_div_right h cap)



theorem d001262
    (mu0 : Measure Omega)
    (mu : Theta → Measure Omega) (target : Theta → ℝ)
    (cap : Theta → ENNReal)
    (hmu : ∀ theta, mu theta ≪ mu0)
    (hcap0 : ∀ theta, cap theta ≠ 0) :
    LowerSemicontinuous
      (fun d : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 mu0) =>
        ⨆ theta, _root_.GD.N0230.N0712.d001258 mu0 (mu theta) (target theta) d /
          cap theta) := by
  exact lowerSemicontinuous_iSup fun theta =>
    _root_.GD.N0230.N0712.d001261
      mu0 (mu theta) (hmu theta) (target theta) (cap theta) (hcap0 theta)

end

end N0712
end N0230
end GD

#print axioms _root_.GD.N0230.N0712.d001259
#print axioms _root_.GD.N0230.N0712.d001260
#print axioms _root_.GD.N0230.N0712.d001261
#print axioms _root_.GD.N0230.N0712.d001262
