import GD.Module0870
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences














open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0232.N0720.N1291

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1271

def d013414 (x : _root_.GD.N0232.N0720.N1436.d013217) (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) : C(_root_.GD.N0232.N0720.N1290.d004131, ℝ) where
  toFun t := _root_.GD.N0232.N0720.N1271.d013404 x t ^ (-(5 / 2 : ℝ))
  continuous_toFun :=
    (_root_.GD.N0232.N0720.N1271.d013405.comp (continuous_const.prodMk continuous_id)).rpow_const
      (fun t ↦ Or.inl (_root_.GD.N0232.N0720.N1271.d013407 hx t).ne')

def d013415 (x : _root_.GD.N0232.N0720.N1436.d013217) (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    C(_root_.GD.N0232.N0720.N1290.d004131, ℝ) where
  toFun t := (t : ℝ) * _root_.GD.N0232.N0720.N1291.d013414 x hx t
  continuous_toFun := continuous_subtype_val.mul (_root_.GD.N0232.N0720.N1291.d013414 x hx).continuous


def d013416 (mu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)

theorem d013417 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) : Continuous (fun mu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131 ↦
      _root_.GD.N0232.N0720.N1291.d013416 mu x) := by
  have hN := ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0720.N1291.d013415 x hx)
  have hD := ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0720.N1291.d013414 x hx)
  apply hN.div hD
  intro mu
  exact (_root_.GD.N0232.N0720.N1290.d004146 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x)
    (_root_.GD.N0232.N0720.N1271.d013405.comp (continuous_const.prodMk continuous_id))
    (_root_.GD.N0232.N0720.N1271.d013407 hx) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)).ne'



theorem d013418 (mu : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131) :
    ∃ (nu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131) (phi : ℕ → ℕ), StrictMono phi ∧
      ∀ x ∈ _root_.GD.N0232.N0720.N1436.d013218,
        Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1291.d013416 (mu (phi n)) x) atTop (𝓝 (_root_.GD.N0232.N0720.N1291.d013416 nu x)) := by
  obtain ⟨nu, phi, hphi, hlim⟩ := SeqCompactSpace.tendsto_subseq mu
  refine ⟨nu, phi, hphi, ?_⟩
  intro x hx
  exact (_root_.GD.N0232.N0720.N1291.d013417 hx).tendsto nu |>.comp hlim




theorem d013419
    (mu : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (rho : Measure _root_.GD.N0232.N0720.N1436.d013217)
    (hphysical : ∀ᵐ x ∂rho, x ∈ _root_.GD.N0232.N0720.N1436.d013218)
    (hlim : ∀ᵐ x ∂rho, Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1291.d013416 (mu n) x) atTop (𝓝 (g x))) :
    ∃ nu : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131,
      g =ᵐ[rho] fun x ↦ _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (nu : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  obtain ⟨nu, phi, hphi, hpost⟩ := _root_.GD.N0232.N0720.N1291.d013418 mu
  refine ⟨nu, ?_⟩
  filter_upwards [hphysical, hlim] with x hx hgx
  exact tendsto_nhds_unique (hgx.comp hphi.tendsto_atTop) (hpost x hx)

end
end GD.N0232.N0720.N1291

#print axioms _root_.GD.N0232.N0720.N1291.d013418
#print axioms _root_.GD.N0232.N0720.N1291.d013419
