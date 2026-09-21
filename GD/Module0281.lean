import GD.Module0279
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences










open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1304

open _root_.GD.N0232.N0720.N1290

noncomputable section

def d004174 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : Continuous P) (hp : ∀ t, 0 < P t) : C(_root_.GD.N0232.N0720.N1290.d004131, ℝ) where
  toFun t := P t ^ (-q)
  continuous_toFun := hP.rpow_const (fun t ↦ Or.inl (hp t).ne')

def d004175 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : Continuous P) (hp : ∀ t, 0 < P t) : C(_root_.GD.N0232.N0720.N1290.d004131, ℝ) where
  toFun t := (t : ℝ) * _root_.GD.N0232.N0720.N1304.d004174 q P hP hp t
  continuous_toFun := continuous_subtype_val.mul (_root_.GD.N0232.N0720.N1304.d004174 q P hP hp).continuous

theorem d004176 (q : ℝ) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : Continuous P) (hp : ∀ t, 0 < P t) :
    Continuous (fun μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1290.d004140 q P (μ : Measure _root_.GD.N0232.N0720.N1290.d004131)) := by
  have hN := ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0720.N1304.d004175 q P hP hp)
  have hD := ProbabilityMeasure.continuous_integral_continuousMap (_root_.GD.N0232.N0720.N1304.d004174 q P hP hp)
  exact hN.div hD (fun μ ↦ (_root_.GD.N0232.N0720.N1290.d004146 q P hP hp (μ : Measure _root_.GD.N0232.N0720.N1290.d004131)).ne')

theorem d004177 {X : Type*}
    (q : ℝ) (P : X → _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (domain : Set X)
    (hP : ∀ x ∈ domain, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (μ : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131) :
    ∃ (ν : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131) (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ x ∈ domain, Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1290.d004140 q (P x) (μ (ψ j) : Measure _root_.GD.N0232.N0720.N1290.d004131)) atTop
        (𝓝 (_root_.GD.N0232.N0720.N1290.d004140 q (P x) (ν : Measure _root_.GD.N0232.N0720.N1290.d004131))) := by
  obtain ⟨ν, ψ, hψ, hlim⟩ := SeqCompactSpace.tendsto_subseq μ
  refine ⟨ν, ψ, hψ, ?_⟩
  intro x hx
  exact ((_root_.GD.N0232.N0720.N1304.d004176 q (P x) (hP x hx).1 (hP x hx).2).tendsto ν).comp hlim



theorem d004178
    {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    (q : ℝ) (P : X → _root_.GD.N0232.N0720.N1290.d004131 → ℝ) (g : X → ℝ)
    (μ : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131)
    (hP : ∀ᵐ x ∂ρ, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hlim : ∀ᵐ x ∂ρ, Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1290.d004140 q (P x) (μ j : Measure _root_.GD.N0232.N0720.N1290.d004131)) atTop (𝓝 (g x))) :
    ∃ ν : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131,
      g =ᵐ[ρ] fun x ↦ _root_.GD.N0232.N0720.N1290.d004140 q (P x) (ν : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  obtain ⟨ν, ψ, hψ, hweak⟩ := SeqCompactSpace.tendsto_subseq μ
  refine ⟨ν, ?_⟩
  filter_upwards [hP, hlim] with x hpx hx
  exact tendsto_nhds_unique (hx.comp hψ.tendsto_atTop)
    (((_root_.GD.N0232.N0720.N1304.d004176 q (P x) hpx.1 hpx.2).tendsto ν).comp hweak)

end
end GD.N0232.N0720.N1304

#print axioms _root_.GD.N0232.N0720.N1304.d004176
#print axioms _root_.GD.N0232.N0720.N1304.d004177
#print axioms _root_.GD.N0232.N0720.N1304.d004178
