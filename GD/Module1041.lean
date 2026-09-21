import GD.Module1040
























open Filter MeasureTheory Topology
open scoped Topology

namespace GD
namespace N0232
namespace N0720
namespace N1112

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0606

variable {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
variable [OpensMeasurableSpace Xi]



theorem d016616
    (eta : ℕ → ℝ) :
    _root_.GD.N0230.N0606.d000961 eta ↔ Tendsto eta atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro heta epsilon hepsilon
    obtain ⟨N, hN⟩ := heta epsilon hepsilon
    refine ⟨N, ?_⟩
    intro n hn
    simpa only [Real.dist_eq, sub_zero] using hN n hn
  · intro heta epsilon hepsilon
    obtain ⟨N, hN⟩ := heta epsilon hepsilon
    refine ⟨N, ?_⟩
    intro n hn
    simpa only [Real.dist_eq, sub_zero] using hN n hn



theorem d016617
    (deficit energy : ℕ → ℝ)
    (hdeficitNonneg : ∀ k, 0 ≤ deficit k)
    (hdeficitEnergy : ∀ k, deficit k ≤ energy k)
    (henergyZero : Tendsto energy atTop (nhds 0)) :
    _root_.GD.N0230.N0606.d000961 deficit := by
  rw [_root_.GD.N0232.N0720.N1112.d016616]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds henergyZero
    (Filter.Eventually.of_forall hdeficitNonneg)
    (Filter.Eventually.of_forall hdeficitEnergy)










theorem d016618
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612 m n chart prior bayes)
    (hsIntegrable : ∀ k, Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) s.value).toReal) (prior k))
    (energy : ℕ → ℝ)
    (hdeficitNonneg : ∀ k, 0 ≤
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k s.value -
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k))
    (hdeficitEnergy : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k s.value -
          _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k) ≤
        energy k)
    (henergyZero : Tendsto energy atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1111.d016615
    m n hm hn chart hchartContinuous hchartSurjective prior hpriorFinite
      hretain s hstrict bayes hbayes hsIntegrable
  exact _root_.GD.N0232.N0720.N1112.d016617
    (fun k ↦
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k s.value -
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k))
    energy hdeficitNonneg hdeficitEnergy henergyZero

end

end N1112
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1112.d016616
#print axioms _root_.GD.N0232.N0720.N1112.d016617
#print axioms _root_.GD.N0232.N0720.N1112.d016618
