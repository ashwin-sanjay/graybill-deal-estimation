import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Bounded













open Filter Set Bornology

namespace GD
namespace N0238
namespace N0750




def d004292 {X : Type*} [TopologicalSpace X]
    (u : ℕ → X) : Prop :=
  ∃ extraction : ℕ → ℕ,
    Tendsto extraction atTop atTop ∧
    ∃ x : X, Tendsto (u ∘ extraction) atTop (nhds x)



theorem d004293
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (u : ℕ → X) (K : Set X) (hK : IsCompact K)
    (hfrequent : ∃ᶠ n in atTop, u n ∈ K) :
    _root_.GD.N0238.N0750.d004292 u := by
  obtain ⟨x, _hx, extraction, hextraction, hlimit⟩ :=
    tendsto_subseq_of_frequently_bounded hK.isBounded hfrequent
  exact ⟨extraction, hextraction.tendsto_atTop, x, hlimit⟩


theorem d004294
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (u : ℕ → X) (hcluster : ¬ _root_.GD.N0238.N0750.d004292 u) :
    Tendsto u atTop (Filter.cocompact X) := by
  refine Filter.hasBasis_cocompact.tendsto_right_iff.mpr ?_
  intro K hK
  by_contra hnot
  have hfrequent : ∃ᶠ n in atTop, u n ∈ K := by
    simpa only [Set.mem_compl_iff, not_not] using (not_eventually.mp hnot)
  exact hcluster
    (_root_.GD.N0238.N0750.d004293 u K hK hfrequent)


theorem d004295
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (base : X) (u : ℕ → X) (hcluster : ¬ _root_.GD.N0238.N0750.d004292 u) :
    Tendsto (fun n ↦ dist (u n) base) atTop atTop := by
  exact (tendsto_dist_right_cocompact_atTop base).comp
    (_root_.GD.N0238.N0750.d004294 u hcluster)



theorem d004296
    {X : Type*} [PseudoMetricSpace X]
    (base : X) (u : ℕ → X)
    (hescape : Tendsto (fun n ↦ dist (u n) base) atTop atTop) :
    ¬ _root_.GD.N0238.N0750.d004292 u := by
  rintro ⟨extraction, hextraction, x, hlimit⟩
  have hfinite : Tendsto (fun n ↦ dist (u (extraction n)) base)
      atTop (nhds (dist x base)) := by
    simpa [Function.comp_def] using
      (hlimit.dist tendsto_const_nhds)
  have hinfinite : Tendsto (fun n ↦ dist (u (extraction n)) base)
      atTop atTop := hescape.comp hextraction
  exact not_tendsto_atTop_of_tendsto_nhds hfinite hinfinite





theorem d004297
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (base : X) (u : ℕ → X) :
    (¬ _root_.GD.N0238.N0750.d004292 u) ↔
      Tendsto (fun n ↦ dist (u n) base) atTop atTop := by
  constructor
  · exact _root_.GD.N0238.N0750.d004295 base u
  · exact _root_.GD.N0238.N0750.d004296 base u

end N0750
end N0238
end GD

#print axioms _root_.GD.N0238.N0750.d004293
#print axioms _root_.GD.N0238.N0750.d004294
#print axioms _root_.GD.N0238.N0750.d004297
