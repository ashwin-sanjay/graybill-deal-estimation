import Mathlib.Topology.Maps.Proper.Basic

















open Set

namespace GD
namespace N0230
namespace N0582

set_option linter.unusedSectionVars false

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



def d000059 (f : X → Y) : Set (X × Y) :=
  {p | p.2 = f p.1}

@[simp] theorem d000060 (f : X → Y) (p : X × Y) :
    p ∈ _root_.GD.N0230.N0582.d000059 f ↔ p.2 = f p.1 := Iff.rfl



theorem d000061
    (f : X → Y) (s : Set Y) :
    f ⁻¹' s = Prod.fst '' (_root_.GD.N0230.N0582.d000059 f ∩ (Set.univ ×ˢ s)) := by
  ext x
  constructor
  · intro hx
    refine ⟨(x, f x), ?_, rfl⟩
    exact ⟨rfl, Set.mem_prod.2 ⟨Set.mem_univ x, hx⟩⟩
  · rintro ⟨p, ⟨hpGraph, hpSlice⟩, rfl⟩
    have hpMem : p.2 ∈ s := (Set.mem_prod.1 hpSlice).2
    simpa [_root_.GD.N0230.N0582.d000059] using hpGraph ▸ hpMem






theorem d000062 [CompactSpace Y]
    (f : X → Y) (hgraph : IsClosed (_root_.GD.N0230.N0582.d000059 f)) :
    Continuous f := by
  rw [continuous_iff_isClosed]
  intro s hs
  rw [_root_.GD.N0230.N0582.d000061]
  exact isClosedMap_fst_of_compactSpace _
    (hgraph.inter (isClosed_univ.prod hs))





theorem d000063 [CompactSpace X]
    (f : X → X) (hgraph : IsClosed (_root_.GD.N0230.N0582.d000059 f)) :
    Continuous f :=
  _root_.GD.N0230.N0582.d000062 f hgraph

end N0582
end N0230
end GD

#print axioms _root_.GD.N0230.N0582.d000062
#print axioms _root_.GD.N0230.N0582.d000063
