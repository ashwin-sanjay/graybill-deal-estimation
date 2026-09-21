import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff
















open Set

namespace GD.N0238



theorem d004298
    {X I : Type*} [TopologicalSpace X]
    (base : Set X)
    (hbase : IsCompact base)
    (P : I → X → Prop)
    (hP : ∀ i, IsClosed {x | P i x})
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ i, P i x) :
    ∃ u : Finset I, ¬ ∃ x, x ∈ base ∧ ∀ i ∈ u, P i x := by
  have hall :
      (base ∩ ⋂ i, {x | P i x}) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    exact hno ⟨x, hx.1, fun i ↦ mem_iInter.mp hx.2 i⟩
  obtain ⟨u, hu⟩ :=
    hbase.elim_finite_subfamily_closed
      (fun i ↦ {x | P i x}) hP hall
  refine ⟨u, ?_⟩
  rintro ⟨x, hxbase, hxP⟩
  have hx :
      x ∈ base ∩ ⋂ i ∈ u, {x | P i x} := by
    refine ⟨hxbase, ?_⟩
    simp only [mem_iInter, mem_setOf_eq]
    intro i hi
    exact hxP i hi
  rw [hu] at hx
  exact hx





theorem d004299
    {X I Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (base : Set X)
    (hbase : IsCompact base)
    (obs : I → X → Y)
    (target : I → Y)
    (hobs : ∀ i, Continuous (obs i))
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ i, obs i x = target i) :
    ∃ u : Finset I,
      ¬ ∃ x, x ∈ base ∧ ∀ i ∈ u, obs i x = target i := by
  apply _root_.GD.N0238.d004298
    base hbase (fun i x ↦ obs i x = target i)
  · intro i
    exact isClosed_eq (hobs i) continuous_const
  · exact hno


theorem d004300
    {X I : Type*} [TopologicalSpace X]
    (base : Set X)
    (hbase : IsCompact base)
    (obs : I → X → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ i, obs i x = 0) :
    ∃ u : Finset I,
      ¬ ∃ x, x ∈ base ∧ ∀ i ∈ u, obs i x = 0 :=
  _root_.GD.N0238.d004299
    base hbase obs (fun _ ↦ 0) hobs hno

end GD.N0238
