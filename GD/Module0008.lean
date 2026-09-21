import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic













open Set

namespace GD
namespace N0230
namespace N0584

variable {X : Type*} [TopologicalSpace X] [T2Space X]



theorem d000064
    (K C : Set X) (A : ℕ → Set X)
    (hK : IsCompact K)
    (hAclosed : ∀ j, IsClosed (A j))
    (hAdecreasing : ∀ j, A (j + 1) ⊆ A j)
    (hlimit : (⋂ j, A j) ⊆ C)
    (hdisjoint : Disjoint K C) :
    ∃ j, Disjoint K (A j) := by
  by_contra hstage
  push Not at hstage
  have hnonempty : ∀ j, (K ∩ A j).Nonempty := by
    intro j
    exact not_disjoint_iff_nonempty_inter.mp (hstage j)
  have hclosed : ∀ j, IsClosed (K ∩ A j) := by
    intro j
    exact hK.isClosed.inter (hAclosed j)
  have hdecreasing : ∀ j, K ∩ A (j + 1) ⊆ K ∩ A j := by
    intro j x hx
    exact ⟨hx.1, hAdecreasing j hx.2⟩
  have hcompact0 : IsCompact (K ∩ A 0) :=
    hK.inter_right (hAclosed 0)
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun j ↦ K ∩ A j) hdecreasing hnonempty hcompact0 hclosed
  have hxK : x ∈ K := (Set.mem_iInter.mp hx 0).1
  have hxA : x ∈ ⋂ j, A j := by
    exact Set.mem_iInter.2 fun j ↦ (Set.mem_iInter.mp hx j).2
  exact (not_disjoint_iff.mpr ⟨x, hxK, hlimit hxA⟩) hdisjoint








theorem d000065
    {I : Type*} (K : Set X) (hK : IsCompact K)
    (f : I → X → ENNReal) (cap : I → ENNReal)
    (hlsc : ∀ i, LowerSemicontinuous (f i))
    (hdisjoint :
      Disjoint K (⋂ i, (f i) ⁻¹' Set.Iic (cap i))) :
    ∃ delta : NNReal, 0 < delta ∧
      Disjoint K
        (⋂ i, (f i) ⁻¹' Set.Iic (cap i + (delta : ENNReal))) := by
  let epsilon : ℕ → NNReal := fun j ↦ 1 / ((j : NNReal) + 1)
  let A : ℕ → Set X := fun j ↦
    ⋂ i, (f i) ⁻¹' Set.Iic (cap i + (epsilon j : ENNReal))
  let C : Set X := ⋂ i, (f i) ⁻¹' Set.Iic (cap i)
  have hAclosed : ∀ j, IsClosed (A j) := by
    intro j
    exact isClosed_iInter fun i ↦ (hlsc i).isClosed_preimage _
  have hAdecreasing : ∀ j, A (j + 1) ⊆ A j := by
    intro j x hx
    simp only [A, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic] at hx ⊢
    intro i
    refine (hx i).trans ?_
    gcongr
    exact Nat.one_div_le_one_div (Nat.le_succ j)
  have hlimit : (⋂ j, A j) ⊆ C := by
    intro x hx
    simp only [C, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
    intro i
    apply ENNReal.le_of_forall_pos_le_add
    intro eta heta hcap
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt heta
    have hxj : f i x ≤ cap i + (epsilon j : ENNReal) := by
      have hxA := Set.mem_iInter.mp hx j
      exact Set.mem_iInter.mp hxA i
    exact hxj.trans (by gcongr)
  obtain ⟨j, hj⟩ := _root_.GD.N0230.N0584.d000064
    K C A hK hAclosed hAdecreasing hlimit hdisjoint
  refine ⟨epsilon j, ?_, ?_⟩
  · dsimp only [epsilon]
    positivity
  · exact hj

end N0584
end N0230
end GD

#print axioms _root_.GD.N0230.N0584.d000064
#print axioms _root_.GD.N0230.N0584.d000065
