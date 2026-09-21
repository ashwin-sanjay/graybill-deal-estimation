import GD.Module0145
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Compactness.Compact
































open Set

namespace GD
namespace N0230
namespace N0567

noncomputable section

open _root_.GD.N0230.N0599
open _root_.GD.N0230.N0718

universe u v

variable {A : Type u} {D : Type v}



structure d001622
    (A : Type u) (D : Type v) (C : Set D) (lo hi : ℝ) where
  profile : A → D → ℝ
  mem_Icc : ∀ a d, d ∈ C → profile a d ∈ Set.Icc lo hi


abbrev d001623 (C : Set D) (lo hi : ℝ) :=
  C → Set.Icc lo hi


def d001624
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) (a : A) :
    _root_.GD.N0230.N0567.d001623 C lo hi :=
  fun d ↦ ⟨F.profile a d.1, F.mem_Icc a d.1 d.2⟩



abbrev d001625
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) :=
  closure (Set.range (_root_.GD.N0230.N0567.d001624 F))




def d001626
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) :
    A → _root_.GD.N0230.N0567.d001625 F :=
  Set.inclusion subset_closure ∘
    Set.rangeFactorization (_root_.GD.N0230.N0567.d001624 F)

@[simp] theorem d001627
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) (a : A) :
    (_root_.GD.N0230.N0567.d001626 F a).1 = _root_.GD.N0230.N0567.d001624 F a := rfl


theorem d001628
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) :
    DenseRange (_root_.GD.N0230.N0567.d001626 F) := by
  exact
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      Set.rangeFactorization_surjective.denseRange
      (continuous_inclusion subset_closure)



noncomputable instance d001629
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) :
    CompactSpace (_root_.GD.N0230.N0567.d001625 F) := by
  letI : CompactSpace (Set.Icc lo hi) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  letI : CompactSpace (_root_.GD.N0230.N0567.d001623 C lo hi) :=
    Pi.compactSpace
  exact isCompact_iff_compactSpace.mp isClosed_closure.isCompact


noncomputable instance d001630
    {C : Set D} {lo hi : ℝ} [Nonempty A]
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) :
    Nonempty (_root_.GD.N0230.N0567.d001625 F) :=
  ⟨_root_.GD.N0230.N0567.d001626 F (Classical.arbitrary A)⟩



def d001631
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (k : _root_.GD.N0230.N0567.d001625 F) (d : D) : ℝ := by
  classical
  exact if hd : d ∈ C then ((k.1 ⟨d, hd⟩ : Set.Icc lo hi) : ℝ) else 0

@[simp] theorem d001632
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (k : _root_.GD.N0230.N0567.d001625 F) {d : D} (hd : d ∈ C) :
    _root_.GD.N0230.N0567.d001631 F k d =
      ((k.1 ⟨d, hd⟩ : Set.Icc lo hi) : ℝ) := by
  simp [_root_.GD.N0230.N0567.d001631, hd]

@[simp] theorem d001633
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (a : A) {d : D} (hd : d ∈ C) :
    _root_.GD.N0230.N0567.d001631 F (_root_.GD.N0230.N0567.d001626 F a) d =
      F.profile a d := by
  simp [_root_.GD.N0230.N0567.d001631, hd, _root_.GD.N0230.N0567.d001624]




theorem d001634
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) (d : D) :
    Continuous (fun k : _root_.GD.N0230.N0567.d001625 F ↦ _root_.GD.N0230.N0567.d001631 F k d) := by
  by_cases hd : d ∈ C
  · have hEval :
        Continuous
          (fun k : _root_.GD.N0230.N0567.d001625 F ↦
            k.1 (⟨d, hd⟩ : C)) :=
      (continuous_apply (⟨d, hd⟩ : C)).comp continuous_subtype_val
    rw [show
      (fun k : _root_.GD.N0230.N0567.d001625 F ↦ _root_.GD.N0230.N0567.d001631 F k d) =
        (fun k : _root_.GD.N0230.N0567.d001625 F ↦
          ((k.1 (⟨d, hd⟩ : C) : Set.Icc lo hi) : ℝ)) by
      funext k
      exact _root_.GD.N0230.N0567.d001632 F k hd]
    exact continuous_subtype_val.comp hEval
  · simpa [_root_.GD.N0230.N0567.d001631, hd] using
      (continuous_const :
        Continuous (fun _ : _root_.GD.N0230.N0567.d001625 F ↦ (0 : ℝ)))



theorem d001635
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (objective : D → ℝ) {d : D} (hd : d ∈ C) :
    IsLUB (Set.range (fun a ↦ F.profile a d)) (objective d) ↔
      IsLUB
        (Set.range (fun k : _root_.GD.N0230.N0567.d001625 F ↦
          _root_.GD.N0230.N0567.d001631 F k d))
        (objective d) := by
  have h :=
    _root_.GD.N0230.N0599.d001615
      (_root_.GD.N0230.N0567.d001626 F)
      (_root_.GD.N0230.N0567.d001628 F)
      (_root_.GD.N0230.N0567.d001631 F) objective d
      (_root_.GD.N0230.N0567.d001634 F d)
  simpa only [_root_.GD.N0230.N0567.d001633 F _ hd] using h



def d001636
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) (d : D) : ℝ :=
  ⨆ a, F.profile a d


theorem d001637
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    {d : D} (hd : d ∈ C) :
    BddAbove (Set.range (fun a ↦ F.profile a d)) := by
  refine ⟨hi, ?_⟩
  rintro value ⟨a, rfl⟩
  exact (F.mem_Icc a d hd).2



theorem d001638
    {C : Set D} {lo hi : ℝ} [Nonempty A]
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    {d : D} (hd : d ∈ C) :
    IsLUB (Set.range (fun a ↦ F.profile a d))
      (_root_.GD.N0230.N0567.d001636 F d) := by
  exact isLUB_ciSup (_root_.GD.N0230.N0567.d001637 F hd)



theorem d001639
    {C : Set D} {lo hi : ℝ} [Nonempty A]
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    {d : D} (hd : d ∈ C) :
    IsLUB
      (Set.range (fun k : _root_.GD.N0230.N0567.d001625 F ↦
        _root_.GD.N0230.N0567.d001631 F k d))
      (_root_.GD.N0230.N0567.d001636 F d) :=
  (_root_.GD.N0230.N0567.d001635 F
    (_root_.GD.N0230.N0567.d001636 F) hd).1
      (_root_.GD.N0230.N0567.d001638 F hd)



theorem d001640
    {C : Set D} {lo hi : ℝ}
    [TopologicalSpace D]
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (hlsc : ∀ a, LowerSemicontinuousOn (F.profile a) C) :
    LowerSemicontinuousOn (_root_.GD.N0230.N0567.d001636 F) C := by
  unfold _root_.GD.N0230.N0567.d001636
  exact lowerSemicontinuousOn_ciSup
    (fun d hd ↦ _root_.GD.N0230.N0567.d001637 F hd) hlsc

section MidpointTax

variable [AddCommGroup D] [Module ℝ D]


def d001641
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (k : _root_.GD.N0230.N0567.d001625 F) (p q : D) : ℝ :=
  (_root_.GD.N0230.N0567.d001631 F k p + _root_.GD.N0230.N0567.d001631 F k q) / 2 -
    _root_.GD.N0230.N0567.d001631 F k (_root_.GD.N0230.N0718.d001528 p q)



theorem d001642
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (k : _root_.GD.N0230.N0567.d001625 F) (p q : D) :
    _root_.GD.N0230.N0567.d001631 F k (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0230.N0567.d001641 F k p q =
      (_root_.GD.N0230.N0567.d001631 F k p +
        _root_.GD.N0230.N0567.d001631 F k q) / 2 := by
  unfold _root_.GD.N0230.N0567.d001641
  ring



theorem d001643
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi) (p q : D) :
    Continuous (fun k : _root_.GD.N0230.N0567.d001625 F ↦ _root_.GD.N0230.N0567.d001641 F k p q) := by
  unfold _root_.GD.N0230.N0567.d001641
  exact
    (((_root_.GD.N0230.N0567.d001634 F p).add
      (_root_.GD.N0230.N0567.d001634 F q)).div_const 2).sub
        (_root_.GD.N0230.N0567.d001634 F (_root_.GD.N0230.N0718.d001528 p q))



theorem d001644
    {C : Set D} {lo hi : ℝ}
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    {p q : D} (hp : p ∈ C) (hq : q ∈ C)
    (hmid : _root_.GD.N0230.N0718.d001528 p q ∈ C)
    (hphysical : ∀ a,
      F.profile a (_root_.GD.N0230.N0718.d001528 p q) ≤
        (F.profile a p + F.profile a q) / 2)
    (k : _root_.GD.N0230.N0567.d001625 F) :
    0 ≤ _root_.GD.N0230.N0567.d001641 F k p q := by
  apply DenseRange.induction_on
    (p := fun z : _root_.GD.N0230.N0567.d001625 F ↦ 0 ≤ _root_.GD.N0230.N0567.d001641 F z p q)
    (_root_.GD.N0230.N0567.d001628 F) k
  · exact isClosed_le continuous_const (_root_.GD.N0230.N0567.d001643 F p q)
  · intro a
    simp only [_root_.GD.N0230.N0567.d001641,
      _root_.GD.N0230.N0567.d001633 F a hp,
      _root_.GD.N0230.N0567.d001633 F a hq,
      _root_.GD.N0230.N0567.d001633 F a hmid]
    exact sub_nonneg.mpr (hphysical a)



theorem d001645
    {C : Set D} {lo hi : ℝ} [Nonempty A]
    (F : _root_.GD.N0230.N0567.d001622 A D C lo hi)
    (hconvex : ∀ a, ConvexOn ℝ C (F.profile a))
    {p q : D} (hp : p ∈ C) (hq : q ∈ C)
    (k : _root_.GD.N0230.N0567.d001625 F) :
    0 ≤ _root_.GD.N0230.N0567.d001641 F k p q := by
  have hCconvex : Convex ℝ C :=
    (hconvex (Classical.arbitrary A)).1
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hCconvex hp hq
    · norm_num
    · norm_num
    · norm_num
  apply _root_.GD.N0230.N0567.d001644 F hp hq hmid _ k
  intro a
  have h :=
    (hconvex a).2 hp hq
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  change
    F.profile a (_root_.GD.N0230.N0718.d001528 p q) ≤
      (1 / 2 : ℝ) * F.profile a p +
        (1 / 2 : ℝ) * F.profile a q at h
  calc
    F.profile a (_root_.GD.N0230.N0718.d001528 p q) ≤
        (1 / 2 : ℝ) * F.profile a p +
          (1 / 2 : ℝ) * F.profile a q := h
    _ = (F.profile a p + F.profile a q) / 2 := by ring

end MidpointTax

end

end N0567
end N0230
end GD

#print axioms _root_.GD.N0230.N0567.d001629
#print axioms _root_.GD.N0230.N0567.d001634
#print axioms _root_.GD.N0230.N0567.d001639
#print axioms _root_.GD.N0230.N0567.d001642
#print axioms _root_.GD.N0230.N0567.d001645
