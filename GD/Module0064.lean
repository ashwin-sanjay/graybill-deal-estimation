import Mathlib.Analysis.Convex.Function
import GD.Module0063















namespace GD
namespace N0230
namespace N0595

open Set
open _root_.GD.N0230.N0566
open _root_.GD.N0230.N0583

variable {D : Type*} [AddCommMonoid D] [Module ℝ D]

omit [AddCommMonoid D] [Module ℝ D] in

theorem d000759
    (objective : ℕ → D → ℝ) (C : Set D) :
    ∀ i, _root_.GD.N0230.N0566.d000753 objective C i ⊆ C := by
  intro i
  induction i with
  | zero =>
      simp
  | succ i ih =>
      exact (_root_.GD.N0230.N0583.d000746 objective C
        (_root_.GD.N0230.N0566.d000753 objective C)
        (_root_.GD.N0230.N0566.d000756 objective C) i).trans ih



theorem d000760
    (objective : ℕ → D → ℝ) (C : Set D)
    (hconvex : ∀ i, ConvexOn ℝ C (objective i)) :
    ∀ i, Convex ℝ (_root_.GD.N0230.N0566.d000753 objective C i) := by
  intro i
  induction i with
  | zero =>
      simpa using (hconvex 0).1
  | succ i ih =>
      rw [_root_.GD.N0230.N0566.d000755]
      intro x hx y hy a b ha hb hab
      have hzPrev : a • x + b • y ∈ _root_.GD.N0230.N0566.d000753 objective C i :=
        ih hx.1 hy.1 ha hb hab
      refine ⟨hzPrev, ?_⟩
      intro e he
      have hxC : x ∈ C := _root_.GD.N0230.N0595.d000759 objective C i hx.1
      have hyC : y ∈ C := _root_.GD.N0230.N0595.d000759 objective C i hy.1
      have hJensen := (hconvex i).2 hxC hyC ha hb hab
      have hxmin : objective i x ≤ objective i e := hx.2 e he
      have hymin : objective i y ≤ objective i e := hy.2 e he
      calc
        objective i (a • x + b • y) ≤
            a • objective i x + b • objective i y := hJensen
        _ ≤ a • objective i e + b • objective i e := by
          exact add_le_add (smul_le_smul_of_nonneg_left hxmin ha)
            (smul_le_smul_of_nonneg_left hymin hb)
        _ = objective i e := by
          simp only [smul_eq_mul]
          rw [← add_mul, hab, one_mul]


def d000761
    (objective : ℕ → D → ℝ) (C : Set D) : Set D :=
  ⋂ i, _root_.GD.N0230.N0566.d000753 objective C i

omit [AddCommMonoid D] [Module ℝ D] in
theorem d000762
    (objective : ℕ → D → ℝ) (C : Set D) (p : D) :
    p ∈ _root_.GD.N0230.N0595.d000761 objective C ↔
      ∀ i, p ∈ _root_.GD.N0230.N0566.d000753 objective C i := by
  simp [_root_.GD.N0230.N0595.d000761]


theorem d000763
    (objective : ℕ → D → ℝ) (C : Set D)
    (hconvex : ∀ i, ConvexOn ℝ C (objective i)) :
    Convex ℝ (_root_.GD.N0230.N0595.d000761 objective C) := by
  exact convex_iInter (_root_.GD.N0230.N0595.d000760 objective C hconvex)

omit [AddCommMonoid D] [Module ℝ D] in


theorem d000764
    (objective : ℕ → D → ℝ) (C : Set D) (f : D → D)
    (hmapC : MapsTo f C C)
    (hinvariant : ∀ i d, d ∈ C → objective i (f d) = objective i d) :
    ∀ i, MapsTo f (_root_.GD.N0230.N0566.d000753 objective C i)
      (_root_.GD.N0230.N0566.d000753 objective C i) := by
  intro i
  induction i with
  | zero =>
      simpa using hmapC
  | succ i ih =>
      intro d hd
      rw [_root_.GD.N0230.N0566.d000755] at hd ⊢
      refine ⟨ih hd.1, ?_⟩
      intro e he
      rw [hinvariant i d
        (_root_.GD.N0230.N0595.d000759 objective C i hd.1)]
      exact hd.2 e he

omit [AddCommMonoid D] [Module ℝ D] in


theorem d000765
    (objective : ℕ → D → ℝ) (C : Set D) (f : D → D)
    (hmapC : MapsTo f C C)
    (hinvariant : ∀ i d, d ∈ C → objective i (f d) = objective i d) :
    MapsTo f (_root_.GD.N0230.N0595.d000761 objective C)
      (_root_.GD.N0230.N0595.d000761 objective C) := by
  intro d hd
  rw [_root_.GD.N0230.N0595.d000762] at hd ⊢
  intro i
  exact _root_.GD.N0230.N0595.d000764 objective C f hmapC hinvariant i (hd i)

section Topology

variable [TopologicalSpace D] [T2Space D]

omit [AddCommMonoid D] [Module ℝ D] in


theorem d000766
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCnonempty : C.Nonempty) (hCcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuous (objective i)) :
    (_root_.GD.N0230.N0595.d000761 objective C).Nonempty := by
  obtain ⟨p, hp, _hlex⟩ :=
    _root_.GD.N0230.N0566.d000757 objective C hCnonempty hCcompact hlsc
  exact ⟨p, (_root_.GD.N0230.N0595.d000762 objective C p).2 hp⟩

omit [AddCommMonoid D] [Module ℝ D] in

theorem d000767
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCnonempty : C.Nonempty) (hCcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuous (objective i)) :
    IsClosed (_root_.GD.N0230.N0595.d000761 objective C) := by
  have hfaces := _root_.GD.N0230.N0566.d000758
    objective C hCnonempty hCcompact hlsc
  exact isClosed_iInter (fun i => (hfaces i).2.2)

omit [AddCommMonoid D] [Module ℝ D] in

theorem d000768
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCnonempty : C.Nonempty) (hCcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuous (objective i)) :
    IsCompact (_root_.GD.N0230.N0595.d000761 objective C) := by
  refine hCcompact.of_isClosed_subset
    (_root_.GD.N0230.N0595.d000767 objective C hCnonempty hCcompact hlsc) ?_
  intro p hp
  have hp0 : p ∈ _root_.GD.N0230.N0566.d000753 objective C 0 :=
    (_root_.GD.N0230.N0595.d000762 objective C p).1 hp 0
  simpa using hp0



theorem d000769
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCnonempty : C.Nonempty) (hCcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuous (objective i))
    (hconvex : ∀ i, ConvexOn ℝ C (objective i)) :
    (_root_.GD.N0230.N0595.d000761 objective C).Nonempty ∧
      IsCompact (_root_.GD.N0230.N0595.d000761 objective C) ∧
      Convex ℝ (_root_.GD.N0230.N0595.d000761 objective C) := by
  exact ⟨_root_.GD.N0230.N0595.d000766 objective C hCnonempty hCcompact hlsc,
    _root_.GD.N0230.N0595.d000768 objective C hCnonempty hCcompact hlsc,
    _root_.GD.N0230.N0595.d000763 objective C hconvex⟩

end Topology

end N0595
end N0230
end GD

#print axioms _root_.GD.N0230.N0595.d000760
#print axioms _root_.GD.N0230.N0595.d000765
#print axioms _root_.GD.N0230.N0595.d000766
#print axioms _root_.GD.N0230.N0595.d000768
#print axioms _root_.GD.N0230.N0595.d000769
