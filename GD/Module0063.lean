import GD.Module0062















namespace GD
namespace N0230
namespace N0566

open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0596

variable {D O : Type*}


def d000753 [Preorder O]
    (objective : ℕ → D → O) (C : Set D) : ℕ → Set D
  | 0 => C
  | n + 1 =>
      {d | d ∈ d000753 objective C n ∧
        ∀ e ∈ d000753 objective C n,
          objective n d ≤ objective n e}

@[simp] theorem d000754
    [Preorder O] (objective : ℕ → D → O) (C : Set D) :
    _root_.GD.N0230.N0566.d000753 objective C 0 = C :=
  rfl

@[simp] theorem d000755
    [Preorder O] (objective : ℕ → D → O) (C : Set D) (n : ℕ) :
    _root_.GD.N0230.N0566.d000753 objective C (n + 1) =
      {d | d ∈ _root_.GD.N0230.N0566.d000753 objective C n ∧
        ∀ e ∈ _root_.GD.N0230.N0566.d000753 objective C n,
          objective n d ≤ objective n e} :=
  rfl


theorem d000756
    [Preorder O] (objective : ℕ → D → O) (C : Set D) :
    _root_.GD.N0230.N0583.d000745 objective C (_root_.GD.N0230.N0566.d000753 objective C) := by
  exact ⟨rfl, fun _ ↦ rfl⟩

variable [TopologicalSpace D]



theorem d000757
    [T2Space D] [LinearOrder O]
    (objective : ℕ → D → O) (C : Set D)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuous (objective i)) :
    ∃ p, (∀ i, p ∈ _root_.GD.N0230.N0566.d000753 objective C i) ∧
      _root_.GD.N0230.N0596.d000730 objective C p := by
  exact _root_.GD.N0230.N0583.d000750
    objective C (_root_.GD.N0230.N0566.d000753 objective C)
    (_root_.GD.N0230.N0566.d000756 objective C)
    hCnonempty hcompact
    (fun i ↦ (hlsc i).lowerSemicontinuousOn _)



theorem d000758
    [T2Space D] [LinearOrder O]
    (objective : ℕ → D → O) (C : Set D)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuous (objective i)) :
    ∀ i, (_root_.GD.N0230.N0566.d000753 objective C i).Nonempty ∧
      IsCompact (_root_.GD.N0230.N0566.d000753 objective C i) ∧
      IsClosed (_root_.GD.N0230.N0566.d000753 objective C i) := by
  exact _root_.GD.N0230.N0583.d000748
    objective C (_root_.GD.N0230.N0566.d000753 objective C)
    (_root_.GD.N0230.N0566.d000756 objective C)
    hCnonempty hcompact
    (fun i ↦ (hlsc i).lowerSemicontinuousOn _)

end N0566
end N0230
end GD

#print axioms _root_.GD.N0230.N0566.d000756
#print axioms _root_.GD.N0230.N0566.d000757
#print axioms _root_.GD.N0230.N0566.d000758
