import GD.Module0135





























namespace GD
namespace N0230
namespace N0628

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0581
open _root_.GD.N0230.N0701

variable {G Theta D : Type*}


def d001542
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ)
    (tax : ℕ → D → D → ℝ) : Prop :=
  ∀ i p q,
    objective i (_root_.GD.N0230.N0718.d001528 p q) + tax i p q =
      (objective i p + objective i q) / 2



def d001543
    (tax : ℕ → D → D → ℝ) : Prop :=
  ∀ p q, p ≠ q → ∃ i, 0 < tax i p q



theorem d001544
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    {p q : D} (hp : ∀ i, p ∈ face i) (hq : ∀ i, q ∈ face i)
    (i : ℕ) :
    objective i p = objective i q := by
  have hpNext := hp (i + 1)
  have hqNext := hq (i + 1)
  rw [htower.2 i] at hpNext hqNext
  exact le_antisymm (hpNext.2 q (hq i)) (hqNext.2 p (hp i))




theorem d001545
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ℝ)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hexact : _root_.GD.N0230.N0628.d001542 objective tax)
    (hcomplete : _root_.GD.N0230.N0628.d001543 tax)
    {p q : D} (hp : ∀ i, p ∈ face i) (hq : ∀ i, q ∈ face i)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  obtain ⟨i, hitax⟩ := hcomplete p q hpq
  refine ⟨i, ?_⟩
  have heq := _root_.GD.N0230.N0628.d001544
    objective C face htower hp hq i
  have hmid := hexact i p q
  linarith






theorem d001546
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ℝ)
    (scale : G → ℕ → ℝ)
    (offset : (g : G) → (i : ℕ) → (Fin i → ℝ) → ℝ)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hconvex : ∀ i, Convex ℝ (face i))
    (hexact : _root_.GD.N0230.N0628.d001542 objective tax)
    (hcomplete : _root_.GD.N0230.N0628.d001543 tax)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001119 objective scale offset) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  apply
    _root_.GD.N0230.N0581.d001541
      risk objective C face scale offset htower hCnonempty hcompact hlsc
      hconvex
  · intro p q hp hq hpq
    exact _root_.GD.N0230.N0628.d001545
      objective C face tax htower hexact hcomplete hp hq hpq
  · exact hhereditary
  · exact hmono
  · exact hC
  · exact hcov

end N0628
end N0230
end GD

#print axioms _root_.GD.N0230.N0628.d001544
#print axioms _root_.GD.N0230.N0628.d001545
#print axioms _root_.GD.N0230.N0628.d001546
