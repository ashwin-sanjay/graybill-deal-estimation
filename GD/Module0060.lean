import GD.Module0059













namespace GD
namespace N0230
namespace N0596

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616

variable {G Theta D O : Type*}


def d000730 [Preorder O]
    (objective : ℕ → D → O) (C : Set D) (p : D) : Prop :=
  p ∈ C ∧ ∀ (i : ℕ) (d : D), d ∈ C →
    (∀ j < i, objective j d = objective j p) →
      objective i p ≤ objective i d


def d000731
    (objective : ℕ → D → O) (C : Set D) (p : D) : Prop :=
  ∀ d, d ∈ C → (∀ i, objective i d = objective i p) → d = p



def d000732 [Preorder O]
    (risk : Theta → D → ENNReal) (objective : ℕ → D → O) : Prop :=
  ∀ i ⦃e d : D⦄, _root_.GD.N0230.N0608.d000672 risk e d →
    objective i e ≤ objective i d


theorem d000733
    [PartialOrder O]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → O)
    (C : Set D) (p : D)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hlex : _root_.GD.N0230.N0596.d000730 objective C p)
    (hfaithful : _root_.GD.N0230.N0596.d000731 objective C p) :
    _root_.GD.N0230.N0608.d000674 risk p := by
  intro e hep
  have heC : e ∈ C := hhereditary hlex.1 hep
  have hall : ∀ i : ℕ, objective i e = objective i p := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
        apply le_antisymm
        · exact hmono i hep
        · exact hlex.2 i e heC (fun j hj ↦ ih j hj)
  exact hfaithful e heC hall

variable [Group G] [MulAction G D]


def d000734
    (objective : ℕ → D → O) : Prop :=
  ∀ (i : ℕ) (g : G) (d : D), objective i (g • d) = objective i d



theorem d000735
    (objective : ℕ → D → O)
    (C : Set D) (p : D)
    (hpC : p ∈ C)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : _root_.GD.N0230.N0596.d000734 (G := G) objective)
    (hfaithful : _root_.GD.N0230.N0596.d000731 objective C p) :
    ∀ g : G, g • p = p := by
  intro g
  apply hfaithful (g • p) (hC g hpC)
  intro i
  exact hinvariant i g p



theorem d000736
    [PartialOrder O]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → O)
    (C : Set D) (p : D)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : _root_.GD.N0230.N0596.d000734 (G := G) objective)
    (hlex : _root_.GD.N0230.N0596.d000730 objective C p)
    (hfaithful : _root_.GD.N0230.N0596.d000731 objective C p) :
    (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    ⟨_root_.GD.N0230.N0596.d000735
        objective C p hlex.1 hC hinvariant hfaithful,
      _root_.GD.N0230.N0596.d000733
        risk objective C p hhereditary hmono hlex hfaithful⟩

end N0596
end N0230
end GD

#print axioms _root_.GD.N0230.N0596.d000733
#print axioms _root_.GD.N0230.N0596.d000735
#print axioms _root_.GD.N0230.N0596.d000736
