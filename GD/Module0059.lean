import GD.Module0055




















namespace GD
namespace N0230
namespace N0616

open _root_.GD.N0230.N0608

variable {G Theta D O : Type*}


def d000721
    (risk : Theta → D → ENNReal) (C : Set D) : Prop :=
  ∀ ⦃d e : D⦄, d ∈ C → _root_.GD.N0230.N0608.d000672 risk e d → e ∈ C



def d000722
    [Preorder O] {n : ℕ} (objective : Fin n → D → O)
    (C : Set D) (p : D) : Prop :=
  p ∈ C ∧ ∀ (i : Fin n) (d : D), d ∈ C →
    (∀ j : Fin n, j < i → objective j d = objective j p) →
      objective i p ≤ objective i d



def d000723
    {n : ℕ} (objective : Fin n → D → O)
    (C : Set D) (p : D) : Prop :=
  ∀ d, d ∈ C → (∀ i, objective i d = objective i p) → d = p


def d000724
    [Preorder O] {n : ℕ} (risk : Theta → D → ENNReal)
    (objective : Fin n → D → O) : Prop :=
  ∀ i ⦃e d : D⦄, _root_.GD.N0230.N0608.d000672 risk e d →
    objective i e ≤ objective i d



theorem d000725
    [PartialOrder O]
    {n : ℕ}
    (risk : Theta → D → ENNReal)
    (objective : Fin n → D → O)
    (C : Set D) (p : D)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0616.d000724 risk objective)
    (hlex : _root_.GD.N0230.N0616.d000722 objective C p)
    (hfaithful : _root_.GD.N0230.N0616.d000723 objective C p) :
    _root_.GD.N0230.N0608.d000674 risk p := by
  intro e hep
  have heC : e ∈ C := hhereditary hlex.1 hep
  have hall : ∀ i : Fin n, objective i e = objective i p := by
    intro i
    induction i using Fin.strong_induction_on with
    | h i ih =>
        apply le_antisymm
        · exact hmono i hep
        · exact hlex.2 i e heC (fun j hj ↦ ih j hj)
  exact hfaithful e heC hall

variable [Group G] [MulAction G D]


def d000726 (C : Set D) : Prop :=
  ∀ (g : G) ⦃d : D⦄, d ∈ C → g • d ∈ C


def d000727
    {n : ℕ} (objective : Fin n → D → O) : Prop :=
  ∀ (i : Fin n) (g : G) (d : D), objective i (g • d) = objective i d




theorem d000728
    {n : ℕ}
    (objective : Fin n → D → O)
    (C : Set D) (p : D)
    (hpC : p ∈ C)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : _root_.GD.N0230.N0616.d000727 (G := G) objective)
    (hfaithful : _root_.GD.N0230.N0616.d000723 objective C p) :
    ∀ g : G, g • p = p := by
  intro g
  apply hfaithful (g • p) (hC g hpC)
  intro i
  exact hinvariant i g p




theorem d000729
    [PartialOrder O]
    {n : ℕ}
    (risk : Theta → D → ENNReal)
    (objective : Fin n → D → O)
    (C : Set D) (p : D)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0616.d000724 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : _root_.GD.N0230.N0616.d000727 (G := G) objective)
    (hlex : _root_.GD.N0230.N0616.d000722 objective C p)
    (hfaithful : _root_.GD.N0230.N0616.d000723 objective C p) :
    (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    ⟨_root_.GD.N0230.N0616.d000728
        objective C p hlex.1 hC hinvariant hfaithful,
      _root_.GD.N0230.N0616.d000725
        risk objective C p hhereditary hmono hlex hfaithful⟩

end N0616
end N0230
end GD

#print axioms _root_.GD.N0230.N0616.d000725
#print axioms _root_.GD.N0230.N0616.d000728
#print axioms _root_.GD.N0230.N0616.d000729
