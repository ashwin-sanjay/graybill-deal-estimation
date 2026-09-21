import GD.Module0060



















namespace GD
namespace N0230
namespace N0654

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596

variable {G Theta D O : Type*}


def d000875
    (objective : ℕ → D → O) (i : ℕ) (d : D) : Fin i → O :=
  fun j ↦ objective j.val d

variable [Group G] [MulAction G D]



def d000876
    [Preorder O]
    (objective : ℕ → D → O)
    (transform : (g : G) → (i : ℕ) → (Fin i → O) → O → O) : Prop :=
  (∀ g i lower, Monotone (transform g i lower)) ∧
    ∀ g i d,
      objective i (g • d) =
        transform g i (_root_.GD.N0230.N0654.d000875 objective i d) (objective i d)



theorem d000877
    [PartialOrder O]
    (objective : ℕ → D → O)
    (transform : (g : G) → (i : ℕ) → (Fin i → O) → O → O)
    (C : Set D) (p : D)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform)
    (hlex : _root_.GD.N0230.N0596.d000730 objective C p) :
    ∀ (i : ℕ) (g : G), objective i (g • p) = objective i p := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro g
      have hgpC : g • p ∈ C := hC g hlex.1
      have hprevGp : ∀ j < i,
          objective j (g • p) = objective j p := by
        intro j hj
        exact ih j hj g
      have hminGp : objective i p ≤ objective i (g • p) :=
        hlex.2 i (g • p) hgpC hprevGp
      let q : D := g⁻¹ • p
      have hqC : q ∈ C := hC g⁻¹ hlex.1
      have hprevQ : ∀ j < i, objective j q = objective j p := by
        intro j hj
        exact ih j hj g⁻¹
      have hminQ : objective i p ≤ objective i q :=
        hlex.2 i q hqC hprevQ
      have hlowerQ : _root_.GD.N0230.N0654.d000875 objective i q =
          _root_.GD.N0230.N0654.d000875 objective i p := by
        funext j
        exact hprevQ j.val j.isLt
      have hcovP := hcov.2 g i p
      have hcovQ := hcov.2 g i q
      have hgq : g • q = p := by
        simp [q]
      rw [hgq, hlowerQ] at hcovQ
      have hforward : objective i (g • p) ≤ objective i p := by
        calc
          objective i (g • p) =
              transform g i (_root_.GD.N0230.N0654.d000875 objective i p)
                (objective i p) := hcovP
          _ ≤ transform g i (_root_.GD.N0230.N0654.d000875 objective i p)
                (objective i q) := hcov.1 g i _ hminQ
          _ = objective i p := hcovQ.symm
      exact le_antisymm hforward hminGp



theorem d000878
    [PartialOrder O]
    (objective : ℕ → D → O)
    (transform : (g : G) → (i : ℕ) → (Fin i → O) → O → O)
    (C : Set D) (p : D)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform)
    (hlex : _root_.GD.N0230.N0596.d000730 objective C p)
    (hfaithful : _root_.GD.N0230.N0596.d000731 objective C p) :
    ∀ g : G, g • p = p := by
  intro g
  apply hfaithful (g • p) (hC g hlex.1)
  intro i
  exact _root_.GD.N0230.N0654.d000877
    objective transform C p hC hcov hlex i g


theorem d000879
    [PartialOrder O]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → O)
    (transform : (g : G) → (i : ℕ) → (Fin i → O) → O → O)
    (C : Set D) (p : D)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform)
    (hlex : _root_.GD.N0230.N0596.d000730 objective C p)
    (hfaithful : _root_.GD.N0230.N0596.d000731 objective C p) :
    (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    ⟨_root_.GD.N0230.N0654.d000878
        objective transform C p hC hcov hlex hfaithful,
      _root_.GD.N0230.N0596.d000733
        risk objective C p hhereditary hmono hlex hfaithful⟩

end N0654
end N0230
end GD

#print axioms _root_.GD.N0230.N0654.d000877
#print axioms _root_.GD.N0230.N0654.d000878
#print axioms _root_.GD.N0230.N0654.d000879
