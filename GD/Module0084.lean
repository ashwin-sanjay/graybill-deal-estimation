import GD.Module0060





















namespace GD
namespace N0230
namespace N0701

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596

variable {G Theta D : Type*}


def d001113
    {n : ℕ} (objective : Fin n → D → ℝ)
    (i : Fin n) (d : D) : Fin i.val → ℝ :=
  fun j ↦ objective ⟨j.val, j.isLt.trans i.isLt⟩ d

variable [Group G] [MulAction G D]


def d001114
    {n : ℕ} (objective : Fin n → D → ℝ)
    (scale : G → Fin n → ℝ)
    (offset : (g : G) → (i : Fin n) → (Fin i.val → ℝ) → ℝ) : Prop :=
  (∀ g i, 0 < scale g i) ∧
    ∀ g i d,
      objective i (g • d) =
        scale g i * objective i d +
          offset g i (_root_.GD.N0230.N0701.d001113 objective i d)



theorem d001115
    {n : ℕ}
    (objective : Fin n → D → ℝ)
    (scale : G → Fin n → ℝ)
    (offset : (g : G) → (i : Fin n) → (Fin i.val → ℝ) → ℝ)
    (C : Set D) (p : D)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001114 objective scale offset)
    (hlex : _root_.GD.N0230.N0616.d000722 objective C p) :
    ∀ (i : Fin n) (g : G), objective i (g • p) = objective i p := by
  intro i
  induction i using Fin.strong_induction_on with
  | h i ih =>
      intro g
      have hgpC : g • p ∈ C := hC g hlex.1
      have hprevGp : ∀ j : Fin n, j < i →
          objective j (g • p) = objective j p := by
        intro j hj
        exact ih j hj g
      have hminGp : objective i p ≤ objective i (g • p) :=
        hlex.2 i (g • p) hgpC hprevGp
      let q : D := g⁻¹ • p
      have hqC : q ∈ C := hC g⁻¹ hlex.1
      have hprevQ : ∀ j : Fin n, j < i →
          objective j q = objective j p := by
        intro j hj
        exact ih j hj g⁻¹
      have hminQ : objective i p ≤ objective i q :=
        hlex.2 i q hqC hprevQ
      have hlowerQ : _root_.GD.N0230.N0701.d001113 objective i q =
          _root_.GD.N0230.N0701.d001113 objective i p := by
        funext j
        exact hprevQ ⟨j.val, j.isLt.trans i.isLt⟩ j.isLt
      have hcovP := hcov.2 g i p
      have hcovQ := hcov.2 g i q
      have hgq : g • q = p := by
        simp [q]
      rw [hgq, hlowerQ] at hcovQ
      have hscale : 0 < scale g i := hcov.1 g i
      apply le_antisymm
      · nlinarith
      · exact hminGp



theorem d001116
    {n : ℕ}
    (objective : Fin n → D → ℝ)
    (scale : G → Fin n → ℝ)
    (offset : (g : G) → (i : Fin n) → (Fin i.val → ℝ) → ℝ)
    (C : Set D) (p : D)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001114 objective scale offset)
    (hlex : _root_.GD.N0230.N0616.d000722 objective C p)
    (hfaithful : _root_.GD.N0230.N0616.d000723 objective C p) :
    ∀ g : G, g • p = p := by
  intro g
  apply hfaithful (g • p) (hC g hlex.1)
  intro i
  exact _root_.GD.N0230.N0701.d001115
    objective scale offset C p hC hcov hlex i g




theorem d001117
    {n : ℕ}
    (risk : Theta → D → ENNReal)
    (objective : Fin n → D → ℝ)
    (scale : G → Fin n → ℝ)
    (offset : (g : G) → (i : Fin n) → (Fin i.val → ℝ) → ℝ)
    (C : Set D) (p : D)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0616.d000724 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001114 objective scale offset)
    (hlex : _root_.GD.N0230.N0616.d000722 objective C p)
    (hfaithful : _root_.GD.N0230.N0616.d000723 objective C p) :
    (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    ⟨_root_.GD.N0230.N0701.d001116
        objective scale offset C p hC hcov hlex hfaithful,
      _root_.GD.N0230.N0616.d000725
        risk objective C p hhereditary hmono hlex hfaithful⟩




def d001118
    (objective : ℕ → D → ℝ) (i : ℕ) (d : D) : Fin i → ℝ :=
  fun j ↦ objective j.val d


def d001119
    (objective : ℕ → D → ℝ)
    (scale : G → ℕ → ℝ)
    (offset : (g : G) → (i : ℕ) → (Fin i → ℝ) → ℝ) : Prop :=
  (∀ g i, 0 < scale g i) ∧
    ∀ g i d,
      objective i (g • d) =
        scale g i * objective i d +
          offset g i (_root_.GD.N0230.N0701.d001118 objective i d)




theorem d001120
    (objective : ℕ → D → ℝ)
    (scale : G → ℕ → ℝ)
    (offset : (g : G) → (i : ℕ) → (Fin i → ℝ) → ℝ)
    (C : Set D) (p : D)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001119 objective scale offset)
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
      have hlowerQ : _root_.GD.N0230.N0701.d001118 objective i q =
          _root_.GD.N0230.N0701.d001118 objective i p := by
        funext j
        exact hprevQ j.val j.isLt
      have hcovP := hcov.2 g i p
      have hcovQ := hcov.2 g i q
      have hgq : g • q = p := by
        simp [q]
      rw [hgq, hlowerQ] at hcovQ
      have hscale : 0 < scale g i := hcov.1 g i
      apply le_antisymm
      · nlinarith
      · exact hminGp


theorem d001121
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ℝ)
    (scale : G → ℕ → ℝ)
    (offset : (g : G) → (i : ℕ) → (Fin i → ℝ) → ℝ)
    (C : Set D) (p : D)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001119 objective scale offset)
    (hlex : _root_.GD.N0230.N0596.d000730 objective C p)
    (hfaithful : _root_.GD.N0230.N0596.d000731 objective C p) :
    (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  constructor
  · intro g
    apply hfaithful (g • p) (hC g hlex.1)
    intro i
    exact _root_.GD.N0230.N0701.d001120
      objective scale offset C p hC hcov hlex i g
  · exact _root_.GD.N0230.N0596.d000733
      risk objective C p hhereditary hmono hlex hfaithful

end N0701
end N0230
end GD

#print axioms _root_.GD.N0230.N0701.d001115
#print axioms _root_.GD.N0230.N0701.d001116
#print axioms _root_.GD.N0230.N0701.d001117
#print axioms _root_.GD.N0230.N0701.d001120
#print axioms _root_.GD.N0230.N0701.d001121
