import GD.Module0060
















namespace GD
namespace N0230
namespace N0583

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596

variable {G Theta D O : Type*}



def d000745 [Preorder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D) : Prop :=
  face 0 = C ∧
    ∀ i, face (i + 1) =
      {d | d ∈ face i ∧ ∀ e ∈ face i, objective i d ≤ objective i e}


theorem d000746
    [Preorder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face) (i : ℕ) :
    face (i + 1) ⊆ face i := by
  rw [htower.2 i]
  intro d hd
  exact hd.1


theorem d000747
    [PartialOrder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    {p : D} (hp : ∀ i, p ∈ face i) :
    _root_.GD.N0230.N0596.d000730 objective C p := by
  have hpC : p ∈ C := by
    rw [← htower.1]
    exact hp 0
  refine ⟨hpC, ?_⟩
  intro i d hdC hties
  have hdface : ∀ n, (∀ j < n, objective j d = objective j p) → d ∈ face n := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [htower.1]
        exact hdC
    | succ n ih =>
        intro hprior
        rw [htower.2 n]
        have hdPrev : d ∈ face n :=
          ih (fun j hj ↦ hprior j (Nat.lt_trans hj (Nat.lt_succ_self n)))
        refine ⟨hdPrev, ?_⟩
        intro e he
        have hpMin : ∀ x ∈ face n, objective n p ≤ objective n x := by
          have hpSucc : p ∈ face (n + 1) := hp (n + 1)
          rw [htower.2 n] at hpSucc
          exact hpSucc.2
        calc
          objective n d = objective n p := hprior n (Nat.lt_succ_self n)
          _ ≤ objective n e := hpMin e he
  have hpSucc : p ∈ face (i + 1) := hp (i + 1)
  rw [htower.2 i] at hpSucc
  exact hpSucc.2 d (hdface i hties)

variable [TopologicalSpace D]




theorem d000748
    [T2Space D] [LinearOrder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i)) :
    ∀ i, (face i).Nonempty ∧ IsCompact (face i) ∧ IsClosed (face i) := by
  intro i
  induction i with
  | zero =>
      rw [htower.1]
      exact ⟨hCnonempty, hcompact, hcompact.isClosed⟩
  | succ i ih =>
      rcases ih with ⟨hiNonempty, hiCompact, _hiClosed⟩
      rcases (hlsc i).exists_isMinOn hiNonempty hiCompact with
        ⟨p, hpFace, hpMin⟩
      have hfaceEq :
          face (i + 1) =
            face i ∩ (objective i) ⁻¹' Set.Iic (objective i p) := by
        rw [htower.2 i]
        ext d
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_Iic]
        constructor
        · intro hd
          exact ⟨hd.1, hd.2 p hpFace⟩
        · intro hd
          refine ⟨hd.1, ?_⟩
          intro e he
          exact hd.2.trans (hpMin he)
      have hnextCompact : IsCompact (face (i + 1)) := by
        rw [hfaceEq]
        exact (hlsc i).isCompact_inter_preimage_Iic hiCompact (objective i p)
      have hpNext : p ∈ face (i + 1) := by
        rw [hfaceEq]
        exact ⟨hpFace, hpMin hpFace⟩
      exact ⟨⟨p, hpNext⟩, hnextCompact, hnextCompact.isClosed⟩



theorem d000749
    [PartialOrder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hnonempty : ∀ i, (face i).Nonempty)
    (hcompact : IsCompact C)
    (hclosed : ∀ i, IsClosed (face i)) :
    ∃ p, (∀ i, p ∈ face i) ∧ _root_.GD.N0230.N0596.d000730 objective C p := by
  have hcompact0 : IsCompact (face 0) := by
    rw [htower.1]
    exact hcompact
  have hinter : (⋂ i, face i).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      face (_root_.GD.N0230.N0583.d000746 objective C face htower) hnonempty hcompact0 hclosed
  rcases hinter with ⟨p, hpInter⟩
  have hp : ∀ i, p ∈ face i := by
    intro i
    exact Set.mem_iInter.mp hpInter i
  exact ⟨p, hp, _root_.GD.N0230.N0583.d000747 objective C face htower hp⟩



theorem d000750
    [T2Space D] [LinearOrder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i)) :
    ∃ p, (∀ i, p ∈ face i) ∧ _root_.GD.N0230.N0596.d000730 objective C p := by
  have hfaces := _root_.GD.N0230.N0583.d000748
    objective C face htower hCnonempty hcompact hlsc
  exact _root_.GD.N0230.N0583.d000749
    objective C face htower (fun i ↦ (hfaces i).1) hcompact
      (fun i ↦ (hfaces i).2.2)

variable [Group G] [MulAction G D]



theorem d000751
    [PartialOrder O]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hnonempty : ∀ i, (face i).Nonempty)
    (hcompact : IsCompact C)
    (hclosed : ∀ i, IsClosed (face i))
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : _root_.GD.N0230.N0596.d000734 (G := G) objective)
    (hfaithful : ∀ p, p ∈ C → _root_.GD.N0230.N0596.d000731 objective C p) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000749
    objective C face htower hnonempty hcompact hclosed with ⟨p, hp, hlex⟩
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0596.d000736
    risk objective C p hhereditary hmono hC hinvariant hlex
      (hfaithful p hlex.1)




theorem d000752
    [T2Space D] [LinearOrder O]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hinvariant : _root_.GD.N0230.N0596.d000734 (G := G) objective)
    (hfaithful : ∀ p, p ∈ C → _root_.GD.N0230.N0596.d000731 objective C p) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  have hfaces := _root_.GD.N0230.N0583.d000748
    objective C face htower hCnonempty hcompact hlsc
  exact _root_.GD.N0230.N0583.d000751
    risk objective C face htower (fun i ↦ (hfaces i).1) hcompact
      (fun i ↦ (hfaces i).2.2) hhereditary hmono hC hinvariant hfaithful

end N0583
end N0230
end GD

#print axioms _root_.GD.N0230.N0583.d000746
#print axioms _root_.GD.N0230.N0583.d000747
#print axioms _root_.GD.N0230.N0583.d000748
#print axioms _root_.GD.N0230.N0583.d000749
#print axioms _root_.GD.N0230.N0583.d000750
#print axioms _root_.GD.N0230.N0583.d000751
#print axioms _root_.GD.N0230.N0583.d000752
