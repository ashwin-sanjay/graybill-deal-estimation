import GD.Module0136


























namespace GD
namespace N0230
namespace N0600

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0581
open _root_.GD.N0230.N0701
open _root_.GD.N0230.N0628

variable {G Theta D O : Type*}



def d001547
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ)
    (tax : ℕ → D → D → ℝ) : Prop :=
  ∀ i p q,
    objective i (_root_.GD.N0230.N0718.d001528 p q) + tax i p q ≤
      (objective i p + objective i q) / 2



theorem d001548
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ)
    (tax : ℕ → D → D → ℝ)
    (hexact : _root_.GD.N0230.N0628.d001542 objective tax) :
    _root_.GD.N0230.N0600.d001547 objective tax := by
  intro i p q
  exact (hexact i p q).le




theorem d001549
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ)
    (exactTax detectorTax : ℕ → D → D → ℝ)
    (hexact : _root_.GD.N0230.N0628.d001542 objective exactTax)
    (hle : ∀ i p q, detectorTax i p q ≤ exactTax i p q) :
    _root_.GD.N0230.N0600.d001547 objective detectorTax := by
  intro i p q
  calc
    objective i (_root_.GD.N0230.N0718.d001528 p q) + detectorTax i p q ≤
        objective i (_root_.GD.N0230.N0718.d001528 p q) + exactTax i p q :=
      add_le_add_right (hle i p q) _
    _ = (objective i p + objective i q) / 2 := hexact i p q



theorem d001547.d001550
    [AddCommGroup D] [Module ℝ D]
    {objective : ℕ → D → ℝ}
    {largeTax smallTax : ℕ → D → D → ℝ}
    (hdom : _root_.GD.N0230.N0600.d001547 objective largeTax)
    (hle : ∀ i p q, smallTax i p q ≤ largeTax i p q) :
    _root_.GD.N0230.N0600.d001547 objective smallTax := by
  intro i p q
  exact (add_le_add_right (hle i p q) _).trans (hdom i p q)




theorem d001551
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ℝ)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hdominated : _root_.GD.N0230.N0600.d001547 objective tax)
    (hcomplete : _root_.GD.N0230.N0628.d001543 tax)
    {p q : D} (hp : ∀ i, p ∈ face i) (hq : ∀ i, q ∈ face i)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  obtain ⟨i, hitax⟩ := hcomplete p q hpq
  refine ⟨i, ?_⟩
  have heq := _root_.GD.N0230.N0628.d001544
    objective C face htower hp hq i
  have hmid := hdominated i p q
  linarith




def d001552
    [AddCommGroup D] [Module ℝ D] (S : Set D) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, _root_.GD.N0230.N0718.d001528 p q ∈ S


theorem d001553
    [AddCommGroup D] [Module ℝ D]
    (S : Set D) (hS : Convex ℝ S) : _root_.GD.N0230.N0600.d001552 S := by
  intro p hp q hq
  unfold _root_.GD.N0230.N0718.d001528
  apply hS hp hq
  · norm_num
  · norm_num
  · norm_num



theorem d001554
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ℝ)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCmidpoint : _root_.GD.N0230.N0600.d001552 C)
    (hdominated : _root_.GD.N0230.N0600.d001547 objective tax)
    (htax : ∀ i p q, 0 ≤ tax i p q) :
    ∀ i, _root_.GD.N0230.N0600.d001552 (face i) := by
  intro i
  induction i with
  | zero =>
      rw [htower.1]
      exact hCmidpoint
  | succ i ih =>
      rw [htower.2 i]
      intro p hp q hq
      refine ⟨ih p hp.1 q hq.1, ?_⟩
      intro e he
      have hpqeq : objective i p = objective i q :=
        le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
      have hmid := hdominated i p q
      have hmid_le_p : objective i (_root_.GD.N0230.N0718.d001528 p q) ≤ objective i p := by
        rw [hpqeq] at hmid
        linarith [htax i p q]
      exact hmid_le_p.trans (hp.2 e he)



theorem d001555
    [LinearOrder O]
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i))
    {p q : D}
    (hp : ∀ i, p ∈ face i)
    (hq : ∀ i, q ∈ face i)
    (hgap : p ≠ q → ∃ i,
      objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p) :
    p = q := by
  by_contra hpq
  obtain ⟨i, hstrict⟩ := hgap hpq
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ face i :=
    hmidpoint i p (hp i) q (hq i)
  have hpSucc : p ∈ face (i + 1) := hp (i + 1)
  rw [htower.2 i] at hpSucc
  exact (not_lt_of_ge (hpSucc.2 _ hmid)) hstrict




theorem d001556
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
    (hdominated : _root_.GD.N0230.N0600.d001547 objective tax)
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
    exact _root_.GD.N0230.N0600.d001551
      objective C face tax htower hdominated hcomplete hp hq hpq
  · exact hhereditary
  · exact hmono
  · exact hC
  · exact hcov






theorem d001557
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
    (hCmidpoint : _root_.GD.N0230.N0600.d001552 C)
    (hdominated : _root_.GD.N0230.N0600.d001547 objective tax)
    (htax : ∀ i p q, 0 ≤ tax i p q)
    (hcomplete : _root_.GD.N0230.N0628.d001543 tax)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001119 objective scale offset) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i) :=
    _root_.GD.N0230.N0600.d001554
      objective C face tax htower hCmidpoint hdominated htax
  have hunique : ∀ d, (∀ i, d ∈ face i) → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hd hp (fun hdp =>
        _root_.GD.N0230.N0600.d001551
          objective C face tax htower hdominated hcomplete hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0701.d001121
    risk objective scale offset C p hhereditary hmono hC hcov hlex hfaithful



theorem d001558
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
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0600.d001547 objective tax)
    (htax : ∀ i p q, 0 ≤ tax i p q)
    (hcomplete : _root_.GD.N0230.N0628.d001543 tax)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001119 objective scale offset) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    _root_.GD.N0230.N0600.d001557
      risk objective C face tax scale offset htower hCnonempty hcompact hlsc
      (_root_.GD.N0230.N0600.d001553 C hCconvex) hdominated htax hcomplete
      hhereditary hmono hC hcov

end N0600
end N0230
end GD

#print axioms _root_.GD.N0230.N0600.d001548
#print axioms _root_.GD.N0230.N0600.d001549
#print axioms _root_.GD.N0230.N0600.d001551
#print axioms _root_.GD.N0230.N0600.d001556
#print axioms _root_.GD.N0230.N0600.d001554
#print axioms _root_.GD.N0230.N0600.d001557
#print axioms _root_.GD.N0230.N0600.d001558
