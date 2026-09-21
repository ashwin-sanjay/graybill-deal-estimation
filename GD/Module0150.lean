import GD.Module0137
import GD.Module0141




















open scoped ENNReal

namespace GD
namespace N0230
namespace N0680

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0701
open _root_.GD.N0230.N0654
open _root_.GD.N0230.N0628
open _root_.GD.N0230.N0600
open _root_.GD.N0230.N0601
open _root_.GD.N0230.N0718

variable {G Theta D O : Type*}


theorem d001666
    [Preorder O]
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face) :
    ∀ i, face i ⊆ C := by
  intro i
  induction i with
  | zero =>
      rw [htower.1]
  | succ i ih =>
      exact (_root_.GD.N0230.N0583.d000746 objective C face htower i).trans ih



def d001667
    [AddCommGroup D] [Module ℝ D]
    (C : Set D) (objective : ℕ → D → ℝ)
    (tax : ℕ → D → D → ℝ) : Prop :=
  ∀ i p, p ∈ C → ∀ q, q ∈ C →
    objective i (_root_.GD.N0230.N0718.d001528 p q) + tax i p q ≤
      (objective i p + objective i q) / 2


def d001668
    (C : Set D) (tax : ℕ → D → D → ℝ) : Prop :=
  ∀ p, p ∈ C → ∀ q, q ∈ C → p ≠ q → ∃ i, 0 < tax i p q


theorem N0801.d001669
    [AddCommGroup D] [Module ℝ D]
    {objective : ℕ → D → ℝ} {tax : ℕ → D → D → ℝ}
    (hdom : _root_.GD.N0230.N0600.d001547 objective tax) (C : Set D) :
    _root_.GD.N0230.N0680.d001667 C objective tax := by
  intro i p _hp q _hq
  exact hdom i p q


theorem N0800.d001670
    {tax : ℕ → D → D → ℝ}
    (hcomplete : _root_.GD.N0230.N0628.d001543 tax) (C : Set D) :
    _root_.GD.N0230.N0680.d001668 C tax := by
  intro p _hp q _hq hpq
  exact hcomplete p q hpq



theorem d001667.d001671
    [AddCommGroup D] [Module ℝ D]
    {C : Set D} {objective : ℕ → D → ℝ}
    {largeTax smallTax : ℕ → D → D → ℝ}
    (hdom : _root_.GD.N0230.N0680.d001667 C objective largeTax)
    (hle : ∀ i p, p ∈ C → ∀ q, q ∈ C →
      smallTax i p q ≤ largeTax i p q) :
    _root_.GD.N0230.N0680.d001667 C objective smallTax := by
  intro i p hp q hq
  exact (add_le_add_right (hle i p hp q hq) _).trans
    (hdom i p hp q hq)



theorem d001672
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ℝ)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hdominated : _root_.GD.N0230.N0680.d001667 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001668 C tax)
    {p q : D} (hp : ∀ i, p ∈ face i) (hq : ∀ i, q ∈ face i)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  have hpC : p ∈ C := (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hp 0)
  have hqC : q ∈ C := (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hq 0)
  obtain ⟨i, hitax⟩ := hcomplete p hpC q hqC hpq
  refine ⟨i, ?_⟩
  have heq := _root_.GD.N0230.N0628.d001544
    objective C face htower hp hq i
  have hmid := hdominated i p hpC q hqC
  linarith



theorem d001673
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ℝ)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCmidpoint : _root_.GD.N0230.N0600.d001552 C)
    (hdominated : _root_.GD.N0230.N0680.d001667 C objective tax)
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
      have hsub := _root_.GD.N0230.N0680.d001666 objective C face htower i
      have hpqeq : objective i p = objective i q :=
        le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
      have hmid := hdominated i p (hsub hp.1) q (hsub hq.1)
      have hmid_le_p : objective i (_root_.GD.N0230.N0718.d001528 p q) ≤ objective i p := by
        rw [hpqeq] at hmid
        linarith [htax i p q]
      exact hmid_le_p.trans (hp.2 e he)



theorem d001674
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
    (hdominated : _root_.GD.N0230.N0680.d001667 C objective tax)
    (htax : ∀ i p q, 0 ≤ tax i p q)
    (hcomplete : _root_.GD.N0230.N0680.d001668 C tax)
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
    _root_.GD.N0230.N0680.d001673
      objective C face tax htower hCmidpoint hdominated htax
  have hunique : ∀ d, (∀ i, d ∈ face i) → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hd hp (fun hdp =>
        _root_.GD.N0230.N0680.d001672
          objective C face tax htower hdominated hcomplete hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0701.d001121
    risk objective scale offset C p hhereditary hmono hC hcov hlex hfaithful



theorem d001675
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
    (hdominated : _root_.GD.N0230.N0680.d001667 C objective tax)
    (htax : ∀ i p q, 0 ≤ tax i p q)
    (hcomplete : _root_.GD.N0230.N0680.d001668 C tax)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001119 objective scale offset) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    _root_.GD.N0230.N0680.d001674
      risk objective C face tax scale offset htower hCnonempty hcompact hlsc
      (_root_.GD.N0230.N0600.d001553 C hCconvex) hdominated htax hcomplete
      hhereditary hmono hC hcov



def d001676
    [AddCommGroup D] [Module ℝ D]
    (C : Set D) (objective : ℕ → D → ENNReal)
    (tax : ℕ → D → D → ENNReal) : Prop :=
  ∀ i p, p ∈ C → ∀ q, q ∈ C →
    objective i (_root_.GD.N0230.N0718.d001528 p q) + tax i p q ≤
      (objective i p + objective i q) / 2


def d001677
    (C : Set D) (tax : ℕ → D → D → ENNReal) : Prop :=
  ∀ p, p ∈ C → ∀ q, q ∈ C → p ≠ q → ∃ i, 0 < tax i p q


theorem N0802.d001678
    [AddCommGroup D] [Module ℝ D]
    {objective : ℕ → D → ENNReal} {tax : ℕ → D → D → ENNReal}
    (hdom : _root_.GD.N0230.N0601.d001578 objective tax) (C : Set D) :
    _root_.GD.N0230.N0680.d001676 C objective tax := by
  intro i p _hp q _hq
  exact hdom i p q


theorem N0799.d001679
    {tax : ℕ → D → D → ENNReal}
    (hcomplete : _root_.GD.N0230.N0601.d001579 tax) (C : Set D) :
    _root_.GD.N0230.N0680.d001677 C tax := by
  intro p _hp q _hq hpq
  exact hcomplete p q hpq



theorem d001680
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    {p q : D} (hp : ∀ i, p ∈ face i) (hq : ∀ i, q ∈ face i)
    (hpfinite : ∀ i, objective i p ≠ ⊤)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  have hpC : p ∈ C := (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hp 0)
  have hqC : q ∈ C := (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hq 0)
  obtain ⟨i, hitax⟩ := hcomplete p hpC q hqC hpq
  refine ⟨i, ?_⟩
  have hpNext : p ∈ face (i + 1) := hp (i + 1)
  have hqNext : q ∈ face (i + 1) := hq (i + 1)
  rw [htower.2 i] at hpNext hqNext
  have heq : objective i p = objective i q :=
    le_antisymm (hpNext.2 q (hq i)) (hqNext.2 p (hp i))
  have hmid := hdominated i p hpC q hqC
  rw [← heq] at hmid
  exact _root_.GD.N0230.N0601.d001581 (hpfinite i) hitax hmid



theorem d001681
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCmidpoint : _root_.GD.N0230.N0600.d001552 C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax) :
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
      have hsub := _root_.GD.N0230.N0680.d001666 objective C face htower i
      have hpqeq : objective i p = objective i q :=
        le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
      calc
        objective i (_root_.GD.N0230.N0718.d001528 p q) ≤
            objective i (_root_.GD.N0230.N0718.d001528 p q) + tax i p q :=
          self_le_add_right _ _
        _ ≤ (objective i p + objective i q) / 2 :=
          hdominated i p (hsub hp.1) q (hsub hq.1)
        _ = objective i p := by
          rw [hpqeq, _root_.GD.N0230.N0601.d001580]
        _ ≤ objective i e := hp.2 e he



theorem d001682
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (transform : (g : G) → (i : ℕ) →
      (Fin i → ENNReal) → ENNReal → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCmidpoint : _root_.GD.N0230.N0600.d001552 C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    (hfinite : ∀ p, (∀ i, p ∈ face i) → ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i) :=
    _root_.GD.N0230.N0680.d001681
      objective C face tax htower hCmidpoint hdominated
  have hunique : ∀ d, (∀ i, d ∈ face i) → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hd hp (fun hdp =>
        _root_.GD.N0230.N0680.d001680
          objective C face tax htower hdominated hcomplete hd hp
          (hfinite d hd) hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0654.d000879
    risk objective transform C p hhereditary hmono hC hcov hlex hfaithful



theorem d001683
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (transform : (g : G) → (i : ℕ) →
      (Fin i → ENNReal) → ENNReal → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    (hfinite : ∀ p, (∀ i, p ∈ face i) → ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    _root_.GD.N0230.N0680.d001682
      risk objective C face tax transform htower hCnonempty hcompact hlsc
      (_root_.GD.N0230.N0600.d001553 C hCconvex) hdominated hcomplete hfinite
      hhereditary hmono hC hcov

end N0680
end N0230
end GD

#print axioms _root_.GD.N0230.N0680.d001666
#print axioms _root_.GD.N0230.N0680.d001672
#print axioms _root_.GD.N0230.N0680.d001673
#print axioms _root_.GD.N0230.N0680.d001675
#print axioms _root_.GD.N0230.N0680.d001680
#print axioms _root_.GD.N0230.N0680.d001681
#print axioms _root_.GD.N0230.N0680.d001683
