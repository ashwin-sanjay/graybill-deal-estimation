import GD.Module0134
import GD.Module0084
import GD.Module0071




















namespace GD
namespace N0230
namespace N0581

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0701
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0654

variable {G Theta D O : Type*}






theorem d001540
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [LinearOrder O]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → O) (C : Set D) (face : ℕ → Set D)
    (transform : (g : G) → (i : ℕ) → (Fin i → O) → O → O)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hconvex : ∀ i, Convex ℝ (face i))
    (hcollective : ∀ p q,
      (∀ i, p ∈ face i) → (∀ i, q ∈ face i) → p ≠ q →
        ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0654.d000876 objective transform) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hunique : ∀ d, (∀ i, d ∈ face i) → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0580.d001538
      objective C face htower hconvex hd hp
        (fun hdp ↦ hcollective d p hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0654.d000879
    risk objective transform C p hhereditary hmono hC hcov hlex hfaithful








theorem d001541
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (scale : G → ℕ → ℝ)
    (offset : (g : G) → (i : ℕ) → (Fin i → ℝ) → ℝ)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hconvex : ∀ i, Convex ℝ (face i))
    (hcollective : ∀ p q,
      (∀ i, p ∈ face i) → (∀ i, q ∈ face i) → p ≠ q →
        ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hcov : _root_.GD.N0230.N0701.d001119 objective scale offset) :
    ∃ p, (∀ i, p ∈ face i) ∧
      (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hunique : ∀ d, (∀ i, d ∈ face i) → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0580.d001538
      objective C face htower hconvex hd hp
        (fun hdp ↦ hcollective d p hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, hp, ?_⟩
  exact _root_.GD.N0230.N0701.d001121
    risk objective scale offset C p hhereditary hmono hC hcov hlex hfaithful

end N0581
end N0230
end GD

#print axioms _root_.GD.N0230.N0581.d001541
#print axioms _root_.GD.N0230.N0581.d001540
