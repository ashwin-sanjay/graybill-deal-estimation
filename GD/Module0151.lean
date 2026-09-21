import GD.Module0150
















open scoped ENNReal

namespace GD
namespace N0230
namespace N0569

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0600
open _root_.GD.N0230.N0601
open _root_.GD.N0230.N0680

variable {G Theta D : Type*}


def d001684 (face : ℕ → Set D) (p : D) : Prop :=
  ∀ i, p ∈ face i


def d001685 (face : ℕ → Set D) (p : D) : Prop :=
  _root_.GD.N0230.N0569.d001684 face p ∧
    ∀ q, _root_.GD.N0230.N0569.d001684 face q → q = p



def d001686
    (act : G → D → D) (face : ℕ → Set D) : Prop :=
  ∀ g p, _root_.GD.N0230.N0569.d001684 face p →
    _root_.GD.N0230.N0569.d001684 face (act g p)



def d001687
    (act : G → D → D) (face : ℕ → Set D) : Prop :=
  ∀ g i, MapsTo (act g) (face i) (face i)



theorem d001687.d001688
    {act : G → D → D} {face : ℕ → Set D}
    (hpres : _root_.GD.N0230.N0569.d001687 act face) :
    _root_.GD.N0230.N0569.d001686 act face := by
  intro g p hp i
  exact hpres g i (hp i)



theorem d001689
    (act : G → D → D) (face : ℕ → Set D) (p : D)
    (hunique : _root_.GD.N0230.N0569.d001685 face p)
    (hpres : _root_.GD.N0230.N0569.d001686 act face) :
    ∀ g, act g p = p := by
  intro g
  exact hunique.2 (act g p) (hpres g p hunique.1)








theorem d001690
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    (hfinite : ∀ p, _root_.GD.N0230.N0569.d001684 face p →
      ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective) :
    ∃ p, _root_.GD.N0230.N0569.d001685 face p ∧
      _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i) :=
    _root_.GD.N0230.N0680.d001681
      objective C face tax htower (_root_.GD.N0230.N0600.d001553 C hCconvex)
      hdominated
  have hunique : ∀ d, _root_.GD.N0230.N0569.d001684 face d → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hd hp (fun hdp =>
        _root_.GD.N0230.N0680.d001680
          objective C face tax htower hdominated hcomplete hd hp
          (hfinite d hd) hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, ⟨hp, hunique⟩, ?_⟩
  exact _root_.GD.N0230.N0596.d000733
    risk objective C p hhereditary hmono hlex hfaithful






theorem d001691
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (act : G → D → D)
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    (hfinite : ∀ p, _root_.GD.N0230.N0569.d001684 face p →
      ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001686 act face) :
    ∃ p, _root_.GD.N0230.N0569.d001684 face p ∧
      (∀ g, act g p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases
      _root_.GD.N0230.N0569.d001690
        risk objective C face tax htower hCnonempty hcompact hlsc hCconvex
        hdominated hcomplete hfinite hhereditary hmono with
    ⟨p, hunique, hterminal⟩
  exact ⟨p, hunique.1,
    _root_.GD.N0230.N0569.d001689 act face p hunique hpres,
    hterminal⟩



theorem d001692
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (act : G → D → D)
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (C : Set D) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    (hfinite : ∀ p, _root_.GD.N0230.N0569.d001684 face p →
      ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001687 act face) :
    ∃ p, _root_.GD.N0230.N0569.d001684 face p ∧
      (∀ g, act g p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    _root_.GD.N0230.N0569.d001691
      act risk objective C face tax htower hCnonempty hcompact hlsc hCconvex
      hdominated hcomplete hfinite hhereditary hmono
      hpres.d001688




def d001693
    {C : Set D} (actC : G → C → C) (face : ℕ → Set D) : Prop :=
  ∀ g pC, _root_.GD.N0230.N0569.d001684 face pC.1 →
    _root_.GD.N0230.N0569.d001684 face (actC g pC).1


def d001694
    {C : Set D} (actC : G → C → C) (face : ℕ → Set D) : Prop :=
  ∀ g i pC, pC.1 ∈ face i → (actC g pC).1 ∈ face i



theorem d001694.d001695
    {C : Set D} {actC : G → C → C} {face : ℕ → Set D}
    (hpres : _root_.GD.N0230.N0569.d001694 actC face) :
    _root_.GD.N0230.N0569.d001693 actC face := by
  intro g pC hp i
  exact hpres g i pC (hp i)



theorem d001696
    {C : Set D} (actC : G → C → C) (face : ℕ → Set D)
    (p : D) (hpC : p ∈ C)
    (hunique : _root_.GD.N0230.N0569.d001685 face p)
    (hpres : _root_.GD.N0230.N0569.d001693 actC face) :
    ∀ g, actC g ⟨p, hpC⟩ = ⟨p, hpC⟩ := by
  intro g
  apply Subtype.ext
  exact hunique.2 (actC g ⟨p, hpC⟩).1
    (hpres g ⟨p, hpC⟩ hunique.1)







theorem d001697
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    {C : Set D} (actC : G → C → C)
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    (hfinite : ∀ p, _root_.GD.N0230.N0569.d001684 face p →
      ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001693 actC face) :
    ∃ pC : C, _root_.GD.N0230.N0569.d001684 face pC.1 ∧
      (∀ g, actC g pC = pC) ∧ _root_.GD.N0230.N0608.d000674 risk pC.1 := by
  rcases
      _root_.GD.N0230.N0569.d001690
        risk objective C face tax htower hCnonempty hcompact hlsc hCconvex
        hdominated hcomplete hfinite hhereditary hmono with
    ⟨p, hunique, hterminal⟩
  have hpC : p ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hunique.1 0)
  let pC : C := ⟨p, hpC⟩
  refine ⟨pC, hunique.1, ?_, hterminal⟩
  exact _root_.GD.N0230.N0569.d001696
    actC face p hpC hunique hpres



theorem d001698
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    {C : Set D} (actC : G → C → C)
    (risk : Theta → D → ENNReal)
    (objective : ℕ → D → ENNReal) (face : ℕ → Set D)
    (tax : ℕ → D → D → ENNReal)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hdominated : _root_.GD.N0230.N0680.d001676 C objective tax)
    (hcomplete : _root_.GD.N0230.N0680.d001677 C tax)
    (hfinite : ∀ p, _root_.GD.N0230.N0569.d001684 face p →
      ∀ i, objective i p ≠ ⊤)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001694 actC face) :
    ∃ pC : C, _root_.GD.N0230.N0569.d001684 face pC.1 ∧
      (∀ g, actC g pC = pC) ∧ _root_.GD.N0230.N0608.d000674 risk pC.1 := by
  exact
    _root_.GD.N0230.N0569.d001697
      actC risk objective face tax htower hCnonempty hcompact hlsc hCconvex
      hdominated hcomplete hfinite hhereditary hmono
      hpres.d001695

end N0569
end N0230
end GD

#print axioms _root_.GD.N0230.N0569.d001687.d001688
#print axioms _root_.GD.N0230.N0569.d001689
#print axioms _root_.GD.N0230.N0569.d001690
#print axioms _root_.GD.N0230.N0569.d001691
#print axioms _root_.GD.N0230.N0569.d001692
#print axioms _root_.GD.N0230.N0569.d001694.d001695
#print axioms _root_.GD.N0230.N0569.d001696
#print axioms _root_.GD.N0230.N0569.d001697
#print axioms _root_.GD.N0230.N0569.d001698
