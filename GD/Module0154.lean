import GD.Module0142
import GD.Module0153




















open scoped ENNReal

namespace GD
namespace N0230
namespace N0705

open Set
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0628
open _root_.GD.N0230.N0600
open _root_.GD.N0230.N0680
open _root_.GD.N0230.N0569
open _root_.GD.N0230.N0577
open _root_.GD.N0230.N0643
open _root_.GD.N0230.N0554
open _root_.GD.N0230.N0651
open _root_.GD.N0230.N0718

variable {G RiskTheta D : Type*}




def d001727
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) : Prop :=
  ∀ p q, _root_.GD.N0230.N0643.d001717 objective C p q → p ≠ q →
    ∃ (i : ℕ) (epsilon : ℝ), 0 < epsilon ∧
      ∀ theta : GradeTheta i,
        epsilon ≤ physicalTax i theta p q +
          _root_.GD.N0230.N0554.d001565 (profile i) (objective i) theta p q



def d001728
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ) (C : Set D) : Prop :=
  ∀ p q, _root_.GD.N0230.N0643.d001717 objective C p q → p ≠ q →
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p







theorem d001729
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700
      GradeTheta profile physicalTax C) :
    _root_.GD.N0230.N0705.d001727
        GradeTheta profile physicalTax objective C ↔
      _root_.GD.N0230.N0705.d001728 objective C := by
  constructor
  · intro hresidual p q hclones hpq
    obtain ⟨i, epsilon, hepsilon, hfloor⟩ :=
      hresidual p q hclones hpq
    have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
      unfold _root_.GD.N0230.N0718.d001528
      apply hCconvex hclones.1 hclones.2.1
      · norm_num
      · norm_num
      · norm_num
    have hpositive : 0 <
        _root_.GD.N0230.N0554.d001563 (objective i) p q :=
      (_root_.GD.N0230.N0651.d001587
        (profile i) (physicalTax i) (objective i) p q
        (hLUB i (_root_.GD.N0230.N0718.d001528 p q) hmidC)
        (fun theta ↦ hexact i theta p hclones.1 q hclones.2.1)).2
        ⟨epsilon, hepsilon, hfloor⟩
    refine ⟨i, ?_⟩
    dsimp [_root_.GD.N0230.N0554.d001563] at hpositive
    rw [← hclones.2.2 i] at hpositive
    linarith
  · intro hstrict p q hclones hpq
    obtain ⟨i, hgap⟩ := hstrict p q hclones hpq
    have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
      unfold _root_.GD.N0230.N0718.d001528
      apply hCconvex hclones.1 hclones.2.1
      · norm_num
      · norm_num
      · norm_num
    have hpositive : 0 <
        _root_.GD.N0230.N0554.d001563 (objective i) p q := by
      dsimp [_root_.GD.N0230.N0554.d001563]
      rw [← hclones.2.2 i]
      linarith
    obtain ⟨epsilon, hepsilon, hfloor⟩ :=
      (_root_.GD.N0230.N0651.d001587
        (profile i) (physicalTax i) (objective i) p q
        (hLUB i (_root_.GD.N0230.N0718.d001528 p q) hmidC)
        (fun theta ↦ hexact i theta p hclones.1 q hclones.2.1)).1
        hpositive
    exact ⟨i, epsilon, hepsilon, hfloor⟩



theorem N0803.d001730
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700
      GradeTheta profile physicalTax C)
    (hmatched : _root_.GD.N0230.N0643.d001718
      GradeTheta profile physicalTax objective C) :
    _root_.GD.N0230.N0705.d001727
      GradeTheta profile physicalTax objective C := by
  apply
    (_root_.GD.N0230.N0705.d001729
      GradeTheta profile physicalTax objective C hCconvex hLUB hexact).2
  intro p q hclones hpq
  obtain ⟨i, eta, theta, _heta, hactive, htax⟩ :=
    hmatched p q hclones hpq
  have hstrict : objective i (_root_.GD.N0230.N0718.d001528 p q) <
      (objective i p + objective i q) / 2 :=
    _root_.GD.N0230.N0643.d001723
      (GradeTheta i) (profile i) (physicalTax i) (objective i) p q
      (fun theta ↦ (hLUB i p hclones.1).1 ⟨theta, rfl⟩)
      (fun theta ↦ (hLUB i q hclones.2.1).1 ⟨theta, rfl⟩)
      (fun theta ↦ hexact i theta p hclones.1 q hclones.2.1)
      eta theta hactive htax
  refine ⟨i, ?_⟩
  calc
    objective i (_root_.GD.N0230.N0718.d001528 p q) <
        (objective i p + objective i q) / 2 := hstrict
    _ = objective i p := by
      rw [← hclones.2.2 i]
      ring



theorem d001731
    [AddCommGroup D] [Module ℝ D]
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hstrict : _root_.GD.N0230.N0705.d001728 objective C)
    {p q : D}
    (hp : _root_.GD.N0230.N0569.d001684 face p)
    (hq : _root_.GD.N0230.N0569.d001684 face q)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  have hpC : p ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hp 0)
  have hqC : q ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hq 0)
  exact hstrict p q
    ⟨hpC, hqC, fun i ↦
      _root_.GD.N0230.N0628.d001544 objective C face htower hp hq i⟩
    hpq


theorem d001732
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (risk : RiskTheta → D → ENNReal)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700
      GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (hseparate : _root_.GD.N0230.N0705.d001727
      GradeTheta profile physicalTax objective C)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective) :
    ∃ p, _root_.GD.N0230.N0569.d001685 face p ∧
      _root_.GD.N0230.N0608.d000674 risk p := by
  rcases _root_.GD.N0230.N0583.d000750
      objective C face htower hCnonempty hcompact hlsc with
    ⟨p, hp, hlex⟩
  have hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i) :=
    _root_.GD.N0230.N0577.d001711
      GradeTheta profile physicalTax objective C face htower hCconvex
      hLUB hexact htax
  have hstrict : _root_.GD.N0230.N0705.d001728
      objective C :=
    (_root_.GD.N0230.N0705.d001729
      GradeTheta profile physicalTax objective C hCconvex hLUB hexact).1
      hseparate
  have hunique : ∀ d, _root_.GD.N0230.N0569.d001684 face d → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hd hp (fun hdp ↦
        _root_.GD.N0230.N0705.d001731
          objective C face htower hstrict hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, ⟨hp, hunique⟩, ?_⟩
  exact _root_.GD.N0230.N0596.d000733
    risk objective C p hhereditary hmono hlex hfaithful


theorem d001733
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    {C : Set D} (actC : G → C → C)
    (risk : RiskTheta → D → ENNReal)
    (objective : ℕ → D → ℝ) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700
      GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (hseparate : _root_.GD.N0230.N0705.d001727
      GradeTheta profile physicalTax objective C)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001693 actC face) :
    ∃ pC : C, _root_.GD.N0230.N0569.d001684 face pC.1 ∧
      (∀ g, actC g pC = pC) ∧ _root_.GD.N0230.N0608.d000674 risk pC.1 := by
  rcases
      _root_.GD.N0230.N0705.d001732
        GradeTheta profile physicalTax risk objective C face htower
        hCnonempty hcompact hlsc hCconvex hLUB hexact htax hseparate
        hhereditary hmono with
    ⟨p, hunique, hterminal⟩
  have hpC : p ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hunique.1 0)
  let pC : C := ⟨p, hpC⟩
  refine ⟨pC, hunique.1, ?_, hterminal⟩
  exact _root_.GD.N0230.N0569.d001696
    actC face p hpC hunique hpres

section SignedAbsoluteValueExample


def d001734 (b : Bool) (x : ℝ) : ℝ :=
  if b then x else -x


def d001735 (_b : Bool) (_p _q : ℝ) : ℝ := 0



theorem d001736 (x : ℝ) :
    IsLUB (Set.range (fun b : Bool ↦ _root_.GD.N0230.N0705.d001734 b x)) |x| := by
  constructor
  · rintro value ⟨b, rfl⟩
    cases b <;> simp [_root_.GD.N0230.N0705.d001734, neg_le_abs, le_abs_self]
  · intro a ha
    have hx : x ≤ a := ha ⟨true, by simp [_root_.GD.N0230.N0705.d001734]⟩
    have hnegx : -x ≤ a := ha ⟨false, by simp [_root_.GD.N0230.N0705.d001734]⟩
    exact (abs_le).2 ⟨by linarith, hx⟩



theorem d001737
    (b : Bool) (p q : ℝ) :
    _root_.GD.N0230.N0705.d001734 b (_root_.GD.N0230.N0718.d001528 p q) + _root_.GD.N0230.N0705.d001735 b p q =
      (_root_.GD.N0230.N0705.d001734 b p + _root_.GD.N0230.N0705.d001734 b q) / 2 := by
  cases b <;> simp [_root_.GD.N0230.N0705.d001734, _root_.GD.N0230.N0705.d001735, _root_.GD.N0230.N0718.d001528] <;> ring



theorem d001738 :
    ∀ b : Bool,
      (1 : ℝ) ≤ _root_.GD.N0230.N0705.d001735 b 1 (-1) +
        _root_.GD.N0230.N0554.d001565 _root_.GD.N0230.N0705.d001734 abs b 1 (-1) := by
  intro b
  cases b <;>
    norm_num [_root_.GD.N0230.N0705.d001734, _root_.GD.N0230.N0705.d001735, _root_.GD.N0230.N0554.d001565]



theorem d001739 :
    ¬ ∃ (eta : ℝ) (b : Bool),
      0 < eta ∧
        abs (_root_.GD.N0230.N0718.d001528 (1 : ℝ) (-1)) - eta <
          _root_.GD.N0230.N0705.d001734 b (_root_.GD.N0230.N0718.d001528 (1 : ℝ) (-1)) ∧
        eta ≤ _root_.GD.N0230.N0705.d001735 b 1 (-1) := by
  rintro ⟨eta, b, heta, _hactive, htax⟩
  dsimp [_root_.GD.N0230.N0705.d001735] at htax
  linarith

end SignedAbsoluteValueExample

end N0705
end N0230
end GD

#print axioms _root_.GD.N0230.N0705.d001729
#print axioms _root_.GD.N0230.N0705.N0803.d001730
#print axioms _root_.GD.N0230.N0705.d001732
#print axioms _root_.GD.N0230.N0705.d001733
#print axioms _root_.GD.N0230.N0705.d001736
#print axioms _root_.GD.N0230.N0705.d001738
#print axioms _root_.GD.N0230.N0705.d001739
