import GD.Module0152
















open scoped ENNReal

namespace GD
namespace N0230
namespace N0643

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
open _root_.GD.N0230.N0718

variable {G RiskTheta D : Type*}



def d001717
    (objective : ℕ → D → ℝ) (C : Set D) (p q : D) : Prop :=
  p ∈ C ∧ q ∈ C ∧ ∀ i, objective i p = objective i q







def d001718
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) : Prop :=
  ∀ p q, _root_.GD.N0230.N0643.d001717 objective C p q → p ≠ q →
    ∃ (i : ℕ) (eta : ℝ) (theta : GradeTheta i),
      0 < eta ∧
        objective i (_root_.GD.N0230.N0718.d001528 p q) - eta <
          profile i theta (_root_.GD.N0230.N0718.d001528 p q) ∧
        eta ≤ physicalTax i theta p q



def d001719
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) : Prop :=
  ∀ p q, _root_.GD.N0230.N0643.d001717 objective C p q → p ≠ q →
    ∃ (i : ℕ) (theta : GradeTheta i),
      objective i (_root_.GD.N0230.N0718.d001528 p q) -
          profile i theta (_root_.GD.N0230.N0718.d001528 p q) <
        physicalTax i theta p q



theorem d001720
    {activity tax : ℝ} (hactivity : 0 ≤ activity) :
    (∃ eta : ℝ, 0 < eta ∧ activity < eta ∧ eta ≤ tax) ↔
      activity < tax := by
  constructor
  · rintro ⟨eta, _, hactivityEta, hetaTax⟩
    exact lt_of_lt_of_le hactivityEta hetaTax
  · intro hactivityTax
    refine ⟨(activity + tax) / 2, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith




theorem d001721
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C) :
    _root_.GD.N0230.N0643.d001718
        GradeTheta profile physicalTax objective C ↔
      _root_.GD.N0230.N0643.d001719
        GradeTheta profile physicalTax objective C := by
  constructor
  · intro hmatched p q hclones hpq
    obtain ⟨i, eta, theta, _, hactive, htax⟩ :=
      hmatched p q hclones hpq
    refine ⟨i, theta, ?_⟩
    linarith
  · intro hbeats p q hclones hpq
    obtain ⟨i, theta, hbeatsTheta⟩ := hbeats p q hclones hpq
    have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
      unfold _root_.GD.N0230.N0718.d001528
      apply hCconvex hclones.1 hclones.2.1
      · norm_num
      · norm_num
      · norm_num
    have hprofileLe :
        profile i theta (_root_.GD.N0230.N0718.d001528 p q) ≤
          objective i (_root_.GD.N0230.N0718.d001528 p q) :=
      (hLUB i (_root_.GD.N0230.N0718.d001528 p q) hmid).1 ⟨theta, rfl⟩
    have hinactivity : 0 ≤
        objective i (_root_.GD.N0230.N0718.d001528 p q) -
          profile i theta (_root_.GD.N0230.N0718.d001528 p q) := by
      linarith
    obtain ⟨eta, heta, hinactivityEta, hetaTax⟩ :=
      (_root_.GD.N0230.N0643.d001720 hinactivity).2 hbeatsTheta
    exact ⟨i, eta, theta, heta, by linarith, hetaTax⟩





theorem N0798.d001722
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D)
    (hcapacity : _root_.GD.N0230.N0577.d001702
      GradeTheta profile physicalTax objective C) :
    _root_.GD.N0230.N0643.d001718
      GradeTheta profile physicalTax objective C := by
  intro p q hclones hpq
  obtain ⟨i, T, hT, hactive⟩ :=
    hcapacity p hclones.1 q hclones.2.1 hpq
  obtain ⟨theta, hnear, htax⟩ := hactive T hT
  exact ⟨i, T, theta, hT, hnear, htax⟩




theorem d001723
    [AddCommGroup D] [Module ℝ D]
    (Theta : Type*)
    (profile : Theta → D → ℝ)
    (physicalTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (p q : D)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q)
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + physicalTax theta p q =
        (profile theta p + profile theta q) / 2)
    (eta : ℝ) (theta : Theta)
    (hactive : objective (_root_.GD.N0230.N0718.d001528 p q) - eta <
      profile theta (_root_.GD.N0230.N0718.d001528 p q))
    (hmatched : eta ≤ physicalTax theta p q) :
    objective (_root_.GD.N0230.N0718.d001528 p q) <
      (objective p + objective q) / 2 := by
  have hp := hupperP theta
  have hq := hupperQ theta
  have hEq := hexact theta
  linarith



theorem d001724
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700
      GradeTheta profile physicalTax C)
    (hseparate : _root_.GD.N0230.N0643.d001718
      GradeTheta profile physicalTax objective C)
    {p q : D}
    (hp : _root_.GD.N0230.N0569.d001684 face p)
    (hq : _root_.GD.N0230.N0569.d001684 face q)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  have hpC : p ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hp 0)
  have hqC : q ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hq 0)
  have hclones : _root_.GD.N0230.N0643.d001717 objective C p q :=
    ⟨hpC, hqC, fun i ↦
      _root_.GD.N0230.N0628.d001544 objective C face htower hp hq i⟩
  obtain ⟨i, eta, theta, heta, hactive, hmatched⟩ :=
    hseparate p q hclones hpq
  have hstrict : objective i (_root_.GD.N0230.N0718.d001528 p q) <
      (objective i p + objective i q) / 2 :=
    _root_.GD.N0230.N0643.d001723
      (GradeTheta i) (profile i) (physicalTax i) (objective i) p q
      (fun theta ↦ (hLUB i p hpC).1 ⟨theta, rfl⟩)
      (fun theta ↦ (hLUB i q hqC).1 ⟨theta, rfl⟩)
      (fun theta ↦ hexact i theta p hpC q hqC)
      eta theta hactive hmatched
  refine ⟨i, ?_⟩
  calc
    objective i (_root_.GD.N0230.N0718.d001528 p q) <
        (objective i p + objective i q) / 2 := hstrict
    _ = objective i p := by
      rw [← hclones.2.2 i]
      ring








theorem d001725
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
    (hseparate : _root_.GD.N0230.N0643.d001718
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
  have hunique : ∀ d, _root_.GD.N0230.N0569.d001684 face d → d = p := by
    intro d hd
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hd hp (fun hdp ↦
        _root_.GD.N0230.N0643.d001724
          GradeTheta profile physicalTax objective C face htower hLUB
          hexact hseparate hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, ⟨hp, hunique⟩, ?_⟩
  exact _root_.GD.N0230.N0596.d000733
    risk objective C p hhereditary hmono hlex hfaithful




theorem d001726
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
    (hseparate : _root_.GD.N0230.N0643.d001718
      GradeTheta profile physicalTax objective C)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001693 actC face) :
    ∃ pC : C, _root_.GD.N0230.N0569.d001684 face pC.1 ∧
      (∀ g, actC g pC = pC) ∧ _root_.GD.N0230.N0608.d000674 risk pC.1 := by
  rcases
      _root_.GD.N0230.N0643.d001725
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

end N0643
end N0230
end GD

#print axioms _root_.GD.N0230.N0643.d001723
#print axioms _root_.GD.N0230.N0643.d001720
#print axioms _root_.GD.N0230.N0643.d001721
#print axioms _root_.GD.N0230.N0643.N0798.d001722
#print axioms _root_.GD.N0230.N0643.d001724
#print axioms _root_.GD.N0230.N0643.d001725
#print axioms _root_.GD.N0230.N0643.d001726
