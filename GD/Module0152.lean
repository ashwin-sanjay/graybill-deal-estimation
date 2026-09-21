import GD.Module0151




















open scoped ENNReal

namespace GD
namespace N0230
namespace N0577

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
open _root_.GD.N0230.N0718

variable {G RiskTheta D : Type*}



def d001699
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) : Prop :=
  ∀ i d, d ∈ C →
    IsLUB (Set.range (fun theta : GradeTheta i ↦ profile i theta d))
      (objective i d)



def d001700
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (C : Set D) : Prop :=
  ∀ i theta p, p ∈ C → ∀ q, q ∈ C →
    profile i theta (_root_.GD.N0230.N0718.d001528 p q) + physicalTax i theta p q =
      (profile i theta p + profile i theta q) / 2


def d001701
    (GradeTheta : ℕ → Type*)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (C : Set D) : Prop :=
  ∀ i theta p, p ∈ C → ∀ q, q ∈ C →
    0 ≤ physicalTax i theta p q





def d001702
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) : Prop :=
  ∀ p, p ∈ C → ∀ q, q ∈ C → p ≠ q →
    ∃ i T, 0 < T ∧
      ∀ eta, 0 < eta →
        ∃ theta : GradeTheta i,
          objective i (_root_.GD.N0230.N0718.d001528 p q) - eta <
              profile i theta (_root_.GD.N0230.N0718.d001528 p q) ∧
            T ≤ physicalTax i theta p q




def d001703
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (face : ℕ → Set D) : Prop :=
  ∀ p, _root_.GD.N0230.N0569.d001684 face p →
    ∀ q, _root_.GD.N0230.N0569.d001684 face q → p ≠ q →
      ∃ i T, 0 < T ∧
        ∀ eta, 0 < eta →
          ∃ theta : GradeTheta i,
            objective i (_root_.GD.N0230.N0718.d001528 p q) - eta <
                profile i theta (_root_.GD.N0230.N0718.d001528 p q) ∧
              T ≤ physicalTax i theta p q



theorem d001702.d001704
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hcapacity : _root_.GD.N0230.N0577.d001702
      GradeTheta profile physicalTax objective C) :
    _root_.GD.N0230.N0577.d001703
      GradeTheta profile physicalTax objective face := by
  intro p hp q hq hpq
  exact hcapacity p
    ((_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hp 0)) q
    ((_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hq 0)) hpq




theorem d001705
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (i : ℕ) {p q : D} (hp : p ∈ C) (hq : q ∈ C) :
    objective i (_root_.GD.N0230.N0718.d001528 p q) ≤
      (objective i p + objective i q) / 2 := by
  have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C :=
    (_root_.GD.N0230.N0600.d001553 C hCconvex) p hp q hq
  refine (hLUB i (_root_.GD.N0230.N0718.d001528 p q) hmidC).2 ?_
  rintro value ⟨theta, rfl⟩
  have hpUpper : profile i theta p ≤ objective i p :=
    (hLUB i p hp).1 ⟨theta, rfl⟩
  have hqUpper : profile i theta q ≤ objective i q :=
    (hLUB i q hq).1 ⟨theta, rfl⟩
  have hEq := hexact i theta p hp q hq
  have hTax := htax i theta p hp q hq
  linarith




theorem d001706
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D)
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C) :
    _root_.GD.N0230.N0680.d001667 C objective (fun _ _ _ ↦ 0) := by
  intro i p hp q hq
  simpa using
    _root_.GD.N0230.N0577.d001705
      GradeTheta profile physicalTax objective C hCconvex hLUB hexact htax
      i hp hq




theorem d001707
    [AddCommGroup D] [Module ℝ D]
    (Theta : Type*)
    (profile : Theta → D → ℝ)
    (physicalTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (C : Set D)
    (p q : D) (hp : p ∈ C) (hq : q ∈ C)
    (hLUB : ∀ d, d ∈ C →
      IsLUB (Set.range (fun theta : Theta ↦ profile theta d)) (objective d))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + physicalTax theta p q =
        (profile theta p + profile theta q) / 2)
    (T : ℝ)
    (hactive : ∀ eta, 0 < eta →
      ∃ theta : Theta,
        objective (_root_.GD.N0230.N0718.d001528 p q) - eta <
            profile theta (_root_.GD.N0230.N0718.d001528 p q) ∧
          T ≤ physicalTax theta p q) :
    objective (_root_.GD.N0230.N0718.d001528 p q) + T ≤
      (objective p + objective q) / 2 := by
  by_contra hnot
  have hstrict :
      (objective p + objective q) / 2 -
          objective (_root_.GD.N0230.N0718.d001528 p q) < T := by
    linarith
  let eta : ℝ :=
    (T - ((objective p + objective q) / 2 -
      objective (_root_.GD.N0230.N0718.d001528 p q))) / 2
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  obtain ⟨theta, hnear, hT⟩ := hactive eta heta
  have hpUpper : profile theta p ≤ objective p :=
    (hLUB p hp).1 ⟨theta, rfl⟩
  have hqUpper : profile theta q ≤ objective q :=
    (hLUB q hq).1 ⟨theta, rfl⟩
  have hEq := hexact theta
  dsimp [eta] at hnear
  linarith



theorem d001708
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (hcapacity : _root_.GD.N0230.N0577.d001703
      GradeTheta profile physicalTax objective face)
    {p q : D}
    (hp : _root_.GD.N0230.N0569.d001684 face p)
    (hq : _root_.GD.N0230.N0569.d001684 face q)
    (hpq : p ≠ q) :
    ∃ i, objective i (_root_.GD.N0230.N0718.d001528 p q) < objective i p := by
  have hpC : p ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hp 0)
  have hqC : q ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hq 0)
  obtain ⟨i, T, hT, hactive⟩ := hcapacity p hp q hq hpq
  have hdom :
      objective i (_root_.GD.N0230.N0718.d001528 p q) + T ≤
        (objective i p + objective i q) / 2 :=
    _root_.GD.N0230.N0577.d001707
      (GradeTheta i) (profile i) (physicalTax i) (objective i) C
      p q hpC hqC (hLUB i) (fun theta ↦ hexact i theta p hpC q hqC)
      T hactive
  have heq := _root_.GD.N0230.N0628.d001544
    objective C face htower hp hq i
  refine ⟨i, ?_⟩
  linarith










theorem d001709
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i))
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    {p q : D}
    (hp : _root_.GD.N0230.N0569.d001684 face p)
    (hq : _root_.GD.N0230.N0569.d001684 face q)
    (i : ℕ) (theta : GradeTheta i) (eta : ℝ)
    (hactive : objective i (_root_.GD.N0230.N0718.d001528 p q) - eta <
      profile i theta (_root_.GD.N0230.N0718.d001528 p q)) :
    physicalTax i theta p q < eta := by
  have hpC : p ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hp 0)
  have hqC : q ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hq 0)
  have hmid : _root_.GD.N0230.N0569.d001684 face (_root_.GD.N0230.N0718.d001528 p q) := by
    intro n
    exact hmidpoint n p (hp n) q (hq n)
  have hpqEq := _root_.GD.N0230.N0628.d001544
    objective C face htower hp hq i
  have hpmEq := _root_.GD.N0230.N0628.d001544
    objective C face htower hp hmid i
  have hpUpper : profile i theta p ≤ objective i p :=
    (hLUB i p hpC).1 ⟨theta, rfl⟩
  have hqUpper : profile i theta q ≤ objective i q :=
    (hLUB i q hqC).1 ⟨theta, rfl⟩
  have hEq := hexact i theta p hpC q hqC
  linarith














theorem d001710
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hmidpoint : ∀ i, _root_.GD.N0230.N0600.d001552 (face i))
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C) :
    _root_.GD.N0230.N0577.d001703
        GradeTheta profile physicalTax objective face ↔
      ∀ p, _root_.GD.N0230.N0569.d001684 face p →
        ∀ q, _root_.GD.N0230.N0569.d001684 face q → q = p := by
  constructor
  · intro hcapacity p hp q hq
    symm
    exact _root_.GD.N0230.N0600.d001555
      objective C face htower hmidpoint hp hq (fun hpq ↦
        _root_.GD.N0230.N0577.d001708
          GradeTheta profile physicalTax objective C face htower hLUB
          hexact hcapacity hp hq hpq)
  · intro hsub p hp q hq hpq
    exact False.elim (hpq (hsub p hp q hq).symm)



theorem d001711
    [AddCommGroup D] [Module ℝ D]
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (objective : ℕ → D → ℝ) (C : Set D) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C) :
    ∀ i, _root_.GD.N0230.N0600.d001552 (face i) := by
  exact _root_.GD.N0230.N0680.d001673
    objective C face (fun _ _ _ ↦ 0) htower
    (_root_.GD.N0230.N0600.d001553 C hCconvex)
    (_root_.GD.N0230.N0577.d001706
      GradeTheta profile physicalTax objective C hCconvex hLUB hexact htax)
    (fun _ _ _ ↦ le_rfl)







theorem d001712
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
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (hcapacity : _root_.GD.N0230.N0577.d001703
      GradeTheta profile physicalTax objective face)
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
        _root_.GD.N0230.N0577.d001708
          GradeTheta profile physicalTax objective C face htower hLUB
          hexact hcapacity hd hp hdp)
  have hfaithful : _root_.GD.N0230.N0596.d000731 objective C p :=
    _root_.GD.N0230.N0580.d001537
      objective C face htower hp hunique
  refine ⟨p, ⟨hp, hunique⟩, ?_⟩
  exact _root_.GD.N0230.N0596.d000733
    risk objective C p hhereditary hmono hlex hfaithful




theorem d001713
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (act : G → D → D)
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
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (hcapacity : _root_.GD.N0230.N0577.d001703
      GradeTheta profile physicalTax objective face)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001686 act face) :
    ∃ p, _root_.GD.N0230.N0569.d001684 face p ∧
      (∀ g, act g p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  rcases
      _root_.GD.N0230.N0577.d001712
        GradeTheta profile physicalTax risk objective C face htower
        hCnonempty hcompact hlsc hCconvex hLUB hexact htax hcapacity
        hhereditary hmono with
    ⟨p, hunique, hterminal⟩
  exact ⟨p, hunique.1,
    _root_.GD.N0230.N0569.d001689 act face p hunique hpres,
    hterminal⟩



theorem d001714
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (act : G → D → D)
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
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (hcapacity : _root_.GD.N0230.N0577.d001703
      GradeTheta profile physicalTax objective face)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001687 act face) :
    ∃ p, _root_.GD.N0230.N0569.d001684 face p ∧
      (∀ g, act g p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  exact
    _root_.GD.N0230.N0577.d001713
      act GradeTheta profile physicalTax risk objective C face htower
      hCnonempty hcompact hlsc hCconvex hLUB hexact htax hcapacity
      hhereditary hmono hpres.d001688








theorem d001715
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    {C : Set D} (actC : G → C → C)
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (risk : RiskTheta → D → ENNReal)
    (objective : ℕ → D → ℝ) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (hcapacity : _root_.GD.N0230.N0577.d001703
      GradeTheta profile physicalTax objective face)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001693 actC face) :
    ∃ pC : C, _root_.GD.N0230.N0569.d001684 face pC.1 ∧
      (∀ g, actC g pC = pC) ∧ _root_.GD.N0230.N0608.d000674 risk pC.1 := by
  rcases
      _root_.GD.N0230.N0577.d001712
        GradeTheta profile physicalTax risk objective C face htower
        hCnonempty hcompact hlsc hCconvex hLUB hexact htax hcapacity
        hhereditary hmono with
    ⟨p, hunique, hterminal⟩
  have hpC : p ∈ C :=
    (_root_.GD.N0230.N0680.d001666 objective C face htower 0) (hunique.1 0)
  let pC : C := ⟨p, hpC⟩
  refine ⟨pC, hunique.1, ?_, hterminal⟩
  exact _root_.GD.N0230.N0569.d001696
    actC face p hpC hunique hpres



theorem d001716
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    {C : Set D} (actC : G → C → C)
    (GradeTheta : ℕ → Type*)
    (profile : (i : ℕ) → GradeTheta i → D → ℝ)
    (physicalTax : (i : ℕ) → GradeTheta i → D → D → ℝ)
    (risk : RiskTheta → D → ENNReal)
    (objective : ℕ → D → ℝ) (face : ℕ → Set D)
    (htower : _root_.GD.N0230.N0583.d000745 objective C face)
    (hCnonempty : C.Nonempty)
    (hcompact : IsCompact C)
    (hlsc : ∀ i, LowerSemicontinuousOn (objective i) (face i))
    (hCconvex : Convex ℝ C)
    (hLUB : _root_.GD.N0230.N0577.d001699 GradeTheta profile objective C)
    (hexact : _root_.GD.N0230.N0577.d001700 GradeTheta profile physicalTax C)
    (htax : _root_.GD.N0230.N0577.d001701 GradeTheta physicalTax C)
    (hcapacity : _root_.GD.N0230.N0577.d001703
      GradeTheta profile physicalTax objective face)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0596.d000732 risk objective)
    (hpres : _root_.GD.N0230.N0569.d001694 actC face) :
    ∃ pC : C, _root_.GD.N0230.N0569.d001684 face pC.1 ∧
      (∀ g, actC g pC = pC) ∧ _root_.GD.N0230.N0608.d000674 risk pC.1 := by
  exact
    _root_.GD.N0230.N0577.d001715
      actC GradeTheta profile physicalTax risk objective face htower
      hCnonempty hcompact hlsc hCconvex hLUB hexact htax hcapacity
      hhereditary hmono hpres.d001695

end N0577
end N0230
end GD

#print axioms _root_.GD.N0230.N0577.d001705
#print axioms _root_.GD.N0230.N0577.d001702.d001704
#print axioms _root_.GD.N0230.N0577.d001706
#print axioms _root_.GD.N0230.N0577.d001707
#print axioms _root_.GD.N0230.N0577.d001708
#print axioms _root_.GD.N0230.N0577.d001709
#print axioms _root_.GD.N0230.N0577.d001710
#print axioms _root_.GD.N0230.N0577.d001711
#print axioms _root_.GD.N0230.N0577.d001712
#print axioms _root_.GD.N0230.N0577.d001713
#print axioms _root_.GD.N0230.N0577.d001714
#print axioms _root_.GD.N0230.N0577.d001715
#print axioms _root_.GD.N0230.N0577.d001716
