import GD.Module0143
import GD.Module0101























namespace GD
namespace N0230
namespace N0553

noncomputable section

open Set
open _root_.GD.N0230.N0554
open _root_.GD.N0230.N0587
open _root_.GD.N0230.N0585
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0718

variable {ProfileTheta RiskTheta D G : Type*}



def d001612
    (profile : ProfileTheta → D → ℝ)
    (profileTax : ProfileTheta → D → D → ℝ)
    (objective : D → ℝ) (C : Set D) : Prop :=
  ∀ p q, p ∈ C → q ∈ C →
    IsMinOn objective C p → IsMinOn objective C q →
    ∀ theta,
      profile theta p = objective p →
      profile theta q = objective q →
      profileTax theta p q = 0 → p = q




theorem d001613
    [TopologicalSpace ProfileTheta] [CompactSpace ProfileTheta]
    [Nonempty ProfileTheta]
    [AddCommGroup D] [Module ℝ D]
    (profile : ProfileTheta → D → ℝ)
    (profileTax : ProfileTheta → D → D → ℝ)
    (objective : D → ℝ) (C : Set D)
    (hCconvex : Convex ℝ C)
    (hLUB : ∀ d ∈ C,
      IsLUB (Set.range (fun theta ↦ profile theta d)) (objective d))
    (hexact : ∀ p ∈ C, ∀ q ∈ C, ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ p ∈ C, ∀ q ∈ C, ∀ theta,
      0 ≤ profileTax theta p q)
    (hlscResidual : ∀ p ∈ C, ∀ q ∈ C,
      LowerSemicontinuous (fun theta ↦
        profileTax theta p q +
          _root_.GD.N0230.N0554.d001565 profile objective theta p q))
    (hfaithful : _root_.GD.N0230.N0553.d001612
      profile profileTax objective C) :
    _root_.GD.N0230.N0585.d001306 objective C := by
  intro p q hpC hqC hpMin hqMin
  exact _root_.GD.N0230.N0587.d001601
    C hCconvex profile profileTax objective hpC hqC hpMin hqMin
    hLUB (hexact p hpC q hqC) (htax p hpC q hqC)
    (hlscResidual p hpC q hqC)
    (hfaithful p q hpC hqC hpMin hqMin)











theorem d001614
    [TopologicalSpace ProfileTheta] [CompactSpace ProfileTheta]
    [Nonempty ProfileTheta]
    [TopologicalSpace D]
    [AddCommGroup D] [Module ℝ D]
    (profile : ProfileTheta → D → ℝ)
    (profileTax : ProfileTheta → D → D → ℝ)
    (risk : RiskTheta → D → ENNReal)
    (objective : D → ℝ) {C : Set D}
    (actC : G → C → C)
    (hCnonempty : C.Nonempty)
    (hCcompact : IsCompact C)
    (hobjectiveLsc : LowerSemicontinuousOn objective C)
    (hCconvex : Convex ℝ C)
    (hLUB : ∀ d ∈ C,
      IsLUB (Set.range (fun theta ↦ profile theta d)) (objective d))
    (hexact : ∀ p ∈ C, ∀ q ∈ C, ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ p ∈ C, ∀ q ∈ C, ∀ theta,
      0 ≤ profileTax theta p q)
    (hlscResidual : ∀ p ∈ C, ∀ q ∈ C,
      LowerSemicontinuous (fun theta ↦
        profileTax theta p q +
          _root_.GD.N0230.N0554.d001565 profile objective theta p q))
    (hfaithful : _root_.GD.N0230.N0553.d001612
      profile profileTax objective C)
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hmono : _root_.GD.N0230.N0585.d001305 risk objective)
    (hpreserve : ∀ g (d : C), objective (actC g d : D) = objective d) :
    ∃ pC : C,
      IsMinOn objective C pC.1 ∧
      (∀ g, actC g pC = pC) ∧
      _root_.GD.N0230.N0608.d000674 risk pC.1 := by
  have hrigid : _root_.GD.N0230.N0585.d001306 objective C :=
    _root_.GD.N0230.N0553.d001613
      profile profileTax objective C hCconvex hLUB hexact htax
      hlscResidual hfaithful
  obtain ⟨p, hpC, hpMin⟩ :=
    hobjectiveLsc.exists_isMinOn hCnonempty hCcompact
  let pC : C := ⟨p, hpC⟩
  have hfixed : ∀ g, actC g pC = pC := by
    intro g
    apply Subtype.ext
    have hactMin : IsMinOn objective C (actC g pC : D) := by
      intro d hdC
      rw [hpreserve g pC]
      exact hpMin hdC
    exact (hrigid hpC (actC g pC).property hpMin hactMin).symm
  have hterminal : _root_.GD.N0230.N0608.d000674 risk p := by
    intro e hep
    have heC : e ∈ C := hhereditary hpC hep
    have hepObjective : objective e ≤ objective p := hmono hep
    have hpeObjective : objective p ≤ objective e := hpMin heC
    have heMin : IsMinOn objective C e := by
      intro d hdC
      calc
        objective e = objective p := le_antisymm hepObjective hpeObjective
        _ ≤ objective d := hpMin hdC
    exact (hrigid hpC heC hpMin heMin).symm
  exact ⟨pC, hpMin, hfixed, hterminal⟩

end

end N0553
end N0230
end GD

#print axioms _root_.GD.N0230.N0553.d001613
#print axioms _root_.GD.N0230.N0553.d001614
