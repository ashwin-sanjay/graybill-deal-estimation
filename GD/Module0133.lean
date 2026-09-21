import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas


















namespace GD
namespace N0230
namespace N0718

open Set
open Filter

variable {Theta V : Type*}
variable [AddCommGroup V] [Module ℝ V]



noncomputable def d001528 (p q : V) : V :=
  (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q




theorem d001529
    (profile : Theta → V → ℝ) (objective : V → ℝ)
    (tax : Theta → V → V → ℝ)
    {p q : V}
    (hSupP : IsLUB (Set.range fun theta ↦ profile theta p) (objective p))
    (hSupQ : IsLUB (Set.range fun theta ↦ profile theta q) (objective q))
    (hSupMid : IsLUB
      (Set.range fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hpMinMid : objective p ≤ objective (_root_.GD.N0230.N0718.d001528 p q))
    (hpMinQ : objective p ≤ objective q)
    (hqMinP : objective q ≤ objective p)
    (hMidpoint : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
        (profile theta p + profile theta q) / 2 - tax theta p q) :
    ∀ {epsilon : ℝ}, 0 < epsilon →
      ∃ theta, tax theta p q < epsilon := by
  intro epsilon hepsilon
  by_contra hNoSmallTax
  have hTaxLower : ∀ theta, epsilon ≤ tax theta p q := by
    intro theta
    exact le_of_not_gt fun hlt ↦ hNoSmallTax ⟨theta, hlt⟩
  have hObjEq : objective q = objective p :=
    le_antisymm hqMinP hpMinQ
  have hMidUpper : objective (_root_.GD.N0230.N0718.d001528 p q) ≤ objective p - epsilon := by
    apply hSupMid.2
    rintro value ⟨theta, rfl⟩
    have hProfileP : profile theta p ≤ objective p :=
      hSupP.1 ⟨theta, rfl⟩
    have hProfileQ : profile theta q ≤ objective q :=
      hSupQ.1 ⟨theta, rfl⟩
    calc
      profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
          (profile theta p + profile theta q) / 2 - tax theta p q :=
        hMidpoint theta
      _ ≤ (profile theta p + profile theta q) / 2 - epsilon := by
        exact sub_le_sub_left (hTaxLower theta) _
      _ ≤ objective p - epsilon := by
        rw [hObjEq] at hProfileQ
        linarith
  linarith





theorem d001530
    (C : Set V) (hC : Convex ℝ C)
    (profile : Theta → V → ℝ) (objective : V → ℝ)
    (tax : Theta → V → V → ℝ)
    {p q : V}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hpMin : IsMinOn objective C p)
    (hqMin : IsMinOn objective C q)
    (hSup : ∀ d ∈ C,
      IsLUB (Set.range fun theta ↦ profile theta d) (objective d))
    (hMidpoint : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
        (profile theta p + profile theta q) / 2 - tax theta p q) :
    ∀ {epsilon : ℝ}, 0 < epsilon →
      ∃ theta, tax theta p q < epsilon := by
  have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hC hpC hqC
    · norm_num
    · norm_num
    · norm_num
  intro epsilon hepsilon
  exact _root_.GD.N0230.N0718.d001529
    profile objective tax
    (hSup p hpC) (hSup q hqC) (hSup _ hmidC)
    (hpMin hmidC) (hpMin hqC) (hqMin hpC) hMidpoint hepsilon











theorem d001531
    (profile : Theta → V → ℝ) (tax : Theta → V → V → ℝ)
    {p q : V} (level epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hProfileP : ∀ theta, profile theta p ≤ level)
    (hProfileQ : ∀ theta, profile theta q ≤ level)
    (hSupMid : IsLUB
      (Set.range fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)) level)
    (hTaxNonnegative : ∀ theta, 0 ≤ tax theta p q)
    (hExact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + tax theta p q =
        (profile theta p + profile theta q) / 2) :
    ∃ theta,
      level - epsilon < profile theta (_root_.GD.N0230.N0718.d001528 p q) ∧
      tax theta p q < epsilon ∧
      level - 2 * epsilon < profile theta p ∧
      level - 2 * epsilon < profile theta q := by
  obtain ⟨value, hvalueRange, hvalueNear, _hvalueUpper⟩ :=
    hSupMid.exists_between (sub_lt_self level hepsilon)
  obtain ⟨theta, rfl⟩ := hvalueRange
  refine ⟨theta, hvalueNear, ?_, ?_, ?_⟩
  · linarith [hExact theta, hProfileP theta, hProfileQ theta]
  · linarith [hExact theta, hTaxNonnegative theta, hProfileQ theta]
  · linarith [hExact theta, hTaxNonnegative theta, hProfileP theta]





theorem d001532
    (C : Set V) (hC : Convex ℝ C)
    (profile : Theta → V → ℝ) (objective : V → ℝ)
    (tax : Theta → V → V → ℝ)
    {p q : V}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hpMin : IsMinOn objective C p)
    (hqMin : IsMinOn objective C q)
    (hSup : ∀ d ∈ C,
      IsLUB (Set.range fun theta ↦ profile theta d) (objective d))
    (hTaxNonnegative : ∀ theta, 0 ≤ tax theta p q)
    (hExact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + tax theta p q =
        (profile theta p + profile theta q) / 2) :
    ∀ {epsilon : ℝ}, 0 < epsilon →
      ∃ theta,
        objective p - epsilon <
          profile theta (_root_.GD.N0230.N0718.d001528 p q) ∧
        tax theta p q < epsilon ∧
        objective p - 2 * epsilon < profile theta p ∧
        objective p - 2 * epsilon < profile theta q := by
  have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hC hpC hqC
    · norm_num
    · norm_num
    · norm_num
  have hObjEq : objective q = objective p :=
    le_antisymm (hqMin hpC) (hpMin hqC)
  have hProfileP : ∀ theta, profile theta p ≤ objective p := fun theta ↦
    (hSup p hpC).1 ⟨theta, rfl⟩
  have hProfileQ : ∀ theta, profile theta q ≤ objective p := by
    intro theta
    rw [← hObjEq]
    exact (hSup q hqC).1 ⟨theta, rfl⟩
  have hMidUpper : objective (_root_.GD.N0230.N0718.d001528 p q) ≤ objective p := by
    apply (hSup _ hmidC).2
    rintro value ⟨theta, rfl⟩
    linarith [hExact theta, hTaxNonnegative theta,
      hProfileP theta, hProfileQ theta]
  have hObjMid : objective (_root_.GD.N0230.N0718.d001528 p q) = objective p :=
    le_antisymm hMidUpper (hpMin hmidC)
  intro epsilon hepsilon
  apply _root_.GD.N0230.N0718.d001531
    profile tax (objective p) epsilon hepsilon hProfileP hProfileQ
  · rw [← hObjMid]
    exact hSup _ hmidC
  · exact hTaxNonnegative
  · exact hExact



theorem d001533
    (C : Set V) (hC : Convex ℝ C)
    (profile : Theta → V → ℝ) (objective : V → ℝ)
    (tax : Theta → V → V → ℝ)
    {p q : V}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hpMin : IsMinOn objective C p)
    (hqMin : IsMinOn objective C q)
    (hSup : ∀ d ∈ C,
      IsLUB (Set.range fun theta ↦ profile theta d) (objective d))
    (hTaxNonnegative : ∀ theta, 0 ≤ tax theta p q)
    (hExact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + tax theta p q =
        (profile theta p + profile theta q) / 2) :
    ∃ thetaSeq : ℕ → Theta,
      (∀ n : ℕ, objective p - 1 / ((n : ℝ) + 1) <
        profile (thetaSeq n) (_root_.GD.N0230.N0718.d001528 p q)) ∧
      Tendsto (fun n ↦ tax (thetaSeq n) p q) atTop (nhds 0) ∧
      (∀ n : ℕ, objective p - 2 * (1 / ((n : ℝ) + 1)) <
        profile (thetaSeq n) p) ∧
      (∀ n : ℕ, objective p - 2 * (1 / ((n : ℝ) + 1)) <
        profile (thetaSeq n) q) := by
  have hChoose : ∀ n : ℕ, ∃ theta,
      objective p - 1 / ((n : ℝ) + 1) <
          profile theta (_root_.GD.N0230.N0718.d001528 p q) ∧
        tax theta p q < 1 / ((n : ℝ) + 1) ∧
        objective p - 2 * (1 / ((n : ℝ) + 1)) < profile theta p ∧
        objective p - 2 * (1 / ((n : ℝ) + 1)) < profile theta q := by
    intro n
    exact _root_.GD.N0230.N0718.d001532
      C hC profile objective tax hpC hqC hpMin hqMin hSup
      hTaxNonnegative hExact (by positivity)
  choose thetaSeq hthetaSeq using hChoose
  refine ⟨thetaSeq, (fun n : ℕ ↦ (hthetaSeq n).1), ?_,
    (fun n : ℕ ↦ (hthetaSeq n).2.2.1),
    (fun n : ℕ ↦ (hthetaSeq n).2.2.2)⟩
  exact squeeze_zero (fun n ↦ hTaxNonnegative (thetaSeq n))
    (fun n ↦ (hthetaSeq n).2.1.le)
    tendsto_one_div_add_atTop_nhds_zero_nat



theorem d001534
    (C : Set V) (hC : Convex ℝ C)
    (profile : Theta → V → ℝ) (objective : V → ℝ)
    (tax : Theta → V → V → ℝ)
    {p q : V}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hpMin : IsMinOn objective C p)
    (hqMin : IsMinOn objective C q)
    (hSup : ∀ d ∈ C,
      IsLUB (Set.range fun theta ↦ profile theta d) (objective d))
    (hMidpoint : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
        (profile theta p + profile theta q) / 2 - tax theta p q)
    (hPositive : p ≠ q →
      ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ theta, epsilon ≤ tax theta p q) :
    p = q := by
  by_contra hpq
  obtain ⟨epsilon, hepsilon, hTaxLower⟩ := hPositive hpq
  obtain ⟨theta, hTaxSmall⟩ :=
    _root_.GD.N0230.N0718.d001530
      C hC profile objective tax hpC hqC hpMin hqMin hSup hMidpoint hepsilon
  exact (not_lt_of_ge (hTaxLower theta)) hTaxSmall



theorem d001535
    (C : Set V) (hC : Convex ℝ C)
    (profile : Theta → V → ℝ) (objective : V → ℝ)
    (tax : Theta → V → V → ℝ)
    {p q : V}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hpMin : IsMinOn objective C p)
    (hqMin : IsMinOn objective C q)
    (hSup : ∀ d ∈ C,
      IsLUB (Set.range fun theta ↦ profile theta d) (objective d))
    (hMidpoint : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
        (profile theta p + profile theta q) / 2 - tax theta p q)
    (hTaxNonnegative : ∀ theta, 0 ≤ tax theta p q) :
    ∃ thetaSeq : ℕ → Theta,
      Tendsto (fun n ↦ tax (thetaSeq n) p q) atTop (nhds 0) := by
  have hChoose : ∀ n : ℕ,
      ∃ theta, tax theta p q < 1 / ((n : ℝ) + 1) := by
    intro n
    exact _root_.GD.N0230.N0718.d001530
      C hC profile objective tax hpC hqC hpMin hqMin hSup hMidpoint
      (by positivity)
  choose thetaSeq hthetaSeq using hChoose
  refine ⟨thetaSeq, squeeze_zero (fun n ↦ hTaxNonnegative (thetaSeq n))
    (fun n ↦ (hthetaSeq n).le) ?_⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end N0718
end N0230
end GD

#print axioms _root_.GD.N0230.N0718.d001529
#print axioms _root_.GD.N0230.N0718.d001530
#print axioms _root_.GD.N0230.N0718.d001531
#print axioms _root_.GD.N0230.N0718.d001532
#print axioms _root_.GD.N0230.N0718.d001533
#print axioms _root_.GD.N0230.N0718.d001534
#print axioms _root_.GD.N0230.N0718.d001535
