import GD.Module0143






















open Set

namespace GD
namespace N0230
namespace N0599

noncomputable section

open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0554
open _root_.GD.N0230.N0587

variable {A K D : Type*}




theorem d001615
    [TopologicalSpace K]
    (j : A → K) (hdense : DenseRange j)
    (profile : K → D → ℝ) (objective : D → ℝ) (d : D)
    (hcontinuous : Continuous (fun k ↦ profile k d)) :
    IsLUB (Set.range (fun a ↦ profile (j a) d)) (objective d) ↔
      IsLUB (Set.range (fun k ↦ profile k d)) (objective d) := by
  constructor
  · intro hphysical
    constructor
    · rintro value ⟨k, rfl⟩
      exact DenseRange.induction_on
        (p := fun z ↦ profile z d ≤ objective d)
        hdense k (isClosed_le hcontinuous continuous_const)
        (fun a ↦ hphysical.1 ⟨a, rfl⟩)
    · intro bound hbound
      apply hphysical.2
      rintro value ⟨a, rfl⟩
      exact hbound ⟨j a, rfl⟩
  · intro hambient
    constructor
    · rintro value ⟨a, rfl⟩
      exact hambient.1 ⟨j a, rfl⟩
    · intro bound hbound
      apply hambient.2
      rintro value ⟨k, rfl⟩
      exact DenseRange.induction_on
        (p := fun z ↦ profile z d ≤ bound)
        hdense k (isClosed_le hcontinuous continuous_const)
        (fun a ↦ hbound ⟨a, rfl⟩)




theorem d001616
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (j : A → K) (hdense : DenseRange j)
    (profile : K → D → ℝ) (objective : D → ℝ) (d : D)
    (hcontinuous : Continuous (fun k ↦ profile k d))
    (hphysical :
      IsLUB (Set.range (fun a ↦ profile (j a) d)) (objective d)) :
    ∃ k, profile k d = objective d := by
  have hambient :
      IsLUB (Set.range (fun k ↦ profile k d)) (objective d) :=
    (_root_.GD.N0230.N0599.d001615
      j hdense profile objective d hcontinuous).1 hphysical
  obtain ⟨k, _hk, hkmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty
      hcontinuous.continuousOn
  refine ⟨k, le_antisymm (hambient.1 ⟨k, rfl⟩) ?_⟩
  apply hambient.2
  rintro value ⟨z, rfl⟩
  exact hkmax (Set.mem_univ z)















theorem d001617
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [AddCommGroup D] [Module ℝ D]
    (j : A → K) (hdense : DenseRange j)
    (profile : K → D → ℝ)
    (profileTax : K → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hphysicalP : IsLUB
      (Set.range (fun a ↦ profile (j a) p)) (objective p))
    (hphysicalQ : IsLUB
      (Set.range (fun a ↦ profile (j a) q)) (objective q))
    (hphysicalMid : IsLUB
      (Set.range (fun a ↦ profile (j a) (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hcontinuousP : Continuous (fun k ↦ profile k p))
    (hcontinuousQ : Continuous (fun k ↦ profile k q))
    (hcontinuousMid : Continuous
      (fun k ↦ profile k (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ k,
      profile k (_root_.GD.N0230.N0718.d001528 p q) + profileTax k p q =
        (profile k p + profile k q) / 2)
    (htax : ∀ k, 0 ≤ profileTax k p q) :
    _root_.GD.N0230.N0554.d001563 objective p q = 0 ↔
      _root_.GD.N0230.N0587.d001590 profile profileTax objective p q := by
  have hambientP : IsLUB
      (Set.range (fun k ↦ profile k p)) (objective p) :=
    (_root_.GD.N0230.N0599.d001615
      j hdense profile objective p hcontinuousP).1 hphysicalP
  have hambientQ : IsLUB
      (Set.range (fun k ↦ profile k q)) (objective q) :=
    (_root_.GD.N0230.N0599.d001615
      j hdense profile objective q hcontinuousQ).1 hphysicalQ
  have hambientMid : IsLUB
      (Set.range (fun k ↦ profile k (_root_.GD.N0230.N0718.d001528 p q)))
        (objective (_root_.GD.N0230.N0718.d001528 p q)) :=
    (_root_.GD.N0230.N0599.d001615
      j hdense profile objective (_root_.GD.N0230.N0718.d001528 p q)
        hcontinuousMid).1 hphysicalMid
  exact
    _root_.GD.N0230.N0587.d001596
      profile profileTax objective p q hambientMid hexact htax
      (fun k ↦ hambientP.1 ⟨k, rfl⟩)
      (fun k ↦ hambientQ.1 ⟨k, rfl⟩)
      hcontinuousMid










theorem d001618
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [AddCommGroup D] [Module ℝ D]
    (j : A → K) (hdense : DenseRange j)
    (profile : K → D → ℝ)
    (profileTax : K → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hphysicalP : IsLUB
      (Set.range (fun a ↦ profile (j a) p)) (objective p))
    (hphysicalQ : IsLUB
      (Set.range (fun a ↦ profile (j a) q)) (objective q))
    (hphysicalMid : IsLUB
      (Set.range (fun a ↦ profile (j a) (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hcontinuousP : Continuous (fun k ↦ profile k p))
    (hcontinuousQ : Continuous (fun k ↦ profile k q))
    (hcontinuousMid : Continuous
      (fun k ↦ profile k (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ k,
      profile k (_root_.GD.N0230.N0718.d001528 p q) + profileTax k p q =
        (profile k p + profile k q) / 2)
    (htax : ∀ k, 0 ≤ profileTax k p q)
    (hphysicalFaithful : ∀ a, profileTax (j a) p q = 0 → p = q)
    (hpq : p ≠ q)
    (hflat : _root_.GD.N0230.N0554.d001563 objective p q = 0) :
    ∃ k, k ∉ Set.range j ∧
      profileTax k p q = 0 ∧
      profile k p = objective p ∧
      profile k q = objective q := by
  obtain ⟨k, hzero, hpMax, hqMax⟩ :=
    (_root_.GD.N0230.N0599.d001617
      j hdense profile profileTax objective p q
      hphysicalP hphysicalQ hphysicalMid
      hcontinuousP hcontinuousQ hcontinuousMid hexact htax).1 hflat
  refine ⟨k, ?_, hzero, hpMax, hqMax⟩
  rintro ⟨a, rfl⟩
  exact hpq (hphysicalFaithful a hzero)




theorem d001619
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [AddCommGroup D] [Module ℝ D]
    (j : A → K) (hdense : DenseRange j)
    (profile : K → D → ℝ)
    (profileTax : K → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hphysicalP : IsLUB
      (Set.range (fun a ↦ profile (j a) p)) (objective p))
    (hphysicalQ : IsLUB
      (Set.range (fun a ↦ profile (j a) q)) (objective q))
    (hphysicalMid : IsLUB
      (Set.range (fun a ↦ profile (j a) (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hcontinuousP : Continuous (fun k ↦ profile k p))
    (hcontinuousQ : Continuous (fun k ↦ profile k q))
    (hcontinuousMid : Continuous
      (fun k ↦ profile k (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ k,
      profile k (_root_.GD.N0230.N0718.d001528 p q) + profileTax k p q =
        (profile k p + profile k q) / 2)
    (htax : ∀ k, 0 ≤ profileTax k p q) :
    0 < _root_.GD.N0230.N0554.d001563 objective p q ↔
      ¬ _root_.GD.N0230.N0587.d001590 profile profileTax objective p q := by
  have hambientP : IsLUB
      (Set.range (fun k ↦ profile k p)) (objective p) :=
    (_root_.GD.N0230.N0599.d001615
      j hdense profile objective p hcontinuousP).1 hphysicalP
  have hambientQ : IsLUB
      (Set.range (fun k ↦ profile k q)) (objective q) :=
    (_root_.GD.N0230.N0599.d001615
      j hdense profile objective q hcontinuousQ).1 hphysicalQ
  have hambientMid : IsLUB
      (Set.range (fun k ↦ profile k (_root_.GD.N0230.N0718.d001528 p q)))
        (objective (_root_.GD.N0230.N0718.d001528 p q)) :=
    (_root_.GD.N0230.N0599.d001615
      j hdense profile objective (_root_.GD.N0230.N0718.d001528 p q)
        hcontinuousMid).1 hphysicalMid
  exact _root_.GD.N0230.N0587.d001597
    profile profileTax objective p q hambientMid hexact htax
    (fun k ↦ hambientP.1 ⟨k, rfl⟩)
    (fun k ↦ hambientQ.1 ⟨k, rfl⟩)
    (_root_.GD.N0230.N0587.d001594
      profile profileTax objective p q hexact hcontinuousMid)




theorem d001620
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [AddCommGroup D] [Module ℝ D]
    (j : A → K) (hdense : DenseRange j)
    (profile : K → D → ℝ)
    (profileTax : K → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hphysicalP : IsLUB
      (Set.range (fun a ↦ profile (j a) p)) (objective p))
    (hphysicalQ : IsLUB
      (Set.range (fun a ↦ profile (j a) q)) (objective q))
    (hphysicalMid : IsLUB
      (Set.range (fun a ↦ profile (j a) (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hcontinuousP : Continuous (fun k ↦ profile k p))
    (hcontinuousQ : Continuous (fun k ↦ profile k q))
    (hcontinuousMid : Continuous
      (fun k ↦ profile k (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ k,
      profile k (_root_.GD.N0230.N0718.d001528 p q) + profileTax k p q =
        (profile k p + profile k q) / 2)
    (htax : ∀ k, 0 ≤ profileTax k p q)
    (hfaithful : ∀ k, profileTax k p q = 0 → p = q)
    (hpq : p ≠ q) :
    0 < _root_.GD.N0230.N0554.d001563 objective p q := by
  apply (_root_.GD.N0230.N0599.d001619
    j hdense profile profileTax objective p q
    hphysicalP hphysicalQ hphysicalMid
    hcontinuousP hcontinuousQ hcontinuousMid hexact htax).2
  rintro ⟨k, hzero, _hp, _hq⟩
  exact hpq (hfaithful k hzero)








theorem d001621
    {H : Type*} [NormedAddCommGroup H]
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [AddCommGroup D] [Module ℝ D]
    (j : A → K) (hdense : DenseRange j)
    (profile : K → D → ℝ)
    (response : K → D → H)
    (objective : D → ℝ) (p q : D)
    (hphysicalP : IsLUB
      (Set.range (fun a ↦ profile (j a) p)) (objective p))
    (hphysicalQ : IsLUB
      (Set.range (fun a ↦ profile (j a) q)) (objective q))
    (hphysicalMid : IsLUB
      (Set.range (fun a ↦ profile (j a) (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hcontinuousP : Continuous (fun k ↦ profile k p))
    (hcontinuousQ : Continuous (fun k ↦ profile k q))
    (hcontinuousMid : Continuous
      (fun k ↦ profile k (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ k,
      profile k (_root_.GD.N0230.N0718.d001528 p q) +
          ‖response k p - response k q‖ ^ 2 / 4 =
        (profile k p + profile k q) / 2)
    (hseparates : ∀ k, response k p = response k q → p = q)
    (hpq : p ≠ q) :
    0 < _root_.GD.N0230.N0554.d001563 objective p q := by
  let tax : K → D → D → ℝ := fun k x y ↦
    ‖response k x - response k y‖ ^ 2 / 4
  apply _root_.GD.N0230.N0599.d001620
    j hdense profile tax objective p q
    hphysicalP hphysicalQ hphysicalMid
    hcontinuousP hcontinuousQ hcontinuousMid
  · exact hexact
  · intro k
    dsimp [tax]
    positivity
  · intro k hzero
    have hnormZero : ‖response k p - response k q‖ = 0 := by
      have hnormNonnegative : 0 ≤ ‖response k p - response k q‖ :=
        norm_nonneg _
      dsimp [tax] at hzero
      nlinarith
    apply hseparates k
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormZero)
  · exact hpq

end

end N0599
end N0230
end GD

#print axioms _root_.GD.N0230.N0599.d001615
#print axioms _root_.GD.N0230.N0599.d001616
#print axioms _root_.GD.N0230.N0599.d001617
#print axioms _root_.GD.N0230.N0599.d001618
#print axioms _root_.GD.N0230.N0599.d001619
#print axioms _root_.GD.N0230.N0599.d001620
#print axioms _root_.GD.N0230.N0599.d001621
