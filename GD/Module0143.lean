import GD.Module0142
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
































open Filter Set

namespace GD
namespace N0230
namespace N0587

noncomputable section

open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0554
open _root_.GD.N0230.N0651

variable {Theta D : Type*}



def d001590
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D) : Prop :=
  ∃ theta,
    profileTax theta p q = 0 ∧
      profile theta p = objective p ∧
      profile theta q = objective q







theorem d001591
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q) :
    _root_.GD.N0230.N0554.d001563 objective p q = 0 ↔
      ∃ thetaSeq : ℕ → Theta,
        Tendsto (fun n ↦ profileTax (thetaSeq n) p q)
          atTop (nhds 0) ∧
        Tendsto (fun n ↦ objective p - profile (thetaSeq n) p)
          atTop (nhds 0) ∧
        Tendsto (fun n ↦ objective q - profile (thetaSeq n) q)
          atTop (nhds 0) := by
  let htriple :=
    _root_.GD.N0230.N0651.d001589
      profile profileTax objective p q hLUB hexact htax hupperP hupperQ
  constructor
  · intro hzero
    have hchoose : ∀ n : ℕ, ∃ theta,
        profileTax theta p q < 1 / ((n : ℝ) + 1) ∧
        objective p - profile theta p <
          2 * (1 / ((n : ℝ) + 1)) ∧
        objective q - profile theta q <
          2 * (1 / ((n : ℝ) + 1)) := by
      intro n
      exact (htriple.1 hzero) (1 / ((n : ℝ) + 1)) (by positivity)
    choose thetaSeq hthetaSeq using hchoose
    refine ⟨thetaSeq, ?_, ?_, ?_⟩
    · exact squeeze_zero
        (fun n ↦ htax (thetaSeq n))
        (fun n ↦ (hthetaSeq n).1.le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    · apply squeeze_zero
        (fun n ↦ sub_nonneg.2 (hupperP (thetaSeq n)))
        (fun n ↦ (hthetaSeq n).2.1.le)
      simpa using
        (tendsto_const_nhds.mul
          tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ ↦
              2 * (1 / ((n : ℝ) + 1))) atTop (nhds (2 * 0)))
    · apply squeeze_zero
        (fun n ↦ sub_nonneg.2 (hupperQ (thetaSeq n)))
        (fun n ↦ (hthetaSeq n).2.2.le)
      simpa using
        (tendsto_const_nhds.mul
          tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ ↦
              2 * (1 / ((n : ℝ) + 1))) atTop (nhds (2 * 0)))
  · rintro ⟨thetaSeq, htaxZero, hgapPZero, hgapQZero⟩
    apply htriple.2
    intro epsilon hepsilon
    have htaxSmall : ∀ᶠ n in atTop,
        profileTax (thetaSeq n) p q < epsilon :=
      (tendsto_order.1 htaxZero).2 epsilon hepsilon
    have hgapPSmall : ∀ᶠ n in atTop,
        objective p - profile (thetaSeq n) p < 2 * epsilon :=
      (tendsto_order.1 hgapPZero).2 (2 * epsilon) (by linarith)
    have hgapQSmall : ∀ᶠ n in atTop,
        objective q - profile (thetaSeq n) q < 2 * epsilon :=
      (tendsto_order.1 hgapQZero).2 (2 * epsilon) (by linarith)
    have hall : ∀ᶠ n in atTop,
        profileTax (thetaSeq n) p q < epsilon ∧
        objective p - profile (thetaSeq n) p < 2 * epsilon ∧
        objective q - profile (thetaSeq n) q < 2 * epsilon := by
      filter_upwards [htaxSmall, hgapPSmall, hgapQSmall] with n hn hp hq
      exact ⟨hn, hp, hq⟩
    obtain ⟨n, hn⟩ := hall.exists
    exact ⟨thetaSeq n, hn⟩







theorem d001592
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hlsc : LowerSemicontinuous (fun theta ↦
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q)) :
    ∃ theta,
      profileTax theta p q +
          _root_.GD.N0230.N0554.d001565 profile objective theta p q =
        _root_.GD.N0230.N0554.d001563 objective p q := by
  let residual : Theta → ℝ := fun theta ↦
    profileTax theta p q +
      _root_.GD.N0230.N0554.d001565 profile objective theta p q
  obtain ⟨theta, _htheta, hmin⟩ :=
    (hlsc.lowerSemicontinuousOn Set.univ).exists_isMinOn
      (Set.univ_nonempty : Set.univ.Nonempty) isCompact_univ
  have hGLB :=
    _root_.GD.N0230.N0651.d001586
      profile profileTax objective p q hLUB hexact
  refine ⟨theta, le_antisymm ?_ ?_⟩
  · apply hGLB.2
    rintro value ⟨eta, rfl⟩
    exact hmin (Set.mem_univ eta)
  · exact hGLB.1 ⟨theta, rfl⟩



theorem d001593
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q) :
    0 ≤ _root_.GD.N0230.N0554.d001563 objective p q := by
  have hGLB :=
    _root_.GD.N0230.N0651.d001586
      profile profileTax objective p q hLUB hexact
  apply hGLB.2
  rintro value ⟨theta, rfl⟩
  exact add_nonneg (htax theta)
    (_root_.GD.N0230.N0554.d001568 profile objective theta p q
      (hupperP theta) (hupperQ theta))






theorem d001594
    [TopologicalSpace Theta]
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hcontinuousMidpoint : Continuous
      (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q))) :
    LowerSemicontinuous (fun theta ↦
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q) := by
  have hfunction :
      (fun theta ↦ profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q) =
      (fun theta ↦ _root_.GD.N0230.N0554.d001563 objective p q +
        _root_.GD.N0230.N0554.d001564 profile objective theta p q) := by
    funext theta
    exact
      _root_.GD.N0230.N0554.d001566
        profile profileTax objective theta p q (hexact theta)
  rw [hfunction]
  apply Continuous.lowerSemicontinuous
  change Continuous
    ((fun _ : Theta ↦ _root_.GD.N0230.N0554.d001563 objective p q) +
      (fun theta ↦ objective (_root_.GD.N0230.N0718.d001528 p q) -
        profile theta (_root_.GD.N0230.N0718.d001528 p q)))
  exact continuous_const.add (continuous_const.sub hcontinuousMidpoint)







theorem d001595
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q)
    (hlsc : LowerSemicontinuous (fun theta ↦
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q)) :
    _root_.GD.N0230.N0554.d001563 objective p q = 0 ↔
      _root_.GD.N0230.N0587.d001590 profile profileTax objective p q := by
  have hnonnegative := _root_.GD.N0230.N0587.d001593
    profile profileTax objective p q hLUB hexact htax hupperP hupperQ
  constructor
  · intro hzero
    obtain ⟨theta, htheta⟩ :=
      _root_.GD.N0230.N0587.d001592
        profile profileTax objective p q hLUB hexact hlsc
    have hsum : profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q = 0 := by
      simpa [hzero] using htheta
    have hslackNonnegative :
        0 ≤ _root_.GD.N0230.N0554.d001565 profile objective theta p q :=
      _root_.GD.N0230.N0554.d001568 profile objective theta p q
        (hupperP theta) (hupperQ theta)
    have htaxZero : profileTax theta p q = 0 := by
      linarith [htax theta]
    have hgapPZero : objective p - profile theta p = 0 := by
      unfold _root_.GD.N0230.N0554.d001565 at hsum hslackNonnegative
      linarith [hupperP theta, hupperQ theta]
    have hgapQZero : objective q - profile theta q = 0 := by
      unfold _root_.GD.N0230.N0554.d001565 at hsum hslackNonnegative
      linarith [hupperP theta, hupperQ theta]
    exact ⟨theta, htaxZero, by linarith, by linarith⟩
  · rintro ⟨theta, htaxZero, hpMax, hqMax⟩
    have hGLB :=
      _root_.GD.N0230.N0651.d001586
        profile profileTax objective p q hLUB hexact
    have hupperZero : _root_.GD.N0230.N0554.d001563 objective p q ≤ 0 := by
      have hle := hGLB.1 ⟨theta, rfl⟩
      simpa [_root_.GD.N0230.N0554.d001565, htaxZero, hpMax, hqMax] using hle
    exact le_antisymm hupperZero hnonnegative





theorem d001596
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q)
    (hcontinuousMidpoint : Continuous
      (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q))) :
    _root_.GD.N0230.N0554.d001563 objective p q = 0 ↔
      _root_.GD.N0230.N0587.d001590 profile profileTax objective p q := by
  exact _root_.GD.N0230.N0587.d001595
    profile profileTax objective p q hLUB hexact htax hupperP hupperQ
    (_root_.GD.N0230.N0587.d001594
      profile profileTax objective p q hexact hcontinuousMidpoint)




theorem d001597
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q)
    (hlsc : LowerSemicontinuous (fun theta ↦
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q)) :
    0 < _root_.GD.N0230.N0554.d001563 objective p q ↔
      ¬ _root_.GD.N0230.N0587.d001590 profile profileTax objective p q := by
  have hnonnegative := _root_.GD.N0230.N0587.d001593
    profile profileTax objective p q hLUB hexact htax hupperP hupperQ
  have hzeroIff :=
    _root_.GD.N0230.N0587.d001595
      profile profileTax objective p q hLUB hexact htax hupperP hupperQ hlsc
  constructor
  · intro hpositive hcommon
    have hzero := hzeroIff.2 hcommon
    linarith
  · intro hno
    have hne : _root_.GD.N0230.N0554.d001563 objective p q ≠ 0 := fun hzero ↦
      hno (hzeroIff.1 hzero)
    exact lt_of_le_of_ne hnonnegative (Ne.symm hne)



theorem d001598
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q)
    (hlsc : LowerSemicontinuous (fun theta ↦
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q))
    (hfaithful : ∀ theta, profileTax theta p q = 0 → p = q)
    (hpq : p ≠ q) :
    0 < _root_.GD.N0230.N0554.d001563 objective p q := by
  apply (_root_.GD.N0230.N0587.d001597
    profile profileTax objective p q hLUB hexact htax hupperP hupperQ hlsc).2
  rintro ⟨theta, htaxZero, _hpMax, _hqMax⟩
  exact hpq (hfaithful theta htaxZero)


theorem d001599
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q)
    (hcontinuousMidpoint : Continuous
      (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
    (hfaithful : ∀ theta, profileTax theta p q = 0 → p = q)
    (hpq : p ≠ q) :
    0 < _root_.GD.N0230.N0554.d001563 objective p q := by
  exact _root_.GD.N0230.N0587.d001598
    profile profileTax objective p q hLUB hexact htax hupperP hupperQ
    (_root_.GD.N0230.N0587.d001594
      profile profileTax objective p q hexact hcontinuousMidpoint)
    hfaithful hpq



theorem d001600
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (C : Set D) (hC : Convex ℝ C)
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    {p q : D} (hpC : p ∈ C) (hqC : q ∈ C)
    (hpMin : IsMinOn objective C p)
    (hqMin : IsMinOn objective C q)
    (hLUB : ∀ d ∈ C,
      IsLUB (Set.range (fun theta ↦ profile theta d)) (objective d))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hlsc : LowerSemicontinuous (fun theta ↦
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q))
    (hfaithful : ∀ theta, profileTax theta p q = 0 → p = q) :
    p = q := by
  by_contra hpq
  have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hC hpC hqC
    · norm_num
    · norm_num
    · norm_num
  have hupperP : ∀ theta, profile theta p ≤ objective p := fun theta ↦
    (hLUB p hpC).1 ⟨theta, rfl⟩
  have hupperQ : ∀ theta, profile theta q ≤ objective q := fun theta ↦
    (hLUB q hqC).1 ⟨theta, rfl⟩
  have hpositive : 0 < _root_.GD.N0230.N0554.d001563 objective p q :=
    _root_.GD.N0230.N0587.d001598
      profile profileTax objective p q (hLUB _ hmidC) hexact htax
      hupperP hupperQ hlsc hfaithful hpq
  have hObjEq : objective p = objective q :=
    le_antisymm (hpMin hqC) (hqMin hpC)
  have hstrict : objective (_root_.GD.N0230.N0718.d001528 p q) < objective p := by
    unfold _root_.GD.N0230.N0554.d001563 at hpositive
    rw [hObjEq] at hpositive
    linarith
  exact (not_lt_of_ge (hpMin hmidC)) hstrict










theorem d001601
    [TopologicalSpace Theta] [CompactSpace Theta] [Nonempty Theta]
    [AddCommGroup D] [Module ℝ D]
    (C : Set D) (hC : Convex ℝ C)
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    {p q : D} (hpC : p ∈ C) (hqC : q ∈ C)
    (hpMin : IsMinOn objective C p)
    (hqMin : IsMinOn objective C q)
    (hLUB : ∀ d ∈ C,
      IsLUB (Set.range (fun theta ↦ profile theta d)) (objective d))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (htax : ∀ theta, 0 ≤ profileTax theta p q)
    (hlsc : LowerSemicontinuous (fun theta ↦
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q))
    (hactiveFaithful : ∀ theta,
      profile theta p = objective p →
      profile theta q = objective q →
      profileTax theta p q = 0 → p = q) :
    p = q := by
  have hmidC : _root_.GD.N0230.N0718.d001528 p q ∈ C := by
    unfold _root_.GD.N0230.N0718.d001528
    apply hC hpC hqC
    · norm_num
    · norm_num
    · norm_num
  have hupperP : ∀ theta, profile theta p ≤ objective p := fun theta ↦
    (hLUB p hpC).1 ⟨theta, rfl⟩
  have hupperQ : ∀ theta, profile theta q ≤ objective q := fun theta ↦
    (hLUB q hqC).1 ⟨theta, rfl⟩
  have hObjEq : objective p = objective q :=
    le_antisymm (hpMin hqC) (hqMin hpC)
  have hnonnegative :
      0 ≤ _root_.GD.N0230.N0554.d001563 objective p q :=
    _root_.GD.N0230.N0587.d001593
      profile profileTax objective p q (hLUB _ hmidC) hexact htax
      hupperP hupperQ
  have hnonpositive :
      _root_.GD.N0230.N0554.d001563 objective p q ≤ 0 := by
    unfold _root_.GD.N0230.N0554.d001563
    rw [hObjEq]
    have hminimum := hpMin hmidC
    change objective p ≤ objective (_root_.GD.N0230.N0718.d001528 p q) at hminimum
    linarith
  have hflat : _root_.GD.N0230.N0554.d001563 objective p q = 0 :=
    le_antisymm hnonpositive hnonnegative
  obtain ⟨theta, htaxZero, hpActive, hqActive⟩ :=
    (_root_.GD.N0230.N0587.d001595
      profile profileTax objective p q (hLUB _ hmidC) hexact htax
      hupperP hupperQ hlsc).1 hflat
  exact hactiveFaithful theta hpActive hqActive htaxZero





def d001602 (n : ℕ) (x : ℝ) : ℝ :=
  x + (x ^ 2 - 1) / ((n : ℝ) + 1)


def d001603 (n : ℕ) (p q : ℝ) : ℝ :=
  (p - q) ^ 2 / (4 * ((n : ℝ) + 1))



theorem d001604
    (n : ℕ) (p q : ℝ) :
    _root_.GD.N0230.N0587.d001602 n (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0230.N0587.d001603 n p q =
      (_root_.GD.N0230.N0587.d001602 n p + _root_.GD.N0230.N0587.d001602 n q) / 2 := by
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold _root_.GD.N0230.N0587.d001602 _root_.GD.N0230.N0587.d001603 _root_.GD.N0230.N0718.d001528
  norm_num [smul_eq_mul]
  field_simp
  ring



theorem d001605
    (n : ℕ) {p q : ℝ} (hpq : p ≠ q) :
    0 < _root_.GD.N0230.N0587.d001603 n p q := by
  unfold _root_.GD.N0230.N0587.d001603
  exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.2 hpq)) (by positivity)


theorem d001606 (x : ℝ) :
    Tendsto (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001602 n x)
      atTop (nhds x) := by
  have hvanish : Tendsto
      (fun n : ℕ ↦ (x ^ 2 - 1) * (1 / ((n : ℝ) + 1)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto
            (fun n : ℕ ↦ (x ^ 2 - 1) * (1 / ((n : ℝ) + 1)))
            atTop (nhds ((x ^ 2 - 1) * 0)))
  simpa [_root_.GD.N0230.N0587.d001602, div_eq_mul_inv] using
    (tendsto_const_nhds.add hvanish)



theorem d001607
    (u : ℕ → ℝ) (a : ℝ)
    (hupper : ∀ n, u n ≤ a)
    (hlimit : Tendsto u atTop (nhds a)) :
    IsLUB (Set.range u) a := by
  constructor
  · rintro value ⟨n, rfl⟩
    exact hupper n
  · intro b hb
    by_contra hnot
    have hba : b < a := lt_of_not_ge hnot
    have habove : ∀ᶠ n in atTop, b < u n :=
      (tendsto_order.1 hlimit).1 b hba
    obtain ⟨n, hn⟩ := habove.exists
    exact (not_lt_of_ge (hb ⟨n, rfl⟩)) hn



theorem d001608
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    _root_.GD.N0230.N0587.d001602 n x ≤ x := by
  have hxSq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hden : 0 < (n : ℝ) + 1 := by positivity
  unfold _root_.GD.N0230.N0587.d001602
  have hquotient : (x ^ 2 - 1) / ((n : ℝ) + 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  linarith



theorem d001609
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsLUB (Set.range (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001602 n x)) x := by
  exact _root_.GD.N0230.N0587.d001607
    (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001602 n x) x
    (_root_.GD.N0230.N0587.d001608 hx)
    (_root_.GD.N0230.N0587.d001606 x)



theorem d001610 (p q : ℝ) :
    Tendsto (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001603 n p q)
      atTop (nhds 0) := by
  have hvanish : Tendsto
      (fun n : ℕ ↦ ((p - q) ^ 2 / 4) *
        (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto
            (fun n : ℕ ↦ ((p - q) ^ 2 / 4) *
              (1 / ((n : ℝ) + 1)))
            atTop (nhds (((p - q) ^ 2 / 4) * 0)))
  have heq :
      (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001603 n p q) =
      (fun n : ℕ ↦ ((p - q) ^ 2 / 4) *
        (1 / ((n : ℝ) + 1))) := by
    funext n
    unfold _root_.GD.N0230.N0587.d001603
    field_simp
  rw [heq]
  exact hvanish








theorem d001611
    {p q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hpq : p ≠ q) :
    (∀ n, 0 < _root_.GD.N0230.N0587.d001603 n p q) ∧
      IsLUB (Set.range (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001602 n p)) p ∧
      IsLUB (Set.range (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001602 n q)) q ∧
      IsLUB (Set.range (fun n : ℕ ↦
        _root_.GD.N0230.N0587.d001602 n (_root_.GD.N0230.N0718.d001528 p q)))
        (_root_.GD.N0230.N0718.d001528 p q) ∧
      _root_.GD.N0230.N0554.d001563 (fun x : ℝ ↦ x) p q = 0 ∧
      Tendsto (fun n : ℕ ↦ _root_.GD.N0230.N0587.d001603 n p q)
        atTop (nhds 0) := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ Set.Icc (0 : ℝ) 1 := by
    unfold _root_.GD.N0230.N0718.d001528
    constructor <;> norm_num [smul_eq_mul] <;> nlinarith [hp.1, hp.2, hq.1, hq.2]
  refine ⟨fun n ↦ _root_.GD.N0230.N0587.d001605 n hpq,
    _root_.GD.N0230.N0587.d001609 hp,
    _root_.GD.N0230.N0587.d001609 hq,
    _root_.GD.N0230.N0587.d001609 hmid, ?_,
    _root_.GD.N0230.N0587.d001610 p q⟩
  unfold _root_.GD.N0230.N0554.d001563 _root_.GD.N0230.N0718.d001528
  norm_num [smul_eq_mul]
  ring

end

end N0587
end N0230
end GD

#print axioms _root_.GD.N0230.N0587.d001591
#print axioms _root_.GD.N0230.N0587.d001592
#print axioms _root_.GD.N0230.N0587.d001593
#print axioms _root_.GD.N0230.N0587.d001594
#print axioms _root_.GD.N0230.N0587.d001595
#print axioms _root_.GD.N0230.N0587.d001596
#print axioms _root_.GD.N0230.N0587.d001597
#print axioms _root_.GD.N0230.N0587.d001598
#print axioms _root_.GD.N0230.N0587.d001599
#print axioms _root_.GD.N0230.N0587.d001600
#print axioms _root_.GD.N0230.N0587.d001601
#print axioms _root_.GD.N0230.N0587.d001604
#print axioms _root_.GD.N0230.N0587.d001611
