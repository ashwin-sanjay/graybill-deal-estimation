import GD.Module0139
















namespace GD
namespace N0230
namespace N0651

open Set
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0554

variable {Theta D : Type*}








theorem d001586
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2) :
    IsGLB
      (Set.range (fun theta ↦
        profileTax theta p q +
          _root_.GD.N0230.N0554.d001565 profile objective theta p q))
      (_root_.GD.N0230.N0554.d001563 objective p q) := by
  constructor
  · rintro value ⟨theta, rfl⟩
    change _root_.GD.N0230.N0554.d001563 objective p q ≤
      profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q
    have hprofileLe :
        profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
          objective (_root_.GD.N0230.N0718.d001528 p q) :=
      hLUB.1 ⟨theta, rfl⟩
    have hgap : 0 ≤
        _root_.GD.N0230.N0554.d001564 profile objective theta p q :=
      _root_.GD.N0230.N0554.d001567
        profile objective theta p q hprofileLe
    rw [_root_.GD.N0230.N0554.d001566
      profile profileTax objective theta p q (hexact theta)]
    linarith
  · intro lower hlower
    have hprofileUpper : ∀ value ∈
        Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)),
        value ≤ (objective p + objective q) / 2 - lower := by
      rintro value ⟨theta, rfl⟩
      have hresidual := hlower ⟨theta, rfl⟩
      have hconservation :=
        _root_.GD.N0230.N0554.d001566
          profile profileTax objective theta p q (hexact theta)
      dsimp [_root_.GD.N0230.N0554.d001563,
        _root_.GD.N0230.N0554.d001564] at hconservation
      linarith
    have hobjectiveUpper := hLUB.2 hprofileUpper
    dsimp [_root_.GD.N0230.N0554.d001563]
    linarith



theorem d001587
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ) (p q : D)
    (hLUB : IsLUB
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2) :
    0 < _root_.GD.N0230.N0554.d001563 objective p q ↔
      ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ theta,
        epsilon ≤ profileTax theta p q +
          _root_.GD.N0230.N0554.d001565 profile objective theta p q := by
  let hGLB :=
    _root_.GD.N0230.N0651.d001586
      profile profileTax objective p q hLUB hexact
  constructor
  · intro hpositive
    exact ⟨_root_.GD.N0230.N0554.d001563 objective p q, hpositive,
      fun theta ↦ hGLB.1 ⟨theta, rfl⟩⟩
  · rintro ⟨epsilon, hepsilon, hfloor⟩
    have hepsilonLe : epsilon ≤
        _root_.GD.N0230.N0554.d001563 objective p q := by
      apply hGLB.2
      rintro value ⟨theta, rfl⟩
      exact hfloor theta
    exact lt_of_lt_of_le hepsilon hepsilonLe



theorem d001588
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
    (hresidualNonnegative : ∀ theta,
      0 ≤ profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q) :
    _root_.GD.N0230.N0554.d001563 objective p q = 0 ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∃ theta,
        profileTax theta p q +
          _root_.GD.N0230.N0554.d001565 profile objective theta p q < epsilon := by
  let hGLB :=
    _root_.GD.N0230.N0651.d001586
      profile profileTax objective p q hLUB hexact
  have hdeficitNonnegative :
      0 ≤ _root_.GD.N0230.N0554.d001563 objective p q := by
    apply hGLB.2
    rintro value ⟨theta, rfl⟩
    exact hresidualNonnegative theta
  constructor
  · intro hzero epsilon hepsilon
    by_contra hnone
    have hfloor : ∀ theta,
        epsilon ≤ profileTax theta p q +
          _root_.GD.N0230.N0554.d001565 profile objective theta p q := by
      intro theta
      exact le_of_not_gt (fun hlt ↦ hnone ⟨theta, hlt⟩)
    have hepsilonLe : epsilon ≤
        _root_.GD.N0230.N0554.d001563 objective p q := by
      apply hGLB.2
      rintro value ⟨theta, rfl⟩
      exact hfloor theta
    rw [hzero] at hepsilonLe
    linarith
  · intro hcollapse
    apply le_antisymm
    · by_contra hnot
      have hpositive : 0 < _root_.GD.N0230.N0554.d001563 objective p q :=
        lt_of_not_ge hnot
      obtain ⟨theta, htheta⟩ :=
        hcollapse (_root_.GD.N0230.N0554.d001563 objective p q) hpositive
      have hlower := hGLB.1 ⟨theta, rfl⟩
      linarith
    · exact hdeficitNonnegative



theorem d001589
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
      ∀ epsilon : ℝ, 0 < epsilon → ∃ theta,
        profileTax theta p q < epsilon ∧
        objective p - profile theta p < 2 * epsilon ∧
        objective q - profile theta q < 2 * epsilon := by
  rw [_root_.GD.N0230.N0651.d001588
    profile profileTax objective p q hLUB hexact]
  · constructor
    · intro hcollapse epsilon hepsilon
      obtain ⟨theta, htotal⟩ := hcollapse epsilon hepsilon
      have hslackNonnegative := _root_.GD.N0230.N0554.d001568
        profile objective theta p q (hupperP theta) (hupperQ theta)
      have htaxLt : profileTax theta p q < epsilon := by
        linarith [htax theta]
      have hslackLt :
          _root_.GD.N0230.N0554.d001565 profile objective theta p q < epsilon := by
        linarith [htax theta]
      obtain ⟨hpLt, hqLt⟩ :=
        _root_.GD.N0230.N0554.d001573
          profile objective theta p q epsilon
          (hupperP theta) (hupperQ theta) hslackLt
      exact ⟨theta, htaxLt, hpLt, hqLt⟩
    · intro htriple epsilon hepsilon
      obtain ⟨theta, htaxLt, hpLt, hqLt⟩ :=
        htriple (epsilon / 4) (by linarith)
      refine ⟨theta, ?_⟩
      unfold _root_.GD.N0230.N0554.d001565
      linarith
  · intro theta
    exact add_nonneg (htax theta)
      (_root_.GD.N0230.N0554.d001568 profile objective theta p q
        (hupperP theta) (hupperQ theta))

end N0651
end N0230
end GD

#print axioms _root_.GD.N0230.N0651.d001586
#print axioms _root_.GD.N0230.N0651.d001587
#print axioms _root_.GD.N0230.N0651.d001588
#print axioms _root_.GD.N0230.N0651.d001589
