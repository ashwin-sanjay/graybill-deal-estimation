import GD.Module0137


















namespace GD
namespace N0230
namespace N0555

open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0628
open _root_.GD.N0230.N0600

variable {Theta D : Type*}



theorem d001559
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (hupper : ∀ theta d, profile theta d ≤ objective d)
    (hexact : ∀ theta p q,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (theta : Theta) (p q : D) (epsilon : ℝ)
    (hactive : objective (_root_.GD.N0230.N0718.d001528 p q) - epsilon ≤
      profile theta (_root_.GD.N0230.N0718.d001528 p q)) :
    profileTax theta p q ≤
      (objective p + objective q) / 2 -
        objective (_root_.GD.N0230.N0718.d001528 p q) + epsilon := by
  have hp := hupper theta p
  have hq := hupper theta q
  have hEq := hexact theta p q
  linarith




theorem d001560
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (detectorTax : D → D → ℝ)
    (hupper : ∀ theta d, profile theta d ≤ objective d)
    (hexact : ∀ theta p q,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hactiveDetector : ∀ p q epsilon, 0 < epsilon →
      ∃ theta,
        objective (_root_.GD.N0230.N0718.d001528 p q) - epsilon ≤
          profile theta (_root_.GD.N0230.N0718.d001528 p q) ∧
        detectorTax p q ≤ profileTax theta p q)
    (p q : D) :
    objective (_root_.GD.N0230.N0718.d001528 p q) + detectorTax p q ≤
      (objective p + objective q) / 2 := by
  by_contra hnot
  have hstrict :
      (objective p + objective q) / 2 -
          objective (_root_.GD.N0230.N0718.d001528 p q) < detectorTax p q := by
    linarith
  let epsilon : ℝ :=
    (detectorTax p q -
      ((objective p + objective q) / 2 -
        objective (_root_.GD.N0230.N0718.d001528 p q))) / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  obtain ⟨theta, hactive, hdetector⟩ :=
    hactiveDetector p q epsilon hepsilon
  have hprofile := _root_.GD.N0230.N0555.d001559
    profile profileTax objective hupper hexact theta p q epsilon hactive
  dsimp [epsilon] at hprofile
  linarith




theorem d001561
    [AddCommGroup D] [Module ℝ D]
    (profile : ℕ → Theta → D → ℝ)
    (profileTax : ℕ → Theta → D → D → ℝ)
    (objective : ℕ → D → ℝ)
    (detectorTax : ℕ → D → D → ℝ)
    (hupper : ∀ i theta d, profile i theta d ≤ objective i d)
    (hexact : ∀ i theta p q,
      profile i theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax i theta p q =
        (profile i theta p + profile i theta q) / 2)
    (hactiveDetector : ∀ i p q epsilon, 0 < epsilon →
      ∃ theta,
        objective i (_root_.GD.N0230.N0718.d001528 p q) - epsilon ≤
          profile i theta (_root_.GD.N0230.N0718.d001528 p q) ∧
        detectorTax i p q ≤ profileTax i theta p q) :
    _root_.GD.N0230.N0600.d001547 objective detectorTax := by
  intro i p q
  exact _root_.GD.N0230.N0555.d001560
    (profile i) (profileTax i) (objective i) (detectorTax i)
    (hupper i) (hexact i) (hactiveDetector i) p q




theorem d001562
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (detectorTax : D → D → ℝ)
    (p q : D)
    (hupperP : ∀ theta, profile theta p ≤ objective p)
    (hupperQ : ∀ theta, profile theta q ≤ objective q)
    (hexact : ∀ theta,
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hSupMid : IsLUB
      (Set.range (fun theta => profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hnearActiveDetector : ∀ epsilon, 0 < epsilon → ∀ theta,
      objective (_root_.GD.N0230.N0718.d001528 p q) - epsilon <
          profile theta (_root_.GD.N0230.N0718.d001528 p q) →
        detectorTax p q ≤ profileTax theta p q) :
    objective (_root_.GD.N0230.N0718.d001528 p q) + detectorTax p q ≤
      (objective p + objective q) / 2 := by
  by_contra hnot
  have hstrict :
      (objective p + objective q) / 2 -
          objective (_root_.GD.N0230.N0718.d001528 p q) < detectorTax p q := by
    linarith
  let epsilon : ℝ :=
    (detectorTax p q -
      ((objective p + objective q) / 2 -
        objective (_root_.GD.N0230.N0718.d001528 p q))) / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  obtain ⟨value, ⟨theta, hthetaValue⟩, hnear, _⟩ :=
    hSupMid.exists_between
      (sub_lt_self (objective (_root_.GD.N0230.N0718.d001528 p q)) hepsilon)
  subst value
  have hdetector := hnearActiveDetector epsilon hepsilon theta hnear
  have hEq := hexact theta
  have hp := hupperP theta
  have hq := hupperQ theta
  dsimp [epsilon] at hnear
  linarith

end N0555
end N0230
end GD

#print axioms _root_.GD.N0230.N0555.d001559
#print axioms _root_.GD.N0230.N0555.d001560
#print axioms _root_.GD.N0230.N0555.d001561
#print axioms _root_.GD.N0230.N0555.d001562
