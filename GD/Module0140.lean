import GD.Module0138















namespace GD
namespace N0230
namespace N0578

open Set
open _root_.GD.N0230.N0718

variable {Theta D : Type*}










theorem d001577
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
      (Set.range (fun theta ↦ profile theta (_root_.GD.N0230.N0718.d001528 p q)))
      (objective (_root_.GD.N0230.N0718.d001528 p q)))
    (hcofinalRetention : ∀ eta, 0 < eta →
      ∃ theta,
        objective (_root_.GD.N0230.N0718.d001528 p q) - eta <
            profile theta (_root_.GD.N0230.N0718.d001528 p q) ∧
          detectorTax p q ≤ profileTax theta p q) :
    objective (_root_.GD.N0230.N0718.d001528 p q) + detectorTax p q ≤
      (objective p + objective q) / 2 := by
  by_contra hnot
  have hstrict :
      (objective p + objective q) / 2 -
          objective (_root_.GD.N0230.N0718.d001528 p q) < detectorTax p q := by
    linarith
  let eta : ℝ :=
    (detectorTax p q -
      ((objective p + objective q) / 2 -
        objective (_root_.GD.N0230.N0718.d001528 p q))) / 2
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  obtain ⟨theta, hnear, hdetector⟩ := hcofinalRetention eta heta
  have hmidUpper :
      profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
        objective (_root_.GD.N0230.N0718.d001528 p q) :=
    hSupMid.1 ⟨theta, rfl⟩
  have hEq := hexact theta
  have hpBound := hupperP theta
  have hqBound := hupperQ theta
  dsimp [eta] at hnear
  linarith

end N0578
end N0230
end GD

#print axioms _root_.GD.N0230.N0578.d001577
