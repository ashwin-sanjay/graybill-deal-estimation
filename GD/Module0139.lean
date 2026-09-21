import GD.Module0138






















namespace GD
namespace N0230
namespace N0554

noncomputable section

open _root_.GD.N0230.N0718

variable {Theta D : Type*}


def d001563
    [AddCommGroup D] [Module ℝ D]
    (objective : D → ℝ) (p q : D) : ℝ :=
  (objective p + objective q) / 2 -
    objective (_root_.GD.N0230.N0718.d001528 p q)



def d001564
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ) (objective : D → ℝ)
    (theta : Theta) (p q : D) : ℝ :=
  objective (_root_.GD.N0230.N0718.d001528 p q) -
    profile theta (_root_.GD.N0230.N0718.d001528 p q)



def d001565
    (profile : Theta → D → ℝ) (objective : D → ℝ)
    (theta : Theta) (p q : D) : ℝ :=
  ((objective p - profile theta p) +
    (objective q - profile theta q)) / 2






theorem d001566
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (theta : Theta) (p q : D)
    (hexact :
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2) :
    profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q =
      _root_.GD.N0230.N0554.d001563 objective p q +
        _root_.GD.N0230.N0554.d001564 profile objective theta p q := by
  unfold _root_.GD.N0230.N0554.d001565 _root_.GD.N0230.N0554.d001563
    _root_.GD.N0230.N0554.d001564
  linarith



theorem d001567
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ) (objective : D → ℝ)
    (theta : Theta) (p q : D)
    (hmid : profile theta (_root_.GD.N0230.N0718.d001528 p q) ≤
      objective (_root_.GD.N0230.N0718.d001528 p q)) :
    0 ≤ _root_.GD.N0230.N0554.d001564 profile objective theta p q := by
  unfold _root_.GD.N0230.N0554.d001564
  linarith



theorem d001568
    (profile : Theta → D → ℝ) (objective : D → ℝ)
    (theta : Theta) (p q : D)
    (hp : profile theta p ≤ objective p)
    (hq : profile theta q ≤ objective q) :
    0 ≤ _root_.GD.N0230.N0554.d001565 profile objective theta p q := by
  unfold _root_.GD.N0230.N0554.d001565
  linarith


theorem d001569
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ) (objective : D → ℝ)
    (theta : Theta) (p q : D)
    (hupper : ∀ d, profile theta d ≤ objective d) :
    0 ≤ _root_.GD.N0230.N0554.d001564 profile objective theta p q ∧
      0 ≤ _root_.GD.N0230.N0554.d001565 profile objective theta p q := by
  exact ⟨
    _root_.GD.N0230.N0554.d001567
      profile objective theta p q (hupper (_root_.GD.N0230.N0718.d001528 p q)),
    _root_.GD.N0230.N0554.d001568
      profile objective theta p q (hupper p) (hupper q)⟩




theorem d001570
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (theta : Theta) (p q : D) (eta : ℝ)
    (hexact :
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hactive :
      _root_.GD.N0230.N0554.d001564 profile objective theta p q < eta) :
    profileTax theta p q +
        _root_.GD.N0230.N0554.d001565 profile objective theta p q <
      _root_.GD.N0230.N0554.d001563 objective p q + eta := by
  rw [_root_.GD.N0230.N0554.d001566
    profile profileTax objective theta p q hexact]
  linarith





theorem d001571
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (theta : Theta) (p q : D) (eta : ℝ)
    (hexact :
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hdeficit : _root_.GD.N0230.N0554.d001563 objective p q = 0)
    (htax : 0 ≤ profileTax theta p q)
    (hslack : 0 ≤ _root_.GD.N0230.N0554.d001565 profile objective theta p q)
    (hactive :
      _root_.GD.N0230.N0554.d001564 profile objective theta p q < eta) :
    profileTax theta p q < eta ∧
      _root_.GD.N0230.N0554.d001565 profile objective theta p q < eta := by
  have hsum :=
    _root_.GD.N0230.N0554.d001570
      profile profileTax objective theta p q eta hexact hactive
  rw [hdeficit, zero_add] at hsum
  constructor <;> linarith



theorem d001572
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (theta : Theta) (p q : D) (eta : ℝ)
    (hexact :
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hdeficit : _root_.GD.N0230.N0554.d001563 objective p q = 0)
    (htax : 0 ≤ profileTax theta p q)
    (hp : profile theta p ≤ objective p)
    (hq : profile theta q ≤ objective q)
    (hactive : objective (_root_.GD.N0230.N0718.d001528 p q) - eta <
      profile theta (_root_.GD.N0230.N0718.d001528 p q)) :
    profileTax theta p q < eta ∧
      _root_.GD.N0230.N0554.d001565 profile objective theta p q < eta := by
  apply _root_.GD.N0230.N0554.d001571
    profile profileTax objective theta p q eta hexact hdeficit htax
    (_root_.GD.N0230.N0554.d001568 profile objective theta p q hp hq)
  unfold _root_.GD.N0230.N0554.d001564
  linarith



theorem d001573
    (profile : Theta → D → ℝ) (objective : D → ℝ)
    (theta : Theta) (p q : D) (eta : ℝ)
    (hp : profile theta p ≤ objective p)
    (hq : profile theta q ≤ objective q)
    (hslack : _root_.GD.N0230.N0554.d001565 profile objective theta p q < eta) :
    objective p - profile theta p < 2 * eta ∧
      objective q - profile theta q < 2 * eta := by
  unfold _root_.GD.N0230.N0554.d001565 at hslack
  constructor <;> linarith




theorem d001574
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (theta : Theta) (p q : D) (eta : ℝ)
    (hexact :
      profile theta (_root_.GD.N0230.N0718.d001528 p q) + profileTax theta p q =
        (profile theta p + profile theta q) / 2)
    (hdeficit : _root_.GD.N0230.N0554.d001563 objective p q = 0)
    (htax : 0 ≤ profileTax theta p q)
    (hp : profile theta p ≤ objective p)
    (hq : profile theta q ≤ objective q)
    (hactive : objective (_root_.GD.N0230.N0718.d001528 p q) - eta <
      profile theta (_root_.GD.N0230.N0718.d001528 p q)) :
    profileTax theta p q < eta ∧
      objective p - profile theta p < 2 * eta ∧
      objective q - profile theta q < 2 * eta := by
  obtain ⟨hTaxLt, hSlackLt⟩ :=
    _root_.GD.N0230.N0554.d001572
      profile profileTax objective theta p q eta hexact hdeficit htax
      hp hq hactive
  obtain ⟨hpLt, hqLt⟩ :=
    _root_.GD.N0230.N0554.d001573
      profile objective theta p q eta hp hq hSlackLt
  exact ⟨hTaxLt, hpLt, hqLt⟩




theorem d001575
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (thetaSeq : ℕ → Theta) (p q : D)
    (hexact : ∀ n,
      profile (thetaSeq n) (_root_.GD.N0230.N0718.d001528 p q) +
          profileTax (thetaSeq n) p q =
        (profile (thetaSeq n) p + profile (thetaSeq n) q) / 2)
    (hactive : Filter.Tendsto
      (fun n ↦ _root_.GD.N0230.N0554.d001564
        profile objective (thetaSeq n) p q)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ profileTax (thetaSeq n) p q +
        _root_.GD.N0230.N0554.d001565 profile objective (thetaSeq n) p q)
      Filter.atTop (nhds (_root_.GD.N0230.N0554.d001563 objective p q)) := by
  have hsum : Filter.Tendsto
      (fun n ↦ _root_.GD.N0230.N0554.d001563 objective p q +
        _root_.GD.N0230.N0554.d001564 profile objective (thetaSeq n) p q)
      Filter.atTop
      (nhds (_root_.GD.N0230.N0554.d001563 objective p q + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds hactive
  have heq :
      (fun n ↦ profileTax (thetaSeq n) p q +
        _root_.GD.N0230.N0554.d001565 profile objective (thetaSeq n) p q) =
      (fun n ↦ _root_.GD.N0230.N0554.d001563 objective p q +
        _root_.GD.N0230.N0554.d001564 profile objective (thetaSeq n) p q) := by
    funext n
    exact _root_.GD.N0230.N0554.d001566
      profile profileTax objective (thetaSeq n) p q (hexact n)
  rw [heq]
  simpa using hsum



theorem d001576
    [AddCommGroup D] [Module ℝ D]
    (profile : Theta → D → ℝ)
    (profileTax : Theta → D → D → ℝ)
    (objective : D → ℝ)
    (thetaSeq : ℕ → Theta) (p q : D)
    (hexact : ∀ n,
      profile (thetaSeq n) (_root_.GD.N0230.N0718.d001528 p q) +
          profileTax (thetaSeq n) p q =
        (profile (thetaSeq n) p + profile (thetaSeq n) q) / 2)
    (hactive : Filter.Tendsto
      (fun n ↦ _root_.GD.N0230.N0554.d001564
        profile objective (thetaSeq n) p q)
      Filter.atTop (nhds 0))
    (hdeficit : _root_.GD.N0230.N0554.d001563 objective p q = 0) :
    Filter.Tendsto
      (fun n ↦ profileTax (thetaSeq n) p q +
        _root_.GD.N0230.N0554.d001565 profile objective (thetaSeq n) p q)
      Filter.atTop (nhds 0) := by
  simpa [hdeficit] using
    _root_.GD.N0230.N0554.d001575
      profile profileTax objective thetaSeq p q hexact hactive

end

end N0554
end N0230
end GD

#print axioms _root_.GD.N0230.N0554.d001566
#print axioms _root_.GD.N0230.N0554.d001567
#print axioms _root_.GD.N0230.N0554.d001568
#print axioms _root_.GD.N0230.N0554.d001569
#print axioms _root_.GD.N0230.N0554.d001570
#print axioms _root_.GD.N0230.N0554.d001571
#print axioms _root_.GD.N0230.N0554.d001572
#print axioms _root_.GD.N0230.N0554.d001573
#print axioms _root_.GD.N0230.N0554.d001574
#print axioms _root_.GD.N0230.N0554.d001575
#print axioms _root_.GD.N0230.N0554.d001576
