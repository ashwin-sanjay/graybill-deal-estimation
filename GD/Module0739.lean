import GD.Module0140
import GD.Module0738
















open MeasureTheory Set

namespace GD
namespace N0232
namespace N0719
namespace N0807

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0555
open _root_.GD.N0230.N0578












theorem d011049
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hcollar : Nonempty {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon})
    (detectorTax : _root_.GD.N0232.N0719.N0816.d010975 k sizes → _root_.GD.N0232.N0719.N0816.d010975 k sizes → ℝ)
    (hnearActiveDetector : ∀ eta, 0 < eta →
      ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
        _root_.GD.N0232.N0719.N0812.d011046
              k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) - eta <
            _root_.GD.N0232.N0719.N0811.d011036
              k sizes hk hsizes theta.1 (_root_.GD.N0230.N0718.d001528 p q) →
          detectorTax p q ≤
            _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q) :
    _root_.GD.N0232.N0719.N0812.d011046
          k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) +
        detectorTax p q ≤
      (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon p +
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon q) / 2 := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    unfold _root_.GD.N0230.N0718.d001528
    apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hp hq
    · norm_num
    · norm_num
    · norm_num
  have hupperP : ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p ≤
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon p := by
    intro theta
    exact
      (_root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes active epsilon hp hcollar).1 ⟨theta, rfl⟩
  have hupperQ : ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q ≤
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon q := by
    intro theta
    exact
      (_root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes active epsilon hq hcollar).1 ⟨theta, rfl⟩
  have hexact : ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
          (_root_.GD.N0230.N0718.d001528 p q) +
          _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q =
        (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p +
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q) / 2 := by
    intro theta
    exact _root_.GD.N0232.N0719.N0811.d011040
      k sizes hk hsizes theta.1 hp hq
  have hSupMid := _root_.GD.N0232.N0719.N0812.d011048
    k sizes hk hsizes active epsilon hmid hcollar
  by_contra hnot
  have hstrict :
      (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon p +
          _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon q) / 2 -
          _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon
            (_root_.GD.N0230.N0718.d001528 p q) < detectorTax p q := by
    linarith
  let eta : ℝ :=
    (detectorTax p q -
      ((_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon p +
          _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon q) / 2 -
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon
          (_root_.GD.N0230.N0718.d001528 p q))) / 2
  have heta : 0 < eta := by
    dsimp [eta]
    linarith
  obtain ⟨value, ⟨theta, hthetaValue⟩, hnear, _⟩ :=
    hSupMid.exists_between
      (sub_lt_self
        (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon
          (_root_.GD.N0230.N0718.d001528 p q)) heta)
  subst value
  have hdetector := hnearActiveDetector eta heta theta hnear
  have hEq := hexact theta
  have hpBound := hupperP theta
  have hqBound := hupperQ theta
  dsimp [eta] at hnear
  linarith








theorem d011050
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hcollar : Nonempty {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon})
    (detectorTax : _root_.GD.N0232.N0719.N0816.d010975 k sizes → _root_.GD.N0232.N0719.N0816.d010975 k sizes → ℝ)
    (hcofinalRetention : ∀ eta, 0 < eta →
      ∃ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
        _root_.GD.N0232.N0719.N0812.d011046
              k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) - eta <
            _root_.GD.N0232.N0719.N0811.d011036
              k sizes hk hsizes theta.1 (_root_.GD.N0230.N0718.d001528 p q) ∧
          detectorTax p q ≤
            _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q) :
    _root_.GD.N0232.N0719.N0812.d011046
          k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) +
        detectorTax p q ≤
      (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon p +
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon q) / 2 := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    unfold _root_.GD.N0230.N0718.d001528
    apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hp hq
    · norm_num
    · norm_num
    · norm_num
  have hupperP : ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p ≤
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon p := by
    intro theta
    exact
      (_root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes active epsilon hp hcollar).1 ⟨theta, rfl⟩
  have hupperQ : ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q ≤
        _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon q := by
    intro theta
    exact
      (_root_.GD.N0232.N0719.N0812.d011048
        k sizes hk hsizes active epsilon hq hcollar).1 ⟨theta, rfl⟩
  have hexact : ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1
          (_root_.GD.N0230.N0718.d001528 p q) +
          _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta.1 p q =
        (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 p +
          _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 q) / 2 := by
    intro theta
    exact _root_.GD.N0232.N0719.N0811.d011040
      k sizes hk hsizes theta.1 hp hq
  exact _root_.GD.N0230.N0578.d001577
    (Theta := {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon})
    (D := _root_.GD.N0232.N0719.N0816.d010975 k sizes)
    (fun theta d ↦ _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 d)
    (fun theta p q ↦ _root_.GD.N0232.N0719.N0811.d011037
      k sizes hk hsizes theta.1 p q)
    (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon)
    detectorTax p q hupperP hupperQ hexact
    (_root_.GD.N0232.N0719.N0812.d011048
      k sizes hk hsizes active epsilon hmid hcollar)
    hcofinalRetention

end

end N0807
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0807.d011049
#print axioms _root_.GD.N0232.N0719.N0807.d011050
