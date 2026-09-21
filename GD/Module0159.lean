import Mathlib.Data.ENNReal.Real






















open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N1001

variable {Theta Decision Randomized : Type*}


def d001793
    (risk : Theta -> Decision -> ℝ≥0∞)
    (e d : Decision) : Prop :=
  forall theta, risk theta e <= risk theta d


def d001794
    (risk : Theta -> Decision -> ℝ≥0∞)
    (d : Decision) : Prop :=
  forall e, _root_.GD.N0232.N0719.N1001.d001793 risk e d -> e = d








structure d001795
    (Theta Decision Randomized : Type*) where
  deterministicRisk : Theta -> Decision -> ℝ≥0∞
  randomizedRisk : Theta -> Randomized -> ℝ≥0∞
  barycenter : Randomized -> Decision
  dispersion : Theta -> Randomized -> ℝ≥0∞
  pure : Decision -> Randomized
  risk_decomposition : forall theta kappa,
    randomizedRisk theta kappa =
      deterministicRisk theta (barycenter kappa) + dispersion theta kappa
  barycenter_pure : forall d, barycenter (pure d) = d
  zero_dispersion_identifies : forall theta kappa,
    dispersion theta kappa = 0 -> kappa = pure (barycenter kappa)

namespace d001795

variable (Q : _root_.GD.N0232.N0719.N1001.d001795 Theta Decision Randomized)



theorem d001796
    {kappa : Randomized} {d : Decision}
    (hdom : forall theta,
      Q.randomizedRisk theta kappa <= Q.deterministicRisk theta d) :
    _root_.GD.N0232.N0719.N1001.d001793 Q.deterministicRisk (Q.barycenter kappa) d := by
  intro theta
  calc
    Q.deterministicRisk theta (Q.barycenter kappa) <=
        Q.deterministicRisk theta (Q.barycenter kappa) +
          Q.dispersion theta kappa := by
      exact le_self_add
    _ = Q.randomizedRisk theta kappa :=
      (Q.risk_decomposition theta kappa).symm
    _ <= Q.deterministicRisk theta d := hdom theta



theorem d001797
    {a b : ℝ≥0∞} (ha : a ≠ ∞) (h : a + b <= a) :
    b = 0 := by
  have h' : a + b <= a + 0 := by simpa using h
  have hb : b <= 0 :=
    (WithTop.add_le_add_iff_left ha).1 h'
  exact bot_unique hb









theorem d001798
    {d : Decision} {kappa : Randomized} {theta0 : Theta}
    (hterminal : _root_.GD.N0232.N0719.N1001.d001794 Q.deterministicRisk d)
    (hfinite : Q.deterministicRisk theta0 d ≠ ∞)
    (hdom : forall theta,
      Q.randomizedRisk theta kappa <= Q.deterministicRisk theta d) :
    kappa = Q.pure d := by
  have hbary : Q.barycenter kappa = d :=
    hterminal (Q.barycenter kappa)
      (Q.d001796 hdom)
  have hsum :
      Q.deterministicRisk theta0 d + Q.dispersion theta0 kappa <=
        Q.deterministicRisk theta0 d := by
    calc
      Q.deterministicRisk theta0 d + Q.dispersion theta0 kappa =
          Q.deterministicRisk theta0 (Q.barycenter kappa) +
            Q.dispersion theta0 kappa := by rw [hbary]
      _ = Q.randomizedRisk theta0 kappa :=
        (Q.risk_decomposition theta0 kappa).symm
      _ <= Q.deterministicRisk theta0 d := hdom theta0
  have hdisp : Q.dispersion theta0 kappa = 0 :=
    _root_.GD.N0232.N0719.N1001.d001795.d001797 hfinite hsum
  calc
    kappa = Q.pure (Q.barycenter kappa) :=
      Q.zero_dispersion_identifies theta0 kappa hdisp
    _ = Q.pure d := by rw [hbary]



theorem d001799
    {d : Decision} {kappa : Randomized} {theta0 : Theta}
    (hterminal : _root_.GD.N0232.N0719.N1001.d001794 Q.deterministicRisk d)
    (hfinite : Q.deterministicRisk theta0 d ≠ ∞)
    (hne : kappa ≠ Q.pure d) :
    exists theta,
      Q.deterministicRisk theta d < Q.randomizedRisk theta kappa := by
  by_contra hno
  apply hne
  apply Q.d001798 hterminal hfinite
  intro theta
  exact le_of_not_gt (fun hlt => hno ⟨theta, hlt⟩)

end d001795

end N1001
end N0719
end N0232
end GD
