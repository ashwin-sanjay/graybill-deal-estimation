import GD.Module0160
import GD.Module0763











open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0719
namespace N1000

noncomputable section

open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)



def d012398
    (kappa : Kernel (_root_.GD.N0232.N0719.N0859.d010811 k sizes) ℝ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ≥0∞ :=
  _root_.GD.N0230.N0642.d001800.d001823 kappa
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) theta.location



theorem d012399
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0230.N0642.d001800.d001817
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        theta.location d =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  rfl



theorem d012400
    (kappa : Kernel (_root_.GD.N0232.N0719.N0859.d010811 k sizes) ℝ)
    [IsMarkovKernel kappa]
    (hdom : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N1000.d012398 k sizes kappa theta ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N1013.d011537
            k sizes hk hsizes)) :
    ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      ∀ᵐ omega ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta,
        kappa omega = Measure.dirac
          (_root_.GD.N0232.N0719.N1013.d011537
            k sizes hk hsizes omega) := by
  apply _root_.GD.N0230.N0642.d001800.d001839
    (experiment := _root_.GD.N0232.N0719.N0859.d010812 k sizes)
    (target := fun theta : _root_.GD.N0232.N0719.N0859.d010809 k =>
      theta.location)
    (terminal :=
      _root_.GD.N0232.N0719.N1013.d011537
        k sizes hk hsizes)
    (kappa := kappa)
    (theta0 := _root_.GD.N0232.N0719.N0859.d010810 k)
  · intro d hd hdDom
    apply
      _root_.GD.N0232.N0719.N1013.d011543
        k sizes hk hsizes d hd
    intro theta
    simpa [_root_.GD.N0232.N0719.N1000.d012399] using hdDom theta
  · rw [_root_.GD.N0232.N0719.N1000.d012399,
      _root_.GD.N0232.N0719.N1013.d011540,
      _root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  · intro theta
    simpa [_root_.GD.N0232.N0719.N1000.d012398,
      _root_.GD.N0232.N0719.N1000.d012399] using hdom theta
  · exact
      _root_.GD.N0232.N0719.N0859.d010814 k sizes




theorem d012401
    (kappa : Kernel (_root_.GD.N0232.N0719.N0859.d010811 k sizes) ℝ)
    [IsMarkovKernel kappa]
    (hne : ¬ ∀ᵐ omega ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes,
      kappa omega = Measure.dirac
        (_root_.GD.N0232.N0719.N1013.d011537
          k sizes hk hsizes omega)) :
    ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
          (_root_.GD.N0232.N0719.N1013.d011537
            k sizes hk hsizes) <
        _root_.GD.N0232.N0719.N1000.d012398 k sizes kappa theta := by
  apply _root_.GD.N0230.N0642.d001800.d001841
    (experiment := _root_.GD.N0232.N0719.N0859.d010812 k sizes)
    (target := fun theta : _root_.GD.N0232.N0719.N0859.d010809 k =>
      theta.location)
    (terminal :=
      _root_.GD.N0232.N0719.N1013.d011537
        k sizes hk hsizes)
    (kappa := kappa)
    (theta0 := _root_.GD.N0232.N0719.N0859.d010810 k)
  · intro d hd hdDom
    apply
      _root_.GD.N0232.N0719.N1013.d011543
        k sizes hk hsizes d hd
    intro theta
    simpa [_root_.GD.N0232.N0719.N1000.d012399] using hdDom theta
  · rw [_root_.GD.N0232.N0719.N1000.d012399,
      _root_.GD.N0232.N0719.N1013.d011540,
      _root_.GD.N0232.N0719.N0859.d010829]
    exact ENNReal.ofReal_ne_top
  · exact
      _root_.GD.N0232.N0719.N0859.d010814 k sizes
  · simpa [_root_.GD.N0232.N0719.N0859.d010813,
      _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0859.d010810,
      _root_.GD.N0232.N0719.d009182] using hne

end

end N1000
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N1000.d012400
#print axioms _root_.GD.N0232.N0719.N1000.d012401
