import GD.Module0160
import GD.Module0912











open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1420

noncomputable section

open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800
open _root_.GD.N0232.N0720.N1080

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



def d014715
    (kappa : Kernel (_root_.GD.N0232.N0720.N1080.d014170 m n) ℝ)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ≥0∞ :=
  _root_.GD.N0230.N0642.d001800.d001823 kappa (_root_.GD.N0232.N0720.N1080.d014171 m n theta) theta.location



theorem d014716
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) theta.location d =
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
  rfl



theorem d014717
    (kappa : Kernel (_root_.GD.N0232.N0720.N1080.d014170 m n) ℝ) [IsMarkovKernel kappa]
    (hdom : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1420.d014715 m n kappa theta ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n theta
          (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn)) :
    ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta,
      kappa omega =
        Measure.dirac (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn omega) := by
  apply _root_.GD.N0230.N0642.d001800.d001839
    (experiment := _root_.GD.N0232.N0720.N1080.d014171 m n)
    (target := fun theta : _root_.GD.N0232.N0720.N1080.d014168 => theta.location)
    (terminal := _root_.GD.N0232.N0720.N1080.d014194 m n hm hn)
    (kappa := kappa)
    (theta0 := _root_.GD.N0232.N0720.N1080.d014169)
  · intro d hd hdDom
    apply _root_.GD.N0232.N0720.N1080.d014202 m n hm hn d hd
    intro theta
    simpa [_root_.GD.N0232.N0720.N1420.d014716] using hdDom theta
  · rw [_root_.GD.N0232.N0720.N1420.d014716,
      _root_.GD.N0232.N0720.N1080.d014200,
      _root_.GD.N0232.N0720.N1080.d014190]
    exact ENNReal.ofReal_ne_top
  · intro theta
    simpa [_root_.GD.N0232.N0720.N1420.d014715,
      _root_.GD.N0232.N0720.N1420.d014716] using hdom theta
  · exact _root_.GD.N0232.N0720.N1080.d014173 m n




theorem d014718
    (kappa : Kernel (_root_.GD.N0232.N0720.N1080.d014170 m n) ℝ) [IsMarkovKernel kappa]
    (hne : ¬ ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      kappa omega =
        Measure.dirac (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn omega)) :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta
          (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) <
        _root_.GD.N0232.N0720.N1420.d014715 m n kappa theta := by
  apply _root_.GD.N0230.N0642.d001800.d001841
    (experiment := _root_.GD.N0232.N0720.N1080.d014171 m n)
    (target := fun theta : _root_.GD.N0232.N0720.N1080.d014168 => theta.location)
    (terminal := _root_.GD.N0232.N0720.N1080.d014194 m n hm hn)
    (kappa := kappa)
    (theta0 := _root_.GD.N0232.N0720.N1080.d014169)
  · intro d hd hdDom
    apply _root_.GD.N0232.N0720.N1080.d014202 m n hm hn d hd
    intro theta
    simpa [_root_.GD.N0232.N0720.N1420.d014716] using hdDom theta
  · rw [_root_.GD.N0232.N0720.N1420.d014716,
      _root_.GD.N0232.N0720.N1080.d014200,
      _root_.GD.N0232.N0720.N1080.d014190]
    exact ENNReal.ofReal_ne_top
  · exact _root_.GD.N0232.N0720.N1080.d014173 m n
  · simpa [_root_.GD.N0232.N0720.N1080.d014172] using hne

end

end N1420
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1420.d014717
#print axioms _root_.GD.N0232.N0720.N1420.d014718
