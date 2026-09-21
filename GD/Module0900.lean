import GD.Module0898














open MeasureTheory ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1423

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1504



theorem d014018
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ q, (_root_.GD.N0232.N0720.N1091.d012759 p q - p) ^ 2
      ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta) =
      _root_.GD.N0232.N0720.N1091.d012790 alpha beta p :=
  _root_.GD.N0232.N0720.N1091.d012799
    halpha hbeta hp0 hp1 (_root_.GD.N0232.N0720.N1504.d013979 halpha hbeta)



theorem d014019
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ q, (_root_.GD.N0232.N0720.N1091.d012759 p q - p) ^ 2
      ∂_root_.GD.N0232.N0720.N1091.d012754 alpha beta) =
      _root_.GD.N0232.N0720.N1091.d012791 alpha beta p := by
  rw [_root_.GD.N0232.N0720.N1423.d014018
    halpha hbeta hp0 hp1]
  exact _root_.GD.N0232.N0720.N1091.d012800
    halpha hbeta hp0 hp1



theorem d014020
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0120.d008809 alpha beta p
        (fun z : ℝ × ℝ => (z.1 - p) ^ 2) =
      _root_.GD.N0232.N0720.N1091.d012791 alpha beta p :=
  _root_.GD.N0232.N0720.N1091.d012801
    halpha hbeta hp0 hp1 (_root_.GD.N0232.N0720.N1504.d013979 halpha hbeta)



theorem d014021
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0120.d008809 alpha beta p
        (fun z : ℝ × ℝ => (z.1 - p) ^ 2) =
      ∫ u,
        p ^ 2 * (1 - p) ^ 2 *
          (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u) ^ 2 /
            (_root_.GD.N0232.N0720.N1091.d012764 alpha beta p u) ^ 2
        ∂betaMeasure alpha beta := by
  rw [_root_.GD.N0232.N0720.N1423.d014020
    halpha hbeta hp0 hp1]
  rfl



theorem d014022
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {U D L F : Omega → ℝ}
    {alpha beta p Sigma : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun omega => D omega * (L omega - p)) 2 P)
    (hOrthogonality :
      (∫ omega, U omega * (D omega * (L omega - p)) ∂P) = 0)
    (hLaw : _root_.GD.N0125.d008847
      P D L F alpha beta p Sigma) :
    _root_.GD.N0141.d006684 P
          (_root_.GD.N0141.d006685 U D L p) -
        _root_.GD.N0141.d006684 P U =
      Sigma * _root_.GD.N0232.N0720.N1091.d012791 alpha beta p :=
  _root_.GD.N0232.N0720.N1091.d012802
    halpha hbeta hp0 hp1 hU hWeight hOrthogonality hLaw
      (_root_.GD.N0232.N0720.N1504.d013979 halpha hbeta)


theorem d014023
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {U D L F : Omega → ℝ}
    {alpha beta p Sigma : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun omega => D omega * (L omega - p)) 2 P)
    (hOrthogonality :
      (∫ omega, U omega * (D omega * (L omega - p)) ∂P) = 0)
    (hLaw : _root_.GD.N0125.d008847
      P D L F alpha beta p Sigma) :
    _root_.GD.N0141.d006684 P
          (_root_.GD.N0141.d006685 U D L p) -
        _root_.GD.N0141.d006684 P U =
      Sigma *
        ∫ u,
          p ^ 2 * (1 - p) ^ 2 *
            (_root_.GD.N0232.N0720.N1091.d012765 alpha beta u) ^ 2 /
              (_root_.GD.N0232.N0720.N1091.d012764 alpha beta p u) ^ 2
          ∂betaMeasure alpha beta := by
  rw [_root_.GD.N0232.N0720.N1423.d014022
    halpha hbeta hp0 hp1 hU hWeight hOrthogonality hLaw]
  rfl

end

end N1423
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1423.d014018
#print axioms _root_.GD.N0232.N0720.N1423.d014019
#print axioms _root_.GD.N0232.N0720.N1423.d014020
#print axioms _root_.GD.N0232.N0720.N1423.d014021
#print axioms _root_.GD.N0232.N0720.N1423.d014022
#print axioms _root_.GD.N0232.N0720.N1423.d014023
