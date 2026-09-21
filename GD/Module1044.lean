import GD.Module1001
import GD.Module1009
import GD.Module1034
import GD.Module0961
































open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1180

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1172
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1182
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229


def d016651
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (z : _root_.GD.N0232.N0720.N1172.d015905 ×
      _root_.GD.N0232.N0720.N1172.d015905) :
      _root_.GD.N0232.N0720.N1172.d015905 ×
        _root_.GD.N0232.N0720.N1172.d015905 :=
  (_root_.GD.N0232.N0720.N1172.d015906 g z.1, _root_.GD.N0232.N0720.N1172.d015906 g z.2)



def d016652
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ≥0∞ :=
  ENNReal.ofReal
    (_root_.GD.N0232.N0720.N1499.d015001 2 2
      (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • x))



def d016653
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ≥0∞ :=
  ENNReal.ofReal
    (_root_.GD.N0232.N0720.N1499.d015001 2 2
      (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) x)


def d016654 (g : _root_.GD.N0232.N0719.N0946.d009229) : ℝ≥0∞ :=
  ENNReal.ofReal (g.d009239 ^ 2)








theorem d016655
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (z : _root_.GD.N0232.N0720.N1172.d015905 ×
      _root_.GD.N0232.N0720.N1172.d015905)
    (hreference :
      _root_.GD.N0232.N0720.N1182.d016048 rho (_root_.GD.N0232.N0720.N1180.d016651 g z) =
        ∫⁻ x,
          _root_.GD.N0232.N0720.N1182.d016045 rho (g • x)
              (_root_.GD.N0232.N0720.N1180.d016651 g z) *
            _root_.GD.N0232.N0720.N1180.d016653 g x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2)
    (hdensity : ∀ x,
      _root_.GD.N0232.N0720.N1182.d016045 rho (g • x)
          (_root_.GD.N0232.N0720.N1180.d016651 g z) =
        _root_.GD.N0232.N0720.N1180.d016654 g * _root_.GD.N0232.N0720.N1180.d016652 g x *
          _root_.GD.N0232.N0720.N1182.d016045 rho x z)
    (hcocycle : ∀ x,
      _root_.GD.N0232.N0720.N1180.d016652 g x *
        _root_.GD.N0232.N0720.N1180.d016653 g x = 1)
    (hmeas : AEMeasurable
      (fun x ↦ _root_.GD.N0232.N0720.N1182.d016045 rho x z)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    _root_.GD.N0232.N0720.N1182.d016048 rho (_root_.GD.N0232.N0720.N1180.d016651 g z) =
      _root_.GD.N0232.N0720.N1180.d016654 g * _root_.GD.N0232.N0720.N1182.d016048 rho z := by
  rw [hreference]
  calc
    (∫⁻ x,
        _root_.GD.N0232.N0720.N1182.d016045 rho (g • x)
            (_root_.GD.N0232.N0720.N1180.d016651 g z) *
          _root_.GD.N0232.N0720.N1180.d016653 g x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) =
        ∫⁻ x, _root_.GD.N0232.N0720.N1180.d016654 g *
          _root_.GD.N0232.N0720.N1182.d016045 rho x z ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
      apply lintegral_congr
      intro x
      rw [hdensity x]
      calc
        (_root_.GD.N0232.N0720.N1180.d016654 g * _root_.GD.N0232.N0720.N1180.d016652 g x *
              _root_.GD.N0232.N0720.N1182.d016045 rho x z) *
            _root_.GD.N0232.N0720.N1180.d016653 g x =
            _root_.GD.N0232.N0720.N1180.d016654 g *
              _root_.GD.N0232.N0720.N1182.d016045 rho x z *
                (_root_.GD.N0232.N0720.N1180.d016652 g x *
                  _root_.GD.N0232.N0720.N1180.d016653 g x) := by
              ac_rfl
        _ = _root_.GD.N0232.N0720.N1180.d016654 g *
              _root_.GD.N0232.N0720.N1182.d016045 rho x z := by
              rw [hcocycle x, mul_one]
    _ = _root_.GD.N0232.N0720.N1180.d016654 g *
          _root_.GD.N0232.N0720.N1182.d016048 rho z := by
      rw [lintegral_const_mul'' _ hmeas]
      rfl

end

end N1180
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1180.d016655
