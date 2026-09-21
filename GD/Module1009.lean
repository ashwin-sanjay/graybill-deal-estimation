import GD.Module1008



























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1182

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1179




def d016042
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0232.N0720.N1173.d015937 theta x)






def d016043
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ≥0∞ :=
  ∫⁻ theta, _root_.GD.N0232.N0720.N1182.d016042 theta x ∂_root_.GD.N0232.N0720.N1173.d015934 rho


def d016044
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0232.N0720.N1179.d016029 h z ^ 2)




def d016045
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (x : _root_.GD.N0232.N0720.N1173.d015936) (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ≥0∞ :=
  _root_.GD.N0232.N0720.N1182.d016042 z.1 x * _root_.GD.N0232.N0720.N1182.d016042 z.2 x /
    _root_.GD.N0232.N0720.N1182.d016043 rho x


def d016046
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (x : _root_.GD.N0232.N0720.N1173.d015936) (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ≥0∞ :=
  _root_.GD.N0232.N0720.N1182.d016044 h z *
    _root_.GD.N0232.N0720.N1182.d016045 rho x z




def d016047
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
    _root_.GD.N0232.N0720.N1182.d016046 rho h x z ∂
      (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho) ∂
        _root_.GD.N0232.N0720.N1080.d014172 2 2



def d016048
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) : ℝ≥0∞ :=
  ∫⁻ x, _root_.GD.N0232.N0720.N1182.d016045 rho x z ∂_root_.GD.N0232.N0720.N1080.d014172 2 2


def d016049
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933,
    _root_.GD.N0232.N0720.N1182.d016044 h z * _root_.GD.N0232.N0720.N1182.d016048 rho z ∂
      (_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)



theorem d016050
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 < _root_.GD.N0232.N0720.N1182.d016042 theta x := by
  exact ENNReal.ofReal_pos.mpr
    (_root_.GD.N0232.N0720.N1499.d015005 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x)

theorem d016051
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1182.d016042 theta x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem d016052
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) :
    _root_.GD.N0232.N0720.N1182.d016044 h z ≠ ⊤ :=
  ENNReal.ofReal_ne_top



theorem d016053 (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    Measurable (_root_.GD.N0232.N0720.N1182.d016042 theta) := by
  exact
    (_root_.GD.N0232.N0720.N1499.d015002 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta)).ennreal_ofReal



theorem d016054 (x : _root_.GD.N0232.N0720.N1173.d015936) :
    Measurable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦ _root_.GD.N0232.N0720.N1182.d016042 theta x) := by
  unfold _root_.GD.N0232.N0720.N1182.d016042 _root_.GD.N0232.N0720.N1173.d015937 _root_.GD.N0232.N0720.N1173.d015935
  exact
    ((_root_.GD.N0232.N0720.N1499.d015007 2 2 x).comp
      (_root_.GD.N0232.N0720.N1486.d015877
        2 2 (by norm_num) (by norm_num))).measurable.ennreal_ofReal





theorem d016055
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (x : _root_.GD.N0232.N0720.N1173.d015936) (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933)
    (hpos : 0 < _root_.GD.N0232.N0720.N1182.d016043 rho x)
    (hfinite : _root_.GD.N0232.N0720.N1182.d016043 rho x ≠ ⊤) :
    _root_.GD.N0232.N0720.N1182.d016043 rho x *
        _root_.GD.N0232.N0720.N1182.d016045 rho x z =
      _root_.GD.N0232.N0720.N1182.d016042 z.1 x * _root_.GD.N0232.N0720.N1182.d016042 z.2 x := by
  unfold _root_.GD.N0232.N0720.N1182.d016045
  exact ENNReal.mul_div_cancel (ne_of_gt hpos) hfinite



theorem d016056
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (hEvidence : AEMeasurable (_root_.GD.N0232.N0720.N1182.d016043 rho)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (z : _root_.GD.N0232.N0720.N1173.d015933 × _root_.GD.N0232.N0720.N1173.d015933) :
    AEMeasurable (fun x ↦ _root_.GD.N0232.N0720.N1182.d016045 rho x z)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  unfold _root_.GD.N0232.N0720.N1182.d016045
  exact
    ((_root_.GD.N0232.N0720.N1182.d016053 z.1).aemeasurable.mul
      (_root_.GD.N0232.N0720.N1182.d016053 z.2).aemeasurable).div hEvidence
















theorem d016057
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (h : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hEvidence : AEMeasurable (_root_.GD.N0232.N0720.N1182.d016043 rho)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hjoint : AEMeasurable
      (Function.uncurry (_root_.GD.N0232.N0720.N1182.d016046 rho h))
      ((_root_.GD.N0232.N0720.N1080.d014172 2 2).prod
        ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1173.d015934 rho)))) :
    _root_.GD.N0232.N0720.N1182.d016047 rho h =
      _root_.GD.N0232.N0720.N1182.d016049 rho h := by
  letI : SigmaFinite (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
    unfold _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  letI : SFinite (_root_.GD.N0232.N0720.N1080.d014172 2 2) := inferInstance
  unfold _root_.GD.N0232.N0720.N1182.d016047 _root_.GD.N0232.N0720.N1182.d016049
  rw [MeasureTheory.lintegral_lintegral_swap hjoint]
  apply lintegral_congr
  intro z
  unfold _root_.GD.N0232.N0720.N1182.d016046 _root_.GD.N0232.N0720.N1182.d016048
  rw [lintegral_const_mul'' _
    (_root_.GD.N0232.N0720.N1182.d016056 rho hEvidence z)]

end

end N1182
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1182.d016055
#print axioms _root_.GD.N0232.N0720.N1182.d016057
