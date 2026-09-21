import GD.Module1911









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0197
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1228
open _root_.GD.N0230.N0611



theorem d030958
    (C : Set (_root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ))
    (hC : ∀ d ∈ C, Measurable d) :
    ENNReal.ofReal ((1 + Real.pi / 4) / 2) ≤
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num)) C := by
  exact le_iInf fun d => le_iInf fun hd =>
    _root_.GD.N0162.d030952 d (hC d hd)


theorem d030959 :
    ENNReal.ofReal ((1 + Real.pi / 4) / 2) ≤
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num))
        (_root_.GD.N0232.N0720.N1256.d015545 3 3) := by
  exact _root_.GD.N0197.d030958 (_root_.GD.N0232.N0720.N1256.d015545 3 3) (fun _ hd => hd)



theorem d030960 :
    ENNReal.ofReal ((1 + Real.pi / 4) / 2) ≤
      ⨅ d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ, ⨅ _hd : Measurable d, ⨆ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 3 3 theta d /
          _root_.GD.N0232.N0720.N1080.d014197 3 3 theta (_root_.GD.N0232.N0720.N1080.d014175 3 3) := by
  simpa only [_root_.GD.N0230.N0611.d003517, _root_.GD.N0230.N0611.d003516, _root_.GD.N0232.N0720.N1256.d015545, Set.mem_setOf_eq,
    _root_.GD.N0232.N0720.N1228.d016744, _root_.GD.N0232.N0720.N1066.d014320,
    _root_.GD.N0232.N0720.N1080.d014199 3 3 (by norm_num) (by norm_num)] using
      _root_.GD.N0197.d030959

end
end GD.N0197

#print axioms _root_.GD.N0197.d030958
#print axioms _root_.GD.N0197.d030959
#print axioms _root_.GD.N0197.d030960
