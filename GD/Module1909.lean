import GD.Module1906
import GD.Module1908

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace GD.N0017
noncomputable section
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0012
open _root_.GD.N0022.N0255



theorem d030930 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1/1000 : ℝ) < ENNReal.ofReal _root_.GD.N0012.d030890 := by
  rw [_root_.GD.N0012.d030890, ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact ENNReal.add_lt_add_right ENNReal.ofReal_ne_top
    _root_.GD.N0010.d030858



theorem d030931 (hmargin : _root_.GD.N0012.d030892) :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1/1000 : ℝ) < _root_.GD.N0022.N0255.d030394 3 3 :=
  _root_.GD.N0017.d030930.trans_le (_root_.GD.N0012.d030904 hmargin)

theorem d030932 (hlower : _root_.GD.N0012.d030893) :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1/1000 : ℝ) < _root_.GD.N0022.N0255.d030394 3 3 :=
  _root_.GD.N0017.d030931 (_root_.GD.N0012.d030896 hlower)



theorem d030933 :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 + ENNReal.ofReal (1/1000 : ℝ) < _root_.GD.N0022.N0255.d030394 3 3 :=
  _root_.GD.N0017.d030932 _root_.GD.N0058.d030916

end
end GD.N0017

#print axioms _root_.GD.N0017.d030930
#print axioms _root_.GD.N0017.d030931
#print axioms _root_.GD.N0017.d030932
#print axioms _root_.GD.N0017.d030933
