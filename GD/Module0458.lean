import GD.Module0456

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32000
set_option maxHeartbeats 0

namespace GD.N0059

theorem d007121 : _root_.GD.N0059.d007011 _root_.GD.N0059.d007016 _root_.GD.N0059.d007017 _root_.GD.N0059.d007100 = true := by
  rw [_root_.GD.N0059.d007100, _root_.GD.N0059.d007012]
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    _root_.GD.N0059.d007025,
    _root_.GD.N0059.d007027,
    _root_.GD.N0059.d007029,
    _root_.GD.N0059.d007031,
    _root_.GD.N0059.d007033,
    _root_.GD.N0059.d007035,
    _root_.GD.N0059.d007037,
    _root_.GD.N0059.d007039,
    _root_.GD.N0059.d007041,
    _root_.GD.N0059.d007043,
    _root_.GD.N0059.d007045,
    _root_.GD.N0059.d007047,
    _root_.GD.N0059.d007049,
    _root_.GD.N0059.d007051,
    _root_.GD.N0059.d007053,
    _root_.GD.N0059.d007055,
    _root_.GD.N0059.d007057,
    _root_.GD.N0059.d007059,
    _root_.GD.N0059.d007061,
    _root_.GD.N0059.d007063,
    _root_.GD.N0059.d007065,
    _root_.GD.N0059.d007067,
    _root_.GD.N0059.d007069,
    _root_.GD.N0059.d007071,
    _root_.GD.N0059.d007073,
    _root_.GD.N0059.d007075,
    _root_.GD.N0059.d007077,
    _root_.GD.N0059.d007079,
    _root_.GD.N0059.d007081,
    _root_.GD.N0059.d007083,
    _root_.GD.N0059.d007085,
    _root_.GD.N0059.d007087,
    _root_.GD.N0059.d007089,
    _root_.GD.N0059.d007091,
    _root_.GD.N0059.d007093,
    _root_.GD.N0059.d007095,
    _root_.GD.N0059.d007097,
    _root_.GD.N0059.d007099]

theorem d007122 {c : _root_.GD.N0059.d006978} (hc : c ∈ _root_.GD.N0059.d007100) : c.d006994 :=
  _root_.GD.N0059.d007014 _root_.GD.N0059.d007121 hc

theorem d007123 {c : _root_.GD.N0059.d006978} (hc : c ∈ _root_.GD.N0059.d007100) :
    c.d006995 _root_.GD.N0059.d007016 _root_.GD.N0059.d007017 := _root_.GD.N0059.d007015 _root_.GD.N0059.d007121 hc

theorem d007124 : _root_.GD.N0059.d007100.length = 2393 := by decide

theorem d007125 :
    (_root_.GD.N0059.d007100.map _root_.GD.N0059.d006978.d006979).IsChain (· < ·) := by decide

theorem d007126 :
    _root_.GD.N0059.d007000 _root_.GD.N0059.d007100 = 1709368612906862813690857739743261132972032 := by decide

theorem d007127 :
    (1709368612906862813690857739743261132972032 : ℕ) * 52500 =
      32167 * 2 ^ 141 + 73343327468478394547600126986228910672674816 := by decide

theorem d007128 :
    32167 * 2 ^ 141 < _root_.GD.N0059.d007000 _root_.GD.N0059.d007100 * 52500 := by
  rw [_root_.GD.N0059.d007126]
  decide

end GD.N0059

#print axioms _root_.GD.N0059.d007121
#print axioms _root_.GD.N0059.d007122
#print axioms _root_.GD.N0059.d007123
#print axioms _root_.GD.N0059.d007124
#print axioms _root_.GD.N0059.d007125
#print axioms _root_.GD.N0059.d007126
#print axioms _root_.GD.N0059.d007127
#print axioms _root_.GD.N0059.d007128
